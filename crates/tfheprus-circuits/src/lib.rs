//! Plonky3 circuit mirrors for `tfheprus-core`.

pub mod range_check;

use p3_circuit::circuit::Circuit;
use p3_circuit::{CircuitBuilder, ExprId};
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks as P3Goldilocks;
use range_check::{range_check_expr, register_range_check_npo};
use tfheprus_core::ggsw::cmux;
use tfheprus_core::{
    bootstrap_without_keyswitch, decompose_polynomial, decomposition_gadget_factor,
    mod_switch_to_exponent, negacyclic_ntt, primitive_power_of_two_root, sample_extract_index_zero,
    EvaluationKey, GgswCiphertext, GlevCiphertext, GlweCiphertext, Goldilocks, LweCiphertext,
    Params, Polynomial, TestPolynomial, GOLDILOCKS_MODULUS, GOLDILOCKS_TWO_ADICITY,
};

pub const SELECTOR_DIGEST_WIDTH: usize = 4;

const SELECTOR_DIGEST_CHUNK_SIZE: usize = 64;
const SELECTOR_DIGEST_MIX_ROUNDS: usize = 3;
const SELECTOR_DIGEST_MDS: [[u64; SELECTOR_DIGEST_WIDTH]; SELECTOR_DIGEST_WIDTH] =
    [[2, 3, 5, 7], [7, 2, 3, 5], [5, 7, 2, 3], [3, 5, 7, 2]];

#[derive(Clone)]
struct GlweExpr {
    mask: Vec<Vec<ExprId>>,
    body: Vec<ExprId>,
}

#[derive(Clone)]
struct GlweNttExpr {
    mask: Vec<Vec<ExprId>>,
    body: Vec<ExprId>,
}

#[derive(Clone)]
struct GlevNttExpr {
    levels: Vec<GlweNttExpr>,
}

#[derive(Clone)]
struct GgswNttExpr {
    rows: Vec<GlevNttExpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolyMulInstance {
    pub lhs: Polynomial,
    pub rhs: Polynomial,
    pub product: Polynomial,
}

impl PolyMulInstance {
    pub fn new(lhs: Polynomial, rhs: Polynomial) -> Self {
        let product = lhs.mul(&rhs);
        Self { lhs, rhs, product }
    }

    pub fn degree(&self) -> usize {
        self.lhs.len()
    }

    pub fn public_inputs(&self) -> Vec<P3Goldilocks> {
        assert_eq!(self.lhs.len(), self.rhs.len());
        assert_eq!(self.lhs.len(), self.product.len());
        let mut inputs = Vec::with_capacity(self.lhs.len() * 3);
        inputs.extend(self.lhs.coeffs().iter().copied().map(core_to_p3));
        inputs.extend(self.rhs.coeffs().iter().copied().map(core_to_p3));
        inputs.extend(self.product.coeffs().iter().copied().map(core_to_p3));
        inputs
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct MulXaiInstance {
    pub input: Polynomial,
    pub exponent: usize,
    pub output: Polynomial,
}

impl MulXaiInstance {
    pub fn new(input: Polynomial, exponent: usize) -> Self {
        let output = input.mul_xai(exponent);
        Self {
            input,
            exponent,
            output,
        }
    }

    pub fn degree(&self) -> usize {
        self.input.len()
    }

    pub fn public_inputs(&self) -> Vec<P3Goldilocks> {
        assert_eq!(self.input.len(), self.output.len());
        let mut inputs = Vec::with_capacity(self.input.len() * 2);
        inputs.extend(self.input.coeffs().iter().copied().map(core_to_p3));
        inputs.extend(self.output.coeffs().iter().copied().map(core_to_p3));
        inputs
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SampleExtractInstance {
    pub glwe: GlweCiphertext,
    pub lwe: LweCiphertext,
}

impl SampleExtractInstance {
    pub fn new(glwe: GlweCiphertext) -> Self {
        let lwe = sample_extract_index_zero(&glwe);
        Self { glwe, lwe }
    }

    pub fn degree(&self) -> usize {
        self.glwe.body.len()
    }

    pub fn glwe_dimension(&self) -> usize {
        self.glwe.mask.len()
    }

    pub fn public_inputs(&self) -> Vec<P3Goldilocks> {
        let degree = self.degree();
        assert_eq!(self.lwe.mask.len(), self.glwe_dimension() * degree);

        let mut inputs = Vec::with_capacity(self.glwe_dimension() * degree * 2 + degree + 1);
        for poly in &self.glwe.mask {
            assert_eq!(poly.len(), degree);
            inputs.extend(poly.coeffs().iter().copied().map(core_to_p3));
        }
        inputs.extend(self.glwe.body.coeffs().iter().copied().map(core_to_p3));
        inputs.extend(self.lwe.mask.iter().copied().map(core_to_p3));
        inputs.push(core_to_p3(self.lwe.body));
        inputs
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActualPbsInstance {
    pub params: Params,
    pub input: LweCiphertext,
    pub test_polynomial: TestPolynomial,
    pub evaluation_key: EvaluationKey,
    pub output: LweCiphertext,
    pub initial_exponent: usize,
    pub mask_exponents: Vec<usize>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActualPbsStepInstance {
    pub params: Params,
    pub mask_value: Goldilocks,
    pub input_accumulator: GlweCiphertext,
    pub selector: GgswCiphertext,
    pub output_accumulator: GlweCiphertext,
    pub exponent: usize,
}

impl ActualPbsStepInstance {
    pub fn new(
        params: Params,
        mask_value: Goldilocks,
        input_accumulator: GlweCiphertext,
        selector: GgswCiphertext,
    ) -> Self {
        assert_eq!(input_accumulator.mask.len(), params.glwe_dimension);
        assert_eq!(input_accumulator.body.len(), params.polynomial_size);
        assert_eq!(selector.rows.len(), params.glwe_dimension + 1);

        let exponent = mod_switch_to_exponent(&params, mask_value);
        let rotated = input_accumulator.mul_xai(exponent);
        let output_accumulator = cmux(&params, &input_accumulator, &rotated, &selector);

        Self {
            params,
            mask_value,
            input_accumulator,
            selector,
            output_accumulator,
            exponent,
        }
    }

    pub fn public_inputs(&self) -> Vec<P3Goldilocks> {
        let mut inputs = Vec::new();
        inputs.push(core_to_p3(self.mask_value));
        append_glwe_public_inputs(&mut inputs, &self.input_accumulator);
        append_ggsw_ntt_public_inputs(&mut inputs, &self.selector);
        append_glwe_public_inputs(&mut inputs, &self.output_accumulator);
        inputs
    }

    pub fn private_inputs(&self) -> Vec<P3Goldilocks> {
        let mut inputs = Vec::new();
        append_actual_pbs_step_private_inputs(
            &self.params,
            self.mask_value,
            &self.input_accumulator,
            self.exponent,
            &mut inputs,
        );
        inputs
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActualPbsStepPrivateInstance {
    pub params: Params,
    pub mask_value: Goldilocks,
    pub input_accumulator: GlweCiphertext,
    pub selector: GgswCiphertext,
    pub selector_digest: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    pub output_accumulator: GlweCiphertext,
    pub exponent: usize,
}

impl ActualPbsStepPrivateInstance {
    pub fn new(
        params: Params,
        mask_value: Goldilocks,
        input_accumulator: GlweCiphertext,
        selector: GgswCiphertext,
    ) -> Self {
        assert_eq!(input_accumulator.mask.len(), params.glwe_dimension);
        assert_eq!(input_accumulator.body.len(), params.polynomial_size);
        assert_eq!(selector.rows.len(), params.glwe_dimension + 1);

        let exponent = mod_switch_to_exponent(&params, mask_value);
        let rotated = input_accumulator.mul_xai(exponent);
        let output_accumulator = cmux(&params, &input_accumulator, &rotated, &selector);
        let selector_digest = selector_ntt_digest(&selector);

        Self {
            params,
            mask_value,
            input_accumulator,
            selector,
            selector_digest,
            output_accumulator,
            exponent,
        }
    }

    pub fn public_inputs(&self) -> Vec<P3Goldilocks> {
        let mut inputs = Vec::new();
        inputs.push(core_to_p3(self.mask_value));
        append_glwe_public_inputs(&mut inputs, &self.input_accumulator);
        inputs.extend(self.selector_digest.iter().copied().map(core_to_p3));
        append_glwe_public_inputs(&mut inputs, &self.output_accumulator);
        inputs
    }

    pub fn private_inputs(&self) -> Vec<P3Goldilocks> {
        let mut inputs = Vec::new();
        append_ggsw_ntt_private_inputs(&mut inputs, &self.selector);
        append_actual_pbs_step_private_inputs(
            &self.params,
            self.mask_value,
            &self.input_accumulator,
            self.exponent,
            &mut inputs,
        );
        inputs
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActualPbsStepChainInstance {
    pub params: Params,
    pub mask_value: Goldilocks,
    pub input_accumulator: GlweCiphertext,
    pub selector: GgswCiphertext,
    pub bsk_digest_in: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    pub bsk_digest_out: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    pub mask_digest_in: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    pub mask_digest_out: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    pub output_accumulator: GlweCiphertext,
    pub exponent: usize,
}

impl ActualPbsStepChainInstance {
    pub fn new(
        params: Params,
        mask_value: Goldilocks,
        input_accumulator: GlweCiphertext,
        selector: GgswCiphertext,
        bsk_digest_in: [Goldilocks; SELECTOR_DIGEST_WIDTH],
        mask_digest_in: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    ) -> Self {
        assert_eq!(input_accumulator.mask.len(), params.glwe_dimension);
        assert_eq!(input_accumulator.body.len(), params.polynomial_size);
        assert_eq!(selector.rows.len(), params.glwe_dimension + 1);

        let exponent = mod_switch_to_exponent(&params, mask_value);
        let rotated = input_accumulator.mul_xai(exponent);
        let output_accumulator = cmux(&params, &input_accumulator, &rotated, &selector);
        let bsk_digest_out = pbs_bsk_digest_update(bsk_digest_in, &selector);
        let mask_digest_out = pbs_mask_digest_update(mask_digest_in, mask_value);

        Self {
            params,
            mask_value,
            input_accumulator,
            selector,
            bsk_digest_in,
            bsk_digest_out,
            mask_digest_in,
            mask_digest_out,
            output_accumulator,
            exponent,
        }
    }

    pub fn public_inputs(&self) -> Vec<P3Goldilocks> {
        let mut inputs = Vec::new();
        append_glwe_public_inputs(&mut inputs, &self.input_accumulator);
        append_digest_public_inputs(&mut inputs, &self.bsk_digest_in);
        append_digest_public_inputs(&mut inputs, &self.bsk_digest_out);
        append_digest_public_inputs(&mut inputs, &self.mask_digest_in);
        append_digest_public_inputs(&mut inputs, &self.mask_digest_out);
        append_glwe_public_inputs(&mut inputs, &self.output_accumulator);
        inputs
    }

    pub fn private_inputs(&self) -> Vec<P3Goldilocks> {
        let mut inputs = Vec::new();
        append_ggsw_ntt_private_inputs(&mut inputs, &self.selector);
        inputs.push(core_to_p3(self.mask_value));
        append_actual_pbs_step_private_inputs(
            &self.params,
            self.mask_value,
            &self.input_accumulator,
            self.exponent,
            &mut inputs,
        );
        inputs
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActualPbsChainChunkInstance {
    pub params: Params,
    pub mask_values: Vec<Goldilocks>,
    pub input_accumulator: GlweCiphertext,
    pub selectors: Vec<GgswCiphertext>,
    pub bsk_digest_in: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    pub bsk_digest_out: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    pub mask_digest_in: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    pub mask_digest_out: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    pub output_accumulator: GlweCiphertext,
    pub exponents: Vec<usize>,
}

impl ActualPbsChainChunkInstance {
    pub fn new(
        params: Params,
        mask_values: Vec<Goldilocks>,
        input_accumulator: GlweCiphertext,
        selectors: Vec<GgswCiphertext>,
        bsk_digest_in: [Goldilocks; SELECTOR_DIGEST_WIDTH],
        mask_digest_in: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    ) -> Self {
        assert!(!mask_values.is_empty());
        assert_eq!(mask_values.len(), selectors.len());
        assert_eq!(input_accumulator.mask.len(), params.glwe_dimension);
        assert_eq!(input_accumulator.body.len(), params.polynomial_size);
        for selector in &selectors {
            assert_eq!(selector.rows.len(), params.glwe_dimension + 1);
        }

        let mut acc = input_accumulator.clone();
        let mut bsk_digest = bsk_digest_in;
        let mut mask_digest = mask_digest_in;
        let mut exponents = Vec::with_capacity(mask_values.len());
        for (&mask_value, selector) in mask_values.iter().zip(selectors.iter()) {
            let exponent = mod_switch_to_exponent(&params, mask_value);
            let rotated = acc.mul_xai(exponent);
            acc = cmux(&params, &acc, &rotated, selector);
            bsk_digest = pbs_bsk_digest_update(bsk_digest, selector);
            mask_digest = pbs_mask_digest_update(mask_digest, mask_value);
            exponents.push(exponent);
        }

        Self {
            params,
            mask_values,
            input_accumulator,
            selectors,
            bsk_digest_in,
            bsk_digest_out: bsk_digest,
            mask_digest_in,
            mask_digest_out: mask_digest,
            output_accumulator: acc,
            exponents,
        }
    }

    pub fn step_count(&self) -> usize {
        self.mask_values.len()
    }

    pub fn public_inputs(&self) -> Vec<P3Goldilocks> {
        let mut inputs = Vec::new();
        append_glwe_public_inputs(&mut inputs, &self.input_accumulator);
        append_digest_public_inputs(&mut inputs, &self.bsk_digest_in);
        append_digest_public_inputs(&mut inputs, &self.bsk_digest_out);
        append_digest_public_inputs(&mut inputs, &self.mask_digest_in);
        append_digest_public_inputs(&mut inputs, &self.mask_digest_out);
        append_glwe_public_inputs(&mut inputs, &self.output_accumulator);
        inputs
    }

    pub fn private_inputs(&self) -> Vec<P3Goldilocks> {
        let mut inputs = Vec::new();
        let mut acc = self.input_accumulator.clone();
        for ((&mask_value, selector), &exponent) in self
            .mask_values
            .iter()
            .zip(self.selectors.iter())
            .zip(self.exponents.iter())
        {
            append_ggsw_ntt_private_inputs(&mut inputs, selector);
            inputs.push(core_to_p3(mask_value));
            append_actual_pbs_step_private_inputs(
                &self.params,
                mask_value,
                &acc,
                exponent,
                &mut inputs,
            );
            let rotated = acc.mul_xai(exponent);
            acc = cmux(&self.params, &acc, &rotated, selector);
        }
        inputs
    }
}

impl ActualPbsInstance {
    pub fn new(
        params: Params,
        input: LweCiphertext,
        test_polynomial: TestPolynomial,
        evaluation_key: EvaluationKey,
    ) -> Self {
        assert_eq!(input.mask.len(), params.lwe_dimension);
        assert_eq!(test_polynomial.poly.len(), params.polynomial_size);
        assert_eq!(evaluation_key.bootstrapping_key.len(), params.lwe_dimension);

        let body_exponent = mod_switch_to_exponent(&params, input.body);
        let initial_exponent =
            (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
        let mask_exponents = input
            .mask
            .iter()
            .map(|&value| mod_switch_to_exponent(&params, value))
            .collect::<Vec<_>>();
        assert!(
            mask_exponents.iter().any(|&exponent| exponent != 0),
            "actual PBS proof requires at least one nonzero mask rotation"
        );

        let output =
            bootstrap_without_keyswitch(&params, &evaluation_key, &input, &test_polynomial);

        Self {
            params,
            input,
            test_polynomial,
            evaluation_key,
            output,
            initial_exponent,
            mask_exponents,
        }
    }

    pub fn nonzero_rotation_count(&self) -> usize {
        self.mask_exponents
            .iter()
            .filter(|&&exponent| exponent != 0)
            .count()
    }

    pub fn public_inputs(&self) -> Vec<P3Goldilocks> {
        assert_eq!(self.input.mask.len(), self.params.lwe_dimension);
        assert_eq!(self.test_polynomial.poly.len(), self.params.polynomial_size);
        assert_eq!(
            self.output.mask.len(),
            self.params.glwe_dimension * self.params.polynomial_size
        );

        let mut inputs = Vec::new();
        inputs.extend(self.input.mask.iter().copied().map(core_to_p3));
        inputs.push(core_to_p3(self.input.body));
        append_polynomial_public_inputs(&mut inputs, &self.test_polynomial.poly);
        append_evaluation_key_ntt_public_inputs(&mut inputs, &self.evaluation_key);
        inputs.extend(self.output.mask.iter().copied().map(core_to_p3));
        inputs.push(core_to_p3(self.output.body));
        inputs
    }

    pub fn private_inputs(&self) -> Vec<P3Goldilocks> {
        let mut inputs = Vec::new();
        append_torus_decomposition_private_inputs(self.input.body, &mut inputs);
        let mut acc = GlweCiphertext::trivial(
            self.test_polynomial.poly.mul_xai(self.initial_exponent),
            self.params.glwe_dimension,
        );

        for ((&exponent, selector), &mask_value) in self
            .mask_exponents
            .iter()
            .zip(self.evaluation_key.bootstrapping_key.iter())
            .zip(self.input.mask.iter())
        {
            append_torus_decomposition_private_inputs(mask_value, &mut inputs);
            let rotated = acc.mul_xai(exponent);
            let diff = rotated.sub(&acc);
            for poly in &diff.mask {
                append_decomposition_private_inputs(&self.params, poly, &mut inputs);
            }
            append_decomposition_private_inputs(&self.params, &diff.body, &mut inputs);
            acc = cmux(&self.params, &acc, &rotated, selector);
        }

        inputs
    }
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct ActualPbsCircuitProfile {
    pub cmux_count: usize,
    pub nonzero_rotation_count: usize,
    pub bootstrapping_key_public_inputs: usize,
    pub public_inputs: usize,
    pub private_inputs: usize,
    pub torus_private_inputs: usize,
    pub decomposition_coefficients: usize,
    pub decomposition_private_inputs_per_coeff: usize,
    pub approximate_decomposition: bool,
}

impl ActualPbsCircuitProfile {
    pub fn estimate(params: &Params, nonzero_rotation_count: usize) -> Self {
        let glwe_polynomial_count = params.glwe_dimension + 1;
        let bootstrapping_key_public_inputs = params.lwe_dimension
            * glwe_polynomial_count
            * params.decomposition_level_count
            * glwe_polynomial_count
            * params.polynomial_size;
        let public_inputs = params.lwe_dimension
            + 1
            + params.polynomial_size
            + bootstrapping_key_public_inputs
            + params.glwe_dimension * params.polynomial_size
            + 1;

        let approximate_decomposition = !uses_exact_binary_decomposition(params);
        let decomposition_private_inputs_per_coeff =
            params.decomposition_level_count + if approximate_decomposition { 2 } else { 0 };
        let decomposition_coefficients =
            params.lwe_dimension * glwe_polynomial_count * params.polynomial_size;
        let torus_private_inputs = 64 * (params.lwe_dimension + 1);
        let private_inputs = torus_private_inputs
            + decomposition_coefficients * decomposition_private_inputs_per_coeff;

        Self {
            cmux_count: params.lwe_dimension,
            nonzero_rotation_count,
            bootstrapping_key_public_inputs,
            public_inputs,
            private_inputs,
            torus_private_inputs,
            decomposition_coefficients,
            decomposition_private_inputs_per_coeff,
            approximate_decomposition,
        }
    }

    pub fn from_instance(instance: &ActualPbsInstance) -> Self {
        Self::estimate(&instance.params, instance.nonzero_rotation_count())
    }
}

pub fn build_poly_mul_circuit(
    degree: usize,
) -> Result<Circuit<P3Goldilocks>, p3_circuit::CircuitError> {
    assert!(degree > 0);
    assert!(degree.is_power_of_two());

    let mut builder = CircuitBuilder::<P3Goldilocks>::new();
    let lhs = builder.alloc_public_inputs(degree, "poly_mul_lhs");
    let rhs = builder.alloc_public_inputs(degree, "poly_mul_rhs");
    let expected = builder.alloc_public_inputs(degree, "poly_mul_expected");

    let computed = poly_mul_expr(&mut builder, &lhs, &rhs);

    for (actual, expected) in computed.into_iter().zip(expected) {
        builder.connect(actual, expected);
    }

    Ok(builder.build()?)
}

pub fn build_mul_xai_circuit(
    degree: usize,
    exponent: usize,
) -> Result<Circuit<P3Goldilocks>, p3_circuit::CircuitError> {
    assert!(degree > 0);
    assert!(degree.is_power_of_two());

    let mut builder = CircuitBuilder::<P3Goldilocks>::new();
    let input = builder.alloc_public_inputs(degree, "mul_xai_input");
    let expected = builder.alloc_public_inputs(degree, "mul_xai_expected");

    let zero = builder.define_const(P3Goldilocks::ZERO);
    let mut computed = vec![zero; degree];
    let modulus = 2 * degree;
    let exponent = exponent % modulus;

    for (i, &cell) in input.iter().enumerate() {
        let target = (i + exponent) % modulus;
        if target < degree {
            computed[target] = builder.add(computed[target], cell);
        } else {
            computed[target - degree] = builder.sub(computed[target - degree], cell);
        }
    }

    for (actual, expected) in computed.into_iter().zip(expected) {
        builder.connect(actual, expected);
    }

    Ok(builder.build()?)
}

pub fn build_sample_extract_circuit(
    glwe_dimension: usize,
    degree: usize,
) -> Result<Circuit<P3Goldilocks>, p3_circuit::CircuitError> {
    assert!(glwe_dimension > 0);
    assert!(degree > 0);
    assert!(degree.is_power_of_two());

    let mut builder = CircuitBuilder::<P3Goldilocks>::new();
    let mut glwe_masks = Vec::with_capacity(glwe_dimension);
    for _ in 0..glwe_dimension {
        glwe_masks.push(builder.alloc_public_inputs(degree, "sample_extract_mask"));
    }
    let glwe_body = builder.alloc_public_inputs(degree, "sample_extract_body");
    let lwe_mask = builder.alloc_public_inputs(glwe_dimension * degree, "sample_extract_lwe_mask");
    let lwe_body = builder.alloc_public_inputs(1, "sample_extract_lwe_body");

    let zero = builder.define_const(P3Goldilocks::ZERO);
    for (row, poly) in glwe_masks.iter().enumerate() {
        let offset = row * degree;
        builder.connect(poly[0], lwe_mask[offset]);
        for i in 1..degree {
            let negated = builder.sub(zero, poly[degree - i]);
            builder.connect(negated, lwe_mask[offset + i]);
        }
    }
    builder.connect(glwe_body[0], lwe_body[0]);

    Ok(builder.build()?)
}

pub fn build_actual_pbs_circuit(
    instance: &ActualPbsInstance,
) -> Result<Circuit<P3Goldilocks>, p3_circuit::CircuitError> {
    assert!(instance.params.polynomial_size > 0);
    assert!(instance.params.polynomial_size.is_power_of_two());
    assert!(instance.params.lwe_dimension > 0);
    assert!(instance.params.glwe_dimension > 0);
    assert_eq!(
        instance.evaluation_key.bootstrapping_key.len(),
        instance.params.lwe_dimension
    );

    let mut builder = CircuitBuilder::<P3Goldilocks>::new();
    register_range_check_npo(&mut builder, instance.params.decomposition_base_log);
    if let Some(error_bits) = decomposition_error_bits(&instance.params) {
        register_range_check_npo(&mut builder, error_bits);
    }
    let input_mask = builder.alloc_public_inputs(instance.params.lwe_dimension, "actual_pbs_mask");
    let input_body = builder.alloc_public_inputs(1, "actual_pbs_body");
    let test_poly =
        builder.alloc_public_inputs(instance.params.polynomial_size, "actual_pbs_test_poly");
    let bootstrapping_key = (0..instance.params.lwe_dimension)
        .map(|_| alloc_public_ggsw_ntt(&mut builder, &instance.params))
        .collect::<Vec<_>>();
    let output_mask = builder.alloc_public_inputs(
        instance.params.glwe_dimension * instance.params.polynomial_size,
        "actual_pbs_output_mask",
    );
    let output_body = builder.alloc_public_inputs(1, "actual_pbs_output_body");

    let body_exponent_bits = mod_switch_exponent_bits_expr(
        &mut builder,
        input_body[0],
        instance.params.exponent_modulus(),
    );
    let initial_exponent_bits =
        negate_bits_mod_power_of_two_expr(&mut builder, &body_exponent_bits);

    let mut acc = GlweExpr {
        mask: vec![
            vec![builder.define_const(P3Goldilocks::ZERO); instance.params.polynomial_size];
            instance.params.glwe_dimension
        ],
        body: mul_xai_by_bits_expr(&mut builder, &test_poly, &initial_exponent_bits),
    };

    for (&mask_cell, selector) in input_mask.iter().zip(bootstrapping_key.iter()) {
        let exponent_bits = mod_switch_exponent_bits_expr(
            &mut builder,
            mask_cell,
            instance.params.exponent_modulus(),
        );
        let rotated = glwe_mul_xai_by_bits_expr(&mut builder, &acc, &exponent_bits);
        acc = cmux_expr(&mut builder, &instance.params, &acc, &rotated, selector);
    }

    connect_sample_extract(&mut builder, &acc, &output_mask, output_body[0]);

    Ok(builder.build()?)
}

pub fn build_actual_pbs_step_circuit(
    instance: &ActualPbsStepInstance,
) -> Result<Circuit<P3Goldilocks>, p3_circuit::CircuitError> {
    assert!(instance.params.polynomial_size > 0);
    assert!(instance.params.polynomial_size.is_power_of_two());
    assert!(instance.params.glwe_dimension > 0);

    let mut builder = CircuitBuilder::<P3Goldilocks>::new();
    register_range_check_npo(&mut builder, instance.params.decomposition_base_log);
    if let Some(error_bits) = decomposition_error_bits(&instance.params) {
        register_range_check_npo(&mut builder, error_bits);
    }

    let mask_value = builder.alloc_public_inputs(1, "actual_pbs_step_mask");
    let input_accumulator = alloc_public_glwe(&mut builder, &instance.params);
    let selector = alloc_public_ggsw_ntt(&mut builder, &instance.params);
    let output_accumulator = alloc_public_glwe(&mut builder, &instance.params);

    let exponent_bits = mod_switch_exponent_bits_expr(
        &mut builder,
        mask_value[0],
        instance.params.exponent_modulus(),
    );
    let rotated = glwe_mul_xai_by_bits_expr(&mut builder, &input_accumulator, &exponent_bits);
    let computed = cmux_expr(
        &mut builder,
        &instance.params,
        &input_accumulator,
        &rotated,
        &selector,
    );
    connect_glwe(&mut builder, &computed, &output_accumulator);

    Ok(builder.build()?)
}

pub fn build_actual_pbs_step_private_circuit(
    instance: &ActualPbsStepPrivateInstance,
) -> Result<Circuit<P3Goldilocks>, p3_circuit::CircuitError> {
    assert!(instance.params.polynomial_size > 0);
    assert!(instance.params.polynomial_size.is_power_of_two());
    assert!(instance.params.glwe_dimension > 0);

    let mut builder = CircuitBuilder::<P3Goldilocks>::new();
    register_range_check_npo(&mut builder, instance.params.decomposition_base_log);
    if let Some(error_bits) = decomposition_error_bits(&instance.params) {
        register_range_check_npo(&mut builder, error_bits);
    }

    let mask_value = builder.alloc_public_inputs(1, "actual_pbs_step_private_mask");
    let input_accumulator = alloc_public_glwe(&mut builder, &instance.params);
    let selector_digest =
        builder.alloc_public_inputs(SELECTOR_DIGEST_WIDTH, "actual_pbs_step_selector_digest");
    let output_accumulator = alloc_public_glwe(&mut builder, &instance.params);
    let selector = alloc_private_ggsw_ntt(&mut builder, &instance.params);

    let computed_digest = selector_digest_expr(&mut builder, &selector);
    for (&computed, &expected) in computed_digest.iter().zip(selector_digest.iter()) {
        builder.connect(computed, expected);
    }

    let exponent_bits = mod_switch_exponent_bits_expr(
        &mut builder,
        mask_value[0],
        instance.params.exponent_modulus(),
    );
    let rotated = glwe_mul_xai_by_bits_expr(&mut builder, &input_accumulator, &exponent_bits);
    let computed = cmux_expr(
        &mut builder,
        &instance.params,
        &input_accumulator,
        &rotated,
        &selector,
    );
    connect_glwe(&mut builder, &computed, &output_accumulator);

    Ok(builder.build()?)
}

pub fn build_actual_pbs_step_chain_circuit(
    instance: &ActualPbsStepChainInstance,
) -> Result<Circuit<P3Goldilocks>, p3_circuit::CircuitError> {
    assert!(instance.params.polynomial_size > 0);
    assert!(instance.params.polynomial_size.is_power_of_two());
    assert!(instance.params.glwe_dimension > 0);

    let mut builder = CircuitBuilder::<P3Goldilocks>::new();
    register_range_check_npo(&mut builder, instance.params.decomposition_base_log);
    if let Some(error_bits) = decomposition_error_bits(&instance.params) {
        register_range_check_npo(&mut builder, error_bits);
    }

    let input_accumulator = alloc_public_glwe(&mut builder, &instance.params);
    let bsk_digest_in = alloc_public_digest(&mut builder, "actual_pbs_step_bsk_digest_in");
    let bsk_digest_out = alloc_public_digest(&mut builder, "actual_pbs_step_bsk_digest_out");
    let mask_digest_in = alloc_public_digest(&mut builder, "actual_pbs_step_mask_digest_in");
    let mask_digest_out = alloc_public_digest(&mut builder, "actual_pbs_step_mask_digest_out");
    let output_accumulator = alloc_public_glwe(&mut builder, &instance.params);
    let selector = alloc_private_ggsw_ntt(&mut builder, &instance.params);
    let mask_value = builder.alloc_private_input("actual_pbs_step_private_mask_value");

    let computed_bsk_digest_out =
        digest_update_expr(&mut builder, bsk_digest_in, ggsw_ntt_expr_values(&selector));
    connect_digest(&mut builder, &computed_bsk_digest_out, &bsk_digest_out);
    let computed_mask_digest_out = digest_update_expr(&mut builder, mask_digest_in, [mask_value]);
    connect_digest(&mut builder, &computed_mask_digest_out, &mask_digest_out);

    let exponent_bits =
        mod_switch_exponent_bits_expr(&mut builder, mask_value, instance.params.exponent_modulus());
    let rotated = glwe_mul_xai_by_bits_expr(&mut builder, &input_accumulator, &exponent_bits);
    let computed = cmux_expr(
        &mut builder,
        &instance.params,
        &input_accumulator,
        &rotated,
        &selector,
    );
    connect_glwe(&mut builder, &computed, &output_accumulator);

    Ok(builder.build()?)
}

pub fn build_actual_pbs_chain_chunk_circuit(
    instance: &ActualPbsChainChunkInstance,
) -> Result<Circuit<P3Goldilocks>, p3_circuit::CircuitError> {
    assert!(instance.params.polynomial_size > 0);
    assert!(instance.params.polynomial_size.is_power_of_two());
    assert!(instance.params.glwe_dimension > 0);
    assert!(!instance.mask_values.is_empty());
    assert_eq!(instance.mask_values.len(), instance.selectors.len());

    let mut builder = CircuitBuilder::<P3Goldilocks>::new();
    register_range_check_npo(&mut builder, instance.params.decomposition_base_log);
    if let Some(error_bits) = decomposition_error_bits(&instance.params) {
        register_range_check_npo(&mut builder, error_bits);
    }

    let mut acc = alloc_public_glwe(&mut builder, &instance.params);
    let mut bsk_digest = alloc_public_digest(&mut builder, "actual_pbs_chunk_bsk_digest_in");
    let bsk_digest_out = alloc_public_digest(&mut builder, "actual_pbs_chunk_bsk_digest_out");
    let mut mask_digest = alloc_public_digest(&mut builder, "actual_pbs_chunk_mask_digest_in");
    let mask_digest_out = alloc_public_digest(&mut builder, "actual_pbs_chunk_mask_digest_out");
    let output_accumulator = alloc_public_glwe(&mut builder, &instance.params);

    for _ in 0..instance.step_count() {
        let selector = alloc_private_ggsw_ntt(&mut builder, &instance.params);
        let mask_value = builder.alloc_private_input("actual_pbs_chunk_private_mask_value");
        bsk_digest = digest_update_expr(&mut builder, bsk_digest, ggsw_ntt_expr_values(&selector));
        mask_digest = digest_update_expr(&mut builder, mask_digest, [mask_value]);

        let exponent_bits = mod_switch_exponent_bits_expr(
            &mut builder,
            mask_value,
            instance.params.exponent_modulus(),
        );
        let rotated = glwe_mul_xai_by_bits_expr(&mut builder, &acc, &exponent_bits);
        acc = cmux_expr(&mut builder, &instance.params, &acc, &rotated, &selector);
    }

    connect_digest(&mut builder, &bsk_digest, &bsk_digest_out);
    connect_digest(&mut builder, &mask_digest, &mask_digest_out);
    connect_glwe(&mut builder, &acc, &output_accumulator);

    Ok(builder.build()?)
}

pub fn core_to_p3(value: Goldilocks) -> P3Goldilocks {
    P3Goldilocks::from_u64(value.value())
}

pub fn selector_ntt_digest(ct: &GgswCiphertext) -> [Goldilocks; SELECTOR_DIGEST_WIDTH] {
    selector_digest_from_values(ggsw_ntt_values(ct))
}

pub fn pbs_bsk_digest_initial() -> [Goldilocks; SELECTOR_DIGEST_WIDTH] {
    digest_initial_state(0x6273_6b5f_6368_6169)
}

pub fn pbs_mask_digest_initial() -> [Goldilocks; SELECTOR_DIGEST_WIDTH] {
    digest_initial_state(0x6d61_736b_6368_6169)
}

pub fn pbs_bsk_digest_update(
    previous: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    selector: &GgswCiphertext,
) -> [Goldilocks; SELECTOR_DIGEST_WIDTH] {
    digest_update_from_values(previous, ggsw_ntt_values(selector))
}

pub fn pbs_mask_digest_update(
    previous: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    mask_value: Goldilocks,
) -> [Goldilocks; SELECTOR_DIGEST_WIDTH] {
    digest_update_from_values(previous, [mask_value])
}

fn append_polynomial_public_inputs(inputs: &mut Vec<P3Goldilocks>, poly: &Polynomial) {
    inputs.extend(poly.coeffs().iter().copied().map(core_to_p3));
}

fn append_glwe_public_inputs(inputs: &mut Vec<P3Goldilocks>, ct: &GlweCiphertext) {
    for poly in &ct.mask {
        append_polynomial_public_inputs(inputs, poly);
    }
    append_polynomial_public_inputs(inputs, &ct.body);
}

fn append_digest_public_inputs(
    inputs: &mut Vec<P3Goldilocks>,
    digest: &[Goldilocks; SELECTOR_DIGEST_WIDTH],
) {
    inputs.extend(digest.iter().copied().map(core_to_p3));
}

fn append_polynomial_ntt_public_inputs(inputs: &mut Vec<P3Goldilocks>, poly: &Polynomial) {
    inputs.extend(negacyclic_ntt(poly.coeffs()).into_iter().map(core_to_p3));
}

fn append_glwe_ntt_public_inputs(inputs: &mut Vec<P3Goldilocks>, ct: &GlweCiphertext) {
    for poly in &ct.mask {
        append_polynomial_ntt_public_inputs(inputs, poly);
    }
    append_polynomial_ntt_public_inputs(inputs, &ct.body);
}

fn append_glev_ntt_public_inputs(inputs: &mut Vec<P3Goldilocks>, ct: &GlevCiphertext) {
    for level in &ct.levels {
        append_glwe_ntt_public_inputs(inputs, level);
    }
}

fn append_ggsw_ntt_public_inputs(inputs: &mut Vec<P3Goldilocks>, ct: &GgswCiphertext) {
    for row in &ct.rows {
        append_glev_ntt_public_inputs(inputs, row);
    }
}

fn append_ggsw_ntt_private_inputs(inputs: &mut Vec<P3Goldilocks>, ct: &GgswCiphertext) {
    inputs.extend(ggsw_ntt_values(ct).into_iter().map(core_to_p3));
}

fn append_evaluation_key_ntt_public_inputs(inputs: &mut Vec<P3Goldilocks>, ek: &EvaluationKey) {
    for ggsw in &ek.bootstrapping_key {
        append_ggsw_ntt_public_inputs(inputs, ggsw);
    }
}

fn append_actual_pbs_step_private_inputs(
    params: &Params,
    mask_value: Goldilocks,
    input_accumulator: &GlweCiphertext,
    exponent: usize,
    inputs: &mut Vec<P3Goldilocks>,
) {
    append_torus_decomposition_private_inputs(mask_value, inputs);
    let rotated = input_accumulator.mul_xai(exponent);
    let diff = rotated.sub(input_accumulator);
    for poly in &diff.mask {
        append_decomposition_private_inputs(params, poly, inputs);
    }
    append_decomposition_private_inputs(params, &diff.body, inputs);
}

fn ggsw_ntt_values(ct: &GgswCiphertext) -> Vec<Goldilocks> {
    let mut values = Vec::new();
    for row in &ct.rows {
        for level in &row.levels {
            for poly in &level.mask {
                values.extend(negacyclic_ntt(poly.coeffs()));
            }
            values.extend(negacyclic_ntt(level.body.coeffs()));
        }
    }
    values
}

fn selector_digest_from_values(
    values: impl IntoIterator<Item = Goldilocks>,
) -> [Goldilocks; SELECTOR_DIGEST_WIDTH] {
    digest_update_from_values(core::array::from_fn(selector_digest_initial_state), values)
}

fn digest_update_from_values(
    mut state: [Goldilocks; SELECTOR_DIGEST_WIDTH],
    values: impl IntoIterator<Item = Goldilocks>,
) -> [Goldilocks; SELECTOR_DIGEST_WIDTH] {
    let mut count = 0usize;
    for value in values {
        selector_digest_absorb(&mut state, count, value);
        count += 1;
        if count.is_multiple_of(SELECTOR_DIGEST_CHUNK_SIZE) {
            selector_digest_mix(&mut state, count);
        }
    }
    state[0] += Goldilocks::from_u64(count as u64);
    selector_digest_mix(&mut state, count);
    state
}

fn selector_digest_absorb(
    state: &mut [Goldilocks; SELECTOR_DIGEST_WIDTH],
    index: usize,
    value: Goldilocks,
) {
    let lane = index % SELECTOR_DIGEST_WIDTH;
    state[lane] += value * selector_digest_absorb_coeff(index, lane);
}

fn selector_digest_mix(state: &mut [Goldilocks; SELECTOR_DIGEST_WIDTH], domain: usize) {
    for round in 0..SELECTOR_DIGEST_MIX_ROUNDS {
        let powered = core::array::from_fn(|lane| {
            (state[lane] + selector_digest_round_const(domain, round, lane)).pow(7)
        });
        *state = selector_digest_mds_native(&powered);
    }
}

fn selector_digest_mds_native(
    values: &[Goldilocks; SELECTOR_DIGEST_WIDTH],
) -> [Goldilocks; SELECTOR_DIGEST_WIDTH] {
    core::array::from_fn(|row| {
        values
            .iter()
            .zip(SELECTOR_DIGEST_MDS[row].iter())
            .map(|(&value, &coeff)| value * Goldilocks::from_u64(coeff))
            .sum()
    })
}

fn digest_initial_state(tag: u64) -> [Goldilocks; SELECTOR_DIGEST_WIDTH] {
    core::array::from_fn(|lane| selector_digest_const(tag, lane, 0, 0))
}

fn selector_digest_initial_state(lane: usize) -> Goldilocks {
    selector_digest_const(0x5446_4845_7072_7573, lane, 0, 0)
}

fn selector_digest_absorb_coeff(index: usize, lane: usize) -> Goldilocks {
    selector_digest_const(0x0062_736b_5f6e_7474, index, lane, 0)
}

fn selector_digest_round_const(domain: usize, round: usize, lane: usize) -> Goldilocks {
    selector_digest_const(0x7062_735f_7374_6570, domain, round, lane)
}

fn selector_digest_const(tag: u64, a: usize, b: usize, c: usize) -> Goldilocks {
    let raw = tag as u128
        + (a as u128 + 1) * 0x9e37_79b9_7f4a_7c15u128
        + (b as u128 + 1) * 0xbf58_476d_1ce4_e5b9u128
        + (c as u128 + 1) * 0x94d0_49bb_1331_11ebu128;
    Goldilocks::from_u64((raw % GOLDILOCKS_MODULUS as u128) as u64)
}

fn append_decomposition_private_inputs(
    params: &Params,
    poly: &Polynomial,
    inputs: &mut Vec<P3Goldilocks>,
) {
    let digits = decompose_polynomial(params, poly);
    for coeff_index in 0..poly.len() {
        let mut reconstructed = Goldilocks::ZERO;
        for (level_index, digit_poly) in digits.iter().enumerate() {
            let signed_digit = digit_poly[coeff_index];
            inputs.push(core_to_p3(private_digit_input(params, signed_digit)));
            reconstructed += signed_digit * decomposition_gadget_factor(params, level_index);
        }
        if decomposition_error_bits(params).is_some() {
            let error = poly[coeff_index] - reconstructed;
            let (magnitude, sign_bit) = signed_magnitude(error);
            inputs.push(core_to_p3(magnitude));
            inputs.push(P3Goldilocks::from_u64(sign_bit));
        }
    }
}

fn append_torus_decomposition_private_inputs(value: Goldilocks, inputs: &mut Vec<P3Goldilocks>) {
    for bit_index in 0..64 {
        let bit = (value.value() >> bit_index) & 1;
        inputs.push(P3Goldilocks::from_u64(bit));
    }
}

fn private_digit_input(params: &Params, signed_digit: Goldilocks) -> Goldilocks {
    if uses_exact_binary_decomposition(params) {
        signed_digit
    } else {
        let half_base = 1u64 << (params.decomposition_base_log - 1);
        let signed = small_signed_value(signed_digit);
        Goldilocks::from_u64((signed + half_base as i64) as u64)
    }
}

fn small_signed_value(value: Goldilocks) -> i64 {
    let canonical = value.value();
    if canonical <= i64::MAX as u64 {
        canonical as i64
    } else {
        -((GOLDILOCKS_MODULUS - canonical) as i64)
    }
}

fn signed_magnitude(value: Goldilocks) -> (Goldilocks, u64) {
    let canonical = value.value();
    if canonical <= GOLDILOCKS_MODULUS / 2 {
        (value, 0)
    } else {
        (Goldilocks::from_u64(GOLDILOCKS_MODULUS - canonical), 1)
    }
}

fn uses_exact_binary_decomposition(params: &Params) -> bool {
    params.decomposition_base_log * params.decomposition_level_count == 64
}

fn decomposition_error_bits(params: &Params) -> Option<usize> {
    if uses_exact_binary_decomposition(params) {
        None
    } else {
        let dropped_bits = 64 - params.decomposition_base_log * params.decomposition_level_count;
        Some((dropped_bits + 2).min(63))
    }
}

fn alloc_public_ggsw_ntt(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
) -> GgswNttExpr {
    let rows = (0..=params.glwe_dimension)
        .map(|_| alloc_public_glev_ntt(builder, params))
        .collect();
    GgswNttExpr { rows }
}

fn alloc_private_ggsw_ntt(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
) -> GgswNttExpr {
    let rows = (0..=params.glwe_dimension)
        .map(|_| alloc_private_glev_ntt(builder, params))
        .collect();
    GgswNttExpr { rows }
}

fn alloc_public_glwe(builder: &mut CircuitBuilder<P3Goldilocks>, params: &Params) -> GlweExpr {
    let mask = (0..params.glwe_dimension)
        .map(|_| builder.alloc_public_inputs(params.polynomial_size, "actual_pbs_glwe_mask"))
        .collect();
    let body = builder.alloc_public_inputs(params.polynomial_size, "actual_pbs_glwe_body");
    GlweExpr { mask, body }
}

fn alloc_public_digest(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    label: &'static str,
) -> [ExprId; SELECTOR_DIGEST_WIDTH] {
    builder.alloc_public_input_array(label)
}

fn alloc_public_glev_ntt(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
) -> GlevNttExpr {
    let levels = (0..params.decomposition_level_count)
        .map(|_| alloc_public_glwe_ntt(builder, params))
        .collect();
    GlevNttExpr { levels }
}

fn alloc_private_glev_ntt(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
) -> GlevNttExpr {
    let levels = (0..params.decomposition_level_count)
        .map(|_| alloc_private_glwe_ntt(builder, params))
        .collect();
    GlevNttExpr { levels }
}

fn alloc_public_glwe_ntt(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
) -> GlweNttExpr {
    let mask = (0..params.glwe_dimension)
        .map(|_| builder.alloc_public_inputs(params.polynomial_size, "actual_pbs_glwe_mask_ntt"))
        .collect();
    let body = builder.alloc_public_inputs(params.polynomial_size, "actual_pbs_glwe_body_ntt");
    GlweNttExpr { mask, body }
}

fn alloc_private_glwe_ntt(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
) -> GlweNttExpr {
    let mask = (0..params.glwe_dimension)
        .map(|_| builder.alloc_private_inputs(params.polynomial_size, "actual_pbs_glwe_mask_ntt"))
        .collect();
    let body = builder.alloc_private_inputs(params.polynomial_size, "actual_pbs_glwe_body_ntt");
    GlweNttExpr { mask, body }
}

fn connect_sample_extract(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    ct: &GlweExpr,
    output_mask: &[ExprId],
    output_body: ExprId,
) {
    let degree = ct.body.len();
    for (row, poly) in ct.mask.iter().enumerate() {
        let offset = row * degree;
        builder.connect(poly[0], output_mask[offset]);
        for i in 1..degree {
            let negated = sub_from_zero(builder, poly[degree - i]);
            builder.connect(negated, output_mask[offset + i]);
        }
    }
    builder.connect(ct.body[0], output_body);
}

fn connect_glwe(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    actual: &GlweExpr,
    expected: &GlweExpr,
) {
    for (actual_poly, expected_poly) in actual.mask.iter().zip(expected.mask.iter()) {
        for (&actual_coeff, &expected_coeff) in actual_poly.iter().zip(expected_poly.iter()) {
            builder.connect(actual_coeff, expected_coeff);
        }
    }
    for (&actual_coeff, &expected_coeff) in actual.body.iter().zip(expected.body.iter()) {
        builder.connect(actual_coeff, expected_coeff);
    }
}

fn connect_digest(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    actual: &[ExprId; SELECTOR_DIGEST_WIDTH],
    expected: &[ExprId; SELECTOR_DIGEST_WIDTH],
) {
    for (&actual_limb, &expected_limb) in actual.iter().zip(expected.iter()) {
        builder.connect(actual_limb, expected_limb);
    }
}

fn selector_digest_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    selector: &GgswNttExpr,
) -> [ExprId; SELECTOR_DIGEST_WIDTH] {
    let state = core::array::from_fn(|lane| {
        builder.define_const(core_to_p3(selector_digest_initial_state(lane)))
    });
    digest_update_expr(builder, state, ggsw_ntt_expr_values(selector))
}

fn digest_update_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    mut state: [ExprId; SELECTOR_DIGEST_WIDTH],
    values: impl IntoIterator<Item = ExprId>,
) -> [ExprId; SELECTOR_DIGEST_WIDTH] {
    let mut count = 0usize;

    for value in values {
        selector_digest_absorb_expr(builder, &mut state, count, value);
        count += 1;
        if count.is_multiple_of(SELECTOR_DIGEST_CHUNK_SIZE) {
            selector_digest_mix_expr(builder, &mut state, count);
        }
    }

    let count_const = builder.define_const(core_to_p3(Goldilocks::from_u64(count as u64)));
    state[0] = builder.add(state[0], count_const);
    selector_digest_mix_expr(builder, &mut state, count);
    state
}

fn ggsw_ntt_expr_values(selector: &GgswNttExpr) -> Vec<ExprId> {
    let mut values = Vec::new();
    for row in &selector.rows {
        for level in &row.levels {
            for poly in &level.mask {
                values.extend(poly.iter().copied());
            }
            values.extend(level.body.iter().copied());
        }
    }
    values
}

fn selector_digest_absorb_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    state: &mut [ExprId; SELECTOR_DIGEST_WIDTH],
    index: usize,
    value: ExprId,
) {
    let lane = index % SELECTOR_DIGEST_WIDTH;
    let term = mul_const_expr(builder, value, selector_digest_absorb_coeff(index, lane));
    state[lane] = builder.add(state[lane], term);
}

fn selector_digest_mix_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    state: &mut [ExprId; SELECTOR_DIGEST_WIDTH],
    domain: usize,
) {
    for round in 0..SELECTOR_DIGEST_MIX_ROUNDS {
        let powered = core::array::from_fn(|lane| {
            let round_const =
                builder.define_const(core_to_p3(selector_digest_round_const(domain, round, lane)));
            let shifted = builder.add(state[lane], round_const);
            pow7_expr(builder, shifted)
        });
        *state = selector_digest_mds_expr(builder, &powered);
    }
}

fn selector_digest_mds_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    values: &[ExprId; SELECTOR_DIGEST_WIDTH],
) -> [ExprId; SELECTOR_DIGEST_WIDTH] {
    core::array::from_fn(|row| {
        let zero = builder.define_const(P3Goldilocks::ZERO);
        values
            .iter()
            .zip(SELECTOR_DIGEST_MDS[row].iter())
            .fold(zero, |acc, (&value, &coeff)| {
                let term = mul_const_expr(builder, value, Goldilocks::from_u64(coeff));
                builder.add(acc, term)
            })
    })
}

fn pow7_expr(builder: &mut CircuitBuilder<P3Goldilocks>, value: ExprId) -> ExprId {
    let squared = builder.mul(value, value);
    let fourth = builder.mul(squared, squared);
    let sixth = builder.mul(fourth, squared);
    builder.mul(sixth, value)
}

fn cmux_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
    c0: &GlweExpr,
    c1: &GlweExpr,
    selector: &GgswNttExpr,
) -> GlweExpr {
    let diff = glwe_sub_expr(builder, c1, c0);
    let product = external_product_expr(builder, params, &diff, selector);
    glwe_add_expr(builder, &product, c0)
}

fn external_product_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
    ct: &GlweExpr,
    ggsw: &GgswNttExpr,
) -> GlweExpr {
    let mut acc = zero_glwe_expr(builder, params);
    for (mask_poly, row) in ct.mask.iter().zip(ggsw.rows.iter()) {
        let product = glev_external_product_by_plain_poly_expr(builder, params, row, mask_poly);
        acc = glwe_add_expr(builder, &acc, &product);
    }
    let body_product = glev_external_product_by_plain_poly_expr(
        builder,
        params,
        &ggsw.rows[params.glwe_dimension],
        &ct.body,
    );
    glwe_add_expr(builder, &acc, &body_product)
}

fn glev_external_product_by_plain_poly_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
    ct: &GlevNttExpr,
    poly: &[ExprId],
) -> GlweExpr {
    let digits = decompose_poly_expr(builder, params, poly);
    let mut acc = zero_glwe_expr(builder, params);
    for (digit_poly, level_ct) in digits.iter().zip(ct.levels.iter()) {
        let digit_ntt = negacyclic_ntt_expr(builder, digit_poly);
        let product = glwe_mul_by_plain_poly_ntt_expr(builder, level_ct, &digit_ntt);
        acc = glwe_add_expr(builder, &acc, &product);
    }
    acc
}

fn decompose_poly_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
    poly: &[ExprId],
) -> Vec<Vec<ExprId>> {
    let zero = builder.define_const(P3Goldilocks::ZERO);
    let mut levels = vec![vec![zero; poly.len()]; params.decomposition_level_count];
    for (coeff_index, &coeff) in poly.iter().enumerate() {
        let mut reconstructed = zero;
        for (level_index, level) in levels.iter_mut().enumerate() {
            let raw_digit = builder.alloc_private_input("decomp_digit");
            range_check_expr(builder, raw_digit, params.decomposition_base_log);
            let digit = signed_digit_expr(builder, params, raw_digit);
            let factor = decomposition_gadget_factor(params, level_index);
            let scaled_digit = mul_const_expr(builder, digit, factor);
            reconstructed = builder.add(reconstructed, scaled_digit);
            level[coeff_index] = digit;
        }
        let reconstructed = add_approximation_error_expr(builder, params, reconstructed);
        builder.connect(coeff, reconstructed);
    }
    levels
}

fn signed_digit_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
    raw_digit: ExprId,
) -> ExprId {
    if uses_exact_binary_decomposition(params) {
        raw_digit
    } else {
        let half_base = Goldilocks::from_u64(1u64 << (params.decomposition_base_log - 1));
        let neg_half_const = builder.define_const(core_to_p3(-half_base));
        builder.add(raw_digit, neg_half_const)
    }
}

fn add_approximation_error_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
    reconstructed: ExprId,
) -> ExprId {
    let Some(error_bits) = decomposition_error_bits(params) else {
        return reconstructed;
    };

    let error_magnitude = builder.alloc_private_input("decomp_error_magnitude");
    range_check_expr(builder, error_magnitude, error_bits);
    let error_sign = builder.alloc_private_input("decomp_error_sign");
    builder.assert_bool(error_sign);

    let doubled_error = mul_const_expr(builder, error_magnitude, Goldilocks::from_u64(2));
    let signed_correction = builder.mul(error_sign, doubled_error);
    let neg_signed_correction = mul_const_expr(builder, signed_correction, -Goldilocks::ONE);
    let signed_error = builder.add(error_magnitude, neg_signed_correction);
    builder.add(reconstructed, signed_error)
}

fn mod_switch_exponent_bits_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    value: ExprId,
    exponent_modulus: usize,
) -> Vec<ExprId> {
    assert!(exponent_modulus.is_power_of_two());
    let exponent_bits = exponent_modulus.trailing_zeros() as usize;
    let shift = 64 - exponent_bits;
    let value_bits = decompose_canonical_torus_expr(builder, value);
    let raw_bits = value_bits[shift..64].to_vec();
    add_bit_mod_power_of_two_expr(builder, &raw_bits, value_bits[shift - 1])
}

fn decompose_canonical_torus_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    value: ExprId,
) -> Vec<ExprId> {
    let zero = builder.define_const(P3Goldilocks::ZERO);
    let one = builder.define_const(P3Goldilocks::ONE);
    let mut reconstructed = zero;
    let mut low_word = zero;
    let mut high_all_ones = one;
    let mut bits = Vec::with_capacity(64);

    for bit_index in 0..64 {
        let bit = builder.alloc_private_input("torus_bit");
        builder.assert_bool(bit);
        bits.push(bit);

        let scale = Goldilocks::from_u64(1u64 << bit_index);
        let scaled_bit = mul_const_expr(builder, bit, scale);
        reconstructed = builder.add(reconstructed, scaled_bit);

        if bit_index < 32 {
            low_word = builder.add(low_word, scaled_bit);
        } else {
            high_all_ones = builder.mul(high_all_ones, bit);
        }
    }

    builder.connect(value, reconstructed);
    let canonical_overflow = builder.mul(high_all_ones, low_word);
    builder.connect(canonical_overflow, zero);

    bits
}

fn add_bit_mod_power_of_two_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    bits: &[ExprId],
    addend: ExprId,
) -> Vec<ExprId> {
    let mut carry = addend;
    bits.iter()
        .map(|&bit| {
            let bit_and_carry = builder.mul(bit, carry);
            let bit_plus_carry = builder.add(bit, carry);
            let two_bit_and_carry = builder.add(bit_and_carry, bit_and_carry);
            let sum_bit = builder.sub(bit_plus_carry, two_bit_and_carry);
            carry = bit_and_carry;
            sum_bit
        })
        .collect()
}

fn negate_bits_mod_power_of_two_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    bits: &[ExprId],
) -> Vec<ExprId> {
    let one = builder.define_const(P3Goldilocks::ONE);
    let inverted = bits
        .iter()
        .map(|&bit| builder.sub(one, bit))
        .collect::<Vec<_>>();
    add_bit_mod_power_of_two_expr(builder, &inverted, one)
}

fn zero_glwe_expr(builder: &mut CircuitBuilder<P3Goldilocks>, params: &Params) -> GlweExpr {
    let zero = builder.define_const(P3Goldilocks::ZERO);
    GlweExpr {
        mask: vec![vec![zero; params.polynomial_size]; params.glwe_dimension],
        body: vec![zero; params.polynomial_size],
    }
}

fn glwe_mul_by_plain_poly_ntt_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    ct: &GlweNttExpr,
    poly_ntt: &[ExprId],
) -> GlweExpr {
    GlweExpr {
        mask: ct
            .mask
            .iter()
            .map(|mask_poly| poly_mul_ntt_evals_expr(builder, poly_ntt, mask_poly))
            .collect(),
        body: poly_mul_ntt_evals_expr(builder, poly_ntt, &ct.body),
    }
}

fn glwe_mul_xai_by_bits_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    ct: &GlweExpr,
    exponent_bits: &[ExprId],
) -> GlweExpr {
    GlweExpr {
        mask: ct
            .mask
            .iter()
            .map(|poly| mul_xai_by_bits_expr(builder, poly, exponent_bits))
            .collect(),
        body: mul_xai_by_bits_expr(builder, &ct.body, exponent_bits),
    }
}

fn glwe_add_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    lhs: &GlweExpr,
    rhs: &GlweExpr,
) -> GlweExpr {
    GlweExpr {
        mask: lhs
            .mask
            .iter()
            .zip(rhs.mask.iter())
            .map(|(a, b)| poly_add_expr(builder, a, b))
            .collect(),
        body: poly_add_expr(builder, &lhs.body, &rhs.body),
    }
}

fn glwe_sub_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    lhs: &GlweExpr,
    rhs: &GlweExpr,
) -> GlweExpr {
    GlweExpr {
        mask: lhs
            .mask
            .iter()
            .zip(rhs.mask.iter())
            .map(|(a, b)| poly_sub_expr(builder, a, b))
            .collect(),
        body: poly_sub_expr(builder, &lhs.body, &rhs.body),
    }
}

fn poly_add_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    lhs: &[ExprId],
    rhs: &[ExprId],
) -> Vec<ExprId> {
    lhs.iter()
        .zip(rhs.iter())
        .map(|(&a, &b)| builder.add(a, b))
        .collect()
}

fn poly_sub_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    lhs: &[ExprId],
    rhs: &[ExprId],
) -> Vec<ExprId> {
    lhs.iter()
        .zip(rhs.iter())
        .map(|(&a, &b)| builder.sub(a, b))
        .collect()
}

fn poly_mul_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    lhs: &[ExprId],
    rhs: &[ExprId],
) -> Vec<ExprId> {
    assert_eq!(lhs.len(), rhs.len());
    let lhs_eval = negacyclic_ntt_expr(builder, lhs);
    let rhs_eval = negacyclic_ntt_expr(builder, rhs);
    poly_mul_ntt_evals_expr(builder, &lhs_eval, &rhs_eval)
}

fn poly_mul_ntt_evals_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    lhs_eval: &[ExprId],
    rhs_eval: &[ExprId],
) -> Vec<ExprId> {
    assert_eq!(lhs_eval.len(), rhs_eval.len());

    let mut product = lhs_eval
        .iter()
        .zip(rhs_eval.iter())
        .map(|(&a, &b)| builder.mul(a, b))
        .collect::<Vec<_>>();

    negacyclic_intt_expr(builder, &mut product)
}

fn negacyclic_ntt_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    values: &[ExprId],
) -> Vec<ExprId> {
    let n = values.len();
    assert!(2 * n <= (1usize << GOLDILOCKS_TWO_ADICITY));

    let psi = primitive_power_of_two_root(2 * n);
    let mut evals = twist_expr(builder, values, psi);
    ntt_expr(builder, &mut evals, false);
    evals
}

fn negacyclic_intt_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    values: &mut [ExprId],
) -> Vec<ExprId> {
    let n = values.len();
    assert!(2 * n <= (1usize << GOLDILOCKS_TWO_ADICITY));

    let psi = primitive_power_of_two_root(2 * n);
    let psi_inv = psi.inverse().expect("root of unity is nonzero");
    ntt_expr(builder, values, true);
    untwist_expr(builder, values, psi_inv)
}

fn ntt_expr(builder: &mut CircuitBuilder<P3Goldilocks>, values: &mut [ExprId], inverse: bool) {
    let n = values.len();
    assert!(n.is_power_of_two());
    bit_reverse_expr(values);

    let mut len = 2;
    while len <= n {
        let mut root = primitive_power_of_two_root(len);
        if inverse {
            root = root.inverse().expect("root of unity is nonzero");
        }

        let half = len / 2;
        for chunk_start in (0..n).step_by(len) {
            let mut twiddle = Goldilocks::ONE;
            for j in 0..half {
                let left_index = chunk_start + j;
                let right_index = left_index + half;
                let u = values[left_index];
                let v = mul_const_expr(builder, values[right_index], twiddle);
                values[left_index] = builder.add(u, v);
                values[right_index] = builder.sub(u, v);
                twiddle *= root;
            }
        }

        len *= 2;
    }

    if inverse {
        let inv_n = Goldilocks::from_u64(n as u64)
            .inverse()
            .expect("NTT length is nonzero");
        for value in values {
            *value = mul_const_expr(builder, *value, inv_n);
        }
    }
}

fn twist_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    values: &[ExprId],
    psi: Goldilocks,
) -> Vec<ExprId> {
    let mut twiddle = Goldilocks::ONE;
    values
        .iter()
        .map(|&value| {
            let out = mul_const_expr(builder, value, twiddle);
            twiddle *= psi;
            out
        })
        .collect()
}

fn untwist_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    values: &[ExprId],
    psi_inv: Goldilocks,
) -> Vec<ExprId> {
    let mut twiddle = Goldilocks::ONE;
    values
        .iter()
        .map(|&value| {
            let out = mul_const_expr(builder, value, twiddle);
            twiddle *= psi_inv;
            out
        })
        .collect()
}

fn mul_const_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    value: ExprId,
    constant: Goldilocks,
) -> ExprId {
    if constant == Goldilocks::ZERO {
        builder.define_const(P3Goldilocks::ZERO)
    } else if constant == Goldilocks::ONE {
        value
    } else {
        let constant = builder.define_const(core_to_p3(constant));
        builder.mul(value, constant)
    }
}

fn bit_reverse_expr(values: &mut [ExprId]) {
    let n = values.len();
    let bits = n.trailing_zeros();
    for i in 0..n {
        let j = i.reverse_bits() >> (usize::BITS - bits);
        if i < j {
            values.swap(i, j);
        }
    }
}

fn mul_xai_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    poly: &[ExprId],
    exponent: usize,
) -> Vec<ExprId> {
    let n = poly.len();
    let modulus = 2 * n;
    let exponent = exponent % modulus;
    let zero = builder.define_const(P3Goldilocks::ZERO);
    let mut out = vec![zero; n];
    for (i, &cell) in poly.iter().enumerate() {
        let target = (i + exponent) % modulus;
        if target < n {
            out[target] = builder.add(out[target], cell);
        } else {
            out[target - n] = builder.sub(out[target - n], cell);
        }
    }
    out
}

fn mul_xai_by_bits_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    poly: &[ExprId],
    exponent_bits: &[ExprId],
) -> Vec<ExprId> {
    let mut current = poly.to_vec();
    for (bit_index, &bit) in exponent_bits.iter().enumerate() {
        let rotated = mul_xai_expr(builder, &current, 1usize << bit_index);
        current = select_poly_expr(builder, bit, &current, &rotated);
    }
    current
}

fn select_poly_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    selector: ExprId,
    when_zero: &[ExprId],
    when_one: &[ExprId],
) -> Vec<ExprId> {
    when_zero
        .iter()
        .zip(when_one.iter())
        .map(|(&zero_value, &one_value)| select_expr(builder, selector, zero_value, one_value))
        .collect()
}

fn select_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    selector: ExprId,
    when_zero: ExprId,
    when_one: ExprId,
) -> ExprId {
    let delta = builder.sub(when_one, when_zero);
    let selected_delta = builder.mul(selector, delta);
    builder.add(when_zero, selected_delta)
}

fn sub_from_zero(builder: &mut CircuitBuilder<P3Goldilocks>, value: ExprId) -> ExprId {
    let zero = builder.define_const(P3Goldilocks::ZERO);
    builder.sub(zero, value)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn poly_mul_circuit_runs_against_native_instance() {
        let lhs = Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]);
        let rhs = Polynomial::from_coeffs(vec![5u64.into(), 6u64.into(), 7u64.into(), 8u64.into()]);
        let instance = PolyMulInstance::new(lhs, rhs);
        let circuit = build_poly_mul_circuit(instance.degree()).unwrap();
        let mut runner = circuit.runner();
        runner.set_public_inputs(&instance.public_inputs()).unwrap();
        runner.run().unwrap();
    }

    #[test]
    fn mul_xai_circuit_runs_against_native_instance() {
        let input =
            Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]);
        let instance = MulXaiInstance::new(input, 5);
        let circuit = build_mul_xai_circuit(instance.degree(), instance.exponent).unwrap();
        let mut runner = circuit.runner();
        runner.set_public_inputs(&instance.public_inputs()).unwrap();
        runner.run().unwrap();
    }

    #[test]
    fn sample_extract_circuit_runs_against_native_instance() {
        let glwe = GlweCiphertext {
            mask: vec![Polynomial::from_coeffs(vec![
                1u64.into(),
                2u64.into(),
                3u64.into(),
                4u64.into(),
            ])],
            body: Polynomial::from_coeffs(vec![5u64.into(), 6u64.into(), 7u64.into(), 8u64.into()]),
        };
        let instance = SampleExtractInstance::new(glwe);
        let circuit =
            build_sample_extract_circuit(instance.glwe_dimension(), instance.degree()).unwrap();
        let mut runner = circuit.runner();
        runner.set_public_inputs(&instance.public_inputs()).unwrap();
        runner.run().unwrap();
    }

    #[test]
    fn actual_pbs_circuit_runs_against_native_instance() {
        let params = Params::new(1, 4, 1, 16, 4, 4);
        run_actual_pbs_circuit_with_params(params);
    }

    #[test]
    fn actual_pbs_circuit_runs_with_approximate_decomposition() {
        let params = Params::new(1, 4, 1, 5, 4, 4);
        run_actual_pbs_circuit_with_params(params);
    }

    #[test]
    fn actual_pbs_step_circuit_runs_with_approximate_decomposition() {
        let params = Params::new(1, 4, 1, 5, 4, 4);
        let input_accumulator = GlweCiphertext::trivial(
            Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]),
            params.glwe_dimension,
        );
        let mask_step = tfheprus_core::GOLDILOCKS_MODULUS / params.exponent_modulus() as u64;
        let instance = ActualPbsStepInstance::new(
            params,
            Goldilocks::from_u64(mask_step),
            input_accumulator,
            zero_ggsw(&Params::new(1, 4, 1, 5, 4, 4)),
        );
        let circuit = build_actual_pbs_step_circuit(&instance).unwrap();
        let mut runner = circuit.runner();
        runner.set_public_inputs(&instance.public_inputs()).unwrap();
        runner
            .set_private_inputs(&instance.private_inputs())
            .unwrap();
        runner.run().unwrap();
    }

    #[test]
    fn actual_pbs_step_private_circuit_binds_private_selector_digest() {
        let params = Params::new(1, 4, 1, 5, 4, 4);
        let input_accumulator = GlweCiphertext::trivial(
            Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]),
            params.glwe_dimension,
        );
        let mask_step = tfheprus_core::GOLDILOCKS_MODULUS / params.exponent_modulus() as u64;
        let selector = nonzero_ggsw(&params);
        let public_step = ActualPbsStepInstance::new(
            params.clone(),
            Goldilocks::from_u64(mask_step),
            input_accumulator.clone(),
            selector.clone(),
        );
        let instance = ActualPbsStepPrivateInstance::new(
            params.clone(),
            Goldilocks::from_u64(mask_step),
            input_accumulator,
            selector,
        );
        let selector_field_count = (params.glwe_dimension + 1)
            * params.decomposition_level_count
            * (params.glwe_dimension + 1)
            * params.polynomial_size;
        assert_eq!(
            instance.public_inputs().len(),
            public_step.public_inputs().len() - selector_field_count + SELECTOR_DIGEST_WIDTH
        );

        let circuit = build_actual_pbs_step_private_circuit(&instance).unwrap();
        let mut runner = circuit.runner();
        runner.set_public_inputs(&instance.public_inputs()).unwrap();
        runner
            .set_private_inputs(&instance.private_inputs())
            .unwrap();
        runner.run().unwrap();
    }

    #[test]
    fn actual_pbs_step_chain_circuit_binds_private_selector_and_mask() {
        let params = Params::new(1, 4, 1, 5, 4, 4);
        let input_accumulator = GlweCiphertext::trivial(
            Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]),
            params.glwe_dimension,
        );
        let mask_step = tfheprus_core::GOLDILOCKS_MODULUS / params.exponent_modulus() as u64;
        let instance = ActualPbsStepChainInstance::new(
            params.clone(),
            Goldilocks::from_u64(mask_step),
            input_accumulator,
            nonzero_ggsw(&params),
            pbs_bsk_digest_initial(),
            pbs_mask_digest_initial(),
        );
        assert_eq!(
            instance.public_inputs().len(),
            2 * (params.glwe_dimension + 1) * params.polynomial_size + 4 * SELECTOR_DIGEST_WIDTH
        );

        let circuit = build_actual_pbs_step_chain_circuit(&instance).unwrap();
        let mut runner = circuit.runner();
        runner.set_public_inputs(&instance.public_inputs()).unwrap();
        runner
            .set_private_inputs(&instance.private_inputs())
            .unwrap();
        runner.run().unwrap();
    }

    #[test]
    fn actual_pbs_chain_chunk_circuit_composes_private_steps() {
        let params = Params::new(1, 4, 1, 5, 4, 4);
        let input_accumulator = GlweCiphertext::trivial(
            Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]),
            params.glwe_dimension,
        );
        let mask_step = tfheprus_core::GOLDILOCKS_MODULUS / params.exponent_modulus() as u64;
        let instance = ActualPbsChainChunkInstance::new(
            params.clone(),
            vec![
                Goldilocks::from_u64(mask_step),
                Goldilocks::from_u64(mask_step * 2),
            ],
            input_accumulator,
            vec![nonzero_ggsw(&params), nonzero_ggsw(&params)],
            pbs_bsk_digest_initial(),
            pbs_mask_digest_initial(),
        );
        assert_eq!(instance.step_count(), 2);
        assert_eq!(
            instance.public_inputs().len(),
            2 * (params.glwe_dimension + 1) * params.polynomial_size + 4 * SELECTOR_DIGEST_WIDTH
        );

        let circuit = build_actual_pbs_chain_chunk_circuit(&instance).unwrap();
        let mut runner = circuit.runner();
        runner.set_public_inputs(&instance.public_inputs()).unwrap();
        runner
            .set_private_inputs(&instance.private_inputs())
            .unwrap();
        runner.run().unwrap();
    }

    fn run_actual_pbs_circuit_with_params(params: Params) {
        let input_message = 1;
        let output_message = 3;
        let mask_step = tfheprus_core::GOLDILOCKS_MODULUS / params.exponent_modulus() as u64;
        let input = LweCiphertext {
            mask: vec![Goldilocks::from_u64(mask_step)],
            body: tfheprus_core::encode_message(&params, input_message),
        };
        let test_polynomial = TestPolynomial::single_slot(&params, input_message, output_message);
        let evaluation_key = EvaluationKey {
            bootstrapping_key: vec![zero_ggsw(&params)],
        };
        let instance = ActualPbsInstance::new(params, input, test_polynomial, evaluation_key);
        let profile = ActualPbsCircuitProfile::from_instance(&instance);
        assert_eq!(profile.public_inputs, instance.public_inputs().len());
        assert_eq!(profile.private_inputs, instance.private_inputs().len());
        let circuit = build_actual_pbs_circuit(&instance).unwrap();
        let mut runner = circuit.runner();
        runner.set_public_inputs(&instance.public_inputs()).unwrap();
        runner
            .set_private_inputs(&instance.private_inputs())
            .unwrap();
        runner.run().unwrap();
    }

    fn zero_ggsw(params: &Params) -> GgswCiphertext {
        GgswCiphertext {
            rows: vec![zero_glev(params); params.glwe_dimension + 1],
        }
    }

    fn nonzero_ggsw(params: &Params) -> GgswCiphertext {
        GgswCiphertext {
            rows: (0..=params.glwe_dimension)
                .map(|row| nonzero_glev(params, row))
                .collect(),
        }
    }

    fn nonzero_glev(params: &Params, row: usize) -> GlevCiphertext {
        GlevCiphertext {
            levels: (0..params.decomposition_level_count)
                .map(|level| nonzero_glwe(params, row, level))
                .collect(),
        }
    }

    fn nonzero_glwe(params: &Params, row: usize, level: usize) -> GlweCiphertext {
        let mask = (0..params.glwe_dimension)
            .map(|mask_row| indexed_poly(params, 17 + row * 31 + level * 7 + mask_row * 3))
            .collect();
        let body = indexed_poly(params, 97 + row * 31 + level * 7);
        GlweCiphertext { mask, body }
    }

    fn indexed_poly(params: &Params, offset: usize) -> Polynomial {
        Polynomial::from_coeffs(
            (0..params.polynomial_size)
                .map(|index| Goldilocks::from_u64((offset + index + 1) as u64))
                .collect(),
        )
    }

    fn zero_glev(params: &Params) -> GlevCiphertext {
        GlevCiphertext {
            levels: vec![
                GlweCiphertext::trivial(
                    Polynomial::zero(params.polynomial_size),
                    params.glwe_dimension
                );
                params.decomposition_level_count
            ],
        }
    }
}
