//! Plonky3 circuit mirrors for `tfheprus-core`.

pub mod range_check;

use p3_circuit::circuit::Circuit;
use p3_circuit::{CircuitBuilder, ExprId};
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks as P3Goldilocks;
use range_check::{range_check_expr, register_range_check_npo};
use tfheprus_core::ggsw::cmux;
use tfheprus_core::{
    bootstrap_without_keyswitch, decompose_polynomial, mod_switch_to_exponent, negacyclic_ntt,
    primitive_power_of_two_root, sample_extract_index_zero, EvaluationKey, GgswCiphertext,
    GlevCiphertext, GlweCiphertext, Goldilocks, LweCiphertext, Params, Polynomial, TestPolynomial,
    GOLDILOCKS_TWO_ADICITY,
};

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

pub fn core_to_p3(value: Goldilocks) -> P3Goldilocks {
    P3Goldilocks::from_u64(value.value())
}

fn append_polynomial_public_inputs(inputs: &mut Vec<P3Goldilocks>, poly: &Polynomial) {
    inputs.extend(poly.coeffs().iter().copied().map(core_to_p3));
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

fn append_evaluation_key_ntt_public_inputs(inputs: &mut Vec<P3Goldilocks>, ek: &EvaluationKey) {
    for ggsw in &ek.bootstrapping_key {
        append_ggsw_ntt_public_inputs(inputs, ggsw);
    }
}

fn append_decomposition_private_inputs(
    params: &Params,
    poly: &Polynomial,
    inputs: &mut Vec<P3Goldilocks>,
) {
    let digits = decompose_polynomial(params, poly);
    for coeff_index in 0..poly.len() {
        for digit_poly in &digits {
            let digit = digit_poly[coeff_index];
            inputs.push(core_to_p3(digit));
        }
    }
}

fn append_torus_decomposition_private_inputs(value: Goldilocks, inputs: &mut Vec<P3Goldilocks>) {
    for bit_index in 0..64 {
        let bit = (value.value() >> bit_index) & 1;
        inputs.push(P3Goldilocks::from_u64(bit));
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

fn alloc_public_glev_ntt(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
) -> GlevNttExpr {
    let levels = (0..params.decomposition_level_count)
        .map(|_| alloc_public_glwe_ntt(builder, params))
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
            let digit = builder.alloc_private_input("decomp_digit");
            range_check_expr(builder, digit, params.decomposition_base_log);
            let scale = Goldilocks::from_u64(1u64 << (params.decomposition_base_log * level_index));
            let scale_const = builder.define_const(core_to_p3(scale));
            let scaled_digit = builder.mul(digit, scale_const);
            reconstructed = builder.add(reconstructed, scaled_digit);
            level[coeff_index] = digit;
        }
        builder.connect(coeff, reconstructed);
    }
    levels
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
