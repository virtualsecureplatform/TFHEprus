//! Plonky3 circuit mirrors for `tfheprus-core`.

use p3_circuit::circuit::Circuit;
use p3_circuit::{CircuitBuilder, ExprId};
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks as P3Goldilocks;
use tfheprus_core::ggsw::cmux;
use tfheprus_core::{
    bootstrap_without_keyswitch, decompose_polynomial, mod_switch_to_exponent,
    sample_extract_index_zero, EvaluationKey, GgswCiphertext, GlevCiphertext, GlweCiphertext,
    Goldilocks, LweCiphertext, Params, Polynomial, TestPolynomial,
};

#[derive(Clone)]
struct GlweExpr {
    mask: Vec<Vec<ExprId>>,
    body: Vec<ExprId>,
}

#[derive(Clone)]
struct GlevExpr {
    levels: Vec<GlweExpr>,
}

#[derive(Clone)]
struct GgswExpr {
    rows: Vec<GlevExpr>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct PolyMulInstance {
    pub lhs: Polynomial,
    pub rhs: Polynomial,
    pub product: Polynomial,
}

impl PolyMulInstance {
    pub fn new(lhs: Polynomial, rhs: Polynomial) -> Self {
        let product = lhs.mul_naive(&rhs);
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
        append_evaluation_key_public_inputs(&mut inputs, &self.evaluation_key);
        inputs.extend(self.output.mask.iter().copied().map(core_to_p3));
        inputs.push(core_to_p3(self.output.body));
        inputs
    }

    pub fn private_inputs(&self) -> Vec<P3Goldilocks> {
        let mut inputs = Vec::new();
        let mut acc = GlweCiphertext::trivial(
            self.test_polynomial.poly.mul_xai(self.initial_exponent),
            self.params.glwe_dimension,
        );

        for ((&exponent, selector), _mask_value) in self
            .mask_exponents
            .iter()
            .zip(self.evaluation_key.bootstrapping_key.iter())
            .zip(self.input.mask.iter())
        {
            if exponent == 0 {
                continue;
            }

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

    let zero = builder.define_const(P3Goldilocks::ZERO);
    let mut computed = vec![zero; degree];

    for (i, &lhs_cell) in lhs.iter().enumerate() {
        for (j, &rhs_cell) in rhs.iter().enumerate() {
            let product = builder.mul(lhs_cell, rhs_cell);
            let target = i + j;
            if target < degree {
                computed[target] = builder.add(computed[target], product);
            } else {
                computed[target - degree] = builder.sub(computed[target - degree], product);
            }
        }
    }

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
    let input_mask = builder.alloc_public_inputs(instance.params.lwe_dimension, "actual_pbs_mask");
    let input_body = builder.alloc_public_inputs(1, "actual_pbs_body");
    let test_poly =
        builder.alloc_public_inputs(instance.params.polynomial_size, "actual_pbs_test_poly");
    let bootstrapping_key = (0..instance.params.lwe_dimension)
        .map(|_| alloc_public_ggsw(&mut builder, &instance.params))
        .collect::<Vec<_>>();
    let output_mask = builder.alloc_public_inputs(
        instance.params.glwe_dimension * instance.params.polynomial_size,
        "actual_pbs_output_mask",
    );
    let output_body = builder.alloc_public_inputs(1, "actual_pbs_output_body");

    for (&cell, &value) in input_mask.iter().zip(instance.input.mask.iter()) {
        connect_to_constant(&mut builder, cell, value);
    }
    connect_to_constant(&mut builder, input_body[0], instance.input.body);

    let mut acc = GlweExpr {
        mask: vec![
            vec![builder.define_const(P3Goldilocks::ZERO); instance.params.polynomial_size];
            instance.params.glwe_dimension
        ],
        body: mul_xai_expr(&mut builder, &test_poly, instance.initial_exponent),
    };

    for (&exponent, selector) in instance.mask_exponents.iter().zip(bootstrapping_key.iter()) {
        if exponent == 0 {
            continue;
        }

        let rotated = glwe_mul_xai_expr(&mut builder, &acc, exponent);
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

fn append_glwe_public_inputs(inputs: &mut Vec<P3Goldilocks>, ct: &GlweCiphertext) {
    for poly in &ct.mask {
        append_polynomial_public_inputs(inputs, poly);
    }
    append_polynomial_public_inputs(inputs, &ct.body);
}

fn append_glev_public_inputs(inputs: &mut Vec<P3Goldilocks>, ct: &GlevCiphertext) {
    for level in &ct.levels {
        append_glwe_public_inputs(inputs, level);
    }
}

fn append_ggsw_public_inputs(inputs: &mut Vec<P3Goldilocks>, ct: &GgswCiphertext) {
    for row in &ct.rows {
        append_glev_public_inputs(inputs, row);
    }
}

fn append_evaluation_key_public_inputs(inputs: &mut Vec<P3Goldilocks>, ek: &EvaluationKey) {
    for ggsw in &ek.bootstrapping_key {
        append_ggsw_public_inputs(inputs, ggsw);
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
            for bit_index in 0..params.decomposition_base_log {
                let bit = (digit.value() >> bit_index) & 1;
                inputs.push(P3Goldilocks::from_u64(bit));
            }
        }
    }
}

fn alloc_public_ggsw(builder: &mut CircuitBuilder<P3Goldilocks>, params: &Params) -> GgswExpr {
    let rows = (0..=params.glwe_dimension)
        .map(|_| alloc_public_glev(builder, params))
        .collect();
    GgswExpr { rows }
}

fn alloc_public_glev(builder: &mut CircuitBuilder<P3Goldilocks>, params: &Params) -> GlevExpr {
    let levels = (0..params.decomposition_level_count)
        .map(|_| alloc_public_glwe(builder, params))
        .collect();
    GlevExpr { levels }
}

fn alloc_public_glwe(builder: &mut CircuitBuilder<P3Goldilocks>, params: &Params) -> GlweExpr {
    let mask = (0..params.glwe_dimension)
        .map(|_| builder.alloc_public_inputs(params.polynomial_size, "actual_pbs_glwe_mask"))
        .collect();
    let body = builder.alloc_public_inputs(params.polynomial_size, "actual_pbs_glwe_body");
    GlweExpr { mask, body }
}

fn connect_to_constant(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    cell: ExprId,
    value: Goldilocks,
) {
    if value == Goldilocks::ZERO {
        let one = builder.define_const(P3Goldilocks::ONE);
        let must_be_one = builder.add(cell, one);
        builder.connect(must_be_one, one);
    } else {
        let expected = builder.define_const(core_to_p3(value));
        builder.connect(cell, expected);
    }
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
    selector: &GgswExpr,
) -> GlweExpr {
    let diff = glwe_sub_expr(builder, c1, c0);
    let product = external_product_expr(builder, params, &diff, selector);
    glwe_add_expr(builder, &product, c0)
}

fn external_product_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    params: &Params,
    ct: &GlweExpr,
    ggsw: &GgswExpr,
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
    ct: &GlevExpr,
    poly: &[ExprId],
) -> GlweExpr {
    let digits = decompose_poly_expr(builder, params, poly);
    let mut acc = zero_glwe_expr(builder, params);
    for (digit_poly, level_ct) in digits.iter().zip(ct.levels.iter()) {
        let product = glwe_mul_by_plain_poly_expr(builder, level_ct, digit_poly);
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
            let digit_from_bits =
                constrain_digit_bits(builder, digit, params.decomposition_base_log);
            builder.connect(digit, digit_from_bits);
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

fn constrain_digit_bits(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    _digit: ExprId,
    bit_count: usize,
) -> ExprId {
    let mut reconstructed = builder.define_const(P3Goldilocks::ZERO);
    for bit_index in 0..bit_count {
        let bit = builder.alloc_private_input("decomp_bit");
        builder.assert_bool(bit);
        let scale = Goldilocks::from_u64(1u64 << bit_index);
        let scale_const = builder.define_const(core_to_p3(scale));
        let scaled_bit = builder.mul(bit, scale_const);
        reconstructed = builder.add(reconstructed, scaled_bit);
    }
    reconstructed
}

fn zero_glwe_expr(builder: &mut CircuitBuilder<P3Goldilocks>, params: &Params) -> GlweExpr {
    let zero = builder.define_const(P3Goldilocks::ZERO);
    GlweExpr {
        mask: vec![vec![zero; params.polynomial_size]; params.glwe_dimension],
        body: vec![zero; params.polynomial_size],
    }
}

fn glwe_mul_by_plain_poly_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    ct: &GlweExpr,
    poly: &[ExprId],
) -> GlweExpr {
    GlweExpr {
        mask: ct
            .mask
            .iter()
            .map(|mask_poly| poly_mul_expr(builder, mask_poly, poly))
            .collect(),
        body: poly_mul_expr(builder, &ct.body, poly),
    }
}

fn glwe_mul_xai_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    ct: &GlweExpr,
    exponent: usize,
) -> GlweExpr {
    GlweExpr {
        mask: ct
            .mask
            .iter()
            .map(|poly| mul_xai_expr(builder, poly, exponent))
            .collect(),
        body: mul_xai_expr(builder, &ct.body, exponent),
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
    let n = lhs.len();
    let zero = builder.define_const(P3Goldilocks::ZERO);
    let mut out = vec![zero; n];
    for (i, &lhs_cell) in lhs.iter().enumerate() {
        for (j, &rhs_cell) in rhs.iter().enumerate() {
            let product = builder.mul(lhs_cell, rhs_cell);
            let target = i + j;
            if target < n {
                out[target] = builder.add(out[target], product);
            } else {
                out[target - n] = builder.sub(out[target - n], product);
            }
        }
    }
    out
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
