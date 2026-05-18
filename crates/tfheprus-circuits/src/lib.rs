//! Plonky3 circuit mirrors for `tfheprus-core`.

use p3_circuit::circuit::Circuit;
use p3_circuit::CircuitBuilder;
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks as P3Goldilocks;
use tfheprus_core::{
    mod_switch_to_exponent, sample_extract_index_zero, GlweCiphertext, Goldilocks, LweCiphertext,
    Params, Polynomial, TestPolynomial,
};

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
pub struct TrivialPbsInstance {
    pub params: Params,
    pub input: LweCiphertext,
    pub test_polynomial: TestPolynomial,
    pub output: LweCiphertext,
    pub initial_exponent: usize,
}

impl TrivialPbsInstance {
    pub fn new(params: Params, input: LweCiphertext, test_polynomial: TestPolynomial) -> Self {
        assert_eq!(input.mask.len(), params.lwe_dimension);
        assert_eq!(test_polynomial.poly.len(), params.polynomial_size);
        assert!(
            input.mask.iter().all(|&value| value == Goldilocks::ZERO),
            "trivial PBS PoC requires an all-zero LWE mask"
        );

        let body_exponent = mod_switch_to_exponent(&params, input.body);
        let initial_exponent =
            (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
        let accumulator = GlweCiphertext::trivial(
            test_polynomial.poly.mul_xai(initial_exponent),
            params.glwe_dimension,
        );
        let output = sample_extract_index_zero(&accumulator);

        Self {
            params,
            input,
            test_polynomial,
            output,
            initial_exponent,
        }
    }

    pub fn public_inputs(&self) -> Vec<P3Goldilocks> {
        assert_eq!(self.input.mask.len(), self.params.lwe_dimension);
        assert_eq!(self.test_polynomial.poly.len(), self.params.polynomial_size);
        assert_eq!(
            self.output.mask.len(),
            self.params.glwe_dimension * self.params.polynomial_size
        );

        let mut inputs = Vec::with_capacity(
            self.params.lwe_dimension
                + 1
                + self.params.polynomial_size
                + self.output.mask.len()
                + 1,
        );
        inputs.extend(self.input.mask.iter().copied().map(core_to_p3));
        inputs.push(core_to_p3(self.input.body));
        inputs.extend(
            self.test_polynomial
                .poly
                .coeffs()
                .iter()
                .copied()
                .map(core_to_p3),
        );
        inputs.extend(self.output.mask.iter().copied().map(core_to_p3));
        inputs.push(core_to_p3(self.output.body));
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

pub fn build_trivial_pbs_circuit(
    params: &Params,
    initial_exponent: usize,
    input_body: Goldilocks,
) -> Result<Circuit<P3Goldilocks>, p3_circuit::CircuitError> {
    assert!(params.polynomial_size > 0);
    assert!(params.polynomial_size.is_power_of_two());
    assert!(params.lwe_dimension > 0);
    assert!(params.glwe_dimension > 0);

    let mut builder = CircuitBuilder::<P3Goldilocks>::new();
    let input_mask = builder.alloc_public_inputs(params.lwe_dimension, "pbs_input_mask");
    let input_body_cell = builder.alloc_public_inputs(1, "pbs_input_body");
    let test_poly = builder.alloc_public_inputs(params.polynomial_size, "pbs_test_poly");
    let output_mask = builder.alloc_public_inputs(
        params.glwe_dimension * params.polynomial_size,
        "pbs_output_mask",
    );
    let output_body = builder.alloc_public_inputs(1, "pbs_output_body");

    let zero = builder.define_const(P3Goldilocks::ZERO);
    let one = builder.define_const(P3Goldilocks::ONE);
    let expected_input_body = builder.define_const(core_to_p3(input_body));
    for cell in input_mask {
        let must_be_one = builder.add(cell, one);
        builder.connect(must_be_one, one);
    }
    builder.connect(input_body_cell[0], expected_input_body);

    let mut rotated = vec![zero; params.polynomial_size];
    let modulus = params.exponent_modulus();
    let initial_exponent = initial_exponent % modulus;
    for (i, &cell) in test_poly.iter().enumerate() {
        let target = (i + initial_exponent) % modulus;
        if target < params.polynomial_size {
            rotated[target] = builder.add(rotated[target], cell);
        } else {
            rotated[target - params.polynomial_size] =
                builder.sub(rotated[target - params.polynomial_size], cell);
        }
    }

    for cell in output_mask {
        let must_be_one = builder.add(cell, one);
        builder.connect(must_be_one, one);
    }
    builder.connect(rotated[0], output_body[0]);

    Ok(builder.build()?)
}

pub fn core_to_p3(value: Goldilocks) -> P3Goldilocks {
    P3Goldilocks::from_u64(value.value())
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
    fn trivial_pbs_circuit_runs_against_native_instance() {
        let params = Params::toy();
        let input_message = 1;
        let output_message = 3;
        let input = LweCiphertext {
            mask: vec![Goldilocks::ZERO; params.lwe_dimension],
            body: tfheprus_core::encode_message(&params, input_message),
        };
        let test_polynomial = TestPolynomial::single_slot(&params, input_message, output_message);
        let instance = TrivialPbsInstance::new(params, input, test_polynomial);
        let circuit = build_trivial_pbs_circuit(
            &instance.params,
            instance.initial_exponent,
            instance.input.body,
        )
        .unwrap();
        let mut runner = circuit.runner();
        runner.set_public_inputs(&instance.public_inputs()).unwrap();
        runner.run().unwrap();
    }
}
