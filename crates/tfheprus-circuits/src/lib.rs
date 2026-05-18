//! Plonky3 circuit mirrors for `tfheprus-core`.

use p3_circuit::circuit::Circuit;
use p3_circuit::CircuitBuilder;
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks as P3Goldilocks;
use tfheprus_core::{Goldilocks, Polynomial};

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
}
