//! Plonky3-backed prove/verify proof-of-concept entry points.

use core::fmt;

use p3_batch_stark::ProverData;
use p3_circuit_prover::common::get_airs_and_degrees_with_prep;
use p3_circuit_prover::config::{self, GoldilocksConfig};
use p3_circuit_prover::{
    BatchStarkProof, BatchStarkProver, CircuitProverData, ConstraintProfile, TablePacking,
};
use p3_goldilocks::Goldilocks as P3Goldilocks;
use tfheprus_circuits::{build_poly_mul_circuit, PolyMulInstance};

pub struct PolyMulProof {
    pub degree: usize,
    pub public_inputs: Vec<P3Goldilocks>,
    pub proof: BatchStarkProof<GoldilocksConfig>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum PolyMulProofError {
    StatementMismatch,
    Plonky3(String),
}

impl fmt::Display for PolyMulProofError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StatementMismatch => write!(f, "proof does not match the requested statement"),
            Self::Plonky3(message) => write!(f, "plonky3 error: {message}"),
        }
    }
}

impl std::error::Error for PolyMulProofError {}

pub fn prove_poly_mul(instance: &PolyMulInstance) -> Result<PolyMulProof, PolyMulProofError> {
    let circuit = build_poly_mul_circuit(instance.degree())
        .map_err(|error| PolyMulProofError::Plonky3(format!("{error:?}")))?;
    let public_inputs = instance.public_inputs();

    let config = config::goldilocks();
    let table_packing = TablePacking::default();
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 1>(
            &circuit,
            &table_packing,
            &[],
            &[],
            ConstraintProfile::Standard,
        )
        .map_err(|error| PolyMulProofError::Plonky3(format!("{error:?}")))?;
    let (airs, degrees): (Vec<_>, Vec<usize>) = airs_degrees.into_iter().unzip();
    let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let mut runner = circuit.runner();
    runner
        .set_public_inputs(&public_inputs)
        .map_err(|error| PolyMulProofError::Plonky3(format!("{error:?}")))?;
    let traces = runner
        .run()
        .map_err(|error| PolyMulProofError::Plonky3(format!("{error:?}")))?;

    let prover = BatchStarkProver::new(config).with_table_packing(table_packing);
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| PolyMulProofError::Plonky3(format!("{error:?}")))?;

    Ok(PolyMulProof {
        degree: instance.degree(),
        public_inputs,
        proof,
    })
}

pub fn verify_poly_mul_proof(
    instance: &PolyMulInstance,
    proof: &PolyMulProof,
) -> Result<(), PolyMulProofError> {
    if proof.degree != instance.degree() || proof.public_inputs != instance.public_inputs() {
        return Err(PolyMulProofError::StatementMismatch);
    }

    let config = config::goldilocks();
    let prover =
        BatchStarkProver::new(config).with_table_packing(proof.proof.table_packing.clone());
    prover
        .verify_all_tables(&proof.proof)
        .map_err(|error| PolyMulProofError::Plonky3(format!("{error:?}")))
}

pub fn prove_and_verify_poly_mul(instance: &PolyMulInstance) -> Result<(), PolyMulProofError> {
    let proof = prove_poly_mul(instance)?;
    verify_poly_mul_proof(instance, &proof)
}

#[cfg(test)]
mod tests {
    use tfheprus_core::Polynomial;

    use super::*;

    #[test]
    fn proves_and_verifies_toy_negacyclic_polynomial_mul() {
        let lhs = Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]);
        let rhs = Polynomial::from_coeffs(vec![5u64.into(), 6u64.into(), 7u64.into(), 8u64.into()]);
        let instance = PolyMulInstance::new(lhs, rhs);

        prove_and_verify_poly_mul(&instance).unwrap();
    }

    #[test]
    fn rejects_statement_mismatch_before_plonky3_verification() {
        let lhs = Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]);
        let rhs = Polynomial::from_coeffs(vec![5u64.into(), 6u64.into(), 7u64.into(), 8u64.into()]);
        let instance = PolyMulInstance::new(lhs, rhs);
        let proof = prove_poly_mul(&instance).unwrap();

        let other_lhs =
            Polynomial::from_coeffs(vec![2u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]);
        let other_rhs =
            Polynomial::from_coeffs(vec![5u64.into(), 6u64.into(), 7u64.into(), 8u64.into()]);
        let other_instance = PolyMulInstance::new(other_lhs, other_rhs);

        assert_eq!(
            verify_poly_mul_proof(&other_instance, &proof),
            Err(PolyMulProofError::StatementMismatch)
        );
    }
}
