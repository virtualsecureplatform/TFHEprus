//! Plonky3-backed prove/verify proof-of-concept entry points.

use core::fmt;

use p3_batch_stark::ProverData;
use p3_circuit::circuit::Circuit;
use p3_circuit_prover::common::get_airs_and_degrees_with_prep;
use p3_circuit_prover::config::{self, GoldilocksConfig};
use p3_circuit_prover::{
    BatchStarkProof, BatchStarkProver, CircuitProverData, ConstraintProfile, TablePacking,
};
use p3_goldilocks::Goldilocks as P3Goldilocks;
use tfheprus_circuits::{
    build_actual_pbs_circuit, build_mul_xai_circuit, build_poly_mul_circuit,
    build_sample_extract_circuit, ActualPbsInstance, MulXaiInstance, PolyMulInstance,
    SampleExtractInstance,
};
use tfheprus_core::Params;

pub struct PolyMulProof {
    pub degree: usize,
    pub public_inputs: Vec<P3Goldilocks>,
    pub proof: BatchStarkProof<GoldilocksConfig>,
}

pub struct MulXaiProof {
    pub degree: usize,
    pub exponent: usize,
    pub public_inputs: Vec<P3Goldilocks>,
    pub proof: BatchStarkProof<GoldilocksConfig>,
}

pub struct SampleExtractProof {
    pub glwe_dimension: usize,
    pub degree: usize,
    pub public_inputs: Vec<P3Goldilocks>,
    pub proof: BatchStarkProof<GoldilocksConfig>,
}

pub struct ActualPbsProof {
    pub params: Params,
    pub initial_exponent: usize,
    pub nonzero_rotation_count: usize,
    pub public_inputs: Vec<P3Goldilocks>,
    pub proof: BatchStarkProof<GoldilocksConfig>,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofError {
    StatementMismatch,
    Plonky3(String),
}

impl fmt::Display for ProofError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StatementMismatch => write!(f, "proof does not match the requested statement"),
            Self::Plonky3(message) => write!(f, "plonky3 error: {message}"),
        }
    }
}

impl std::error::Error for ProofError {}

pub type PolyMulProofError = ProofError;
pub type MulXaiProofError = ProofError;
pub type SampleExtractProofError = ProofError;
pub type ActualPbsProofError = ProofError;

pub fn prove_poly_mul(instance: &PolyMulInstance) -> Result<PolyMulProof, ProofError> {
    let circuit = build_poly_mul_circuit(instance.degree())
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let public_inputs = instance.public_inputs();
    let proof = prove_circuit(&circuit, &public_inputs, &[])?;

    Ok(PolyMulProof {
        degree: instance.degree(),
        public_inputs,
        proof,
    })
}

pub fn verify_poly_mul_proof(
    instance: &PolyMulInstance,
    proof: &PolyMulProof,
) -> Result<(), ProofError> {
    if proof.degree != instance.degree() || proof.public_inputs != instance.public_inputs() {
        return Err(ProofError::StatementMismatch);
    }

    verify_circuit_proof(&proof.proof)
}

pub fn prove_and_verify_poly_mul(instance: &PolyMulInstance) -> Result<(), ProofError> {
    let proof = prove_poly_mul(instance)?;
    verify_poly_mul_proof(instance, &proof)
}

pub fn prove_mul_xai(instance: &MulXaiInstance) -> Result<MulXaiProof, ProofError> {
    let circuit = build_mul_xai_circuit(instance.degree(), instance.exponent)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let public_inputs = instance.public_inputs();
    let proof = prove_circuit(&circuit, &public_inputs, &[])?;

    Ok(MulXaiProof {
        degree: instance.degree(),
        exponent: instance.exponent,
        public_inputs,
        proof,
    })
}

pub fn verify_mul_xai_proof(
    instance: &MulXaiInstance,
    proof: &MulXaiProof,
) -> Result<(), ProofError> {
    if proof.degree != instance.degree()
        || proof.exponent != instance.exponent
        || proof.public_inputs != instance.public_inputs()
    {
        return Err(ProofError::StatementMismatch);
    }

    verify_circuit_proof(&proof.proof)
}

pub fn prove_and_verify_mul_xai(instance: &MulXaiInstance) -> Result<(), ProofError> {
    let proof = prove_mul_xai(instance)?;
    verify_mul_xai_proof(instance, &proof)
}

pub fn prove_sample_extract(
    instance: &SampleExtractInstance,
) -> Result<SampleExtractProof, ProofError> {
    let circuit = build_sample_extract_circuit(instance.glwe_dimension(), instance.degree())
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let public_inputs = instance.public_inputs();
    let proof = prove_circuit(&circuit, &public_inputs, &[])?;

    Ok(SampleExtractProof {
        glwe_dimension: instance.glwe_dimension(),
        degree: instance.degree(),
        public_inputs,
        proof,
    })
}

pub fn verify_sample_extract_proof(
    instance: &SampleExtractInstance,
    proof: &SampleExtractProof,
) -> Result<(), ProofError> {
    if proof.glwe_dimension != instance.glwe_dimension()
        || proof.degree != instance.degree()
        || proof.public_inputs != instance.public_inputs()
    {
        return Err(ProofError::StatementMismatch);
    }

    verify_circuit_proof(&proof.proof)
}

pub fn prove_and_verify_sample_extract(instance: &SampleExtractInstance) -> Result<(), ProofError> {
    let proof = prove_sample_extract(instance)?;
    verify_sample_extract_proof(instance, &proof)
}

pub fn prove_actual_pbs(instance: &ActualPbsInstance) -> Result<ActualPbsProof, ProofError> {
    let circuit = build_actual_pbs_circuit(instance)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let public_inputs = instance.public_inputs();
    let private_inputs = instance.private_inputs();
    let proof = prove_circuit(&circuit, &public_inputs, &private_inputs)?;

    Ok(ActualPbsProof {
        params: instance.params.clone(),
        initial_exponent: instance.initial_exponent,
        nonzero_rotation_count: instance.nonzero_rotation_count(),
        public_inputs,
        proof,
    })
}

pub fn verify_actual_pbs_proof(
    instance: &ActualPbsInstance,
    proof: &ActualPbsProof,
) -> Result<(), ProofError> {
    if proof.params != instance.params
        || proof.initial_exponent != instance.initial_exponent
        || proof.nonzero_rotation_count != instance.nonzero_rotation_count()
        || proof.public_inputs != instance.public_inputs()
    {
        return Err(ProofError::StatementMismatch);
    }

    verify_circuit_proof(&proof.proof)
}

pub fn prove_and_verify_actual_pbs(instance: &ActualPbsInstance) -> Result<(), ProofError> {
    let proof = prove_actual_pbs(instance)?;
    verify_actual_pbs_proof(instance, &proof)
}

fn prove_circuit(
    circuit: &Circuit<P3Goldilocks>,
    public_inputs: &[P3Goldilocks],
    private_inputs: &[P3Goldilocks],
) -> Result<BatchStarkProof<GoldilocksConfig>, ProofError> {
    let config = config::goldilocks();
    let table_packing = TablePacking::default();
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 1>(
            circuit,
            &table_packing,
            &[],
            &[],
            ConstraintProfile::Standard,
        )
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let (airs, degrees): (Vec<_>, Vec<usize>) = airs_degrees.into_iter().unzip();
    let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let mut runner = circuit.runner();
    runner
        .set_public_inputs(public_inputs)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    runner
        .set_private_inputs(private_inputs)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let traces = runner
        .run()
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    let prover = BatchStarkProver::new(config).with_table_packing(table_packing);
    prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))
}

fn verify_circuit_proof(proof: &BatchStarkProof<GoldilocksConfig>) -> Result<(), ProofError> {
    let config = config::goldilocks();
    let prover = BatchStarkProver::new(config).with_table_packing(proof.table_packing.clone());
    prover
        .verify_all_tables(proof)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use tfheprus_core::{
        bootstrap_without_keyswitch, EvaluationKey, GlweCiphertext, Goldilocks, LweCiphertext,
        Polynomial, SecretKey, TestPolynomial, GOLDILOCKS_MODULUS,
    };

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
            Err(ProofError::StatementMismatch)
        );
    }

    #[test]
    fn proves_and_verifies_toy_mul_xai() {
        let input =
            Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]);
        let instance = MulXaiInstance::new(input, 5);

        prove_and_verify_mul_xai(&instance).unwrap();
    }

    #[test]
    fn rejects_mul_xai_statement_mismatch_before_plonky3_verification() {
        let input =
            Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]);
        let instance = MulXaiInstance::new(input, 5);
        let proof = prove_mul_xai(&instance).unwrap();

        let other_input =
            Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]);
        let other_instance = MulXaiInstance::new(other_input, 6);

        assert_eq!(
            verify_mul_xai_proof(&other_instance, &proof),
            Err(ProofError::StatementMismatch)
        );
    }

    #[test]
    fn proves_and_verifies_sample_extract() {
        let instance = sample_extract_instance([1, 2, 3, 4], [5, 6, 7, 8]);

        prove_and_verify_sample_extract(&instance).unwrap();
    }

    #[test]
    fn rejects_sample_extract_statement_mismatch_before_plonky3_verification() {
        let instance = sample_extract_instance([1, 2, 3, 4], [5, 6, 7, 8]);
        let proof = prove_sample_extract(&instance).unwrap();

        let other_instance = sample_extract_instance([2, 2, 3, 4], [5, 6, 7, 8]);

        assert_eq!(
            verify_sample_extract_proof(&other_instance, &proof),
            Err(ProofError::StatementMismatch)
        );
    }

    fn sample_extract_instance(mask: [u64; 4], body: [u64; 4]) -> SampleExtractInstance {
        let glwe = GlweCiphertext {
            mask: vec![Polynomial::from_coeffs(
                mask.into_iter().map(Into::into).collect(),
            )],
            body: Polynomial::from_coeffs(body.into_iter().map(Into::into).collect()),
        };
        SampleExtractInstance::new(glwe)
    }

    #[test]
    fn proves_and_verifies_actual_toy_pbs_with_nonzero_mask() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(101);
        let sk = SecretKey::generate(&params, &mut rng);
        let ek = EvaluationKey::generate(&params, &sk, &mut rng);
        let input_message = 1;
        let output_message = 3;
        let mask_step = GOLDILOCKS_MODULUS / params.exponent_modulus() as u64;
        let mask = (0..params.lwe_dimension)
            .map(|index| Goldilocks::from_u64(mask_step * ((index as u64 % 15) + 1)))
            .collect();
        let input = LweCiphertext::encrypt_with_mask(&params, &sk.input_lwe, input_message, mask);
        let test_polynomial = TestPolynomial::single_slot(&params, input_message, output_message);
        let native_output = bootstrap_without_keyswitch(&params, &ek, &input, &test_polynomial);
        let instance = ActualPbsInstance::new(params.clone(), input, test_polynomial, ek);

        assert_eq!(instance.nonzero_rotation_count(), params.lwe_dimension);
        assert_eq!(instance.output, native_output);
        assert_eq!(
            instance
                .output
                .decrypt(&params, &sk.extracted_output_lwe_key()),
            output_message
        );
        prove_and_verify_actual_pbs(&instance).unwrap();
    }

    #[test]
    fn rejects_actual_pbs_statement_mismatch_before_plonky3_verification() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(102);
        let sk = SecretKey::generate(&params, &mut rng);
        let ek = EvaluationKey::generate(&params, &sk, &mut rng);
        let input_message = 1;
        let output_message = 3;
        let mask_step = GOLDILOCKS_MODULUS / params.exponent_modulus() as u64;
        let mask = (0..params.lwe_dimension)
            .map(|index| Goldilocks::from_u64(mask_step * ((index as u64 % 15) + 1)))
            .collect();
        let input = LweCiphertext::encrypt_with_mask(&params, &sk.input_lwe, input_message, mask);
        let test_polynomial = TestPolynomial::single_slot(&params, input_message, output_message);
        let instance = ActualPbsInstance::new(params.clone(), input, test_polynomial, ek.clone());
        let proof = prove_actual_pbs(&instance).unwrap();

        let other_mask = (0..params.lwe_dimension)
            .map(|index| Goldilocks::from_u64(mask_step * (((index as u64 + 1) % 15) + 1)))
            .collect();
        let other_input =
            LweCiphertext::encrypt_with_mask(&params, &sk.input_lwe, input_message, other_mask);
        let other_test_polynomial =
            TestPolynomial::single_slot(&params, input_message, output_message);
        let other_instance = ActualPbsInstance::new(params, other_input, other_test_polynomial, ek);

        assert_eq!(
            verify_actual_pbs_proof(&other_instance, &proof),
            Err(ProofError::StatementMismatch)
        );
    }
}
