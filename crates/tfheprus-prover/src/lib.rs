//! Plonky3-backed prove/verify proof-of-concept entry points.

mod range_check;

use core::fmt;

use p3_batch_stark::ProverData;
use p3_circuit::circuit::Circuit;
use p3_circuit_prover::common::get_airs_and_degrees_with_prep;
use p3_circuit_prover::config::{self, GoldilocksConfig};
use p3_circuit_prover::{
    BatchStarkProof, BatchStarkProver, CircuitProverData, ConstraintProfile, PrimitiveTable,
    TablePacking, NUM_PRIMITIVE_TABLES,
};
use p3_goldilocks::Goldilocks as P3Goldilocks;
use range_check::{
    proof_range_check_bit_counts, range_check_bit_counts, RangeCheckAirBuilder,
    RangeCheckPreprocessor, RangeCheckProver, RANGE_CHECK_DEFAULT_LANES,
};
use tfheprus_circuits::{
    build_actual_pbs_circuit, build_actual_pbs_step_chain_circuit, build_actual_pbs_step_circuit,
    build_actual_pbs_step_private_circuit, build_mul_xai_circuit, build_poly_mul_circuit,
    build_sample_extract_circuit, ActualPbsInstance, ActualPbsStepChainInstance,
    ActualPbsStepInstance, ActualPbsStepPrivateInstance, MulXaiInstance, PolyMulInstance,
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

pub struct ActualPbsStepProof {
    pub params: Params,
    pub exponent: usize,
    pub public_inputs: Vec<P3Goldilocks>,
    pub proof: BatchStarkProof<GoldilocksConfig>,
}

pub struct ActualPbsStepPrivateProof {
    pub params: Params,
    pub exponent: usize,
    pub public_inputs: Vec<P3Goldilocks>,
    pub proof: BatchStarkProof<GoldilocksConfig>,
}

pub struct ActualPbsStepChainProof {
    pub params: Params,
    pub exponent: usize,
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
pub type ActualPbsStepProofError = ProofError;
pub type ActualPbsStepPrivateProofError = ProofError;
pub type ActualPbsStepChainProofError = ProofError;

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

    verify_circuit_proof(&proof.proof, &proof.public_inputs)
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

    verify_circuit_proof(&proof.proof, &proof.public_inputs)
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

    verify_circuit_proof(&proof.proof, &proof.public_inputs)
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

    verify_circuit_proof(&proof.proof, &proof.public_inputs)
}

pub fn prove_and_verify_actual_pbs(instance: &ActualPbsInstance) -> Result<(), ProofError> {
    let proof = prove_actual_pbs(instance)?;
    verify_actual_pbs_proof(instance, &proof)
}

pub fn prove_actual_pbs_step(
    instance: &ActualPbsStepInstance,
) -> Result<ActualPbsStepProof, ProofError> {
    let circuit = build_actual_pbs_step_circuit(instance)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let public_inputs = instance.public_inputs();
    let private_inputs = instance.private_inputs();
    let proof = prove_circuit(&circuit, &public_inputs, &private_inputs)?;

    Ok(ActualPbsStepProof {
        params: instance.params.clone(),
        exponent: instance.exponent,
        public_inputs,
        proof,
    })
}

pub fn verify_actual_pbs_step_proof(
    instance: &ActualPbsStepInstance,
    proof: &ActualPbsStepProof,
) -> Result<(), ProofError> {
    if proof.params != instance.params
        || proof.exponent != instance.exponent
        || proof.public_inputs != instance.public_inputs()
    {
        return Err(ProofError::StatementMismatch);
    }

    verify_circuit_proof(&proof.proof, &proof.public_inputs)
}

pub fn prove_and_verify_actual_pbs_step(
    instance: &ActualPbsStepInstance,
) -> Result<(), ProofError> {
    let proof = prove_actual_pbs_step(instance)?;
    verify_actual_pbs_step_proof(instance, &proof)
}

pub fn prove_actual_pbs_step_private(
    instance: &ActualPbsStepPrivateInstance,
) -> Result<ActualPbsStepPrivateProof, ProofError> {
    let circuit = build_actual_pbs_step_private_circuit(instance)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let public_inputs = instance.public_inputs();
    let private_inputs = instance.private_inputs();
    let proof = prove_circuit(&circuit, &public_inputs, &private_inputs)?;

    Ok(ActualPbsStepPrivateProof {
        params: instance.params.clone(),
        exponent: instance.exponent,
        public_inputs,
        proof,
    })
}

pub fn verify_actual_pbs_step_private_proof(
    instance: &ActualPbsStepPrivateInstance,
    proof: &ActualPbsStepPrivateProof,
) -> Result<(), ProofError> {
    if proof.params != instance.params
        || proof.exponent != instance.exponent
        || proof.public_inputs != instance.public_inputs()
    {
        return Err(ProofError::StatementMismatch);
    }

    verify_circuit_proof(&proof.proof, &proof.public_inputs)
}

pub fn prove_and_verify_actual_pbs_step_private(
    instance: &ActualPbsStepPrivateInstance,
) -> Result<(), ProofError> {
    let proof = prove_actual_pbs_step_private(instance)?;
    verify_actual_pbs_step_private_proof(instance, &proof)
}

pub fn prove_actual_pbs_step_chain(
    instance: &ActualPbsStepChainInstance,
) -> Result<ActualPbsStepChainProof, ProofError> {
    let circuit = build_actual_pbs_step_chain_circuit(instance)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let public_inputs = instance.public_inputs();
    let private_inputs = instance.private_inputs();
    let proof = prove_circuit(&circuit, &public_inputs, &private_inputs)?;

    Ok(ActualPbsStepChainProof {
        params: instance.params.clone(),
        exponent: instance.exponent,
        public_inputs,
        proof,
    })
}

pub fn verify_actual_pbs_step_chain_proof(
    instance: &ActualPbsStepChainInstance,
    proof: &ActualPbsStepChainProof,
) -> Result<(), ProofError> {
    if proof.params != instance.params
        || proof.exponent != instance.exponent
        || proof.public_inputs != instance.public_inputs()
    {
        return Err(ProofError::StatementMismatch);
    }

    verify_circuit_proof(&proof.proof, &proof.public_inputs)
}

pub fn prove_and_verify_actual_pbs_step_chain(
    instance: &ActualPbsStepChainInstance,
) -> Result<(), ProofError> {
    let proof = prove_actual_pbs_step_chain(instance)?;
    verify_actual_pbs_step_chain_proof(instance, &proof)
}

fn prove_circuit(
    circuit: &Circuit<P3Goldilocks>,
    public_inputs: &[P3Goldilocks],
    private_inputs: &[P3Goldilocks],
) -> Result<BatchStarkProof<GoldilocksConfig>, ProofError> {
    let config = config::goldilocks();
    let table_packing = TablePacking::default();
    let range_bit_counts = range_check_bit_counts(circuit);
    let range_preprocessors = range_preprocessors(&range_bit_counts);
    let range_air_builders = range_air_builders(&range_bit_counts);
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 1>(
            circuit,
            &table_packing,
            &range_preprocessors,
            &range_air_builders,
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

    let mut prover = BatchStarkProver::new(config).with_table_packing(table_packing);
    register_range_check_provers(&mut prover, &range_bit_counts);
    prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))
}

fn verify_circuit_proof(
    proof: &BatchStarkProof<GoldilocksConfig>,
    expected_public_inputs: &[P3Goldilocks],
) -> Result<(), ProofError> {
    if proof.primitive_public_values.len() != NUM_PRIMITIVE_TABLES {
        return Err(ProofError::Plonky3(
            "invalid primitive public-value table count".into(),
        ));
    }
    if proof.primitive_public_values[PrimitiveTable::Public as usize] != expected_public_inputs {
        return Err(ProofError::StatementMismatch);
    }

    let config = config::goldilocks();
    let mut prover = BatchStarkProver::new(config).with_table_packing(proof.table_packing.clone());
    let range_bit_counts = proof_range_check_bit_counts(proof);
    register_range_check_provers(&mut prover, &range_bit_counts);
    prover
        .verify_all_tables(proof)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))
}

fn range_preprocessors(
    bit_counts: &[usize],
) -> Vec<Box<dyn p3_circuit_prover::common::NpoPreprocessor<P3Goldilocks>>> {
    if bit_counts.is_empty() {
        Vec::new()
    } else {
        vec![Box::new(RangeCheckPreprocessor)]
    }
}

fn range_air_builders(
    bit_counts: &[usize],
) -> Vec<Box<dyn p3_circuit_prover::common::NpoAirBuilder<GoldilocksConfig, 1>>> {
    bit_counts
        .iter()
        .map(|&bit_count| {
            Box::new(RangeCheckAirBuilder::new(
                bit_count,
                RANGE_CHECK_DEFAULT_LANES,
            )) as Box<dyn p3_circuit_prover::common::NpoAirBuilder<GoldilocksConfig, 1>>
        })
        .collect()
}

fn register_range_check_provers(
    prover: &mut BatchStarkProver<GoldilocksConfig>,
    bit_counts: &[usize],
) {
    for &bit_count in bit_counts {
        prover.register_table_prover(Box::new(RangeCheckProver::new(
            bit_count,
            RANGE_CHECK_DEFAULT_LANES,
        )));
    }
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;
    use tfheprus_circuits::{pbs_bsk_digest_initial, pbs_mask_digest_initial};
    use tfheprus_core::{
        bootstrap_without_keyswitch, mod_switch_to_exponent, EvaluationKey, GlweCiphertext,
        Goldilocks, LweCiphertext, Polynomial, SecretKey, TestPolynomial, GOLDILOCKS_MODULUS,
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
    fn rejects_forged_public_input_sidecar() {
        let lhs = Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]);
        let rhs = Polynomial::from_coeffs(vec![5u64.into(), 6u64.into(), 7u64.into(), 8u64.into()]);
        let instance = PolyMulInstance::new(lhs, rhs);
        let mut proof = prove_poly_mul(&instance).unwrap();

        let other_lhs =
            Polynomial::from_coeffs(vec![2u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]);
        let other_rhs =
            Polynomial::from_coeffs(vec![5u64.into(), 6u64.into(), 7u64.into(), 8u64.into()]);
        let other_instance = PolyMulInstance::new(other_lhs, other_rhs);
        proof.public_inputs = other_instance.public_inputs();

        assert_eq!(
            verify_poly_mul_proof(&other_instance, &proof),
            Err(ProofError::StatementMismatch)
        );
    }

    #[test]
    fn rejects_forged_embedded_public_inputs() {
        let lhs = Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]);
        let rhs = Polynomial::from_coeffs(vec![5u64.into(), 6u64.into(), 7u64.into(), 8u64.into()]);
        let instance = PolyMulInstance::new(lhs, rhs);
        let mut proof = prove_poly_mul(&instance).unwrap();

        let other_lhs =
            Polynomial::from_coeffs(vec![2u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]);
        let other_rhs =
            Polynomial::from_coeffs(vec![5u64.into(), 6u64.into(), 7u64.into(), 8u64.into()]);
        let other_instance = PolyMulInstance::new(other_lhs, other_rhs);
        let other_public_inputs = other_instance.public_inputs();
        proof.public_inputs = other_public_inputs.clone();
        proof.proof.primitive_public_values[PrimitiveTable::Public as usize] = other_public_inputs;

        let err = verify_poly_mul_proof(&other_instance, &proof)
            .expect_err("tampered STARK public values must fail verification");
        assert!(
            matches!(err, ProofError::Plonky3(_)),
            "unexpected error: {err:?}"
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
        proves_and_verifies_actual_pbs_with_params(params);
    }

    #[test]
    fn proves_and_verifies_actual_pbs_with_approximate_decomposition() {
        let params = Params::new(1, 4, 1, 5, 4, 4);
        proves_and_verifies_actual_pbs_with_params(params);
    }

    #[test]
    fn proves_and_verifies_actual_pbs_step_with_approximate_decomposition() {
        let params = Params::new(1, 4, 1, 5, 4, 4);
        let instance = actual_pbs_step_instance_with_params(params);
        prove_and_verify_actual_pbs_step(&instance).unwrap();
    }

    #[test]
    fn proves_and_verifies_private_actual_pbs_step_with_approximate_decomposition() {
        let params = Params::new(1, 4, 1, 5, 4, 4);
        let public_instance = actual_pbs_step_instance_with_params(params);
        let private_instance = ActualPbsStepPrivateInstance::new(
            public_instance.params.clone(),
            public_instance.mask_value,
            public_instance.input_accumulator.clone(),
            public_instance.selector.clone(),
        );
        assert_eq!(
            private_instance.output_accumulator,
            public_instance.output_accumulator
        );

        prove_and_verify_actual_pbs_step_private(&private_instance).unwrap();
    }

    #[test]
    fn rejects_private_actual_pbs_step_digest_mismatch() {
        let params = Params::new(1, 4, 1, 5, 4, 4);
        let public_instance = actual_pbs_step_instance_with_params(params);
        let instance = ActualPbsStepPrivateInstance::new(
            public_instance.params.clone(),
            public_instance.mask_value,
            public_instance.input_accumulator.clone(),
            public_instance.selector.clone(),
        );
        let proof = prove_actual_pbs_step_private(&instance).unwrap();
        let mut other_instance = instance.clone();
        other_instance.selector_digest[0] += Goldilocks::ONE;

        assert_eq!(
            verify_actual_pbs_step_private_proof(&other_instance, &proof),
            Err(ProofError::StatementMismatch)
        );
    }

    #[test]
    fn proves_and_verifies_chained_actual_pbs_step_with_approximate_decomposition() {
        let params = Params::new(1, 4, 1, 5, 4, 4);
        let public_instance = actual_pbs_step_instance_with_params(params);
        let chain_instance = ActualPbsStepChainInstance::new(
            public_instance.params.clone(),
            public_instance.mask_value,
            public_instance.input_accumulator.clone(),
            public_instance.selector.clone(),
            pbs_bsk_digest_initial(),
            pbs_mask_digest_initial(),
        );
        assert_eq!(
            chain_instance.output_accumulator,
            public_instance.output_accumulator
        );

        prove_and_verify_actual_pbs_step_chain(&chain_instance).unwrap();
    }

    #[test]
    fn rejects_chained_actual_pbs_step_digest_mismatch() {
        let params = Params::new(1, 4, 1, 5, 4, 4);
        let public_instance = actual_pbs_step_instance_with_params(params);
        let instance = ActualPbsStepChainInstance::new(
            public_instance.params.clone(),
            public_instance.mask_value,
            public_instance.input_accumulator.clone(),
            public_instance.selector.clone(),
            pbs_bsk_digest_initial(),
            pbs_mask_digest_initial(),
        );
        let proof = prove_actual_pbs_step_chain(&instance).unwrap();
        let mut other_instance = instance.clone();
        other_instance.mask_digest_out[0] += Goldilocks::ONE;

        assert_eq!(
            verify_actual_pbs_step_chain_proof(&other_instance, &proof),
            Err(ProofError::StatementMismatch)
        );
    }

    fn proves_and_verifies_actual_pbs_with_params(params: Params) {
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

    fn actual_pbs_step_instance_with_params(params: Params) -> ActualPbsStepInstance {
        let mut rng = ChaCha20Rng::seed_from_u64(103);
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
        let body_exponent = mod_switch_to_exponent(&params, input.body);
        let initial_exponent =
            (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
        let input_accumulator = GlweCiphertext::trivial(
            test_polynomial.poly.mul_xai(initial_exponent),
            params.glwe_dimension,
        );

        ActualPbsStepInstance::new(
            params,
            input.mask[0],
            input_accumulator,
            ek.bootstrapping_key[0].clone(),
        )
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
