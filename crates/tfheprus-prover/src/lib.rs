//! Plonky3-backed prove/verify proof-of-concept entry points.

mod keccak;
mod poseidon_chain;
mod range_check;
mod recursive;

use core::fmt;

use p3_batch_stark::common::CommonData;
use p3_batch_stark::ProverData;
use p3_challenger::DuplexChallenger;
use p3_circuit::circuit::Circuit;
use p3_circuit::ops::Poseidon2Config;
use p3_circuit_prover::common::get_airs_and_degrees_with_prep;
use p3_circuit_prover::config::GoldilocksConfig;
use p3_circuit_prover::{
    poseidon2_air_builders_d1, poseidon2_preprocessor, BatchStarkProof, BatchStarkProver,
    CircuitProverData, ConstraintProfile, PrimitiveTable, TablePacking, NUM_PRIMITIVE_TABLES,
};
use p3_commit::ExtensionMmcs;
use p3_dft::Radix2DitParallel;
use p3_field::{extension::BinomialExtensionField, PrimeCharacteristicRing};
use p3_fri::{FriParameters, TwoAdicFriPcs};
use p3_goldilocks::{Goldilocks as P3Goldilocks, Poseidon2Goldilocks};
use p3_merkle_tree::MerkleTreeMmcs;
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use p3_uni_stark::StarkConfig;
use rand_p3::SeedableRng;
use range_check::{
    proof_range_check_bit_counts, range_check_bit_counts, RangeCheckAirBuilder,
    RangeCheckPreprocessor, RangeCheckProver, RANGE_CHECK_DEFAULT_LANES,
};
use serde::{Deserialize, Serialize};
use tfheprus_circuits::{
    build_actual_pbs_chain_chunk_circuit, build_actual_pbs_chain_chunk_shape_circuit,
    build_actual_pbs_circuit, build_actual_pbs_step_chain_circuit, build_actual_pbs_step_circuit,
    build_actual_pbs_step_private_circuit, build_mul_xai_circuit, build_poly_mul_circuit,
    build_sample_extract_circuit, ActualPbsChainChunkInstance, ActualPbsInstance,
    ActualPbsStepChainInstance, ActualPbsStepInstance, ActualPbsStepPrivateInstance,
    MulXaiInstance, PolyMulInstance, SampleExtractInstance, SELECTOR_DIGEST_WIDTH,
};
use tfheprus_core::Params;

pub use keccak::{
    prove_and_verify_keccak_f1600, prove_keccak_f1600, verify_keccak_f1600, KeccakF1600Proof,
    KeccakF1600Statement,
};

const COMPACT_ACCUMULATOR_DIGEST_TAG: u64 = 0x676c_7765_5f61_6363;
pub(crate) const BASE_PROOF_FRI_LOG_BLOWUP: usize = 1;
pub(crate) const BASE_PROOF_FRI_LOG_FINAL_POLY_LEN: usize = 0;
pub(crate) const BASE_PROOF_FRI_MAX_LOG_ARITY: usize = 3;
pub(crate) const BASE_PROOF_FRI_COMMIT_POW_BITS: usize = 0;
pub(crate) const BASE_PROOF_FRI_QUERY_POW_BITS: usize = 16;
pub(crate) const BASE_PROOF_FRI_NUM_QUERIES: usize = 100;
pub(crate) const PROOF_FRI_LOG_BLOWUP: usize = 4;
pub(crate) const PROOF_FRI_LOG_FINAL_POLY_LEN: usize = 0;
pub(crate) const PROOF_FRI_MAX_LOG_ARITY: usize = 3;
pub(crate) const PROOF_FRI_COMMIT_POW_BITS: usize = 0;
pub(crate) const PROOF_FRI_QUERY_POW_BITS: usize = 20;
pub(crate) const PROOF_FRI_NUM_QUERIES: usize = 20;

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

#[derive(Serialize, Deserialize)]
pub struct ActualPbsChainChunkProof {
    pub params: Params,
    pub step_count: usize,
    pub exponents: Vec<usize>,
    pub public_inputs: Vec<P3Goldilocks>,
    pub proof: BatchStarkProof<GoldilocksConfig>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ActualPbsChainChunkStatement {
    pub params: Params,
    pub step_count: usize,
    pub public_inputs: Vec<P3Goldilocks>,
}

impl ActualPbsChainChunkStatement {
    pub fn from_instance(instance: &ActualPbsChainChunkInstance) -> Self {
        Self {
            params: instance.params.clone(),
            step_count: instance.step_count(),
            public_inputs: instance.public_inputs(),
        }
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct ActualPbsChainSummary {
    pub params: Params,
    pub step_count: usize,
    pub public_inputs: Vec<P3Goldilocks>,
}

impl ActualPbsChainSummary {
    pub fn from_chunk_statement(
        statement: &ActualPbsChainChunkStatement,
    ) -> Result<Self, ProofError> {
        chunk_statement_public_view(statement)?;
        Ok(Self {
            params: statement.params.clone(),
            step_count: statement.step_count,
            public_inputs: statement.public_inputs.clone(),
        })
    }

    pub fn combine(left: &Self, right: &Self) -> Result<Self, ProofError> {
        if left.params != right.params || left.step_count == 0 || right.step_count == 0 {
            return Err(ProofError::StatementMismatch);
        }
        let step_count = left
            .step_count
            .checked_add(right.step_count)
            .ok_or(ProofError::StatementMismatch)?;
        if step_count > left.params.lwe_dimension {
            return Err(ProofError::StatementMismatch);
        }

        let left_view = chunk_summary_public_view(left)?;
        let right_view = chunk_summary_public_view(right)?;
        if left_view.output_accumulator != right_view.input_accumulator
            || left_view.bsk_digest_out != right_view.bsk_digest_in
            || left_view.mask_digest_out != right_view.mask_digest_in
        {
            return Err(ProofError::StatementMismatch);
        }

        let mut public_inputs = Vec::with_capacity(left.public_inputs.len());
        public_inputs.extend_from_slice(left_view.input_accumulator);
        public_inputs.extend_from_slice(left_view.bsk_digest_in);
        public_inputs.extend_from_slice(right_view.bsk_digest_out);
        public_inputs.extend_from_slice(left_view.mask_digest_in);
        public_inputs.extend_from_slice(right_view.mask_digest_out);
        public_inputs.extend_from_slice(right_view.output_accumulator);

        Ok(Self {
            params: left.params.clone(),
            step_count,
            public_inputs,
        })
    }

    pub fn field_values(&self) -> Vec<P3Goldilocks> {
        let mut values = Vec::with_capacity(chain_summary_field_count(&self.params));
        values.extend(param_public_values(&self.params));
        values.push(P3Goldilocks::from_u64(self.step_count as u64));
        values.extend(self.public_inputs.iter().copied());
        values
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct CompactActualPbsChainSummary {
    pub params: Params,
    pub step_count: usize,
    pub public_inputs: Vec<P3Goldilocks>,
}

impl CompactActualPbsChainSummary {
    pub fn from_chunk_statement(
        statement: &ActualPbsChainChunkStatement,
    ) -> Result<Self, ProofError> {
        let view = chunk_statement_public_view(statement)?;
        let mut public_inputs = Vec::with_capacity(compact_chain_summary_public_field_count());
        public_inputs.extend(compact_accumulator_digest(view.input_accumulator));
        public_inputs.extend_from_slice(view.bsk_digest_in);
        public_inputs.extend_from_slice(view.bsk_digest_out);
        public_inputs.extend_from_slice(view.mask_digest_in);
        public_inputs.extend_from_slice(view.mask_digest_out);
        public_inputs.extend(compact_accumulator_digest(view.output_accumulator));

        Ok(Self {
            params: statement.params.clone(),
            step_count: statement.step_count,
            public_inputs,
        })
    }

    pub fn from_full_summary(summary: &ActualPbsChainSummary) -> Result<Self, ProofError> {
        let statement = ActualPbsChainChunkStatement {
            params: summary.params.clone(),
            step_count: summary.step_count,
            public_inputs: summary.public_inputs.clone(),
        };
        Self::from_chunk_statement(&statement)
    }

    pub fn combine(left: &Self, right: &Self) -> Result<Self, ProofError> {
        if left.params != right.params || left.step_count == 0 || right.step_count == 0 {
            return Err(ProofError::StatementMismatch);
        }
        let step_count = left
            .step_count
            .checked_add(right.step_count)
            .ok_or(ProofError::StatementMismatch)?;
        if step_count > left.params.lwe_dimension {
            return Err(ProofError::StatementMismatch);
        }

        let left_view = compact_summary_public_view(left)?;
        let right_view = compact_summary_public_view(right)?;
        if left_view.output_accumulator != right_view.input_accumulator
            || left_view.bsk_digest_out != right_view.bsk_digest_in
            || left_view.mask_digest_out != right_view.mask_digest_in
        {
            return Err(ProofError::StatementMismatch);
        }

        let mut public_inputs = Vec::with_capacity(compact_chain_summary_public_field_count());
        public_inputs.extend_from_slice(left_view.input_accumulator);
        public_inputs.extend_from_slice(left_view.bsk_digest_in);
        public_inputs.extend_from_slice(right_view.bsk_digest_out);
        public_inputs.extend_from_slice(left_view.mask_digest_in);
        public_inputs.extend_from_slice(right_view.mask_digest_out);
        public_inputs.extend_from_slice(right_view.output_accumulator);

        Ok(Self {
            params: left.params.clone(),
            step_count,
            public_inputs,
        })
    }

    pub fn field_values(&self) -> Vec<P3Goldilocks> {
        let mut values = Vec::with_capacity(compact_chain_summary_field_count());
        values.extend(param_public_values(&self.params));
        values.push(P3Goldilocks::from_u64(self.step_count as u64));
        values.extend(self.public_inputs.iter().copied());
        values
    }
}

#[derive(Serialize, Deserialize)]
pub struct RecursiveActualPbsChainChunkProof {
    pub base: ActualPbsChainChunkProof,
    pub recursion: recursive::RecursiveBatchProof,
    pub chain_summary: ActualPbsChainSummary,
}

#[derive(Serialize, Deserialize)]
pub struct CompactRecursiveActualPbsChainChunkProof {
    pub base: ActualPbsChainChunkProof,
    pub recursion: recursive::RecursiveBatchProof,
    pub chain_summary: CompactActualPbsChainSummary,
}

pub struct AggregatedRecursiveActualPbsChainChunkPairProof {
    pub left: RecursiveActualPbsChainChunkProof,
    pub right: RecursiveActualPbsChainChunkProof,
    pub aggregation: recursive::AggregatedRecursiveBatchProof,
    pub chain_summary: ActualPbsChainSummary,
}

pub struct AggregatedRecursiveActualPbsChainChunkTreeProof {
    pub leaves: Vec<RecursiveActualPbsChainChunkProof>,
    pub layers: Vec<Vec<recursive::AggregatedRecursiveBatchProof>>,
    pub chain_summary: ActualPbsChainSummary,
}

#[derive(Serialize, Deserialize)]
pub struct AggregatedRecursiveActualPbsChainNodeProof {
    pub chain_summary: ActualPbsChainSummary,
    pub aggregation: recursive::AggregatedRecursiveBatchProof,
}

#[derive(Serialize, Deserialize)]
pub struct CompactAggregatedRecursiveActualPbsChainNodeProof {
    pub chain_summary: CompactActualPbsChainSummary,
    pub aggregation: recursive::AggregatedRecursiveBatchProof,
}

#[derive(Serialize, Deserialize)]
pub struct AggregatedRecursiveActualPbsChainFrontierProof {
    pub chain_summary: ActualPbsChainSummary,
    pub nodes: Vec<AggregatedRecursiveActualPbsChainNodeProof>,
}

#[derive(Serialize, Deserialize)]
pub struct AggregatedRecursiveActualPbsChainRootProof {
    pub chain_summary: ActualPbsChainSummary,
    pub root: recursive::AggregatedRecursiveBatchProof,
}

#[derive(Serialize, Deserialize)]
pub struct CompactAggregatedRecursiveActualPbsChainRootProof {
    pub chain_summary: CompactActualPbsChainSummary,
    pub root: recursive::AggregatedRecursiveBatchProof,
}

pub enum RecursiveActualPbsChainNode<'a> {
    Leaf(&'a RecursiveActualPbsChainChunkProof),
    Aggregate(&'a AggregatedRecursiveActualPbsChainNodeProof),
}

pub enum CompactRecursiveActualPbsChainNode<'a> {
    Leaf(&'a CompactRecursiveActualPbsChainChunkProof),
    Aggregate(&'a CompactAggregatedRecursiveActualPbsChainNodeProof),
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RecursiveProofSizeBreakdown {
    pub public_inputs_bytes: usize,
    pub batch_stark_bytes: usize,
    pub core_proof_bytes: usize,
    pub commitments_bytes: usize,
    pub opened_values_bytes: usize,
    pub opening_proof_bytes: usize,
    pub global_lookup_data_bytes: usize,
    pub degree_bits_bytes: usize,
    pub primitive_public_values_bytes: usize,
    pub non_primitives_bytes: usize,
    pub structural_metadata_bytes: usize,
}

impl AggregatedRecursiveActualPbsChainChunkTreeProof {
    pub fn leaf_count(&self) -> usize {
        self.leaves.len()
    }

    pub fn layer_count(&self) -> usize {
        self.layers.len()
    }

    pub fn root_public_input_count(&self) -> Option<usize> {
        self.layers
            .last()
            .and_then(|layer| layer.first())
            .map(|proof| proof.public_input_count())
    }

    pub fn root_table_count(&self) -> Option<usize> {
        self.layers
            .last()
            .and_then(|layer| layer.first())
            .map(|proof| proof.table_count())
    }

    pub fn into_root_proof(self) -> Result<AggregatedRecursiveActualPbsChainRootProof, ProofError> {
        let mut root_layer = self
            .layers
            .into_iter()
            .last()
            .ok_or(ProofError::StatementMismatch)?;
        if root_layer.len() != 1 {
            return Err(ProofError::StatementMismatch);
        }
        Ok(AggregatedRecursiveActualPbsChainRootProof {
            chain_summary: self.chain_summary,
            root: root_layer.remove(0),
        })
    }
}

impl AggregatedRecursiveActualPbsChainNodeProof {
    pub fn public_input_count(&self) -> usize {
        self.aggregation.public_input_count()
    }

    pub fn table_count(&self) -> usize {
        self.aggregation.table_count()
    }

    pub fn into_root_proof(self) -> AggregatedRecursiveActualPbsChainRootProof {
        AggregatedRecursiveActualPbsChainRootProof {
            chain_summary: self.chain_summary,
            root: self.aggregation,
        }
    }
}

impl CompactAggregatedRecursiveActualPbsChainNodeProof {
    pub fn public_input_count(&self) -> usize {
        self.aggregation.public_input_count()
    }

    pub fn table_count(&self) -> usize {
        self.aggregation.table_count()
    }

    pub fn into_root_proof(self) -> CompactAggregatedRecursiveActualPbsChainRootProof {
        CompactAggregatedRecursiveActualPbsChainRootProof {
            chain_summary: self.chain_summary,
            root: self.aggregation,
        }
    }
}

impl AggregatedRecursiveActualPbsChainFrontierProof {
    pub fn node_count(&self) -> usize {
        self.nodes.len()
    }

    pub fn total_public_input_count(&self) -> usize {
        self.nodes
            .iter()
            .map(AggregatedRecursiveActualPbsChainNodeProof::public_input_count)
            .sum()
    }

    pub fn max_public_input_count(&self) -> usize {
        self.nodes
            .iter()
            .map(AggregatedRecursiveActualPbsChainNodeProof::public_input_count)
            .max()
            .unwrap_or(0)
    }
}

impl<'a> RecursiveActualPbsChainNode<'a> {
    fn chain_summary(&self) -> &ActualPbsChainSummary {
        match self {
            Self::Leaf(proof) => &proof.chain_summary,
            Self::Aggregate(proof) => &proof.chain_summary,
        }
    }

    fn batch_proof(&self) -> &BatchStarkProof<GoldilocksConfig> {
        match self {
            Self::Leaf(proof) => proof.recursion.batch_proof(),
            Self::Aggregate(proof) => proof.aggregation.batch_proof(),
        }
    }
}

impl<'a> CompactRecursiveActualPbsChainNode<'a> {
    fn chain_summary(&self) -> &CompactActualPbsChainSummary {
        match self {
            Self::Leaf(proof) => &proof.chain_summary,
            Self::Aggregate(proof) => &proof.chain_summary,
        }
    }

    fn batch_proof(&self) -> &BatchStarkProof<GoldilocksConfig> {
        match self {
            Self::Leaf(proof) => proof.recursion.batch_proof(),
            Self::Aggregate(proof) => proof.aggregation.batch_proof(),
        }
    }
}

impl ActualPbsChainChunkProof {
    pub fn public_statement(&self) -> ActualPbsChainChunkStatement {
        ActualPbsChainChunkStatement {
            params: self.params.clone(),
            step_count: self.step_count,
            public_inputs: self.public_inputs.clone(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum ProofError {
    StatementMismatch,
    Plonky3(String),
    Serialization(String),
}

impl fmt::Display for ProofError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StatementMismatch => write!(f, "proof does not match the requested statement"),
            Self::Plonky3(message) => write!(f, "plonky3 error: {message}"),
            Self::Serialization(message) => write!(f, "serialization error: {message}"),
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
pub type ActualPbsChainChunkProofError = ProofError;
pub type RecursiveActualPbsChainChunkProofError = ProofError;

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

pub fn prove_actual_pbs_chain_chunk(
    instance: &ActualPbsChainChunkInstance,
) -> Result<ActualPbsChainChunkProof, ProofError> {
    let circuit = build_actual_pbs_chain_chunk_circuit(instance)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let public_inputs = instance.public_inputs();
    let private_inputs = instance.private_inputs();
    let proof = prove_circuit(&circuit, &public_inputs, &private_inputs)?;

    Ok(ActualPbsChainChunkProof {
        params: instance.params.clone(),
        step_count: instance.step_count(),
        exponents: instance.exponents.clone(),
        public_inputs,
        proof,
    })
}

pub fn verify_actual_pbs_chain_chunk_proof(
    instance: &ActualPbsChainChunkInstance,
    proof: &ActualPbsChainChunkProof,
) -> Result<(), ProofError> {
    if proof.params != instance.params
        || proof.step_count != instance.step_count()
        || proof.exponents != instance.exponents
        || proof.public_inputs != instance.public_inputs()
    {
        return Err(ProofError::StatementMismatch);
    }

    verify_circuit_proof(&proof.proof, &proof.public_inputs)
}

pub fn verify_actual_pbs_chain_chunk_statement_proof(
    statement: &ActualPbsChainChunkStatement,
    proof: &ActualPbsChainChunkProof,
) -> Result<(), ProofError> {
    if proof.params != statement.params
        || proof.step_count != statement.step_count
        || proof.public_inputs != statement.public_inputs
    {
        return Err(ProofError::StatementMismatch);
    }

    let circuit =
        build_actual_pbs_chain_chunk_shape_circuit(&statement.params, statement.step_count)
            .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    verify_circuit_proof_for_circuit(&circuit, &proof.proof, &proof.public_inputs)
}

pub fn prove_and_verify_actual_pbs_chain_chunk(
    instance: &ActualPbsChainChunkInstance,
) -> Result<(), ProofError> {
    let proof = prove_actual_pbs_chain_chunk(instance)?;
    verify_actual_pbs_chain_chunk_proof(instance, &proof)
}

pub fn prove_recursive_actual_pbs_chain_chunk(
    instance: &ActualPbsChainChunkInstance,
) -> Result<RecursiveActualPbsChainChunkProof, ProofError> {
    let base = prove_actual_pbs_chain_chunk(instance)?;
    let chain_summary = ActualPbsChainSummary::from_chunk_statement(&base.public_statement())?;
    let recursion = recursive::prove_recursive_batch_with_leaf_summary(
        &base.proof,
        &chain_summary.field_values(),
        chain_summary_header_len(),
    )?;

    Ok(RecursiveActualPbsChainChunkProof {
        base,
        recursion,
        chain_summary,
    })
}

pub fn prove_private_recursive_actual_pbs_chain_chunk(
    instance: &ActualPbsChainChunkInstance,
) -> Result<RecursiveActualPbsChainChunkProof, ProofError> {
    let base = prove_actual_pbs_chain_chunk(instance)?;
    let chain_summary = ActualPbsChainSummary::from_chunk_statement(&base.public_statement())?;
    let recursion = recursive::prove_private_recursive_batch_with_leaf_summary(
        &base.proof,
        &chain_summary.field_values(),
        chain_summary_header_len(),
    )?;

    Ok(RecursiveActualPbsChainChunkProof {
        base,
        recursion,
        chain_summary,
    })
}

pub fn prove_private_compact_recursive_actual_pbs_chain_chunk(
    instance: &ActualPbsChainChunkInstance,
) -> Result<CompactRecursiveActualPbsChainChunkProof, ProofError> {
    let base = prove_actual_pbs_chain_chunk(instance)?;
    let statement = base.public_statement();
    let chain_summary = CompactActualPbsChainSummary::from_chunk_statement(&statement)?;
    let recursion = recursive::prove_private_recursive_batch_with_compact_leaf_summary(
        &base.proof,
        &chain_summary.field_values(),
        chain_summary_header_len(),
        &chain_summary_layout(&chain_summary.params),
        &compact_chain_summary_layout(),
    )?;

    Ok(CompactRecursiveActualPbsChainChunkProof {
        base,
        recursion,
        chain_summary,
    })
}

pub fn verify_recursive_actual_pbs_chain_chunk_proof(
    instance: &ActualPbsChainChunkInstance,
    proof: &RecursiveActualPbsChainChunkProof,
) -> Result<(), ProofError> {
    verify_actual_pbs_chain_chunk_proof(instance, &proof.base)?;
    let statement = ActualPbsChainChunkStatement::from_instance(instance);
    verify_recursive_actual_pbs_chain_chunk_statement_proof(&statement, proof)
}

pub fn verify_recursive_actual_pbs_chain_chunk_statement_proof(
    statement: &ActualPbsChainChunkStatement,
    proof: &RecursiveActualPbsChainChunkProof,
) -> Result<(), ProofError> {
    verify_actual_pbs_chain_chunk_statement_proof(statement, &proof.base)?;
    let expected_summary = ActualPbsChainSummary::from_chunk_statement(statement)?;
    if proof.chain_summary != expected_summary {
        return Err(ProofError::StatementMismatch);
    }
    recursive::verify_recursive_batch_with_leaf_summary_for_base(
        &proof.base.proof,
        &proof.chain_summary.field_values(),
        &proof.recursion,
    )
}

pub fn verify_private_recursive_actual_pbs_chain_chunk_statement_proof(
    statement: &ActualPbsChainChunkStatement,
    proof: &RecursiveActualPbsChainChunkProof,
) -> Result<(), ProofError> {
    verify_actual_pbs_chain_chunk_statement_proof(statement, &proof.base)?;
    let expected_summary = ActualPbsChainSummary::from_chunk_statement(statement)?;
    if proof.chain_summary != expected_summary {
        return Err(ProofError::StatementMismatch);
    }
    recursive::verify_recursive_batch_with_private_leaf_summary(
        &proof.chain_summary.field_values(),
        &proof.recursion,
    )
}

pub fn verify_private_compact_recursive_actual_pbs_chain_chunk_statement_proof(
    statement: &ActualPbsChainChunkStatement,
    proof: &CompactRecursiveActualPbsChainChunkProof,
) -> Result<(), ProofError> {
    verify_actual_pbs_chain_chunk_statement_proof(statement, &proof.base)?;
    let expected_summary = CompactActualPbsChainSummary::from_chunk_statement(statement)?;
    if proof.chain_summary != expected_summary {
        return Err(ProofError::StatementMismatch);
    }
    recursive::verify_recursive_batch_with_private_leaf_summary(
        &proof.chain_summary.field_values(),
        &proof.recursion,
    )
}

pub fn prove_and_verify_recursive_actual_pbs_chain_chunk(
    instance: &ActualPbsChainChunkInstance,
) -> Result<(), ProofError> {
    let proof = prove_recursive_actual_pbs_chain_chunk(instance)?;
    verify_recursive_actual_pbs_chain_chunk_proof(instance, &proof)
}

pub fn prove_aggregated_recursive_actual_pbs_chain_chunk_pair(
    left: RecursiveActualPbsChainChunkProof,
    right: RecursiveActualPbsChainChunkProof,
) -> Result<AggregatedRecursiveActualPbsChainChunkPairProof, ProofError> {
    let chain_summary = ActualPbsChainSummary::combine(&left.chain_summary, &right.chain_summary)?;
    let aggregation = recursive::prove_aggregate_batch_proofs_with_chain_summary(
        left.recursion.batch_proof(),
        right.recursion.batch_proof(),
        &chain_summary.field_values(),
        Some(&chain_summary_layout(&chain_summary.params)),
    )?;

    Ok(AggregatedRecursiveActualPbsChainChunkPairProof {
        left,
        right,
        aggregation,
        chain_summary,
    })
}

pub fn verify_aggregated_recursive_actual_pbs_chain_chunk_pair_statement_proof(
    left_statement: &ActualPbsChainChunkStatement,
    right_statement: &ActualPbsChainChunkStatement,
    proof: &AggregatedRecursiveActualPbsChainChunkPairProof,
) -> Result<(), ProofError> {
    verify_recursive_actual_pbs_chain_chunk_statement_proof(left_statement, &proof.left)?;
    verify_recursive_actual_pbs_chain_chunk_statement_proof(right_statement, &proof.right)?;
    let expected_summary =
        ActualPbsChainSummary::combine(&proof.left.chain_summary, &proof.right.chain_summary)?;
    if proof.chain_summary != expected_summary {
        return Err(ProofError::StatementMismatch);
    }
    recursive::verify_aggregated_recursive_batch_with_summary_for_child_proofs(
        proof.left.recursion.batch_proof(),
        proof.right.recursion.batch_proof(),
        &proof.chain_summary.field_values(),
        &proof.aggregation,
    )
}

pub fn prove_aggregated_recursive_actual_pbs_chain_node_pair(
    left: RecursiveActualPbsChainNode<'_>,
    right: RecursiveActualPbsChainNode<'_>,
) -> Result<AggregatedRecursiveActualPbsChainNodeProof, ProofError> {
    let chain_summary =
        ActualPbsChainSummary::combine(left.chain_summary(), right.chain_summary())?;
    let aggregation = recursive::prove_aggregate_batch_proofs_with_chain_summary(
        left.batch_proof(),
        right.batch_proof(),
        &chain_summary.field_values(),
        Some(&chain_summary_layout(&chain_summary.params)),
    )?;

    Ok(AggregatedRecursiveActualPbsChainNodeProof {
        chain_summary,
        aggregation,
    })
}

pub fn prove_private_aggregated_recursive_actual_pbs_chain_node_pair(
    left: RecursiveActualPbsChainNode<'_>,
    right: RecursiveActualPbsChainNode<'_>,
) -> Result<AggregatedRecursiveActualPbsChainNodeProof, ProofError> {
    let chain_summary =
        ActualPbsChainSummary::combine(left.chain_summary(), right.chain_summary())?;
    let aggregation = recursive::prove_private_aggregate_batch_proofs_with_chain_summary(
        left.batch_proof(),
        right.batch_proof(),
        &chain_summary.field_values(),
        Some(&chain_summary_layout(&chain_summary.params)),
    )?;

    Ok(AggregatedRecursiveActualPbsChainNodeProof {
        chain_summary,
        aggregation,
    })
}

pub fn prove_private_compact_aggregated_recursive_actual_pbs_chain_node_pair(
    left: CompactRecursiveActualPbsChainNode<'_>,
    right: CompactRecursiveActualPbsChainNode<'_>,
) -> Result<CompactAggregatedRecursiveActualPbsChainNodeProof, ProofError> {
    let chain_summary =
        CompactActualPbsChainSummary::combine(left.chain_summary(), right.chain_summary())?;
    let aggregation = recursive::prove_private_aggregate_batch_proofs_with_chain_summary(
        left.batch_proof(),
        right.batch_proof(),
        &chain_summary.field_values(),
        Some(&compact_chain_summary_layout()),
    )?;

    Ok(CompactAggregatedRecursiveActualPbsChainNodeProof {
        chain_summary,
        aggregation,
    })
}

pub fn verify_aggregated_recursive_actual_pbs_chain_node_pair_proof(
    left: RecursiveActualPbsChainNode<'_>,
    right: RecursiveActualPbsChainNode<'_>,
    proof: &AggregatedRecursiveActualPbsChainNodeProof,
) -> Result<(), ProofError> {
    let expected_summary =
        ActualPbsChainSummary::combine(left.chain_summary(), right.chain_summary())?;
    if proof.chain_summary != expected_summary {
        return Err(ProofError::StatementMismatch);
    }
    recursive::verify_aggregated_recursive_batch_with_summary_for_child_proofs(
        left.batch_proof(),
        right.batch_proof(),
        &proof.chain_summary.field_values(),
        &proof.aggregation,
    )
}

pub fn verify_private_compact_aggregated_recursive_actual_pbs_chain_node_pair_proof(
    left: CompactRecursiveActualPbsChainNode<'_>,
    right: CompactRecursiveActualPbsChainNode<'_>,
    proof: &CompactAggregatedRecursiveActualPbsChainNodeProof,
) -> Result<(), ProofError> {
    let expected_summary =
        CompactActualPbsChainSummary::combine(left.chain_summary(), right.chain_summary())?;
    if proof.chain_summary != expected_summary {
        return Err(ProofError::StatementMismatch);
    }
    recursive::verify_aggregated_recursive_batch_with_summary_for_child_proofs(
        left.batch_proof(),
        right.batch_proof(),
        &proof.chain_summary.field_values(),
        &proof.aggregation,
    )
}

pub fn build_aggregated_recursive_actual_pbs_chain_frontier_proof(
    nodes: Vec<AggregatedRecursiveActualPbsChainNodeProof>,
) -> Result<AggregatedRecursiveActualPbsChainFrontierProof, ProofError> {
    let chain_summary = combine_actual_pbs_chain_summaries(
        &nodes
            .iter()
            .map(|node| node.chain_summary.clone())
            .collect::<Vec<_>>(),
    )?;
    Ok(AggregatedRecursiveActualPbsChainFrontierProof {
        chain_summary,
        nodes,
    })
}

pub fn validate_actual_pbs_chain_chunk_statements(
    statements: &[ActualPbsChainChunkStatement],
) -> Result<(), ProofError> {
    validate_aggregation_leaf_count(statements.len())?;
    let params = &statements[0].params;
    let mut total_steps = 0usize;
    for statement in statements {
        if &statement.params != params || statement.step_count == 0 {
            return Err(ProofError::StatementMismatch);
        }
        total_steps = total_steps
            .checked_add(statement.step_count)
            .ok_or(ProofError::StatementMismatch)?;
        if total_steps > params.lwe_dimension {
            return Err(ProofError::StatementMismatch);
        }
        chunk_statement_public_view(statement)?;
    }

    for pair in statements.windows(2) {
        let left = chunk_statement_public_view(&pair[0])?;
        let right = chunk_statement_public_view(&pair[1])?;
        if left.output_accumulator != right.input_accumulator
            || left.bsk_digest_out != right.bsk_digest_in
            || left.mask_digest_out != right.mask_digest_in
        {
            return Err(ProofError::StatementMismatch);
        }
    }

    Ok(())
}

pub fn combine_actual_pbs_chain_summaries(
    summaries: &[ActualPbsChainSummary],
) -> Result<ActualPbsChainSummary, ProofError> {
    let mut summaries = summaries.iter();
    let mut summary = summaries
        .next()
        .ok_or(ProofError::StatementMismatch)?
        .clone();
    for next in summaries {
        summary = ActualPbsChainSummary::combine(&summary, next)?;
    }
    Ok(summary)
}

pub fn combine_compact_actual_pbs_chain_summaries(
    summaries: &[CompactActualPbsChainSummary],
) -> Result<CompactActualPbsChainSummary, ProofError> {
    let mut summaries = summaries.iter();
    let mut summary = summaries
        .next()
        .ok_or(ProofError::StatementMismatch)?
        .clone();
    for next in summaries {
        summary = CompactActualPbsChainSummary::combine(&summary, next)?;
    }
    Ok(summary)
}

pub fn prove_aggregated_recursive_actual_pbs_chain_chunk_tree(
    leaves: Vec<RecursiveActualPbsChainChunkProof>,
) -> Result<AggregatedRecursiveActualPbsChainChunkTreeProof, ProofError> {
    validate_aggregation_leaf_count(leaves.len())?;

    let mut layers = Vec::new();
    let mut current_nodes = (0..leaves.len())
        .map(AggregationNodeRef::Leaf)
        .collect::<Vec<_>>();
    let mut current_summaries = leaves
        .iter()
        .map(|leaf| leaf.chain_summary.clone())
        .collect::<Vec<_>>();
    while current_nodes.len() > 1 {
        let layer_index = layers.len();
        let pair_count = current_nodes.len() / 2;
        let mut next_layer = Vec::with_capacity(pair_count);
        let mut next_nodes = Vec::with_capacity(current_nodes.len().div_ceil(2));
        let mut next_summaries = Vec::with_capacity(current_summaries.len().div_ceil(2));
        for node_index in 0..pair_count {
            let left =
                aggregation_node_batch_proof(current_nodes[node_index * 2], &leaves, &layers);
            let right =
                aggregation_node_batch_proof(current_nodes[node_index * 2 + 1], &leaves, &layers);
            let chain_summary = ActualPbsChainSummary::combine(
                &current_summaries[node_index * 2],
                &current_summaries[node_index * 2 + 1],
            )?;
            next_layer.push(recursive::prove_aggregate_batch_proofs_with_chain_summary(
                left,
                right,
                &chain_summary.field_values(),
                Some(&chain_summary_layout(&chain_summary.params)),
            )?);
            next_nodes.push(AggregationNodeRef::Aggregate {
                layer_index,
                node_index,
            });
            next_summaries.push(chain_summary);
        }
        if current_nodes.len() % 2 == 1 {
            let carried_node = *current_nodes.last().ok_or(ProofError::StatementMismatch)?;
            next_nodes.push(carried_node);
            next_summaries.push(
                current_summaries
                    .last()
                    .ok_or(ProofError::StatementMismatch)?
                    .clone(),
            );
        }
        layers.push(next_layer);
        current_nodes = next_nodes;
        current_summaries = next_summaries;
    }

    let chain_summary = current_summaries
        .pop()
        .ok_or(ProofError::StatementMismatch)?;

    Ok(AggregatedRecursiveActualPbsChainChunkTreeProof {
        leaves,
        layers,
        chain_summary,
    })
}

pub fn prove_private_aggregated_recursive_actual_pbs_chain_chunk_tree(
    leaves: Vec<RecursiveActualPbsChainChunkProof>,
) -> Result<AggregatedRecursiveActualPbsChainChunkTreeProof, ProofError> {
    validate_aggregation_leaf_count(leaves.len())?;

    let mut layers = Vec::new();
    let mut current_nodes = (0..leaves.len())
        .map(AggregationNodeRef::Leaf)
        .collect::<Vec<_>>();
    let mut current_summaries = leaves
        .iter()
        .map(|leaf| leaf.chain_summary.clone())
        .collect::<Vec<_>>();
    while current_nodes.len() > 1 {
        let layer_index = layers.len();
        let pair_count = current_nodes.len() / 2;
        let mut next_layer = Vec::with_capacity(pair_count);
        let mut next_nodes = Vec::with_capacity(current_nodes.len().div_ceil(2));
        let mut next_summaries = Vec::with_capacity(current_summaries.len().div_ceil(2));
        for node_index in 0..pair_count {
            let left =
                aggregation_node_batch_proof(current_nodes[node_index * 2], &leaves, &layers);
            let right =
                aggregation_node_batch_proof(current_nodes[node_index * 2 + 1], &leaves, &layers);
            let chain_summary = ActualPbsChainSummary::combine(
                &current_summaries[node_index * 2],
                &current_summaries[node_index * 2 + 1],
            )?;
            next_layer.push(
                recursive::prove_private_aggregate_batch_proofs_with_chain_summary(
                    left,
                    right,
                    &chain_summary.field_values(),
                    Some(&chain_summary_layout(&chain_summary.params)),
                )?,
            );
            next_nodes.push(AggregationNodeRef::Aggregate {
                layer_index,
                node_index,
            });
            next_summaries.push(chain_summary);
        }
        if current_nodes.len() % 2 == 1 {
            let carried_node = *current_nodes.last().ok_or(ProofError::StatementMismatch)?;
            next_nodes.push(carried_node);
            next_summaries.push(
                current_summaries
                    .last()
                    .ok_or(ProofError::StatementMismatch)?
                    .clone(),
            );
        }
        layers.push(next_layer);
        current_nodes = next_nodes;
        current_summaries = next_summaries;
    }

    let chain_summary = current_summaries
        .pop()
        .ok_or(ProofError::StatementMismatch)?;

    Ok(AggregatedRecursiveActualPbsChainChunkTreeProof {
        leaves,
        layers,
        chain_summary,
    })
}

pub fn verify_aggregated_recursive_actual_pbs_chain_chunk_tree_statement_proof(
    statements: &[ActualPbsChainChunkStatement],
    proof: &AggregatedRecursiveActualPbsChainChunkTreeProof,
) -> Result<(), ProofError> {
    validate_aggregation_leaf_count(proof.leaves.len())?;
    if statements.len() != proof.leaves.len() {
        return Err(ProofError::StatementMismatch);
    }
    validate_actual_pbs_chain_chunk_statements(statements)?;
    let expected_summary = chain_summary_from_statements(statements)?;
    if proof.chain_summary != expected_summary {
        return Err(ProofError::StatementMismatch);
    }

    for (statement, leaf) in statements.iter().zip(proof.leaves.iter()) {
        verify_recursive_actual_pbs_chain_chunk_statement_proof(statement, leaf)?;
    }

    let mut current_nodes = (0..proof.leaves.len())
        .map(AggregationNodeRef::Leaf)
        .collect::<Vec<_>>();
    let mut current_summaries = proof
        .leaves
        .iter()
        .map(|leaf| leaf.chain_summary.clone())
        .collect::<Vec<_>>();
    for (layer_index, layer) in proof.layers.iter().enumerate() {
        if current_nodes.len() <= 1 {
            return Err(ProofError::StatementMismatch);
        }
        let pair_count = current_nodes.len() / 2;
        if layer.len() != pair_count {
            return Err(ProofError::StatementMismatch);
        }

        let mut next_nodes = Vec::with_capacity(current_nodes.len().div_ceil(2));
        let mut next_summaries = Vec::with_capacity(current_summaries.len().div_ceil(2));
        for (node_index, aggregate) in layer.iter().enumerate() {
            let left = aggregation_node_batch_proof(
                current_nodes[node_index * 2],
                &proof.leaves,
                &proof.layers,
            );
            let right = aggregation_node_batch_proof(
                current_nodes[node_index * 2 + 1],
                &proof.leaves,
                &proof.layers,
            );
            let chain_summary = ActualPbsChainSummary::combine(
                &current_summaries[node_index * 2],
                &current_summaries[node_index * 2 + 1],
            )?;
            recursive::verify_aggregated_recursive_batch_with_summary_for_child_proofs(
                left,
                right,
                &chain_summary.field_values(),
                aggregate,
            )?;
            next_nodes.push(AggregationNodeRef::Aggregate {
                layer_index,
                node_index,
            });
            next_summaries.push(chain_summary);
        }
        if current_nodes.len() % 2 == 1 {
            let carried_node = *current_nodes.last().ok_or(ProofError::StatementMismatch)?;
            next_nodes.push(carried_node);
            next_summaries.push(
                current_summaries
                    .last()
                    .ok_or(ProofError::StatementMismatch)?
                    .clone(),
            );
        }
        current_nodes = next_nodes;
        current_summaries = next_summaries;
    }

    if current_nodes.len() != 1 || current_summaries.len() != 1 {
        return Err(ProofError::StatementMismatch);
    }
    if current_summaries[0] != proof.chain_summary {
        return Err(ProofError::StatementMismatch);
    }
    Ok(())
}

pub fn verify_aggregated_recursive_actual_pbs_chain_root_summary_proof(
    summary: &ActualPbsChainSummary,
    proof: &AggregatedRecursiveActualPbsChainRootProof,
) -> Result<(), ProofError> {
    if &proof.chain_summary != summary {
        return Err(ProofError::StatementMismatch);
    }
    recursive::verify_aggregated_recursive_batch_with_public_summary(
        &proof.root,
        &summary.field_values(),
    )
}

pub fn verify_compact_aggregated_recursive_actual_pbs_chain_root_summary_proof(
    summary: &CompactActualPbsChainSummary,
    proof: &CompactAggregatedRecursiveActualPbsChainRootProof,
) -> Result<(), ProofError> {
    if &proof.chain_summary != summary {
        return Err(ProofError::StatementMismatch);
    }
    recursive::verify_aggregated_recursive_batch_with_public_summary(
        &proof.root,
        &summary.field_values(),
    )
}

pub fn verify_aggregated_recursive_actual_pbs_chain_node_summary_proof(
    summary: &ActualPbsChainSummary,
    proof: &AggregatedRecursiveActualPbsChainNodeProof,
) -> Result<(), ProofError> {
    if &proof.chain_summary != summary {
        return Err(ProofError::StatementMismatch);
    }
    recursive::verify_aggregated_recursive_batch_with_public_summary(
        &proof.aggregation,
        &summary.field_values(),
    )
}

pub fn verify_compact_aggregated_recursive_actual_pbs_chain_node_summary_proof(
    summary: &CompactActualPbsChainSummary,
    proof: &CompactAggregatedRecursiveActualPbsChainNodeProof,
) -> Result<(), ProofError> {
    if &proof.chain_summary != summary {
        return Err(ProofError::StatementMismatch);
    }
    recursive::verify_aggregated_recursive_batch_with_public_summary(
        &proof.aggregation,
        &summary.field_values(),
    )
}

pub fn verify_aggregated_recursive_actual_pbs_chain_frontier_summary_proof(
    summary: &ActualPbsChainSummary,
    proof: &AggregatedRecursiveActualPbsChainFrontierProof,
) -> Result<(), ProofError> {
    if &proof.chain_summary != summary {
        return Err(ProofError::StatementMismatch);
    }
    let combined_summary = combine_actual_pbs_chain_summaries(
        &proof
            .nodes
            .iter()
            .map(|node| node.chain_summary.clone())
            .collect::<Vec<_>>(),
    )?;
    if combined_summary != proof.chain_summary {
        return Err(ProofError::StatementMismatch);
    }
    for node in &proof.nodes {
        verify_aggregated_recursive_actual_pbs_chain_node_summary_proof(&node.chain_summary, node)?;
    }
    Ok(())
}

pub fn serialize_aggregated_recursive_actual_pbs_chain_root_proof(
    proof: &AggregatedRecursiveActualPbsChainRootProof,
) -> Result<Vec<u8>, ProofError> {
    postcard::to_allocvec(proof).map_err(|error| ProofError::Serialization(format!("{error:?}")))
}

pub fn deserialize_aggregated_recursive_actual_pbs_chain_root_proof(
    bytes: &[u8],
) -> Result<AggregatedRecursiveActualPbsChainRootProof, ProofError> {
    let mut proof: AggregatedRecursiveActualPbsChainRootProof = postcard::from_bytes(bytes)
        .map_err(|error| ProofError::Serialization(format!("{error:?}")))?;
    proof.root.rebuild_common_lookups()?;
    Ok(proof)
}

pub fn serialize_compact_aggregated_recursive_actual_pbs_chain_root_proof(
    proof: &CompactAggregatedRecursiveActualPbsChainRootProof,
) -> Result<Vec<u8>, ProofError> {
    postcard::to_allocvec(proof).map_err(|error| ProofError::Serialization(format!("{error:?}")))
}

pub fn deserialize_compact_aggregated_recursive_actual_pbs_chain_root_proof(
    bytes: &[u8],
) -> Result<CompactAggregatedRecursiveActualPbsChainRootProof, ProofError> {
    let mut proof: CompactAggregatedRecursiveActualPbsChainRootProof = postcard::from_bytes(bytes)
        .map_err(|error| ProofError::Serialization(format!("{error:?}")))?;
    proof.root.rebuild_common_lookups()?;
    Ok(proof)
}

pub fn serialize_aggregated_recursive_actual_pbs_chain_node_proof(
    proof: &AggregatedRecursiveActualPbsChainNodeProof,
) -> Result<Vec<u8>, ProofError> {
    postcard::to_allocvec(proof).map_err(|error| ProofError::Serialization(format!("{error:?}")))
}

pub fn deserialize_aggregated_recursive_actual_pbs_chain_node_proof(
    bytes: &[u8],
) -> Result<AggregatedRecursiveActualPbsChainNodeProof, ProofError> {
    let mut proof: AggregatedRecursiveActualPbsChainNodeProof = postcard::from_bytes(bytes)
        .map_err(|error| ProofError::Serialization(format!("{error:?}")))?;
    proof.aggregation.rebuild_common_lookups()?;
    Ok(proof)
}

pub fn serialize_compact_aggregated_recursive_actual_pbs_chain_node_proof(
    proof: &CompactAggregatedRecursiveActualPbsChainNodeProof,
) -> Result<Vec<u8>, ProofError> {
    postcard::to_allocvec(proof).map_err(|error| ProofError::Serialization(format!("{error:?}")))
}

pub fn deserialize_compact_aggregated_recursive_actual_pbs_chain_node_proof(
    bytes: &[u8],
) -> Result<CompactAggregatedRecursiveActualPbsChainNodeProof, ProofError> {
    let mut proof: CompactAggregatedRecursiveActualPbsChainNodeProof = postcard::from_bytes(bytes)
        .map_err(|error| ProofError::Serialization(format!("{error:?}")))?;
    proof.aggregation.rebuild_common_lookups()?;
    Ok(proof)
}

pub fn serialize_aggregated_recursive_actual_pbs_chain_frontier_proof(
    proof: &AggregatedRecursiveActualPbsChainFrontierProof,
) -> Result<Vec<u8>, ProofError> {
    postcard::to_allocvec(proof).map_err(|error| ProofError::Serialization(format!("{error:?}")))
}

pub fn deserialize_aggregated_recursive_actual_pbs_chain_frontier_proof(
    bytes: &[u8],
) -> Result<AggregatedRecursiveActualPbsChainFrontierProof, ProofError> {
    let mut proof: AggregatedRecursiveActualPbsChainFrontierProof = postcard::from_bytes(bytes)
        .map_err(|error| ProofError::Serialization(format!("{error:?}")))?;
    for node in &mut proof.nodes {
        node.aggregation.rebuild_common_lookups()?;
    }
    Ok(proof)
}

pub fn serialize_recursive_actual_pbs_chain_chunk_proof(
    proof: &RecursiveActualPbsChainChunkProof,
) -> Result<Vec<u8>, ProofError> {
    postcard::to_allocvec(proof).map_err(|error| ProofError::Serialization(format!("{error:?}")))
}

pub fn deserialize_recursive_actual_pbs_chain_chunk_proof(
    bytes: &[u8],
) -> Result<RecursiveActualPbsChainChunkProof, ProofError> {
    let mut proof: RecursiveActualPbsChainChunkProof = postcard::from_bytes(bytes)
        .map_err(|error| ProofError::Serialization(format!("{error:?}")))?;
    rebuild_circuit_proof_common_lookups(&mut proof.base.proof)?;
    proof.recursion.rebuild_common_lookups()?;
    Ok(proof)
}

pub fn serialize_compact_recursive_actual_pbs_chain_chunk_proof(
    proof: &CompactRecursiveActualPbsChainChunkProof,
) -> Result<Vec<u8>, ProofError> {
    postcard::to_allocvec(proof).map_err(|error| ProofError::Serialization(format!("{error:?}")))
}

pub fn deserialize_compact_recursive_actual_pbs_chain_chunk_proof(
    bytes: &[u8],
) -> Result<CompactRecursiveActualPbsChainChunkProof, ProofError> {
    let mut proof: CompactRecursiveActualPbsChainChunkProof = postcard::from_bytes(bytes)
        .map_err(|error| ProofError::Serialization(format!("{error:?}")))?;
    rebuild_circuit_proof_common_lookups(&mut proof.base.proof)?;
    proof.recursion.rebuild_common_lookups()?;
    Ok(proof)
}

fn validate_aggregation_leaf_count(leaf_count: usize) -> Result<(), ProofError> {
    if leaf_count < 2 {
        return Err(ProofError::StatementMismatch);
    }
    Ok(())
}

fn chain_summary_from_statements(
    statements: &[ActualPbsChainChunkStatement],
) -> Result<ActualPbsChainSummary, ProofError> {
    let mut summaries = statements
        .iter()
        .map(ActualPbsChainSummary::from_chunk_statement);
    let first = summaries.next().ok_or(ProofError::StatementMismatch)??;
    summaries.try_fold(first, |acc, summary| {
        ActualPbsChainSummary::combine(&acc, &summary?)
    })
}

fn chain_summary_header_len() -> usize {
    param_public_value_count() + 1
}

fn chain_summary_field_count(params: &Params) -> usize {
    chain_summary_header_len() + chain_chunk_public_field_count(params)
}

fn compact_chain_summary_field_count() -> usize {
    chain_summary_header_len() + compact_chain_summary_public_field_count()
}

fn compact_chain_summary_public_field_count() -> usize {
    6 * SELECTOR_DIGEST_WIDTH
}

fn chain_chunk_public_field_count(params: &Params) -> usize {
    2 * chain_glwe_field_count(params) + 4 * SELECTOR_DIGEST_WIDTH
}

fn chain_glwe_field_count(params: &Params) -> usize {
    (params.glwe_dimension + 1) * params.polynomial_size
}

fn param_public_value_count() -> usize {
    6
}

fn param_public_values(params: &Params) -> [P3Goldilocks; 6] {
    [
        P3Goldilocks::from_u64(params.lwe_dimension as u64),
        P3Goldilocks::from_u64(params.polynomial_size as u64),
        P3Goldilocks::from_u64(params.glwe_dimension as u64),
        P3Goldilocks::from_u64(params.decomposition_base_log as u64),
        P3Goldilocks::from_u64(params.decomposition_level_count as u64),
        P3Goldilocks::from_u64(params.plaintext_modulus),
    ]
}

fn chain_summary_layout(params: &Params) -> recursive::ChainSummaryLayout {
    let glwe_len = chain_glwe_field_count(params);
    let digest_len = SELECTOR_DIGEST_WIDTH;
    let header_len = chain_summary_header_len();
    let input_accumulator = header_len..header_len + glwe_len;
    let bsk_digest_in = input_accumulator.end..input_accumulator.end + digest_len;
    let bsk_digest_out = bsk_digest_in.end..bsk_digest_in.end + digest_len;
    let mask_digest_in = bsk_digest_out.end..bsk_digest_out.end + digest_len;
    let mask_digest_out = mask_digest_in.end..mask_digest_in.end + digest_len;
    let output_accumulator = mask_digest_out.end..mask_digest_out.end + glwe_len;
    recursive::ChainSummaryLayout {
        params: 0..param_public_value_count(),
        step_count: param_public_value_count(),
        input_accumulator,
        bsk_digest_in,
        bsk_digest_out,
        mask_digest_in,
        mask_digest_out,
        output_accumulator: output_accumulator.clone(),
        len: output_accumulator.end,
    }
}

fn compact_chain_summary_layout() -> recursive::ChainSummaryLayout {
    let digest_len = SELECTOR_DIGEST_WIDTH;
    let header_len = chain_summary_header_len();
    let input_accumulator = header_len..header_len + digest_len;
    let bsk_digest_in = input_accumulator.end..input_accumulator.end + digest_len;
    let bsk_digest_out = bsk_digest_in.end..bsk_digest_in.end + digest_len;
    let mask_digest_in = bsk_digest_out.end..bsk_digest_out.end + digest_len;
    let mask_digest_out = mask_digest_in.end..mask_digest_in.end + digest_len;
    let output_accumulator = mask_digest_out.end..mask_digest_out.end + digest_len;
    recursive::ChainSummaryLayout {
        params: 0..param_public_value_count(),
        step_count: param_public_value_count(),
        input_accumulator,
        bsk_digest_in,
        bsk_digest_out,
        mask_digest_in,
        mask_digest_out,
        output_accumulator: output_accumulator.clone(),
        len: output_accumulator.end,
    }
}

struct ChunkStatementPublicView<'a> {
    input_accumulator: &'a [P3Goldilocks],
    bsk_digest_in: &'a [P3Goldilocks],
    bsk_digest_out: &'a [P3Goldilocks],
    mask_digest_in: &'a [P3Goldilocks],
    mask_digest_out: &'a [P3Goldilocks],
    output_accumulator: &'a [P3Goldilocks],
}

fn chunk_statement_public_view(
    statement: &ActualPbsChainChunkStatement,
) -> Result<ChunkStatementPublicView<'_>, ProofError> {
    chunk_public_view(&statement.params, &statement.public_inputs)
}

fn chunk_summary_public_view(
    summary: &ActualPbsChainSummary,
) -> Result<ChunkStatementPublicView<'_>, ProofError> {
    chunk_public_view(&summary.params, &summary.public_inputs)
}

fn compact_summary_public_view(
    summary: &CompactActualPbsChainSummary,
) -> Result<ChunkStatementPublicView<'_>, ProofError> {
    compact_public_view(&summary.public_inputs)
}

fn chunk_public_view<'a>(
    params: &Params,
    public_inputs: &'a [P3Goldilocks],
) -> Result<ChunkStatementPublicView<'a>, ProofError> {
    let glwe_len = chain_glwe_field_count(params);
    let digest_len = SELECTOR_DIGEST_WIDTH;
    let expected_len = 2 * glwe_len + 4 * digest_len;
    if public_inputs.len() != expected_len {
        return Err(ProofError::StatementMismatch);
    }

    let inputs = public_inputs;
    let mut offset = 0usize;
    let input_accumulator = &inputs[offset..offset + glwe_len];
    offset += glwe_len;
    let bsk_digest_in = &inputs[offset..offset + digest_len];
    offset += digest_len;
    let bsk_digest_out = &inputs[offset..offset + digest_len];
    offset += digest_len;
    let mask_digest_in = &inputs[offset..offset + digest_len];
    offset += digest_len;
    let mask_digest_out = &inputs[offset..offset + digest_len];
    offset += digest_len;
    let output_accumulator = &inputs[offset..offset + glwe_len];

    Ok(ChunkStatementPublicView {
        input_accumulator,
        bsk_digest_in,
        bsk_digest_out,
        mask_digest_in,
        mask_digest_out,
        output_accumulator,
    })
}

fn compact_public_view<'a>(
    public_inputs: &'a [P3Goldilocks],
) -> Result<ChunkStatementPublicView<'a>, ProofError> {
    let digest_len = SELECTOR_DIGEST_WIDTH;
    let expected_len = compact_chain_summary_public_field_count();
    if public_inputs.len() != expected_len {
        return Err(ProofError::StatementMismatch);
    }

    let inputs = public_inputs;
    let mut offset = 0usize;
    let input_accumulator = &inputs[offset..offset + digest_len];
    offset += digest_len;
    let bsk_digest_in = &inputs[offset..offset + digest_len];
    offset += digest_len;
    let bsk_digest_out = &inputs[offset..offset + digest_len];
    offset += digest_len;
    let mask_digest_in = &inputs[offset..offset + digest_len];
    offset += digest_len;
    let mask_digest_out = &inputs[offset..offset + digest_len];
    offset += digest_len;
    let output_accumulator = &inputs[offset..offset + digest_len];

    Ok(ChunkStatementPublicView {
        input_accumulator,
        bsk_digest_in,
        bsk_digest_out,
        mask_digest_in,
        mask_digest_out,
        output_accumulator,
    })
}

fn compact_accumulator_digest(values: &[P3Goldilocks]) -> [P3Goldilocks; SELECTOR_DIGEST_WIDTH] {
    poseidon_chain::poseidon2_digest_fields(COMPACT_ACCUMULATOR_DIGEST_TAG, values.iter().copied())
}

#[derive(Clone, Copy)]
enum AggregationNodeRef {
    Leaf(usize),
    Aggregate {
        layer_index: usize,
        node_index: usize,
    },
}

fn aggregation_node_batch_proof<'a>(
    node: AggregationNodeRef,
    leaves: &'a [RecursiveActualPbsChainChunkProof],
    layers: &'a [Vec<recursive::AggregatedRecursiveBatchProof>],
) -> &'a BatchStarkProof<GoldilocksConfig> {
    match node {
        AggregationNodeRef::Leaf(index) => leaves[index].recursion.batch_proof(),
        AggregationNodeRef::Aggregate {
            layer_index,
            node_index,
        } => layers[layer_index][node_index].batch_proof(),
    }
}

fn prove_circuit(
    circuit: &Circuit<P3Goldilocks>,
    public_inputs: &[P3Goldilocks],
    private_inputs: &[P3Goldilocks],
) -> Result<BatchStarkProof<GoldilocksConfig>, ProofError> {
    let config = base_goldilocks_config();
    let table_packing = base_proof_table_packing();
    let range_bit_counts = range_check_bit_counts(circuit);
    let preprocessors = base_preprocessors(&range_bit_counts);
    let air_builders = base_air_builders(&range_bit_counts);
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 1>(
            circuit,
            &table_packing,
            &preprocessors,
            &air_builders,
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
    register_base_table_provers(&mut prover, &range_bit_counts);
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

    let config = base_goldilocks_config();
    let mut prover = BatchStarkProver::new(config).with_table_packing(proof.table_packing.clone());
    let range_bit_counts = proof_range_check_bit_counts(proof);
    register_base_table_provers(&mut prover, &range_bit_counts);
    prover
        .verify_all_tables(proof)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))
}

fn rebuild_circuit_proof_common_lookups(
    proof: &mut BatchStarkProof<GoldilocksConfig>,
) -> Result<(), ProofError> {
    let config = base_goldilocks_config();
    let mut prover = BatchStarkProver::new(config).with_table_packing(proof.table_packing.clone());
    let range_bit_counts = proof_range_check_bit_counts(proof);
    register_base_table_provers(&mut prover, &range_bit_counts);
    prover
        .rebuild_common_lookups(proof)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))
}

fn verify_circuit_proof_for_circuit(
    circuit: &Circuit<P3Goldilocks>,
    proof: &BatchStarkProof<GoldilocksConfig>,
    expected_public_inputs: &[P3Goldilocks],
) -> Result<(), ProofError> {
    let expected_common = expected_circuit_common_data(circuit, &proof.table_packing)?;
    if !common_data_matches(&proof.stark_common, &expected_common) {
        return Err(ProofError::StatementMismatch);
    }

    verify_circuit_proof(proof, expected_public_inputs)
}

fn expected_circuit_common_data(
    circuit: &Circuit<P3Goldilocks>,
    table_packing: &TablePacking,
) -> Result<CommonData<GoldilocksConfig>, ProofError> {
    let config = base_goldilocks_config();
    let range_bit_counts = range_check_bit_counts(circuit);
    let preprocessors = base_preprocessors(&range_bit_counts);
    let air_builders = base_air_builders(&range_bit_counts);
    let (airs_degrees, _primitive_columns, _non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 1>(
            circuit,
            table_packing,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let (airs, degrees): (Vec<_>, Vec<usize>) = airs_degrees.into_iter().unzip();
    Ok(ProverData::from_airs_and_degrees(&config, &airs, &degrees).common)
}

fn common_data_matches(
    actual: &CommonData<GoldilocksConfig>,
    expected: &CommonData<GoldilocksConfig>,
) -> bool {
    if actual.lookups.len() != expected.lookups.len() {
        return false;
    }

    match (&actual.preprocessed, &expected.preprocessed) {
        (None, None) => true,
        (Some(actual), Some(expected)) => {
            actual.commitment == expected.commitment
                && actual.matrix_to_instance == expected.matrix_to_instance
                && actual.instances.len() == expected.instances.len()
                && actual.instances.iter().zip(expected.instances.iter()).all(
                    |(actual, expected)| match (actual, expected) {
                        (None, None) => true,
                        (Some(actual), Some(expected)) => {
                            actual.matrix_index == expected.matrix_index
                                && actual.width == expected.width
                                && actual.degree_bits == expected.degree_bits
                        }
                        _ => false,
                    },
                )
        }
        _ => false,
    }
}

fn base_preprocessors(
    bit_counts: &[usize],
) -> Vec<Box<dyn p3_circuit_prover::common::NpoPreprocessor<P3Goldilocks>>> {
    let mut preprocessors = vec![poseidon2_preprocessor::<P3Goldilocks>()];
    preprocessors.extend(range_preprocessors(bit_counts));
    preprocessors
}

fn base_air_builders(
    bit_counts: &[usize],
) -> Vec<Box<dyn p3_circuit_prover::common::NpoAirBuilder<GoldilocksConfig, 1>>> {
    let mut air_builders = poseidon2_air_builders_d1::<GoldilocksConfig>();
    air_builders.extend(range_air_builders(bit_counts));
    air_builders
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

fn register_base_table_provers(
    prover: &mut BatchStarkProver<GoldilocksConfig>,
    bit_counts: &[usize],
) {
    prover.register_poseidon2_table::<1>(Poseidon2Config::GOLDILOCKS_D1_W8);
    register_range_check_provers(prover, bit_counts);
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

type P3Challenge = BinomialExtensionField<P3Goldilocks, 2>;
type P3Hash = PaddingFreeSponge<Poseidon2Goldilocks<8>, 8, 4, 4>;
type P3Compress = TruncatedPermutation<Poseidon2Goldilocks<8>, 2, 4, 8>;
type P3Mmcs = MerkleTreeMmcs<
    <P3Goldilocks as p3_field::Field>::Packing,
    <P3Goldilocks as p3_field::Field>::Packing,
    P3Hash,
    P3Compress,
    2,
    4,
>;

pub(crate) fn base_goldilocks_config() -> GoldilocksConfig {
    goldilocks_config_with_fri(
        BASE_PROOF_FRI_LOG_BLOWUP,
        BASE_PROOF_FRI_LOG_FINAL_POLY_LEN,
        BASE_PROOF_FRI_MAX_LOG_ARITY,
        BASE_PROOF_FRI_NUM_QUERIES,
        BASE_PROOF_FRI_COMMIT_POW_BITS,
        BASE_PROOF_FRI_QUERY_POW_BITS,
    )
}

pub(crate) fn goldilocks_config() -> GoldilocksConfig {
    goldilocks_config_with_fri(
        PROOF_FRI_LOG_BLOWUP,
        PROOF_FRI_LOG_FINAL_POLY_LEN,
        PROOF_FRI_MAX_LOG_ARITY,
        PROOF_FRI_NUM_QUERIES,
        PROOF_FRI_COMMIT_POW_BITS,
        PROOF_FRI_QUERY_POW_BITS,
    )
}

fn goldilocks_config_with_fri(
    log_blowup: usize,
    log_final_poly_len: usize,
    max_log_arity: usize,
    num_queries: usize,
    commit_proof_of_work_bits: usize,
    query_proof_of_work_bits: usize,
) -> GoldilocksConfig {
    let perm = goldilocks_poseidon2_8();
    let hash = P3Hash::new(perm.clone());
    let compress = P3Compress::new(perm.clone());
    let val_mmcs = P3Mmcs::new(hash, compress, 0);
    let challenge_mmcs = ExtensionMmcs::<P3Goldilocks, P3Challenge, P3Mmcs>::new(val_mmcs.clone());
    let dft = Radix2DitParallel::default();
    let fri_params = FriParameters {
        log_blowup,
        log_final_poly_len,
        max_log_arity,
        num_queries,
        commit_proof_of_work_bits,
        query_proof_of_work_bits,
        mmcs: challenge_mmcs,
    };
    let pcs = TwoAdicFriPcs::new(dft, val_mmcs, fri_params);
    let challenger = DuplexChallenger::new(perm);

    StarkConfig::new(pcs, challenger)
}

pub(crate) fn base_proof_table_packing() -> TablePacking {
    TablePacking::default()
        .with_fri_params(BASE_PROOF_FRI_LOG_FINAL_POLY_LEN, BASE_PROOF_FRI_LOG_BLOWUP)
}

pub(crate) fn proof_table_packing() -> TablePacking {
    TablePacking::default().with_fri_params(PROOF_FRI_LOG_FINAL_POLY_LEN, PROOF_FRI_LOG_BLOWUP)
}

pub(crate) fn goldilocks_poseidon2_8() -> Poseidon2Goldilocks<8> {
    let mut rng = rand_p3::rngs::SmallRng::seed_from_u64(1);
    Poseidon2Goldilocks::<8>::new_from_rng_128(&mut rng)
}

#[cfg(test)]
mod tests {
    use p3_field::PrimeCharacteristicRing;
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

    #[test]
    fn proves_and_verifies_chained_actual_pbs_chunk_with_approximate_decomposition() {
        let params = Params::new(2, 4, 1, 5, 4, 4);
        let instance = actual_pbs_chain_chunk_instance_with_params(params, 2);

        prove_and_verify_actual_pbs_chain_chunk(&instance).unwrap();
    }

    #[test]
    fn rejects_chained_actual_pbs_chunk_statement_mismatch() {
        let params = Params::new(2, 4, 1, 5, 4, 4);
        let instance = actual_pbs_chain_chunk_instance_with_params(params, 2);
        let proof = prove_actual_pbs_chain_chunk(&instance).unwrap();
        let mut other_instance = instance.clone();
        other_instance.bsk_digest_out[0] += Goldilocks::ONE;

        assert_eq!(
            verify_actual_pbs_chain_chunk_proof(&other_instance, &proof),
            Err(ProofError::StatementMismatch)
        );
    }

    #[test]
    fn verifies_chained_actual_pbs_chunk_from_public_statement() {
        let params = Params::new(2, 4, 1, 5, 4, 4);
        let instance = actual_pbs_chain_chunk_instance_with_params(params, 2);
        let proof = prove_actual_pbs_chain_chunk(&instance).unwrap();
        let statement = ActualPbsChainChunkStatement::from_instance(&instance);

        verify_actual_pbs_chain_chunk_statement_proof(&statement, &proof).unwrap();

        let mut mismatched_statement = statement.clone();
        mismatched_statement.public_inputs[0] += P3Goldilocks::ONE;
        assert_eq!(
            verify_actual_pbs_chain_chunk_statement_proof(&mismatched_statement, &proof),
            Err(ProofError::StatementMismatch)
        );
    }

    #[test]
    fn validates_chained_actual_pbs_chunk_statement_continuity() {
        let params = Params::new(3, 4, 1, 5, 4, 4);
        let mut rng = ChaCha20Rng::seed_from_u64(104);
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
        let first = ActualPbsChainChunkInstance::new(
            params.clone(),
            input.mask[..1].to_vec(),
            input_accumulator,
            ek.bootstrapping_key[..1].to_vec(),
            pbs_bsk_digest_initial(),
            pbs_mask_digest_initial(),
        );
        let second = ActualPbsChainChunkInstance::new(
            params.clone(),
            input.mask[1..].to_vec(),
            first.output_accumulator.clone(),
            ek.bootstrapping_key[1..].to_vec(),
            first.bsk_digest_out,
            first.mask_digest_out,
        );
        let statements = vec![
            ActualPbsChainChunkStatement::from_instance(&first),
            ActualPbsChainChunkStatement::from_instance(&second),
        ];

        validate_actual_pbs_chain_chunk_statements(&statements).unwrap();
        let first_summary = ActualPbsChainSummary::from_chunk_statement(&statements[0]).unwrap();
        let second_summary = ActualPbsChainSummary::from_chunk_statement(&statements[1]).unwrap();
        let combined_summary =
            ActualPbsChainSummary::combine(&first_summary, &second_summary).unwrap();
        assert_eq!(combined_summary.step_count, params.lwe_dimension);
        assert_eq!(
            combined_summary.public_inputs[..2 * params.polynomial_size],
            statements[0].public_inputs[..2 * params.polynomial_size]
        );

        let first_compact =
            CompactActualPbsChainSummary::from_chunk_statement(&statements[0]).unwrap();
        let second_compact =
            CompactActualPbsChainSummary::from_chunk_statement(&statements[1]).unwrap();
        let combined_compact =
            CompactActualPbsChainSummary::combine(&first_compact, &second_compact).unwrap();
        assert_eq!(combined_compact.step_count, params.lwe_dimension);
        assert_eq!(
            combined_compact.field_values().len(),
            compact_chain_summary_field_count()
        );
        assert_eq!(
            combined_compact,
            CompactActualPbsChainSummary::from_full_summary(&combined_summary).unwrap()
        );

        let mut mismatched_compact = second_compact;
        mismatched_compact.public_inputs[0] += P3Goldilocks::ONE;
        assert_eq!(
            CompactActualPbsChainSummary::combine(&first_compact, &mismatched_compact),
            Err(ProofError::StatementMismatch)
        );

        let mut mismatched_accumulator = statements.clone();
        mismatched_accumulator[1].public_inputs[0] += P3Goldilocks::ONE;
        assert_eq!(
            validate_actual_pbs_chain_chunk_statements(&mismatched_accumulator),
            Err(ProofError::StatementMismatch)
        );

        let mut too_many_steps = statements.clone();
        too_many_steps[1].step_count = params.lwe_dimension;
        assert_eq!(
            validate_actual_pbs_chain_chunk_statements(&too_many_steps),
            Err(ProofError::StatementMismatch)
        );
    }

    #[test]
    fn rejects_chained_actual_pbs_chunk_wrong_circuit_shape() {
        let params = Params::new(2, 4, 1, 5, 4, 4);
        let instance = actual_pbs_chain_chunk_instance_with_params(params, 1);
        let mut proof = prove_actual_pbs_chain_chunk(&instance).unwrap();
        let mut statement = proof.public_statement();
        proof.step_count = 2;
        statement.step_count = 2;

        assert_eq!(
            verify_actual_pbs_chain_chunk_statement_proof(&statement, &proof),
            Err(ProofError::StatementMismatch)
        );
    }

    #[test]
    fn rejects_malformed_root_proof_artifact() {
        match deserialize_aggregated_recursive_actual_pbs_chain_root_proof(&[0xff]) {
            Err(ProofError::Serialization(_)) => {}
            Err(error) => panic!("unexpected error: {error:?}"),
            Ok(_) => panic!("malformed root proof bytes must fail to deserialize"),
        }
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

    fn actual_pbs_chain_chunk_instance_with_params(
        params: Params,
        step_count: usize,
    ) -> ActualPbsChainChunkInstance {
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

        ActualPbsChainChunkInstance::new(
            params,
            input.mask[..step_count].to_vec(),
            input_accumulator,
            ek.bootstrapping_key[..step_count].to_vec(),
            pbs_bsk_digest_initial(),
            pbs_mask_digest_initial(),
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
