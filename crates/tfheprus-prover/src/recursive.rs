use core::ops::Range;

use p3_batch_stark::ProverData;
use p3_circuit::ops::{
    generate_poseidon2_trace, generate_recompose_trace, GoldilocksD2Width8, Op, Poseidon2Config,
};

use p3_circuit::{Circuit, CircuitBuilder, ExprId};
use p3_circuit_prover::common::get_airs_and_degrees_with_prep;
use p3_circuit_prover::config::GoldilocksConfig;
use p3_circuit_prover::{
    poseidon2_air_builders_for_configs, poseidon2_preprocessor, recompose_air_builders,
    recompose_preprocessor, recompose_table_provers, BatchStarkProof, BatchStarkProver,
    CircuitProverData, ConstraintProfile, Poseidon2ProverD2, TablePacking, TableProver,
    NUM_PRIMITIVE_TABLES,
};
use p3_field::extension::BinomialExtensionField;
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::{Goldilocks as P3Goldilocks, Poseidon2Goldilocks};
use p3_lookup::logup::LogUpGadget;
use p3_recursion::backend::replay_batch_layer_transcript;
use p3_recursion::generation::{observe_opened_values, OpeningTranscript};
use p3_recursion::pcs::{
    restore_fri_query_paths, set_fri_mmcs_private_data, InputProofTargets, MerkleCapTargets,
    RecExtensionValMmcs, RecValMmcs,
};
use p3_recursion::public_inputs::BatchStarkVerifierInputsBuilder;
use p3_recursion::verifier::{verify_p3_batch_proof_circuit, VerificationError};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};
use tfheprus_circuits::SELECTOR_DIGEST_WIDTH;

use crate::range_check::{
    proof_range_check_bit_counts, RangeCheckProver, RANGE_CHECK_DEFAULT_LANES,
};
use crate::{
    base_goldilocks_config, goldilocks_config, goldilocks_poseidon2_8, poseidon_chain,
    proof_table_packing, ProofError, RecursiveProofSizeBreakdown, BASE_PROOF_FRI_COMMIT_POW_BITS,
    BASE_PROOF_FRI_LOG_BLOWUP, BASE_PROOF_FRI_LOG_FINAL_POLY_LEN, BASE_PROOF_FRI_MAX_LOG_ARITY,
    BASE_PROOF_FRI_NUM_QUERIES, BASE_PROOF_FRI_QUERY_POW_BITS, PROOF_FRI_COMMIT_POW_BITS,
    PROOF_FRI_LOG_BLOWUP, PROOF_FRI_LOG_FINAL_POLY_LEN, PROOF_FRI_MAX_LOG_ARITY,
    PROOF_FRI_NUM_QUERIES, PROOF_FRI_QUERY_POW_BITS,
};

type F = P3Goldilocks;
type Challenge = BinomialExtensionField<F, 2>;
type Perm = Poseidon2Goldilocks<8>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type InnerFri = p3_recursion::pcs::FriProofTargets<
    F,
    Challenge,
    RecExtensionValMmcs<F, Challenge, 4, RecValMmcs<F, 4, MyHash, MyCompress>>,
    InputProofTargets<F, Challenge, RecValMmcs<F, 4, MyHash, MyCompress>>,
    p3_recursion::pcs::Witness<F>,
>;
type NativeVerifierInputs =
    BatchStarkVerifierInputsBuilder<GoldilocksConfig, MerkleCapTargets<F, 4>, InnerFri>;

// Keep the upstream allocation layout intact and retain the exact Statement
// targets consumed by its verifier for TFHEprus summary constraints.
struct VerifierInputs {
    native: NativeVerifierInputs,
    statement: Vec<ExprId>,
}

impl core::ops::Deref for VerifierInputs {
    type Target = NativeVerifierInputs;
    fn deref(&self) -> &Self::Target {
        &self.native
    }
}

const COMPACT_ACCUMULATOR_DIGEST_TAG: u64 = 0x676c_7765_5f61_6363;

#[derive(Clone, Debug)]
pub(crate) struct ChainSummaryLayout {
    pub params: Range<usize>,
    pub step_count: usize,
    pub input_accumulator: Range<usize>,
    pub bsk_digest_in: Range<usize>,
    pub bsk_digest_out: Range<usize>,
    pub mask_digest_in: Range<usize>,
    pub mask_digest_out: Range<usize>,
    pub output_accumulator: Range<usize>,
    pub len: usize,
}

#[derive(Clone, Debug)]
pub(crate) struct PbsKeyswitchLinkLayout {
    pub compact_summary: ChainSummaryLayout,
    pub key_params: Range<usize>,
    pub key_input_accumulator: Range<usize>,
    pub key_output_lwe: Range<usize>,
    pub final_compact_summary: Range<usize>,
    pub final_output_lwe: Range<usize>,
    pub final_len: usize,
}

#[derive(serde::Deserialize, serde::Serialize)]
pub struct RecursiveBatchProof {
    public_inputs: Vec<Challenge>,
    proof: BatchStarkProof<GoldilocksConfig>,
}

#[derive(serde::Deserialize, serde::Serialize)]
pub struct AggregatedRecursiveBatchProof {
    public_inputs: Vec<Challenge>,
    proof: BatchStarkProof<GoldilocksConfig>,
}

impl RecursiveBatchProof {
    pub(crate) fn batch_proof(&self) -> &BatchStarkProof<GoldilocksConfig> {
        &self.proof
    }

    pub(crate) fn rebuild_common_lookups(&mut self) -> Result<(), ProofError> {
        Ok(())
    }

    pub fn table_count(&self) -> usize {
        self.proof.proof.opened_values.instances.len()
    }

    pub fn public_input_count(&self) -> usize {
        self.public_inputs.len()
    }

    pub fn size_breakdown(&self) -> Result<RecursiveProofSizeBreakdown, ProofError> {
        recursive_proof_size_breakdown(&self.public_inputs, &self.proof)
    }
}

impl AggregatedRecursiveBatchProof {
    pub(crate) fn batch_proof(&self) -> &BatchStarkProof<GoldilocksConfig> {
        &self.proof
    }

    pub(crate) fn rebuild_common_lookups(&mut self) -> Result<(), ProofError> {
        Ok(())
    }

    pub fn table_count(&self) -> usize {
        self.proof.proof.opened_values.instances.len()
    }

    pub fn public_input_count(&self) -> usize {
        self.public_inputs.len()
    }

    pub fn size_breakdown(&self) -> Result<RecursiveProofSizeBreakdown, ProofError> {
        recursive_proof_size_breakdown(&self.public_inputs, &self.proof)
    }
}

pub(crate) fn prove_recursive_batch_with_leaf_summary(
    proof: &BatchStarkProof<GoldilocksConfig>,
    summary: &[F],
    chunk_public_offset: usize,
) -> Result<RecursiveBatchProof, ProofError> {
    let outer_config = goldilocks_config();
    let inner_config = base_goldilocks_config();
    let table_packing = proof_table_packing();
    let table_public_inputs = table_public_inputs(proof);
    let (verification_circuit, verifier_inputs, mmcs_op_ids) =
        build_verifier_circuit_with_leaf_summary(
            proof,
            &inner_config,
            summary,
            chunk_public_offset,
        )?;
    let (mut public_inputs, private_inputs) =
        verifier_inputs.pack_values(&table_public_inputs, &proof.proof, &proof.stark_common);
    append_summary_public_inputs(&mut public_inputs, summary);
    assert_public_ops_have_rows(&verification_circuit)?;
    let mut runner = verification_circuit.runner();
    runner
        .set_public_inputs(&public_inputs)
        .map_err(|error| ProofError::Plonky3(format!("set recursive public inputs: {error:?}")))?;
    runner
        .set_private_inputs(&private_inputs)
        .map_err(|error| ProofError::Plonky3(format!("set recursive private inputs: {error:?}")))?;
    set_proof_fri_private_data(&mut runner, &mmcs_op_ids, proof, base_fri_verifier_params())
        .map_err(|error| ProofError::Plonky3(format!("set recursive FRI private data: {error}")))?;
    let traces = runner.run().map_err(|error| {
        ProofError::Plonky3(format!("run recursive verifier circuit: {error:?}"))
    })?;

    let preprocessors = recursive_verifier_preprocessors(&verification_circuit);
    let air_builders = recursive_verifier_air_builders(&verification_circuit);
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 2>(
            &verification_circuit,
            &table_packing,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
    let prover_data = ProverData::from_airs_and_degrees(&outer_config, &airs, &degrees)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(outer_config, table_packing, summary.len());
    let recursive_proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(RecursiveBatchProof {
        public_inputs: summary_public_inputs(summary),
        proof: recursive_proof,
    })
}

pub(crate) fn prove_private_recursive_batch_with_leaf_summary(
    proof: &BatchStarkProof<GoldilocksConfig>,
    summary: &[F],
    chunk_public_offset: usize,
) -> Result<RecursiveBatchProof, ProofError> {
    let outer_config = goldilocks_config();
    let inner_config = base_goldilocks_config();
    let table_packing = proof_table_packing();
    let (verification_circuit, verifier_inputs, mmcs_op_ids) =
        build_private_verifier_circuit_with_leaf_summary(
            proof,
            &inner_config,
            summary,
            chunk_public_offset,
        )?;
    let public_inputs = execution_public_inputs(&[(&verifier_inputs, proof)], summary);
    let private_inputs = verifier_inputs.pack_private_values(&proof.proof);
    assert_public_ops_have_rows(&verification_circuit)?;
    let mut runner = verification_circuit.runner();
    runner.set_public_inputs(&public_inputs).map_err(|error| {
        ProofError::Plonky3(format!("set private recursive public inputs: {error:?}"))
    })?;
    runner
        .set_private_inputs(&private_inputs)
        .map_err(|error| {
            ProofError::Plonky3(format!("set private recursive verifier inputs: {error:?}"))
        })?;
    set_proof_fri_private_data(&mut runner, &mmcs_op_ids, proof, base_fri_verifier_params())
        .map_err(|error| {
            ProofError::Plonky3(format!("set private recursive FRI private data: {error}"))
        })?;
    let traces = runner.run().map_err(|error| {
        ProofError::Plonky3(format!("run private recursive verifier circuit: {error:?}"))
    })?;

    let preprocessors = recursive_verifier_preprocessors(&verification_circuit);
    let air_builders = recursive_verifier_air_builders(&verification_circuit);
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 2>(
            &verification_circuit,
            &table_packing,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
    let prover_data = ProverData::from_airs_and_degrees(&outer_config, &airs, &degrees)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(outer_config, table_packing, summary.len());
    let recursive_proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(RecursiveBatchProof {
        public_inputs: summary_public_inputs(summary),
        proof: recursive_proof,
    })
}

pub(crate) fn prove_private_recursive_batch_with_compact_leaf_summary(
    proof: &BatchStarkProof<GoldilocksConfig>,
    summary: &[F],
    chunk_public_offset: usize,
    full_layout: &ChainSummaryLayout,
    compact_layout: &ChainSummaryLayout,
) -> Result<RecursiveBatchProof, ProofError> {
    let outer_config = goldilocks_config();
    let inner_config = base_goldilocks_config();
    let table_packing = proof_table_packing();
    let (verification_circuit, verifier_inputs, mmcs_op_ids) =
        build_private_verifier_circuit_with_compact_leaf_summary(
            proof,
            &inner_config,
            summary,
            chunk_public_offset,
            full_layout,
            compact_layout,
        )?;
    let public_inputs = execution_public_inputs(&[(&verifier_inputs, proof)], summary);
    let private_inputs = verifier_inputs.pack_private_values(&proof.proof);
    assert_public_ops_have_rows(&verification_circuit)?;
    let mut runner = verification_circuit.runner();
    runner.set_public_inputs(&public_inputs).map_err(|error| {
        ProofError::Plonky3(format!(
            "set private compact recursive public inputs: {error:?}"
        ))
    })?;
    runner
        .set_private_inputs(&private_inputs)
        .map_err(|error| {
            ProofError::Plonky3(format!(
                "set private compact recursive verifier inputs: {error:?}"
            ))
        })?;
    set_proof_fri_private_data(&mut runner, &mmcs_op_ids, proof, base_fri_verifier_params())
        .map_err(|error| {
            ProofError::Plonky3(format!(
                "set private compact recursive FRI private data: {error}"
            ))
        })?;
    let traces = runner.run().map_err(|error| {
        ProofError::Plonky3(format!(
            "run private compact recursive verifier circuit: {error:?}"
        ))
    })?;

    let preprocessors = recursive_verifier_preprocessors(&verification_circuit);
    let air_builders = recursive_verifier_air_builders(&verification_circuit);
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 2>(
            &verification_circuit,
            &table_packing,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
    let prover_data = ProverData::from_airs_and_degrees(&outer_config, &airs, &degrees)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(outer_config, table_packing, summary.len());
    let recursive_proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(RecursiveBatchProof {
        public_inputs: summary_public_inputs(summary),
        proof: recursive_proof,
    })
}

pub(crate) struct PrivateCompactLeafRecursionProver {
    verification_circuit: Circuit<Challenge>,
    verifier_inputs: VerifierInputs,
    mmcs_op_ids: Vec<p3_circuit::NonPrimitiveOpId>,
    table_packing: TablePacking,
    circuit_prover_data: CircuitProverData<GoldilocksConfig>,
}

impl PrivateCompactLeafRecursionProver {
    pub(crate) fn new(
        proof: &BatchStarkProof<GoldilocksConfig>,
        summary: &[F],
        chunk_public_offset: usize,
        full_layout: &ChainSummaryLayout,
        compact_layout: &ChainSummaryLayout,
    ) -> Result<Self, ProofError> {
        let outer_config = goldilocks_config();
        let inner_config = base_goldilocks_config();
        let table_packing = proof_table_packing();
        let (verification_circuit, verifier_inputs, mmcs_op_ids) =
            build_private_verifier_circuit_with_compact_leaf_summary(
                proof,
                &inner_config,
                summary,
                chunk_public_offset,
                full_layout,
                compact_layout,
            )?;
        let preprocessors = recursive_verifier_preprocessors(&verification_circuit);
        let air_builders = recursive_verifier_air_builders(&verification_circuit);
        let (airs_degrees, primitive_columns, non_primitive_columns) =
            get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 2>(
                &verification_circuit,
                &table_packing,
                &preprocessors,
                &air_builders,
                ConstraintProfile::Standard,
            )
            .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
        let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
        let prover_data = ProverData::from_airs_and_degrees(&outer_config, &airs, &degrees)
            .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
        let circuit_prover_data =
            CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

        Ok(Self {
            verification_circuit,
            verifier_inputs,
            mmcs_op_ids,
            table_packing,
            circuit_prover_data,
        })
    }

    pub(crate) fn prove(
        &self,
        proof: &BatchStarkProof<GoldilocksConfig>,
        summary: &[F],
    ) -> Result<RecursiveBatchProof, ProofError> {
        let public_inputs = execution_public_inputs(&[(&self.verifier_inputs, proof)], summary);
        let private_inputs = self.verifier_inputs.pack_private_values(&proof.proof);
        assert_public_ops_have_rows(&self.verification_circuit)?;
        let mut runner = self.verification_circuit.runner();
        runner.set_public_inputs(&public_inputs).map_err(|error| {
            ProofError::Plonky3(format!(
                "set cached private compact recursive public inputs: {error:?}"
            ))
        })?;
        runner
            .set_private_inputs(&private_inputs)
            .map_err(|error| {
                ProofError::Plonky3(format!(
                    "set cached private compact recursive verifier inputs: {error:?}"
                ))
            })?;
        set_proof_fri_private_data(
            &mut runner,
            &self.mmcs_op_ids,
            proof,
            base_fri_verifier_params(),
        )
        .map_err(|error| {
            ProofError::Plonky3(format!(
                "set cached private compact recursive FRI private data: {error}"
            ))
        })?;
        let traces = runner.run().map_err(|error| {
            ProofError::Plonky3(format!(
                "run cached private compact recursive verifier circuit: {error:?}"
            ))
        })?;

        let prover = recursive_verifier_prover(
            goldilocks_config(),
            self.table_packing.clone(),
            summary.len(),
        );
        let recursive_proof = prover
            .prove_all_tables(&traces, &self.circuit_prover_data)
            .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

        Ok(RecursiveBatchProof {
            public_inputs: summary_public_inputs(summary),
            proof: recursive_proof,
        })
    }
}

pub(crate) struct PrivateCompactAppendRecursionProver {
    verification_circuit: Circuit<Challenge>,
    previous_inputs: VerifierInputs,
    chunk_inputs: VerifierInputs,
    previous_mmcs_op_ids: Vec<p3_circuit::NonPrimitiveOpId>,
    chunk_mmcs_op_ids: Vec<p3_circuit::NonPrimitiveOpId>,
    table_packing: TablePacking,
    circuit_prover_data: CircuitProverData<GoldilocksConfig>,
}

impl PrivateCompactAppendRecursionProver {
    pub(crate) fn new(
        previous: &BatchStarkProof<GoldilocksConfig>,
        chunk: &BatchStarkProof<GoldilocksConfig>,
        chunk_summary: &[F],
        chunk_public_offset: usize,
        full_layout: &ChainSummaryLayout,
        compact_layout: &ChainSummaryLayout,
    ) -> Result<Self, ProofError> {
        let config = goldilocks_config();
        let table_packing = proof_table_packing();
        let (
            verification_circuit,
            previous_inputs,
            chunk_inputs,
            previous_mmcs_op_ids,
            chunk_mmcs_op_ids,
        ) = build_private_append_verifier_circuit_with_compact_chunk_summary(
            previous,
            chunk,
            chunk_summary,
            chunk_public_offset,
            full_layout,
            compact_layout,
        )?;
        let preprocessors = recursive_verifier_preprocessors(&verification_circuit);
        let air_builders = recursive_verifier_air_builders(&verification_circuit);
        let (airs_degrees, primitive_columns, non_primitive_columns) =
            get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 2>(
                &verification_circuit,
                &table_packing,
                &preprocessors,
                &air_builders,
                ConstraintProfile::Standard,
            )
            .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
        let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
        let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees)
            .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
        let circuit_prover_data =
            CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

        Ok(Self {
            verification_circuit,
            previous_inputs,
            chunk_inputs,
            previous_mmcs_op_ids,
            chunk_mmcs_op_ids,
            table_packing,
            circuit_prover_data,
        })
    }

    pub(crate) fn prove(
        &self,
        previous: &BatchStarkProof<GoldilocksConfig>,
        chunk: &BatchStarkProof<GoldilocksConfig>,
        summary: &[F],
    ) -> Result<AggregatedRecursiveBatchProof, ProofError> {
        let public_inputs = execution_public_inputs(
            &[
                (&self.previous_inputs, previous),
                (&self.chunk_inputs, chunk),
            ],
            summary,
        );
        let mut private_inputs = self.previous_inputs.pack_private_values(&previous.proof);
        private_inputs.extend(self.chunk_inputs.pack_private_values(&chunk.proof));
        assert_public_ops_have_rows(&self.verification_circuit)?;

        let mut runner = self.verification_circuit.runner();
        runner.set_public_inputs(&public_inputs).map_err(|error| {
            ProofError::Plonky3(format!(
                "set cached private compact append public inputs: {error:?}"
            ))
        })?;
        runner
            .set_private_inputs(&private_inputs)
            .map_err(|error| {
                ProofError::Plonky3(format!(
                    "set cached private compact append verifier inputs: {error:?}"
                ))
            })?;
        set_proof_fri_private_data(
            &mut runner,
            &self.previous_mmcs_op_ids,
            previous,
            recursive_fri_verifier_params(),
        )
        .map_err(|error| {
            ProofError::Plonky3(format!(
                "set cached previous compact append FRI private data: {error}"
            ))
        })?;
        set_proof_fri_private_data(
            &mut runner,
            &self.chunk_mmcs_op_ids,
            chunk,
            base_fri_verifier_params(),
        )
        .map_err(|error| {
            ProofError::Plonky3(format!(
                "set cached chunk compact append FRI private data: {error}"
            ))
        })?;
        let traces = runner.run().map_err(|error| {
            ProofError::Plonky3(format!(
                "run cached private compact append verifier circuit: {error:?}"
            ))
        })?;

        let prover = recursive_verifier_prover(
            goldilocks_config(),
            self.table_packing.clone(),
            summary.len(),
        );
        let proof = prover
            .prove_all_tables(&traces, &self.circuit_prover_data)
            .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

        Ok(AggregatedRecursiveBatchProof {
            public_inputs: summary_public_inputs(summary),
            proof,
        })
    }
}

pub fn verify_recursive_batch(proof: &RecursiveBatchProof) -> Result<(), ProofError> {
    verify_bound_recursive_statement(&proof.proof, &proof.public_inputs)
}

pub(crate) fn verify_recursive_batch_with_leaf_summary_for_base(
    base_proof: &BatchStarkProof<GoldilocksConfig>,
    summary: &[F],
    recursive_proof: &RecursiveBatchProof,
) -> Result<(), ProofError> {
    let _ = base_proof;
    if recursive_proof.public_inputs != summary_public_inputs(summary) {
        return Err(ProofError::StatementMismatch);
    }
    verify_recursive_batch(recursive_proof)
}

pub(crate) fn verify_recursive_batch_with_private_leaf_summary(
    summary: &[F],
    recursive_proof: &RecursiveBatchProof,
) -> Result<(), ProofError> {
    if recursive_proof.public_inputs != summary_public_inputs(summary) {
        return Err(ProofError::StatementMismatch);
    }
    verify_recursive_batch(recursive_proof)
}

pub(crate) fn prove_aggregate_batch_proofs_with_chain_summary(
    left: &BatchStarkProof<GoldilocksConfig>,
    right: &BatchStarkProof<GoldilocksConfig>,
    summary: &[F],
    layout: Option<&ChainSummaryLayout>,
) -> Result<AggregatedRecursiveBatchProof, ProofError> {
    let config = goldilocks_config();
    let table_packing = proof_table_packing();
    let (verification_circuit, left_inputs, right_inputs, left_mmcs_op_ids, right_mmcs_op_ids) =
        build_aggregation_verifier_circuit_with_chain_summary(
            left, right, &config, summary, layout,
        )?;
    let (mut public_inputs, mut private_inputs) =
        left_inputs.pack_values(&table_public_inputs(left), &left.proof, &left.stark_common);
    let (right_public_inputs, right_private_inputs) = right_inputs.pack_values(
        &table_public_inputs(right),
        &right.proof,
        &right.stark_common,
    );
    public_inputs.extend(right_public_inputs);
    append_summary_public_inputs(&mut public_inputs, summary);
    private_inputs.extend(right_private_inputs);
    assert_public_ops_have_rows(&verification_circuit)?;

    let mut runner = verification_circuit.runner();
    runner
        .set_public_inputs(&public_inputs)
        .map_err(|error| ProofError::Plonky3(format!("set aggregate public inputs: {error:?}")))?;
    runner
        .set_private_inputs(&private_inputs)
        .map_err(|error| ProofError::Plonky3(format!("set aggregate private inputs: {error:?}")))?;
    set_proof_fri_private_data(
        &mut runner,
        &left_mmcs_op_ids,
        left,
        recursive_fri_verifier_params(),
    )
    .map_err(|error| {
        ProofError::Plonky3(format!("set left aggregate FRI private data: {error}"))
    })?;
    set_proof_fri_private_data(
        &mut runner,
        &right_mmcs_op_ids,
        right,
        recursive_fri_verifier_params(),
    )
    .map_err(|error| {
        ProofError::Plonky3(format!("set right aggregate FRI private data: {error}"))
    })?;
    let traces = runner.run().map_err(|error| {
        ProofError::Plonky3(format!("run aggregate verifier circuit: {error:?}"))
    })?;

    let preprocessors = recursive_verifier_preprocessors(&verification_circuit);
    let air_builders = recursive_verifier_air_builders(&verification_circuit);
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 2>(
            &verification_circuit,
            &table_packing,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
    let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(config, table_packing, summary.len());
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(AggregatedRecursiveBatchProof {
        public_inputs: summary_public_inputs(summary),
        proof,
    })
}

pub(crate) fn prove_private_aggregate_batch_proofs_with_chain_summary(
    left: &BatchStarkProof<GoldilocksConfig>,
    right: &BatchStarkProof<GoldilocksConfig>,
    summary: &[F],
    layout: Option<&ChainSummaryLayout>,
) -> Result<AggregatedRecursiveBatchProof, ProofError> {
    let config = goldilocks_config();
    let table_packing = proof_table_packing();
    let (verification_circuit, left_inputs, right_inputs, left_mmcs_op_ids, right_mmcs_op_ids) =
        build_private_aggregation_verifier_circuit_with_chain_summary(
            left, right, &config, summary, layout,
        )?;
    let public_inputs =
        execution_public_inputs(&[(&left_inputs, left), (&right_inputs, right)], summary);
    let mut private_inputs = left_inputs.pack_private_values(&left.proof);
    private_inputs.extend(right_inputs.pack_private_values(&right.proof));
    assert_public_ops_have_rows(&verification_circuit)?;

    let mut runner = verification_circuit.runner();
    runner.set_public_inputs(&public_inputs).map_err(|error| {
        ProofError::Plonky3(format!(
            "set private aggregate public summary inputs: {error:?}"
        ))
    })?;
    runner
        .set_private_inputs(&private_inputs)
        .map_err(|error| {
            ProofError::Plonky3(format!("set private aggregate verifier inputs: {error:?}"))
        })?;
    set_proof_fri_private_data(
        &mut runner,
        &left_mmcs_op_ids,
        left,
        recursive_fri_verifier_params(),
    )
    .map_err(|error| {
        ProofError::Plonky3(format!(
            "set left private aggregate FRI private data: {error}"
        ))
    })?;
    set_proof_fri_private_data(
        &mut runner,
        &right_mmcs_op_ids,
        right,
        recursive_fri_verifier_params(),
    )
    .map_err(|error| {
        ProofError::Plonky3(format!(
            "set right private aggregate FRI private data: {error}"
        ))
    })?;
    let traces = runner.run().map_err(|error| {
        ProofError::Plonky3(format!("run private aggregate verifier circuit: {error:?}"))
    })?;

    let preprocessors = recursive_verifier_preprocessors(&verification_circuit);
    let air_builders = recursive_verifier_air_builders(&verification_circuit);
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 2>(
            &verification_circuit,
            &table_packing,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
    let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(config, table_packing, summary.len());
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(AggregatedRecursiveBatchProof {
        public_inputs: summary_public_inputs(summary),
        proof,
    })
}

pub(crate) fn prove_private_append_batch_proof_with_compact_chunk_summary(
    previous: &BatchStarkProof<GoldilocksConfig>,
    chunk: &BatchStarkProof<GoldilocksConfig>,
    summary: &[F],
    chunk_summary: &[F],
    chunk_public_offset: usize,
    full_layout: &ChainSummaryLayout,
    compact_layout: &ChainSummaryLayout,
) -> Result<AggregatedRecursiveBatchProof, ProofError> {
    let prover = PrivateCompactAppendRecursionProver::new(
        previous,
        chunk,
        chunk_summary,
        chunk_public_offset,
        full_layout,
        compact_layout,
    )?;
    prover.prove(previous, chunk, summary)
}

pub(crate) fn prove_private_aggregate_batch_proofs_with_pbs_keyswitch_link(
    root: &BatchStarkProof<GoldilocksConfig>,
    key_switch: &BatchStarkProof<GoldilocksConfig>,
    root_summary: &[F],
    key_switch_summary: &[F],
    final_summary: &[F],
    layout: &PbsKeyswitchLinkLayout,
) -> Result<AggregatedRecursiveBatchProof, ProofError> {
    let config = goldilocks_config();
    let table_packing = proof_table_packing();
    let (verification_circuit, root_inputs, key_switch_inputs, root_mmcs_op_ids, key_mmcs_op_ids) =
        build_private_aggregation_verifier_circuit_with_pbs_keyswitch_link(
            root,
            key_switch,
            &config,
            root_summary,
            key_switch_summary,
            final_summary,
            layout,
        )?;
    let public_inputs = execution_public_inputs(
        &[(&root_inputs, root), (&key_switch_inputs, key_switch)],
        final_summary,
    );
    let mut private_inputs = root_inputs.pack_private_values(&root.proof);
    private_inputs.extend(key_switch_inputs.pack_private_values(&key_switch.proof));
    assert_public_ops_have_rows(&verification_circuit)?;

    let mut runner = verification_circuit.runner();
    runner.set_public_inputs(&public_inputs).map_err(|error| {
        ProofError::Plonky3(format!(
            "set private PBS/key-switch aggregate public summary inputs: {error:?}"
        ))
    })?;
    runner
        .set_private_inputs(&private_inputs)
        .map_err(|error| {
            ProofError::Plonky3(format!(
                "set private PBS/key-switch aggregate verifier inputs: {error:?}"
            ))
        })?;
    set_proof_fri_private_data(
        &mut runner,
        &root_mmcs_op_ids,
        root,
        recursive_fri_verifier_params(),
    )
    .map_err(|error| {
        ProofError::Plonky3(format!(
            "set compact root private aggregate FRI private data: {error}"
        ))
    })?;
    set_proof_fri_private_data(
        &mut runner,
        &key_mmcs_op_ids,
        key_switch,
        recursive_fri_verifier_params(),
    )
    .map_err(|error| {
        ProofError::Plonky3(format!(
            "set key-switch private aggregate FRI private data: {error}"
        ))
    })?;
    let traces = runner.run().map_err(|error| {
        ProofError::Plonky3(format!(
            "run private PBS/key-switch aggregate verifier circuit: {error:?}"
        ))
    })?;

    let preprocessors = recursive_verifier_preprocessors(&verification_circuit);
    let air_builders = recursive_verifier_air_builders(&verification_circuit);
    let (airs_degrees, primitive_columns, non_primitive_columns) =
        get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 2>(
            &verification_circuit,
            &table_packing,
            &preprocessors,
            &air_builders,
            ConstraintProfile::Standard,
        )
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
    let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(config, table_packing, final_summary.len());
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(AggregatedRecursiveBatchProof {
        public_inputs: summary_public_inputs(final_summary),
        proof,
    })
}

pub fn verify_aggregated_recursive_batch(
    proof: &AggregatedRecursiveBatchProof,
) -> Result<(), ProofError> {
    verify_bound_recursive_statement(&proof.proof, &proof.public_inputs)
}

pub(crate) fn verify_aggregated_recursive_batch_with_public_summary(
    proof: &AggregatedRecursiveBatchProof,
    summary: &[F],
) -> Result<(), ProofError> {
    if proof.public_inputs != summary_public_inputs(summary) {
        return Err(ProofError::StatementMismatch);
    }
    verify_aggregated_recursive_batch(proof)
}

pub(crate) fn verify_aggregated_recursive_batch_with_private_summary(
    proof: &AggregatedRecursiveBatchProof,
    summary: &[F],
) -> Result<(), ProofError> {
    if proof.public_inputs != summary_public_inputs(summary) {
        return Err(ProofError::StatementMismatch);
    }
    verify_aggregated_recursive_batch(proof)
}

pub(crate) fn verify_aggregated_recursive_batch_with_summary_for_child_proofs(
    left: &BatchStarkProof<GoldilocksConfig>,
    right: &BatchStarkProof<GoldilocksConfig>,
    summary: &[F],
    proof: &AggregatedRecursiveBatchProof,
) -> Result<(), ProofError> {
    let _ = (left, right);
    if proof.public_inputs != summary_public_inputs(summary) {
        return Err(ProofError::StatementMismatch);
    }
    verify_aggregated_recursive_batch(proof)
}

fn build_verifier_circuit_with_leaf_summary(
    proof: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
    summary: &[F],
    chunk_public_offset: usize,
) -> Result<
    (
        Circuit<Challenge>,
        VerifierInputs,
        Vec<p3_circuit::NonPrimitiveOpId>,
    ),
    ProofError,
> {
    let mut builder = CircuitBuilder::<Challenge>::new();
    enable_recursive_verifier_ops(&mut builder);

    let base_table_provers = base_table_provers(proof);
    let fri_params = base_fri_verifier_params();
    let (verifier_inputs, mmcs_op_ids) = add_batch_verifier_to_builder(
        &mut builder,
        proof,
        config,
        &base_table_provers,
        &fri_params,
    )?;
    let summary_targets = allocate_summary_public_inputs(&mut builder, summary.len());
    constrain_leaf_summary(
        &mut builder,
        &verifier_inputs,
        &summary_targets,
        summary,
        chunk_public_offset,
    )?;
    let circuit = builder
        .build()
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok((circuit, verifier_inputs, mmcs_op_ids))
}

fn build_private_verifier_circuit_with_leaf_summary(
    proof: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
    summary: &[F],
    chunk_public_offset: usize,
) -> Result<
    (
        Circuit<Challenge>,
        VerifierInputs,
        Vec<p3_circuit::NonPrimitiveOpId>,
    ),
    ProofError,
> {
    let mut builder = CircuitBuilder::<Challenge>::new();
    enable_recursive_verifier_ops(&mut builder);

    let base_table_provers = base_table_provers(proof);
    let fri_params = base_fri_verifier_params();
    let (verifier_inputs, mmcs_op_ids) = add_private_batch_verifier_to_builder(
        &mut builder,
        proof,
        config,
        &base_table_provers,
        &fri_params,
    )?;
    touch_private_verifier_boundary_inputs(&mut builder, &verifier_inputs);
    let summary_targets = allocate_summary_public_inputs(&mut builder, summary.len());
    constrain_leaf_summary(
        &mut builder,
        &verifier_inputs,
        &summary_targets,
        summary,
        chunk_public_offset,
    )?;
    let circuit = builder
        .build()
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok((circuit, verifier_inputs, mmcs_op_ids))
}

fn build_private_verifier_circuit_with_compact_leaf_summary(
    proof: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
    summary: &[F],
    chunk_public_offset: usize,
    full_layout: &ChainSummaryLayout,
    compact_layout: &ChainSummaryLayout,
) -> Result<
    (
        Circuit<Challenge>,
        VerifierInputs,
        Vec<p3_circuit::NonPrimitiveOpId>,
    ),
    ProofError,
> {
    let mut builder = CircuitBuilder::<Challenge>::new();
    enable_recursive_verifier_ops(&mut builder);

    let base_table_provers = base_table_provers(proof);
    let fri_params = base_fri_verifier_params();
    let (verifier_inputs, mmcs_op_ids) = add_private_batch_verifier_to_builder(
        &mut builder,
        proof,
        config,
        &base_table_provers,
        &fri_params,
    )?;
    touch_private_verifier_boundary_inputs(&mut builder, &verifier_inputs);
    let summary_targets = allocate_summary_public_inputs(&mut builder, summary.len());
    constrain_compact_leaf_summary(
        &mut builder,
        &verifier_inputs,
        &summary_targets,
        summary,
        chunk_public_offset,
        full_layout,
        compact_layout,
    )?;
    let circuit = builder
        .build()
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok((circuit, verifier_inputs, mmcs_op_ids))
}

fn build_private_append_verifier_circuit_with_compact_chunk_summary(
    previous: &BatchStarkProof<GoldilocksConfig>,
    chunk: &BatchStarkProof<GoldilocksConfig>,
    chunk_summary: &[F],
    chunk_public_offset: usize,
    full_layout: &ChainSummaryLayout,
    compact_layout: &ChainSummaryLayout,
) -> Result<AggregationVerifierCircuit, ProofError> {
    validate_summary_layout(compact_layout)?;
    let mut builder = CircuitBuilder::<Challenge>::new();
    enable_recursive_verifier_ops(&mut builder);

    let recursive_config = goldilocks_config();
    let recursive_table_provers = base_table_provers(previous);
    let recursive_fri_params = recursive_fri_verifier_params();
    let (previous_inputs, previous_mmcs_op_ids) = add_private_batch_verifier_to_builder(
        &mut builder,
        previous,
        &recursive_config,
        &recursive_table_provers,
        &recursive_fri_params,
    )?;
    touch_private_verifier_boundary_inputs(&mut builder, &previous_inputs);

    let base_config = base_goldilocks_config();
    let base_table_provers = base_table_provers(chunk);
    let base_fri_params = base_fri_verifier_params();
    let (chunk_inputs, chunk_mmcs_op_ids) = add_private_batch_verifier_to_builder(
        &mut builder,
        chunk,
        &base_config,
        &base_table_provers,
        &base_fri_params,
    )?;
    touch_private_verifier_boundary_inputs(&mut builder, &chunk_inputs);

    let summary_targets = allocate_summary_public_inputs(&mut builder, compact_layout.len);
    let previous_summary =
        child_summary_targets(&mut builder, &previous_inputs, previous, compact_layout.len)?;
    let chunk_summary_targets = compact_leaf_summary_targets(
        &mut builder,
        &chunk_inputs,
        chunk_summary,
        chunk_public_offset,
        full_layout,
        compact_layout,
    )?;
    constrain_aggregate_summary_targets(
        &mut builder,
        &previous_summary,
        &chunk_summary_targets,
        &summary_targets,
        compact_layout,
    )?;
    let circuit = builder
        .build()
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok((
        circuit,
        previous_inputs,
        chunk_inputs,
        previous_mmcs_op_ids,
        chunk_mmcs_op_ids,
    ))
}

type AggregationVerifierCircuit = (
    Circuit<Challenge>,
    VerifierInputs,
    VerifierInputs,
    Vec<p3_circuit::NonPrimitiveOpId>,
    Vec<p3_circuit::NonPrimitiveOpId>,
);

fn build_aggregation_verifier_circuit_with_chain_summary(
    left: &BatchStarkProof<GoldilocksConfig>,
    right: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
    summary: &[F],
    layout: Option<&ChainSummaryLayout>,
) -> Result<AggregationVerifierCircuit, ProofError> {
    let mut builder = CircuitBuilder::<Challenge>::new();
    enable_recursive_verifier_ops(&mut builder);

    let recursive_table_provers = base_table_provers(left);
    let fri_params = recursive_fri_verifier_params();
    let (left_inputs, left_mmcs_op_ids) = add_batch_verifier_to_builder(
        &mut builder,
        left,
        config,
        &recursive_table_provers,
        &fri_params,
    )?;
    let (right_inputs, right_mmcs_op_ids) = add_batch_verifier_to_builder(
        &mut builder,
        right,
        config,
        &base_table_provers(right),
        &fri_params,
    )?;
    let summary_targets = allocate_summary_public_inputs(&mut builder, summary.len());
    if let Some(layout) = layout {
        constrain_aggregate_summary(
            &mut builder,
            &left_inputs,
            left,
            &right_inputs,
            right,
            &summary_targets,
            layout,
        )?;
    }
    let circuit = builder
        .build()
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok((
        circuit,
        left_inputs,
        right_inputs,
        left_mmcs_op_ids,
        right_mmcs_op_ids,
    ))
}

fn build_private_aggregation_verifier_circuit_with_chain_summary(
    left: &BatchStarkProof<GoldilocksConfig>,
    right: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
    summary: &[F],
    layout: Option<&ChainSummaryLayout>,
) -> Result<AggregationVerifierCircuit, ProofError> {
    let mut builder = CircuitBuilder::<Challenge>::new();
    enable_recursive_verifier_ops(&mut builder);

    let recursive_table_provers = base_table_provers(left);
    let fri_params = recursive_fri_verifier_params();
    let (left_inputs, left_mmcs_op_ids) = add_private_batch_verifier_to_builder(
        &mut builder,
        left,
        config,
        &recursive_table_provers,
        &fri_params,
    )?;
    touch_private_verifier_boundary_inputs(&mut builder, &left_inputs);
    let (right_inputs, right_mmcs_op_ids) = add_private_batch_verifier_to_builder(
        &mut builder,
        right,
        config,
        &base_table_provers(right),
        &fri_params,
    )?;
    touch_private_verifier_boundary_inputs(&mut builder, &right_inputs);
    let summary_targets = allocate_summary_public_inputs(&mut builder, summary.len());
    if let Some(layout) = layout {
        constrain_aggregate_summary(
            &mut builder,
            &left_inputs,
            left,
            &right_inputs,
            right,
            &summary_targets,
            layout,
        )?;
    }
    let circuit = builder
        .build()
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok((
        circuit,
        left_inputs,
        right_inputs,
        left_mmcs_op_ids,
        right_mmcs_op_ids,
    ))
}

fn build_private_aggregation_verifier_circuit_with_pbs_keyswitch_link(
    root: &BatchStarkProof<GoldilocksConfig>,
    key_switch: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
    root_summary: &[F],
    key_switch_summary: &[F],
    final_summary: &[F],
    layout: &PbsKeyswitchLinkLayout,
) -> Result<AggregationVerifierCircuit, ProofError> {
    let mut builder = CircuitBuilder::<Challenge>::new();
    enable_recursive_verifier_ops(&mut builder);

    let recursive_table_provers = base_table_provers(root);
    let fri_params = recursive_fri_verifier_params();
    let (root_inputs, root_mmcs_op_ids) = add_private_batch_verifier_to_builder(
        &mut builder,
        root,
        config,
        &recursive_table_provers,
        &fri_params,
    )?;
    touch_private_verifier_boundary_inputs(&mut builder, &root_inputs);
    let (key_switch_inputs, key_mmcs_op_ids) = add_private_batch_verifier_to_builder(
        &mut builder,
        key_switch,
        config,
        &base_table_provers(key_switch),
        &fri_params,
    )?;
    touch_private_verifier_boundary_inputs(&mut builder, &key_switch_inputs);
    let summary_targets = allocate_summary_public_inputs(&mut builder, final_summary.len());
    constrain_pbs_keyswitch_link_summary(
        &mut builder,
        &root_inputs,
        root,
        root_summary,
        &key_switch_inputs,
        key_switch,
        key_switch_summary,
        &summary_targets,
        layout,
    )?;
    let circuit = builder
        .build()
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok((
        circuit,
        root_inputs,
        key_switch_inputs,
        root_mmcs_op_ids,
        key_mmcs_op_ids,
    ))
}

fn allocate_summary_public_inputs(
    builder: &mut CircuitBuilder<Challenge>,
    len: usize,
) -> Vec<ExprId> {
    let targets: Vec<_> = (0..len).map(|_| builder.public_input()).collect();
    builder
        .set_statement_exports::<F>(
            &targets
                .iter()
                .copied()
                .map(p3_circuit::StatementExport::Base)
                .collect::<Vec<_>>(),
        )
        .expect("one base-field summary per recursive circuit");
    targets
}

fn constrain_leaf_summary(
    builder: &mut CircuitBuilder<Challenge>,
    verifier_inputs: &VerifierInputs,
    summary_targets: &[ExprId],
    summary: &[F],
    chunk_public_offset: usize,
) -> Result<(), ProofError> {
    if summary_targets.len() != summary.len() || chunk_public_offset > summary.len() {
        return Err(ProofError::StatementMismatch);
    }

    for (target, &value) in summary_targets[..chunk_public_offset]
        .iter()
        .zip(summary.iter())
    {
        let value = builder.define_const(Challenge::from(value));
        assert_equal(builder, *target, value);
    }

    let chunk_public_targets = public_air_targets(verifier_inputs)?;
    let chunk_summary_targets = &summary_targets[chunk_public_offset..];
    if chunk_summary_targets.len() > chunk_public_targets.len() {
        return Err(ProofError::StatementMismatch);
    }
    for (&summary_target, &chunk_target) in chunk_summary_targets.iter().zip(chunk_public_targets) {
        assert_equal(builder, summary_target, chunk_target);
    }

    Ok(())
}

fn constrain_compact_leaf_summary(
    builder: &mut CircuitBuilder<Challenge>,
    verifier_inputs: &VerifierInputs,
    summary_targets: &[ExprId],
    summary: &[F],
    chunk_public_offset: usize,
    full_layout: &ChainSummaryLayout,
    compact_layout: &ChainSummaryLayout,
) -> Result<(), ProofError> {
    validate_summary_layout(full_layout)?;
    validate_summary_layout(compact_layout)?;
    if summary_targets.len() != summary.len()
        || summary_targets.len() != compact_layout.len
        || chunk_public_offset > summary.len()
        || chunk_public_offset > full_layout.len
    {
        return Err(ProofError::StatementMismatch);
    }

    let expected_targets = compact_leaf_summary_targets(
        builder,
        verifier_inputs,
        summary,
        chunk_public_offset,
        full_layout,
        compact_layout,
    )?;
    connect_ranges(
        builder,
        summary_targets,
        0..summary_targets.len(),
        &expected_targets,
        0..expected_targets.len(),
    )?;

    Ok(())
}

fn compact_leaf_summary_targets(
    builder: &mut CircuitBuilder<Challenge>,
    verifier_inputs: &VerifierInputs,
    summary: &[F],
    chunk_public_offset: usize,
    full_layout: &ChainSummaryLayout,
    compact_layout: &ChainSummaryLayout,
) -> Result<Vec<ExprId>, ProofError> {
    validate_summary_layout(full_layout)?;
    validate_summary_layout(compact_layout)?;
    if summary.len() != compact_layout.len
        || chunk_public_offset > summary.len()
        || chunk_public_offset > full_layout.len
    {
        return Err(ProofError::StatementMismatch);
    }

    let chunk_public_targets = public_air_targets(verifier_inputs)?;
    let input_accumulator = summary_range_to_chunk_range(
        full_layout.input_accumulator.clone(),
        chunk_public_offset,
        chunk_public_targets.len(),
    )?;
    let output_accumulator = summary_range_to_chunk_range(
        full_layout.output_accumulator.clone(),
        chunk_public_offset,
        chunk_public_targets.len(),
    )?;

    let input_digest = poseidon_chain::poseidon2_digest_targets_from_base_targets(
        builder,
        COMPACT_ACCUMULATOR_DIGEST_TAG,
        chunk_public_targets[input_accumulator].iter().copied(),
    )
    .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    let output_digest = poseidon_chain::poseidon2_digest_targets_from_base_targets(
        builder,
        COMPACT_ACCUMULATOR_DIGEST_TAG,
        chunk_public_targets[output_accumulator].iter().copied(),
    )
    .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    let mut targets = Vec::with_capacity(compact_layout.len);
    for &value in &summary[..chunk_public_offset] {
        targets.push(builder.define_const(Challenge::from(value)));
    }

    if targets.len() != compact_layout.input_accumulator.start {
        return Err(ProofError::StatementMismatch);
    }
    targets.extend_from_slice(&input_digest);
    push_chunk_range_targets(
        &mut targets,
        chunk_public_targets,
        full_layout.bsk_digest_in.clone(),
        chunk_public_offset,
    )?;
    push_chunk_range_targets(
        &mut targets,
        chunk_public_targets,
        full_layout.bsk_digest_out.clone(),
        chunk_public_offset,
    )?;
    push_chunk_range_targets(
        &mut targets,
        chunk_public_targets,
        full_layout.mask_digest_in.clone(),
        chunk_public_offset,
    )?;
    push_chunk_range_targets(
        &mut targets,
        chunk_public_targets,
        full_layout.mask_digest_out.clone(),
        chunk_public_offset,
    )?;
    if targets.len() != compact_layout.output_accumulator.start {
        return Err(ProofError::StatementMismatch);
    }
    targets.extend_from_slice(&output_digest);
    if targets.len() != compact_layout.len {
        return Err(ProofError::StatementMismatch);
    }

    Ok(targets)
}

fn constrain_pbs_keyswitch_link_summary(
    builder: &mut CircuitBuilder<Challenge>,
    root_inputs: &VerifierInputs,
    root: &BatchStarkProof<GoldilocksConfig>,
    root_summary: &[F],
    key_switch_inputs: &VerifierInputs,
    key_switch: &BatchStarkProof<GoldilocksConfig>,
    key_switch_summary: &[F],
    summary_targets: &[ExprId],
    layout: &PbsKeyswitchLinkLayout,
) -> Result<(), ProofError> {
    validate_pbs_keyswitch_link_layout(layout, root_summary.len(), key_switch_summary.len())?;
    if summary_targets.len() != layout.final_len {
        return Err(ProofError::StatementMismatch);
    }

    let root_summary_targets =
        child_summary_targets(builder, root_inputs, root, root_summary.len())?;
    let key_switch_summary_targets = child_summary_targets(
        builder,
        key_switch_inputs,
        key_switch,
        key_switch_summary.len(),
    )?;
    touch_targets(builder, &key_switch_summary_targets);

    connect_ranges(
        builder,
        summary_targets,
        layout.final_compact_summary.clone(),
        &root_summary_targets,
        0..root_summary.len(),
    )?;
    connect_ranges(
        builder,
        &root_summary_targets,
        layout.compact_summary.params.clone(),
        &key_switch_summary_targets,
        layout.key_params.clone(),
    )?;

    let key_input_digest = poseidon_chain::poseidon2_digest_targets_from_base_targets(
        builder,
        COMPACT_ACCUMULATOR_DIGEST_TAG,
        key_switch_summary_targets[layout.key_input_accumulator.clone()]
            .iter()
            .copied(),
    )
    .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;
    connect_ranges(
        builder,
        &root_summary_targets,
        layout.compact_summary.output_accumulator.clone(),
        &key_input_digest,
        0..SELECTOR_DIGEST_WIDTH,
    )?;

    connect_ranges(
        builder,
        summary_targets,
        layout.final_output_lwe.clone(),
        &key_switch_summary_targets,
        layout.key_output_lwe.clone(),
    )?;

    Ok(())
}

fn constrain_aggregate_summary(
    builder: &mut CircuitBuilder<Challenge>,
    left_inputs: &VerifierInputs,
    left: &BatchStarkProof<GoldilocksConfig>,
    right_inputs: &VerifierInputs,
    right: &BatchStarkProof<GoldilocksConfig>,
    summary_targets: &[ExprId],
    layout: &ChainSummaryLayout,
) -> Result<(), ProofError> {
    validate_summary_layout(layout)?;
    if summary_targets.len() != layout.len {
        return Err(ProofError::StatementMismatch);
    }

    let left_summary = child_summary_targets(builder, left_inputs, left, layout.len)?;
    let right_summary = child_summary_targets(builder, right_inputs, right, layout.len)?;
    constrain_aggregate_summary_targets(
        builder,
        &left_summary,
        &right_summary,
        summary_targets,
        layout,
    )
}

fn constrain_aggregate_summary_targets(
    builder: &mut CircuitBuilder<Challenge>,
    left_summary: &[ExprId],
    right_summary: &[ExprId],
    summary_targets: &[ExprId],
    layout: &ChainSummaryLayout,
) -> Result<(), ProofError> {
    validate_summary_layout(layout)?;
    if left_summary.len() != layout.len
        || right_summary.len() != layout.len
        || summary_targets.len() != layout.len
    {
        return Err(ProofError::StatementMismatch);
    }

    connect_range(builder, left_summary, right_summary, layout.params.clone())?;
    connect_range_to_summary(
        builder,
        summary_targets,
        left_summary,
        layout.params.clone(),
    )?;

    let step_count = builder.add(
        left_summary[layout.step_count],
        right_summary[layout.step_count],
    );
    assert_equal(builder, summary_targets[layout.step_count], step_count);

    connect_ranges(
        builder,
        left_summary,
        layout.output_accumulator.clone(),
        right_summary,
        layout.input_accumulator.clone(),
    )?;
    connect_ranges(
        builder,
        left_summary,
        layout.bsk_digest_out.clone(),
        right_summary,
        layout.bsk_digest_in.clone(),
    )?;
    connect_ranges(
        builder,
        left_summary,
        layout.mask_digest_out.clone(),
        right_summary,
        layout.mask_digest_in.clone(),
    )?;

    connect_range_to_summary(
        builder,
        summary_targets,
        left_summary,
        layout.input_accumulator.clone(),
    )?;
    connect_range_to_summary(
        builder,
        summary_targets,
        left_summary,
        layout.bsk_digest_in.clone(),
    )?;
    connect_range_to_summary(
        builder,
        summary_targets,
        right_summary,
        layout.bsk_digest_out.clone(),
    )?;
    connect_range_to_summary(
        builder,
        summary_targets,
        left_summary,
        layout.mask_digest_in.clone(),
    )?;
    connect_range_to_summary(
        builder,
        summary_targets,
        right_summary,
        layout.mask_digest_out.clone(),
    )?;
    connect_range_to_summary(
        builder,
        summary_targets,
        right_summary,
        layout.output_accumulator.clone(),
    )?;

    Ok(())
}

fn validate_pbs_keyswitch_link_layout(
    layout: &PbsKeyswitchLinkLayout,
    compact_summary_len: usize,
    key_summary_len: usize,
) -> Result<(), ProofError> {
    validate_summary_layout(&layout.compact_summary)?;
    if layout.compact_summary.len != compact_summary_len
        || layout.final_compact_summary.len() != compact_summary_len
        || layout.final_compact_summary.end > layout.final_len
        || layout.final_output_lwe.end > layout.final_len
        || layout.key_params.end > key_summary_len
        || layout.key_input_accumulator.end > key_summary_len
        || layout.key_output_lwe.end > key_summary_len
        || layout.key_input_accumulator.start > layout.key_input_accumulator.end
        || layout.key_output_lwe.start > layout.key_output_lwe.end
    {
        return Err(ProofError::StatementMismatch);
    }
    if layout.compact_summary.output_accumulator.len() != SELECTOR_DIGEST_WIDTH {
        return Err(ProofError::StatementMismatch);
    }
    if layout.final_output_lwe.len() != layout.key_output_lwe.len() {
        return Err(ProofError::StatementMismatch);
    }
    Ok(())
}

fn child_summary_targets(
    _builder: &mut CircuitBuilder<Challenge>,
    verifier_inputs: &VerifierInputs,
    proof: &BatchStarkProof<GoldilocksConfig>,
    summary_len: usize,
) -> Result<Vec<ExprId>, ProofError> {
    let targets = &verifier_inputs.air_public_targets[statement_table_index(proof)?];
    if targets.len() != summary_len {
        return Err(ProofError::StatementMismatch);
    }
    Ok(targets.clone())
}

fn public_air_targets(verifier_inputs: &VerifierInputs) -> Result<&[ExprId], ProofError> {
    Ok(&verifier_inputs.statement)
}

fn validate_summary_layout(layout: &ChainSummaryLayout) -> Result<(), ProofError> {
    for range in [
        layout.params.clone(),
        layout.input_accumulator.clone(),
        layout.bsk_digest_in.clone(),
        layout.bsk_digest_out.clone(),
        layout.mask_digest_in.clone(),
        layout.mask_digest_out.clone(),
        layout.output_accumulator.clone(),
    ] {
        if range.start > range.end || range.end > layout.len {
            return Err(ProofError::StatementMismatch);
        }
    }
    if layout.step_count >= layout.len {
        return Err(ProofError::StatementMismatch);
    }
    Ok(())
}

fn connect_range(
    builder: &mut CircuitBuilder<Challenge>,
    left: &[ExprId],
    right: &[ExprId],
    range: Range<usize>,
) -> Result<(), ProofError> {
    connect_ranges(builder, left, range.clone(), right, range)
}

fn connect_range_to_summary(
    builder: &mut CircuitBuilder<Challenge>,
    summary: &[ExprId],
    source: &[ExprId],
    range: Range<usize>,
) -> Result<(), ProofError> {
    connect_ranges(builder, summary, range.clone(), source, range)
}

fn connect_ranges(
    builder: &mut CircuitBuilder<Challenge>,
    left: &[ExprId],
    left_range: Range<usize>,
    right: &[ExprId],
    right_range: Range<usize>,
) -> Result<(), ProofError> {
    if left_range.len() != right_range.len()
        || left_range.end > left.len()
        || right_range.end > right.len()
    {
        return Err(ProofError::StatementMismatch);
    }
    for (left_index, right_index) in left_range.zip(right_range) {
        assert_equal(builder, left[left_index], right[right_index]);
    }
    Ok(())
}

fn push_chunk_range_targets(
    targets: &mut Vec<ExprId>,
    chunk_public_targets: &[ExprId],
    full_summary_range: Range<usize>,
    chunk_public_offset: usize,
) -> Result<(), ProofError> {
    let chunk_range = summary_range_to_chunk_range(
        full_summary_range,
        chunk_public_offset,
        chunk_public_targets.len(),
    )?;
    targets.extend(chunk_public_targets[chunk_range].iter().copied());
    Ok(())
}

fn summary_range_to_chunk_range(
    summary_range: Range<usize>,
    chunk_public_offset: usize,
    chunk_public_len: usize,
) -> Result<Range<usize>, ProofError> {
    let start = summary_range
        .start
        .checked_sub(chunk_public_offset)
        .ok_or(ProofError::StatementMismatch)?;
    let end = summary_range
        .end
        .checked_sub(chunk_public_offset)
        .ok_or(ProofError::StatementMismatch)?;
    if start > end || end > chunk_public_len {
        return Err(ProofError::StatementMismatch);
    }
    Ok(start..end)
}

fn assert_equal(builder: &mut CircuitBuilder<Challenge>, left: ExprId, right: ExprId) {
    let diff = builder.sub(left, right);
    builder.assert_zero(diff);
}

fn touch_targets(builder: &mut CircuitBuilder<Challenge>, targets: &[ExprId]) {
    let zero = builder.define_const(Challenge::ZERO);
    for &target in targets {
        let negated = builder.sub(zero, target);
        let passthrough = builder.sub(zero, negated);
        assert_equal(builder, passthrough, target);
    }
}

fn touch_private_verifier_boundary_inputs(
    builder: &mut CircuitBuilder<Challenge>,
    verifier_inputs: &VerifierInputs,
) {
    for targets in &verifier_inputs.air_public_targets {
        touch_targets(builder, targets);
    }

    let mut pow_targets = verifier_inputs
        .proof_targets
        .opening_proof
        .commit_pow_witnesses
        .iter()
        .map(|witness| witness.witness)
        .collect::<Vec<_>>();
    pow_targets.push(
        verifier_inputs
            .proof_targets
            .opening_proof
            .pow_witness
            .witness,
    );
    touch_targets(builder, &pow_targets);
}

fn add_batch_verifier_to_builder(
    builder: &mut CircuitBuilder<Challenge>,
    proof: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
    table_provers: &[Box<dyn TableProver<GoldilocksConfig>>],
    fri_params: &p3_recursion::FriVerifierParams,
) -> Result<(VerifierInputs, Vec<p3_circuit::NonPrimitiveOpId>), ProofError> {
    match proof.ext_degree {
        1 => add_batch_verifier_to_builder_with_degree::<1>(
            builder,
            proof,
            config,
            table_provers,
            fri_params,
        ),
        2 => add_batch_verifier_to_builder_with_degree::<2>(
            builder,
            proof,
            config,
            table_provers,
            fri_params,
        ),
        degree => Err(ProofError::Plonky3(format!(
            "unsupported recursive verifier input extension degree: {degree}"
        ))),
    }
}

fn add_private_batch_verifier_to_builder(
    builder: &mut CircuitBuilder<Challenge>,
    proof: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
    table_provers: &[Box<dyn TableProver<GoldilocksConfig>>],
    fri_params: &p3_recursion::FriVerifierParams,
) -> Result<(VerifierInputs, Vec<p3_circuit::NonPrimitiveOpId>), ProofError> {
    match proof.ext_degree {
        1 => add_private_batch_verifier_to_builder_with_degree::<1>(
            builder,
            proof,
            config,
            table_provers,
            fri_params,
        ),
        2 => add_private_batch_verifier_to_builder_with_degree::<2>(
            builder,
            proof,
            config,
            table_provers,
            fri_params,
        ),
        degree => Err(ProofError::Plonky3(format!(
            "unsupported recursive verifier input extension degree: {degree}"
        ))),
    }
}

fn add_batch_verifier_to_builder_with_degree<const D: usize>(
    builder: &mut CircuitBuilder<Challenge>,
    proof: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
    table_provers: &[Box<dyn TableProver<GoldilocksConfig>>],
    fri_params: &p3_recursion::FriVerifierParams,
) -> Result<(VerifierInputs, Vec<p3_circuit::NonPrimitiveOpId>), ProofError> {
    let lookup_gadget = LogUpGadget;
    verify_p3_batch_proof_circuit::<
        GoldilocksConfig,
        MerkleCapTargets<F, 4>,
        InputProofTargets<F, Challenge, RecValMmcs<F, 4, MyHash, MyCompress>>,
        InnerFri,
        LogUpGadget,
        Poseidon2Config,
        8,
        4,
        D,
    >(
        config,
        builder,
        proof,
        fri_params,
        &proof.stark_common,
        &lookup_gadget,
        Poseidon2Config::GOLDILOCKS_D2_W8,
        table_provers,
    )
    .map_err(map_recursion_error)
    .and_then(|(native, op_ids)| {
        let statement = native.air_public_targets[statement_table_index(proof)?].clone();
        Ok((VerifierInputs { native, statement }, op_ids))
    })
}

fn add_private_batch_verifier_to_builder_with_degree<const D: usize>(
    builder: &mut CircuitBuilder<Challenge>,
    proof: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
    table_provers: &[Box<dyn TableProver<GoldilocksConfig>>],
    fri_params: &p3_recursion::FriVerifierParams,
) -> Result<(VerifierInputs, Vec<p3_circuit::NonPrimitiveOpId>), ProofError> {
    add_batch_verifier_to_builder_with_degree::<D>(
        builder,
        proof,
        config,
        table_provers,
        fri_params,
    )
}

fn enable_recursive_verifier_ops(builder: &mut CircuitBuilder<Challenge>) {
    builder.enable_poseidon2_perm_width_8::<GoldilocksD2Width8, _>(
        generate_poseidon2_trace::<Challenge, GoldilocksD2Width8>,
        goldilocks_poseidon2_8(),
    );
    builder.enable_recompose::<F>(generate_recompose_trace::<F, Challenge>);
}

fn recursive_verifier_prover(
    config: GoldilocksConfig,
    table_packing: TablePacking,
    statement_len: usize,
) -> BatchStarkProver<GoldilocksConfig> {
    let mut prover = BatchStarkProver::new(config).with_table_packing(table_packing);
    prover.register_poseidon2_table::<2>(Poseidon2Config::GOLDILOCKS_D2_W8.for_challenger());
    prover.register_poseidon2_table::<2>(Poseidon2Config::GOLDILOCKS_D2_W8);
    prover.register_recompose_table::<2>(true);
    prover.register_table_prover(Box::new(p3_circuit_prover::StatementProver::<2>::new(
        crate::statement_schema(statement_len),
    )));
    prover
}

fn recursive_verifier_preprocessors(
    circuit: &Circuit<Challenge>,
) -> Vec<Box<dyn p3_circuit_prover::common::NpoPreprocessor<F>>> {
    vec![
        poseidon2_preprocessor::<F>(),
        recompose_preprocessor::<F>(true),
        Box::new(p3_circuit_prover::StatementPreprocessor::new(
            circuit
                .statement_schema()
                .expect("recursive statement")
                .clone(),
        )),
    ]
}

fn recursive_verifier_air_builders(
    circuit: &Circuit<Challenge>,
) -> Vec<Box<dyn p3_circuit_prover::common::NpoAirBuilder<GoldilocksConfig, 2>>> {
    let mut air_builders = poseidon2_air_builders_for_configs::<GoldilocksConfig, 2>(vec![
        Poseidon2Config::GOLDILOCKS_D2_W8.for_challenger(),
        Poseidon2Config::GOLDILOCKS_D2_W8,
    ]);
    air_builders.extend(recompose_air_builders::<GoldilocksConfig, 2>(1, true));
    air_builders.push(Box::new(p3_circuit_prover::StatementAirBuilder::<2>::new(
        circuit
            .statement_schema()
            .expect("recursive statement")
            .clone(),
    )));
    air_builders
}

fn table_public_inputs(proof: &BatchStarkProof<GoldilocksConfig>) -> Vec<Vec<F>> {
    let mut inputs = vec![Vec::new(); NUM_PRIMITIVE_TABLES];
    inputs.extend(
        proof
            .non_primitives
            .iter()
            .map(|entry| entry.public_values.clone()),
    );
    inputs
}

fn base_table_provers(
    proof: &BatchStarkProof<GoldilocksConfig>,
) -> Vec<Box<dyn TableProver<GoldilocksConfig>>> {
    let mut provers: Vec<Box<dyn TableProver<GoldilocksConfig>>> =
        vec![Box::new(Poseidon2ProverD2::new(
            Poseidon2Config::GOLDILOCKS_D2_W8,
            ConstraintProfile::Standard,
        ))];
    provers.push(Box::new(
        crate::statement_digest::StatementDigestProver::new(),
    ));
    provers.insert(
        0,
        Box::new(Poseidon2ProverD2::new(
            Poseidon2Config::GOLDILOCKS_D2_W8.for_challenger(),
            ConstraintProfile::Standard,
        )),
    );
    provers.extend(recompose_table_provers::<GoldilocksConfig, 2>(1, true));
    provers.extend(
        proof_range_check_bit_counts(proof)
            .into_iter()
            .map(|bit_count| {
                Box::new(RangeCheckProver::new(bit_count, RANGE_CHECK_DEFAULT_LANES))
                    as Box<dyn TableProver<GoldilocksConfig>>
            }),
    );
    if let Some(entry) = proof
        .non_primitives
        .iter()
        .find(|entry| entry.op_type == p3_circuit::ops::NpoTypeId::statement())
    {
        provers.push(Box::new(p3_circuit_prover::StatementProver::<2>::new(
            crate::statement_schema(entry.public_values.len()),
        )));
    }
    // Recursive verification pairs plugins with the proof manifest by position.
    proof
        .non_primitives
        .iter()
        .filter_map(|entry| {
            provers
                .iter()
                .position(|prover| prover.op_type() == entry.op_type)
                .map(|index| provers.remove(index))
        })
        .collect()
}

// Restore per-query Merkle paths from the shared FRI multiproof using the
// same transcript and parameters as the proof's native verifier.
fn set_proof_fri_private_data(
    runner: &mut p3_circuit::CircuitRunner<'_, Challenge>,
    op_ids: &[p3_circuit::NonPrimitiveOpId],
    proof: &BatchStarkProof<GoldilocksConfig>,
    params: p3_recursion::FriVerifierParams,
) -> Result<(), String> {
    let config = crate::goldilocks_config_with_fri(
        params.log_blowup(),
        params.log_final_poly_len(),
        params.max_log_arity(),
        params.num_queries(),
        params.commit_pow_bits(),
        params.query_pow_bits(),
    );
    let OpeningTranscript {
        mut challenger,
        commitments_with_opening_points,
    } = replay_batch_layer_transcript::<GoldilocksConfig, 2>(
        &config,
        proof,
        &proof.stark_common,
        &base_table_provers(proof),
    )
    .map_err(|error| format!("replay FRI transcript: {error:?}"))?;
    let (mmcs, fri_params) = crate::goldilocks_fri_instance(
        params.log_blowup(),
        params.log_final_poly_len(),
        params.max_log_arity(),
        params.num_queries(),
        params.commit_pow_bits(),
        params.query_pow_bits(),
    );
    observe_opened_values::<GoldilocksConfig>(
        &mut challenger,
        &commitments_with_opening_points,
        fri_params.batch_proof_of_work_bits,
    );
    let claims: Vec<_> = commitments_with_opening_points
        .into_iter()
        .map(Into::into)
        .collect();
    let paths = restore_fri_query_paths(
        &fri_params,
        &mmcs,
        &mmcs,
        &proof.proof.opening_proof,
        &mut challenger,
        &claims,
    )
    .map_err(|error| format!("restore FRI paths: {error:?}"))?;
    set_fri_mmcs_private_data::<F, Challenge, 4>(
        runner,
        op_ids,
        &paths,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
    .map_err(str::to_string)
}

fn recursive_proof_size_breakdown(
    public_inputs: &[Challenge],
    proof: &BatchStarkProof<GoldilocksConfig>,
) -> Result<RecursiveProofSizeBreakdown, ProofError> {
    let public_inputs_bytes = serialized_len(public_inputs)?;
    let batch_stark_bytes = serialized_len(proof)?;
    let core_proof_bytes = serialized_len(&proof.proof)?;
    let commitments_bytes = serialized_len(&proof.proof.commitments)?;
    let opened_values_bytes = serialized_len(&proof.proof.opened_values)?;
    let opening_proof_bytes = serialized_len(&proof.proof.opening_proof)?;
    let global_lookup_data_bytes = serialized_len(&proof.proof.lookup_terminals)?;
    let degree_bits_bytes = serialized_len(&proof.proof.degree_bits)?;
    let primitive_public_values_bytes = 0;
    let non_primitives_bytes = serialized_len(&proof.non_primitives)?;
    let accounted_batch_bytes = core_proof_bytes
        .saturating_add(primitive_public_values_bytes)
        .saturating_add(non_primitives_bytes);
    let structural_metadata_bytes = batch_stark_bytes.saturating_sub(accounted_batch_bytes);

    Ok(RecursiveProofSizeBreakdown {
        public_inputs_bytes,
        batch_stark_bytes,
        core_proof_bytes,
        commitments_bytes,
        opened_values_bytes,
        opening_proof_bytes,
        global_lookup_data_bytes,
        degree_bits_bytes,
        primitive_public_values_bytes,
        non_primitives_bytes,
        structural_metadata_bytes,
    })
}

fn serialized_len<T: serde::Serialize + ?Sized>(value: &T) -> Result<usize, ProofError> {
    postcard::to_allocvec(value)
        .map(|bytes| bytes.len())
        .map_err(|error| ProofError::Serialization(format!("{error:?}")))
}

// Upstream's Public table supplies local execution witnesses; only the Statement
// table is exported by these recursive proofs. Child boundary values stay local.
fn execution_public_inputs(
    children: &[(&VerifierInputs, &BatchStarkProof<GoldilocksConfig>)],
    summary: &[F],
) -> Vec<Challenge> {
    let mut values = Vec::new();
    for (inputs, proof) in children {
        values.extend(inputs.pack_public_values(
            &table_public_inputs(proof),
            &proof.proof,
            &proof.stark_common,
        ));
    }
    append_summary_public_inputs(&mut values, summary);
    values
}

fn append_summary_public_inputs(inputs: &mut Vec<Challenge>, summary: &[F]) {
    inputs.extend(summary.iter().copied().map(Challenge::from));
}

fn summary_public_inputs(summary: &[F]) -> Vec<Challenge> {
    summary.iter().copied().map(Challenge::from).collect()
}

fn assert_public_ops_have_rows(circuit: &Circuit<Challenge>) -> Result<(), ProofError> {
    let missing = circuit
        .ops
        .iter()
        .filter_map(|op| match op {
            Op::Public { out, public_pos } if circuit.public_rows.get(*public_pos) != Some(out) => {
                Some(format!("{out:?}@{public_pos}"))
            }
            _ => None,
        })
        .take(4)
        .collect::<Vec<_>>();
    if missing.is_empty() {
        Ok(())
    } else {
        Err(ProofError::Plonky3(format!(
            "public op rows not mapped after lowering: {}",
            missing.join(", ")
        )))
    }
}

fn base_fri_verifier_params() -> p3_recursion::FriVerifierParams {
    p3_recursion::FriVerifierParams::with_mmcs(
        BASE_PROOF_FRI_LOG_BLOWUP,
        BASE_PROOF_FRI_LOG_FINAL_POLY_LEN,
        BASE_PROOF_FRI_MAX_LOG_ARITY,
        BASE_PROOF_FRI_COMMIT_POW_BITS,
        BASE_PROOF_FRI_QUERY_POW_BITS,
        BASE_PROOF_FRI_NUM_QUERIES,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
}

fn recursive_fri_verifier_params() -> p3_recursion::FriVerifierParams {
    p3_recursion::FriVerifierParams::with_mmcs(
        PROOF_FRI_LOG_BLOWUP,
        PROOF_FRI_LOG_FINAL_POLY_LEN,
        PROOF_FRI_MAX_LOG_ARITY,
        PROOF_FRI_COMMIT_POW_BITS,
        PROOF_FRI_QUERY_POW_BITS,
        PROOF_FRI_NUM_QUERIES,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
}

fn map_recursion_error(error: VerificationError) -> ProofError {
    ProofError::Plonky3(format!("{error:?}"))
}

fn statement_table_index(proof: &BatchStarkProof<GoldilocksConfig>) -> Result<usize, ProofError> {
    let indices: Vec<_> = proof
        .non_primitives
        .iter()
        .enumerate()
        .filter(|(_, entry)| entry.op_type == p3_circuit::ops::NpoTypeId::statement())
        .map(|(index, _)| NUM_PRIMITIVE_TABLES + index)
        .collect();
    if indices.len() != 1 {
        return Err(ProofError::StatementMismatch);
    }
    Ok(indices[0])
}

fn verify_bound_recursive_statement(
    proof: &BatchStarkProof<GoldilocksConfig>,
    inputs: &[Challenge],
) -> Result<(), ProofError> {
    use p3_field::BasedVectorSpace;
    let values = inputs
        .iter()
        .map(|value| {
            let coeffs = value.as_basis_coefficients_slice();
            if coeffs[1] != F::ZERO {
                return Err(ProofError::StatementMismatch);
            }
            Ok(coeffs[0])
        })
        .collect::<Result<Vec<_>, _>>()?;
    let index = statement_table_index(proof)? - NUM_PRIMITIVE_TABLES;
    if proof.non_primitives[index].public_values != values {
        return Err(ProofError::StatementMismatch);
    }
    let prover = recursive_verifier_prover(
        goldilocks_config(),
        proof.table_packing.clone(),
        values.len(),
    );
    prover
        .verify_all_tables::<Challenge>(proof)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[ignore = "recursive proof smoke is expensive"]
    fn proves_recursive_verifier_with_shared_fri_paths() {
        use tfheprus_circuits::PolyMulInstance;
        use tfheprus_core::Polynomial;

        let instance = PolyMulInstance::new(
            Polynomial::from_coeffs(vec![1u64.into(), 2u64.into(), 3u64.into(), 4u64.into()]),
            Polynomial::from_coeffs(vec![5u64.into(), 6u64.into(), 7u64.into(), 8u64.into()]),
        );
        let base = crate::prove_poly_mul(&instance).unwrap();
        let (circuit, inputs, op_ids) = build_verifier_circuit_with_leaf_summary(
            &base.proof,
            &base_goldilocks_config(),
            &base.public_inputs,
            0,
        )
        .unwrap();
        let (mut public, private) = inputs.pack_values(
            &table_public_inputs(&base.proof),
            &base.proof.proof,
            &base.proof.stark_common,
        );
        append_summary_public_inputs(&mut public, &base.public_inputs);
        let mut runner = circuit.runner();
        runner.set_public_inputs(&public).unwrap();
        runner.set_private_inputs(&private).unwrap();
        set_proof_fri_private_data(
            &mut runner,
            &op_ids,
            &base.proof,
            base_fri_verifier_params(),
        )
        .unwrap();
        let traces = runner.run().unwrap();

        let packing = proof_table_packing();
        let (airs_degrees, primitive_columns, non_primitive_columns) =
            get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 2>(
                &circuit,
                &packing,
                &recursive_verifier_preprocessors(&circuit),
                &recursive_verifier_air_builders(&circuit),
                ConstraintProfile::Standard,
            )
            .unwrap();
        let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
        let config = goldilocks_config();
        let data = ProverData::from_airs_and_degrees(&config, &airs, &degrees).unwrap();
        let data = CircuitProverData::new(data, primitive_columns, non_primitive_columns);
        let prover = recursive_verifier_prover(config, packing, base.public_inputs.len());
        let mut proof = prover.prove_all_tables(&traces, &data).unwrap();
        prover.verify_all_tables::<Challenge>(&proof).unwrap();

        let statement = summary_public_inputs(&base.public_inputs);
        verify_bound_recursive_statement(&proof, &statement).unwrap();
        let mut forged = statement.clone();
        forged[0] += Challenge::ONE;
        assert_eq!(
            verify_bound_recursive_statement(&proof, &forged),
            Err(ProofError::StatementMismatch)
        );

        // Changing both the sidecar and its manifest must still fail the STARK.
        let index = statement_table_index(&proof).unwrap() - NUM_PRIMITIVE_TABLES;
        proof.non_primitives[index].public_values[0] += F::ONE;
        assert!(verify_bound_recursive_statement(&proof, &forged).is_err());
        proof.non_primitives[index].public_values[0] -= F::ONE;
        verify_bound_recursive_statement(&proof, &statement).unwrap();

        // Summary fields are base-field values, including during native verification.
        use p3_field::BasedVectorSpace;
        forged = statement.clone();
        forged[0] += Challenge::from_basis_coefficients_slice(&[F::ZERO, F::ONE]).unwrap();
        assert_eq!(
            verify_bound_recursive_statement(&proof, &forged),
            Err(ProofError::StatementMismatch)
        );
        proof.non_primitives.remove(index);
        assert_eq!(
            verify_bound_recursive_statement(&proof, &statement),
            Err(ProofError::StatementMismatch)
        );
    }
}
