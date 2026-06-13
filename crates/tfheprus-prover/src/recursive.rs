use core::ops::Range;

use p3_batch_stark::ProverData;
use p3_circuit::ops::{
    generate_poseidon2_trace, generate_recompose_trace, GoldilocksD2Width8, Op, Poseidon2Config,
};

use p3_circuit::{Circuit, CircuitBuilder, ExprId};
use p3_circuit_prover::common::get_airs_and_degrees_with_prep;
use p3_circuit_prover::config::GoldilocksConfig;
use p3_circuit_prover::{
    poseidon2_air_builders, poseidon2_preprocessor, recompose_air_builders, recompose_preprocessor,
    recompose_table_provers, BatchStarkProof, BatchStarkProver, CircuitProverData,
    ConstraintProfile, Poseidon2ProverD2, PrimitiveTable, TablePacking, TableProver,
    NUM_PRIMITIVE_TABLES,
};
use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::{Goldilocks as P3Goldilocks, Poseidon2Goldilocks};
use p3_lookup::logup::LogUpGadget;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_recursion::pcs::{
    set_fri_mmcs_private_data, InputProofTargets, MerkleCapTargets, RecExtensionValMmcs, RecValMmcs,
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
    BASE_PROOF_FRI_LOG_BLOWUP, BASE_PROOF_FRI_LOG_FINAL_POLY_LEN, BASE_PROOF_FRI_QUERY_POW_BITS,
    PROOF_FRI_COMMIT_POW_BITS, PROOF_FRI_LOG_BLOWUP, PROOF_FRI_LOG_FINAL_POLY_LEN,
    PROOF_FRI_QUERY_POW_BITS,
};

type F = P3Goldilocks;
type Challenge = BinomialExtensionField<F, 2>;
type Perm = Poseidon2Goldilocks<8>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type MyMmcs = MerkleTreeMmcs<
    <F as p3_field::Field>::Packing,
    <F as p3_field::Field>::Packing,
    MyHash,
    MyCompress,
    2,
    4,
>;
type ChallengeMmcs = ExtensionMmcs<F, Challenge, MyMmcs>;
type InnerFri = p3_recursion::pcs::FriProofTargets<
    F,
    Challenge,
    RecExtensionValMmcs<F, Challenge, 4, RecValMmcs<F, 4, MyHash, MyCompress>>,
    InputProofTargets<F, Challenge, RecValMmcs<F, 4, MyHash, MyCompress>>,
    p3_recursion::pcs::Witness<F>,
>;
type VerifierInputs =
    BatchStarkVerifierInputsBuilder<GoldilocksConfig, MerkleCapTargets<F, 4>, InnerFri>;

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
    set_fri_mmcs_private_data::<F, Challenge, ChallengeMmcs, MyMmcs, MyHash, MyCompress, 4>(
        &mut runner,
        &mmcs_op_ids,
        &proof.proof.opening_proof,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
    .map_err(|error| ProofError::Plonky3(format!("set recursive FRI private data: {error}")))?;
    let traces = runner.run().map_err(|error| {
        ProofError::Plonky3(format!("run recursive verifier circuit: {error:?}"))
    })?;

    let preprocessors = vec![
        poseidon2_preprocessor::<F>(),
        recompose_preprocessor::<F>(false),
    ];
    let mut air_builders = poseidon2_air_builders::<GoldilocksConfig, 2>();
    air_builders.extend(recompose_air_builders::<GoldilocksConfig, 2>(1, false));
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
    let prover_data = ProverData::from_airs_and_degrees(&outer_config, &airs, &degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(outer_config, table_packing);
    let recursive_proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(RecursiveBatchProof {
        public_inputs,
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
    let public_inputs = summary_public_inputs(summary);
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
    set_fri_mmcs_private_data::<F, Challenge, ChallengeMmcs, MyMmcs, MyHash, MyCompress, 4>(
        &mut runner,
        &mmcs_op_ids,
        &proof.proof.opening_proof,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
    .map_err(|error| {
        ProofError::Plonky3(format!("set private recursive FRI private data: {error}"))
    })?;
    let traces = runner.run().map_err(|error| {
        ProofError::Plonky3(format!("run private recursive verifier circuit: {error:?}"))
    })?;

    let preprocessors = recursive_verifier_preprocessors();
    let air_builders = recursive_verifier_air_builders();
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
    let prover_data = ProverData::from_airs_and_degrees(&outer_config, &airs, &degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(outer_config, table_packing);
    let recursive_proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(RecursiveBatchProof {
        public_inputs,
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
    let public_inputs = summary_public_inputs(summary);
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
    set_fri_mmcs_private_data::<F, Challenge, ChallengeMmcs, MyMmcs, MyHash, MyCompress, 4>(
        &mut runner,
        &mmcs_op_ids,
        &proof.proof.opening_proof,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
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

    let preprocessors = recursive_verifier_preprocessors();
    let air_builders = recursive_verifier_air_builders();
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
    let prover_data = ProverData::from_airs_and_degrees(&outer_config, &airs, &degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(outer_config, table_packing);
    let recursive_proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(RecursiveBatchProof {
        public_inputs,
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
        let preprocessors = recursive_verifier_preprocessors();
        let air_builders = recursive_verifier_air_builders();
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
        let prover_data = ProverData::from_airs_and_degrees(&outer_config, &airs, &degrees);
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
        let public_inputs = summary_public_inputs(summary);
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
        set_fri_mmcs_private_data::<F, Challenge, ChallengeMmcs, MyMmcs, MyHash, MyCompress, 4>(
            &mut runner,
            &self.mmcs_op_ids,
            &proof.proof.opening_proof,
            Poseidon2Config::GOLDILOCKS_D2_W8,
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

        let prover = recursive_verifier_prover(goldilocks_config(), self.table_packing.clone());
        let recursive_proof = prover
            .prove_all_tables(&traces, &self.circuit_prover_data)
            .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

        Ok(RecursiveBatchProof {
            public_inputs,
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
        let preprocessors = recursive_verifier_preprocessors();
        let air_builders = recursive_verifier_air_builders();
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
        let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees);
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
        let public_inputs = summary_public_inputs(summary);
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
        set_fri_mmcs_private_data::<F, Challenge, ChallengeMmcs, MyMmcs, MyHash, MyCompress, 4>(
            &mut runner,
            &self.previous_mmcs_op_ids,
            &previous.proof.opening_proof,
            Poseidon2Config::GOLDILOCKS_D2_W8,
        )
        .map_err(|error| {
            ProofError::Plonky3(format!(
                "set cached previous compact append FRI private data: {error}"
            ))
        })?;
        set_fri_mmcs_private_data::<F, Challenge, ChallengeMmcs, MyMmcs, MyHash, MyCompress, 4>(
            &mut runner,
            &self.chunk_mmcs_op_ids,
            &chunk.proof.opening_proof,
            Poseidon2Config::GOLDILOCKS_D2_W8,
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

        let prover = recursive_verifier_prover(goldilocks_config(), self.table_packing.clone());
        let proof = prover
            .prove_all_tables(&traces, &self.circuit_prover_data)
            .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

        Ok(AggregatedRecursiveBatchProof {
            public_inputs,
            proof,
        })
    }
}

pub fn verify_recursive_batch(proof: &RecursiveBatchProof) -> Result<(), ProofError> {
    let _ = proof;
    Err(recursive_statement_binding_unsupported())
}

pub(crate) fn verify_recursive_batch_with_leaf_summary_for_base(
    base_proof: &BatchStarkProof<GoldilocksConfig>,
    summary: &[F],
    recursive_proof: &RecursiveBatchProof,
) -> Result<(), ProofError> {
    let mut expected_inputs = recursive_public_inputs_for_batch(base_proof)?;
    append_summary_public_inputs(&mut expected_inputs, summary);
    if recursive_proof.public_inputs != expected_inputs {
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
    set_fri_mmcs_private_data::<F, Challenge, ChallengeMmcs, MyMmcs, MyHash, MyCompress, 4>(
        &mut runner,
        &left_mmcs_op_ids,
        &left.proof.opening_proof,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
    .map_err(|error| {
        ProofError::Plonky3(format!("set left aggregate FRI private data: {error}"))
    })?;
    set_fri_mmcs_private_data::<F, Challenge, ChallengeMmcs, MyMmcs, MyHash, MyCompress, 4>(
        &mut runner,
        &right_mmcs_op_ids,
        &right.proof.opening_proof,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
    .map_err(|error| {
        ProofError::Plonky3(format!("set right aggregate FRI private data: {error}"))
    })?;
    let traces = runner.run().map_err(|error| {
        ProofError::Plonky3(format!("run aggregate verifier circuit: {error:?}"))
    })?;

    let preprocessors = recursive_verifier_preprocessors();
    let air_builders = recursive_verifier_air_builders();
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
    let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(config, table_packing);
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(AggregatedRecursiveBatchProof {
        public_inputs,
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
    let public_inputs = summary_public_inputs(summary);
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
    set_fri_mmcs_private_data::<F, Challenge, ChallengeMmcs, MyMmcs, MyHash, MyCompress, 4>(
        &mut runner,
        &left_mmcs_op_ids,
        &left.proof.opening_proof,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
    .map_err(|error| {
        ProofError::Plonky3(format!(
            "set left private aggregate FRI private data: {error}"
        ))
    })?;
    set_fri_mmcs_private_data::<F, Challenge, ChallengeMmcs, MyMmcs, MyHash, MyCompress, 4>(
        &mut runner,
        &right_mmcs_op_ids,
        &right.proof.opening_proof,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
    .map_err(|error| {
        ProofError::Plonky3(format!(
            "set right private aggregate FRI private data: {error}"
        ))
    })?;
    let traces = runner.run().map_err(|error| {
        ProofError::Plonky3(format!("run private aggregate verifier circuit: {error:?}"))
    })?;

    let preprocessors = recursive_verifier_preprocessors();
    let air_builders = recursive_verifier_air_builders();
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
    let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(config, table_packing);
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(AggregatedRecursiveBatchProof {
        public_inputs,
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
    let public_inputs = summary_public_inputs(final_summary);
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
    set_fri_mmcs_private_data::<F, Challenge, ChallengeMmcs, MyMmcs, MyHash, MyCompress, 4>(
        &mut runner,
        &root_mmcs_op_ids,
        &root.proof.opening_proof,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
    .map_err(|error| {
        ProofError::Plonky3(format!(
            "set compact root private aggregate FRI private data: {error}"
        ))
    })?;
    set_fri_mmcs_private_data::<F, Challenge, ChallengeMmcs, MyMmcs, MyHash, MyCompress, 4>(
        &mut runner,
        &key_mmcs_op_ids,
        &key_switch.proof.opening_proof,
        Poseidon2Config::GOLDILOCKS_D2_W8,
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

    let preprocessors = recursive_verifier_preprocessors();
    let air_builders = recursive_verifier_air_builders();
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
    let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(config, table_packing);
    let proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(AggregatedRecursiveBatchProof {
        public_inputs,
        proof,
    })
}

pub fn verify_aggregated_recursive_batch(
    proof: &AggregatedRecursiveBatchProof,
) -> Result<(), ProofError> {
    let _ = proof;
    Err(recursive_statement_binding_unsupported())
}

pub(crate) fn verify_aggregated_recursive_batch_with_public_summary(
    proof: &AggregatedRecursiveBatchProof,
    summary: &[F],
) -> Result<(), ProofError> {
    verify_public_summary_suffix(&proof.public_inputs, summary)?;
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
    let mut expected_inputs = aggregate_public_inputs_for_batches(left, right)?;
    append_summary_public_inputs(&mut expected_inputs, summary);
    if proof.public_inputs != expected_inputs {
        return Err(ProofError::StatementMismatch);
    }
    verify_aggregated_recursive_batch(proof)
}

fn build_verifier_circuit(
    proof: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
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
    let circuit = builder
        .build()
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok((circuit, verifier_inputs, mmcs_op_ids))
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
    let recursive_table_provers = recursive_batch_table_provers();
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

fn build_aggregation_verifier_circuit(
    left: &BatchStarkProof<GoldilocksConfig>,
    right: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
) -> Result<AggregationVerifierCircuit, ProofError> {
    let mut builder = CircuitBuilder::<Challenge>::new();
    enable_recursive_verifier_ops(&mut builder);

    let recursive_table_provers = recursive_batch_table_provers();
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
        &recursive_table_provers,
        &fri_params,
    )?;
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

fn build_aggregation_verifier_circuit_with_chain_summary(
    left: &BatchStarkProof<GoldilocksConfig>,
    right: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
    summary: &[F],
    layout: Option<&ChainSummaryLayout>,
) -> Result<AggregationVerifierCircuit, ProofError> {
    let mut builder = CircuitBuilder::<Challenge>::new();
    enable_recursive_verifier_ops(&mut builder);

    let recursive_table_provers = recursive_batch_table_provers();
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
        &recursive_table_provers,
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

    let recursive_table_provers = recursive_batch_table_provers();
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
        &recursive_table_provers,
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

    let recursive_table_provers = recursive_batch_table_provers();
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
        &recursive_table_provers,
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
    (0..len).map(|_| builder.public_input()).collect()
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
    _verifier_inputs: &VerifierInputs,
    proof: &BatchStarkProof<GoldilocksConfig>,
    summary_len: usize,
) -> Result<Vec<ExprId>, ProofError> {
    let _ = (proof, summary_len);
    Err(recursive_statement_binding_unsupported())
}

fn public_air_targets(verifier_inputs: &VerifierInputs) -> Result<&[ExprId], ProofError> {
    verifier_inputs
        .air_public_targets
        .get(PrimitiveTable::Public as usize)
        .map(Vec::as_slice)
        .ok_or(ProofError::StatementMismatch)
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
}

fn add_private_batch_verifier_to_builder_with_degree<const D: usize>(
    builder: &mut CircuitBuilder<Challenge>,
    proof: &BatchStarkProof<GoldilocksConfig>,
    config: &GoldilocksConfig,
    table_provers: &[Box<dyn TableProver<GoldilocksConfig>>],
    fri_params: &p3_recursion::FriVerifierParams,
) -> Result<(VerifierInputs, Vec<p3_circuit::NonPrimitiveOpId>), ProofError> {
    let _ = (builder, proof, config, table_provers, fri_params);
    Err(recursive_statement_binding_unsupported())
}

fn recursive_public_inputs_for_batch(
    proof: &BatchStarkProof<GoldilocksConfig>,
) -> Result<Vec<Challenge>, ProofError> {
    let config = base_goldilocks_config();
    let (_circuit, verifier_inputs, _mmcs_op_ids) = build_verifier_circuit(proof, &config)?;
    Ok(verifier_inputs.pack_public_values(
        &table_public_inputs(proof),
        &proof.proof,
        &proof.stark_common,
    ))
}

fn aggregate_public_inputs_for_batches(
    left: &BatchStarkProof<GoldilocksConfig>,
    right: &BatchStarkProof<GoldilocksConfig>,
) -> Result<Vec<Challenge>, ProofError> {
    let config = goldilocks_config();
    let (_circuit, left_inputs, right_inputs, _left_ids, _right_ids) =
        build_aggregation_verifier_circuit(left, right, &config)?;
    let mut public_inputs =
        left_inputs.pack_public_values(&table_public_inputs(left), &left.proof, &left.stark_common);
    public_inputs.extend(right_inputs.pack_public_values(
        &table_public_inputs(right),
        &right.proof,
        &right.stark_common,
    ));
    Ok(public_inputs)
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
) -> BatchStarkProver<GoldilocksConfig> {
    let mut prover = BatchStarkProver::new(config).with_table_packing(table_packing);
    prover.register_poseidon2_table::<2>(Poseidon2Config::GOLDILOCKS_D2_W8);
    prover.register_recompose_table::<2>(false);
    prover
}

fn recursive_verifier_preprocessors() -> Vec<Box<dyn p3_circuit_prover::common::NpoPreprocessor<F>>>
{
    vec![
        poseidon2_preprocessor::<F>(),
        recompose_preprocessor::<F>(false),
    ]
}

fn recursive_verifier_air_builders(
) -> Vec<Box<dyn p3_circuit_prover::common::NpoAirBuilder<GoldilocksConfig, 2>>> {
    let mut air_builders = poseidon2_air_builders::<GoldilocksConfig, 2>();
    air_builders.extend(recompose_air_builders::<GoldilocksConfig, 2>(1, false));
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

fn recursive_batch_table_provers() -> Vec<Box<dyn TableProver<GoldilocksConfig>>> {
    let mut provers: Vec<Box<dyn TableProver<GoldilocksConfig>>> =
        vec![Box::new(Poseidon2ProverD2::new(
            Poseidon2Config::GOLDILOCKS_D2_W8,
            ConstraintProfile::Standard,
        ))];
    provers.extend(recompose_table_provers::<GoldilocksConfig, 2>(1, false));
    provers
}

fn base_table_provers(
    proof: &BatchStarkProof<GoldilocksConfig>,
) -> Vec<Box<dyn TableProver<GoldilocksConfig>>> {
    let mut provers: Vec<Box<dyn TableProver<GoldilocksConfig>>> =
        vec![Box::new(Poseidon2ProverD2::new(
            Poseidon2Config::GOLDILOCKS_D2_W8,
            ConstraintProfile::Standard,
        ))];
    provers.extend(recompose_table_provers::<GoldilocksConfig, 2>(1, false));
    provers.extend(
        proof_range_check_bit_counts(proof)
            .into_iter()
            .map(|bit_count| {
                Box::new(RangeCheckProver::new(bit_count, RANGE_CHECK_DEFAULT_LANES))
                    as Box<dyn TableProver<GoldilocksConfig>>
            }),
    );
    provers
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
    let global_lookup_data_bytes = serialized_len(&proof.proof.global_lookup_data)?;
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

fn append_summary_public_inputs(inputs: &mut Vec<Challenge>, summary: &[F]) {
    inputs.extend(summary.iter().copied().map(Challenge::from));
}

fn summary_public_inputs(summary: &[F]) -> Vec<Challenge> {
    summary.iter().copied().map(Challenge::from).collect()
}

fn verify_public_summary_suffix(inputs: &[Challenge], summary: &[F]) -> Result<(), ProofError> {
    if inputs.len() < summary.len() {
        return Err(ProofError::StatementMismatch);
    }
    let start = inputs.len() - summary.len();
    if inputs[start..]
        .iter()
        .copied()
        .ne(summary.iter().copied().map(Challenge::from))
    {
        return Err(ProofError::StatementMismatch);
    }
    Ok(())
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
        BASE_PROOF_FRI_COMMIT_POW_BITS,
        BASE_PROOF_FRI_QUERY_POW_BITS,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
}

fn recursive_fri_verifier_params() -> p3_recursion::FriVerifierParams {
    p3_recursion::FriVerifierParams::with_mmcs(
        PROOF_FRI_LOG_BLOWUP,
        PROOF_FRI_LOG_FINAL_POLY_LEN,
        PROOF_FRI_COMMIT_POW_BITS,
        PROOF_FRI_QUERY_POW_BITS,
        Poseidon2Config::GOLDILOCKS_D2_W8,
    )
}

fn map_recursion_error(error: VerificationError) -> ProofError {
    ProofError::Plonky3(format!("{error:?}"))
}

fn recursive_statement_binding_unsupported() -> ProofError {
    ProofError::Plonky3(
        "recursive proof public-input binding needs a TFHEprus statement digest on public Plonky3 upstream"
            .into(),
    )
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn verifies_public_summary_suffix() {
        let summary = vec![F::from_u64(1), F::from_u64(2), F::from_u64(3)];
        let mut public_inputs = vec![
            Challenge::from(F::from_u64(9)),
            Challenge::from(F::from_u64(1)),
            Challenge::from(F::from_u64(2)),
            Challenge::from(F::from_u64(3)),
        ];

        verify_public_summary_suffix(&public_inputs, &summary).unwrap();

        public_inputs[2] = Challenge::from(F::from_u64(7));
        assert_eq!(
            verify_public_summary_suffix(&public_inputs, &summary),
            Err(ProofError::StatementMismatch)
        );
        assert_eq!(
            verify_public_summary_suffix(&public_inputs[..2], &summary),
            Err(ProofError::StatementMismatch)
        );
    }
}
