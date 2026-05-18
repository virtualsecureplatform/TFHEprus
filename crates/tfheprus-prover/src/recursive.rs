use p3_batch_stark::ProverData;
use p3_circuit::ops::{
    generate_poseidon2_trace, generate_recompose_trace, GoldilocksD2Width8, Poseidon2Config,
};
use p3_circuit::{Circuit, CircuitBuilder};
use p3_circuit_prover::common::get_airs_and_degrees_with_prep;
use p3_circuit_prover::config::GoldilocksConfig;
use p3_circuit_prover::{
    poseidon2_air_builders, poseidon2_preprocessor, recompose_air_builders, recompose_preprocessor,
    BatchStarkProof, BatchStarkProver, CircuitProverData, ConstraintProfile, PrimitiveTable,
    TablePacking, TableProver,
};
use p3_commit::ExtensionMmcs;
use p3_field::extension::BinomialExtensionField;
use p3_field::BasedVectorSpace;
use p3_goldilocks::{Goldilocks as P3Goldilocks, Poseidon2Goldilocks};
use p3_lookup::logup::LogUpGadget;
use p3_merkle_tree::MerkleTreeMmcs;
use p3_recursion::pcs::{
    set_fri_mmcs_private_data, InputProofTargets, MerkleCapTargets, RecExtensionValMmcs, RecValMmcs,
};
use p3_recursion::public_inputs::BatchStarkVerifierInputsBuilder;
use p3_recursion::verifier::{verify_p3_batch_proof_circuit, VerificationError};
use p3_symmetric::{PaddingFreeSponge, TruncatedPermutation};

use crate::range_check::{
    proof_range_check_bit_counts, RangeCheckProver, RANGE_CHECK_DEFAULT_LANES,
};
use crate::{goldilocks_config, goldilocks_poseidon2_8, ProofError};

type F = P3Goldilocks;
type Challenge = BinomialExtensionField<F, 2>;
type Perm = Poseidon2Goldilocks<8>;
type MyHash = PaddingFreeSponge<Perm, 8, 4, 4>;
type MyCompress = TruncatedPermutation<Perm, 2, 4, 8>;
type MyMmcs = MerkleTreeMmcs<F, F, MyHash, MyCompress, 2, 4>;
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

pub struct RecursiveBatchProof {
    public_inputs: Vec<Challenge>,
    proof: BatchStarkProof<GoldilocksConfig>,
}

impl RecursiveBatchProof {
    pub fn table_count(&self) -> usize {
        self.proof.proof.opened_values.instances.len()
    }

    pub fn public_input_count(&self) -> usize {
        self.public_inputs.len()
    }
}

pub fn prove_recursive_batch(
    proof: &BatchStarkProof<GoldilocksConfig>,
) -> Result<RecursiveBatchProof, ProofError> {
    let config = goldilocks_config();
    let table_packing = TablePacking::default();
    let table_public_inputs = table_public_inputs(proof);
    let (verification_circuit, verifier_inputs, mmcs_op_ids) =
        build_verifier_circuit(proof, &config)?;
    let (public_inputs, private_inputs) =
        verifier_inputs.pack_values(&table_public_inputs, &proof.proof, &proof.stark_common);
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
    let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees);
    let circuit_prover_data =
        CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

    let prover = recursive_verifier_prover(config, table_packing);
    let recursive_proof = prover
        .prove_all_tables(&traces, &circuit_prover_data)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok(RecursiveBatchProof {
        public_inputs,
        proof: recursive_proof,
    })
}

pub fn verify_recursive_batch(proof: &RecursiveBatchProof) -> Result<(), ProofError> {
    let expected_public_values = flatten_extension_values(&proof.public_inputs);
    if proof.proof.primitive_public_values[PrimitiveTable::Public as usize]
        != expected_public_values
    {
        return Err(ProofError::StatementMismatch);
    }

    let config = goldilocks_config();
    let prover = recursive_verifier_prover(config, proof.proof.table_packing.clone());
    prover
        .verify_all_tables(&proof.proof)
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))
}

pub fn verify_recursive_batch_for_base(
    base_proof: &BatchStarkProof<GoldilocksConfig>,
    recursive_proof: &RecursiveBatchProof,
) -> Result<(), ProofError> {
    let expected_inputs = recursive_public_inputs_for_batch(base_proof)?;
    if recursive_proof.public_inputs != expected_inputs {
        return Err(ProofError::StatementMismatch);
    }
    verify_recursive_batch(recursive_proof)
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
    builder.enable_poseidon2_perm_width_8::<GoldilocksD2Width8, _>(
        generate_poseidon2_trace::<Challenge, GoldilocksD2Width8>,
        goldilocks_poseidon2_8(),
    );
    builder.enable_recompose::<F>(generate_recompose_trace::<F, Challenge>);

    let base_table_provers = base_table_provers(proof);
    let lookup_gadget = LogUpGadget;
    let fri_params = fri_verifier_params();
    let (verifier_inputs, mmcs_op_ids) = verify_p3_batch_proof_circuit::<
        GoldilocksConfig,
        MerkleCapTargets<F, 4>,
        InputProofTargets<F, Challenge, RecValMmcs<F, 4, MyHash, MyCompress>>,
        InnerFri,
        LogUpGadget,
        Poseidon2Config,
        8,
        4,
        1,
    >(
        config,
        &mut builder,
        proof,
        &fri_params,
        &proof.stark_common,
        &lookup_gadget,
        Poseidon2Config::GOLDILOCKS_D2_W8,
        &base_table_provers,
    )
    .map_err(map_recursion_error)?;
    let circuit = builder
        .build()
        .map_err(|error| ProofError::Plonky3(format!("{error:?}")))?;

    Ok((circuit, verifier_inputs, mmcs_op_ids))
}

fn recursive_public_inputs_for_batch(
    proof: &BatchStarkProof<GoldilocksConfig>,
) -> Result<Vec<Challenge>, ProofError> {
    let config = goldilocks_config();
    let (_circuit, verifier_inputs, _mmcs_op_ids) = build_verifier_circuit(proof, &config)?;
    Ok(verifier_inputs.pack_public_values(
        &table_public_inputs(proof),
        &proof.proof,
        &proof.stark_common,
    ))
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

fn table_public_inputs(proof: &BatchStarkProof<GoldilocksConfig>) -> Vec<Vec<F>> {
    let mut inputs = proof.primitive_public_values.clone();
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
    proof_range_check_bit_counts(proof)
        .into_iter()
        .map(|bit_count| {
            Box::new(RangeCheckProver::new(bit_count, RANGE_CHECK_DEFAULT_LANES))
                as Box<dyn TableProver<GoldilocksConfig>>
        })
        .collect()
}

fn flatten_extension_values(values: &[Challenge]) -> Vec<F> {
    values
        .iter()
        .flat_map(|value| value.as_basis_coefficients_slice().iter().copied())
        .collect()
}

fn fri_verifier_params() -> p3_recursion::FriVerifierParams {
    p3_recursion::FriVerifierParams::with_mmcs(1, 0, 0, 16, Poseidon2Config::GOLDILOCKS_D2_W8)
}

fn map_recursion_error(error: VerificationError) -> ProofError {
    ProofError::Plonky3(format!("{error:?}"))
}
