use p3_circuit::{CircuitBuilder, CircuitBuilderError, ExprId};
use p3_field::extension::BinomialExtensionField;
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::{Goldilocks as P3Goldilocks, Poseidon2Goldilocks};
use p3_symmetric::{CryptographicHasher, PaddingFreeSponge};

use crate::goldilocks_poseidon2_8;

pub(crate) const POSEIDON2_DIGEST_WIDTH: usize = 4;
const POSEIDON2_RATE_BASE: usize = 4;

type Challenge = BinomialExtensionField<P3Goldilocks, 2>;
type Poseidon2Hash = PaddingFreeSponge<Poseidon2Goldilocks<8>, 8, 4, POSEIDON2_DIGEST_WIDTH>;

pub(crate) fn poseidon2_digest_fields(
    tag: u64,
    values: impl IntoIterator<Item = P3Goldilocks>,
) -> [P3Goldilocks; POSEIDON2_DIGEST_WIDTH] {
    let input = poseidon2_digest_input(tag, values);
    let hasher = Poseidon2Hash::new(goldilocks_poseidon2_8());
    hasher.hash_iter(input)
}

pub(crate) fn poseidon2_digest_targets_from_base_targets(
    builder: &mut CircuitBuilder<Challenge>,
    tag: u64,
    values: impl IntoIterator<Item = ExprId>,
) -> Result<[ExprId; POSEIDON2_DIGEST_WIDTH], CircuitBuilderError> {
    let values = values.into_iter().collect::<Vec<_>>();
    let mut input_targets = Vec::with_capacity(2 + values.len() + POSEIDON2_RATE_BASE);
    input_targets.push(builder.define_const(Challenge::from(P3Goldilocks::from_u64(tag))));
    input_targets
        .push(builder.define_const(Challenge::from(P3Goldilocks::from_u64(values.len() as u64))));
    input_targets.extend(values);
    while input_targets.len() % POSEIDON2_RATE_BASE != 0 {
        input_targets.push(builder.define_const(Challenge::from(P3Goldilocks::ZERO)));
    }

    let mut packed_inputs = Vec::with_capacity(input_targets.len() / 2);
    for chunk in input_targets.chunks_exact(2) {
        packed_inputs.push(builder.recompose_base_coeffs_to_ext_via_alu::<P3Goldilocks>(chunk)?);
    }

    let hash_outputs = builder.add_hash_slice(
        &p3_circuit::ops::Poseidon2Config::GOLDILOCKS_D2_W8,
        &packed_inputs,
        true,
    )?;
    let mut digest = Vec::with_capacity(POSEIDON2_DIGEST_WIDTH);
    for output in hash_outputs.into_iter().take(2) {
        digest.extend(builder.decompose_ext_to_base_coeffs::<P3Goldilocks>(output)?);
    }
    Ok(digest
        .try_into()
        .expect("Goldilocks D2 Poseidon2 digest exposes four base limbs"))
}

fn poseidon2_digest_input(
    tag: u64,
    values: impl IntoIterator<Item = P3Goldilocks>,
) -> Vec<P3Goldilocks> {
    let values = values.into_iter().collect::<Vec<_>>();
    let mut input = Vec::with_capacity(2 + values.len() + POSEIDON2_RATE_BASE);
    input.push(P3Goldilocks::from_u64(tag));
    input.push(P3Goldilocks::from_u64(values.len() as u64));
    input.extend(values);
    while input.len() % POSEIDON2_RATE_BASE != 0 {
        input.push(P3Goldilocks::ZERO);
    }
    input
}

#[cfg(test)]
mod tests {
    use p3_batch_stark::ProverData;
    use p3_circuit::ops::{generate_poseidon2_trace, generate_recompose_trace, GoldilocksD2Width8};
    use p3_circuit_prover::common::get_airs_and_degrees_with_prep;
    use p3_circuit_prover::config::GoldilocksConfig;
    use p3_circuit_prover::{
        poseidon2_air_builders, poseidon2_preprocessor, recompose_air_builders,
        recompose_preprocessor, BatchStarkProver, CircuitProverData, ConstraintProfile,
        TablePacking,
    };
    use p3_field::PrimeCharacteristicRing;

    use super::*;
    use crate::goldilocks_config;

    const TEST_TAG: u64 = 0x706f_7365_6964_6f6e;

    #[test]
    fn poseidon2_digest_targets_match_native_and_prove() {
        let values = [
            P3Goldilocks::from_u64(3),
            P3Goldilocks::from_u64(5),
            P3Goldilocks::from_u64(8),
            P3Goldilocks::from_u64(13),
            P3Goldilocks::from_u64(21),
        ];
        let expected = poseidon2_digest_fields(TEST_TAG, values);

        let mut builder = CircuitBuilder::<Challenge>::new();
        builder.enable_poseidon2_perm_width_8::<GoldilocksD2Width8, _>(
            generate_poseidon2_trace::<Challenge, GoldilocksD2Width8>,
            goldilocks_poseidon2_8(),
        );
        builder
            .enable_recompose::<P3Goldilocks>(generate_recompose_trace::<P3Goldilocks, Challenge>);

        let value_targets = (0..values.len())
            .map(|_| builder.public_input())
            .collect::<Vec<_>>();
        let digest_targets =
            poseidon2_digest_targets_from_base_targets(&mut builder, TEST_TAG, value_targets)
                .unwrap();
        let expected_targets = (0..POSEIDON2_DIGEST_WIDTH)
            .map(|_| builder.public_input())
            .collect::<Vec<_>>();
        for (actual, expected) in digest_targets.into_iter().zip(expected_targets) {
            builder.connect(actual, expected);
        }

        let circuit = builder.build().unwrap();
        let mut runner = circuit.runner();
        let mut public_inputs = values.into_iter().map(Challenge::from).collect::<Vec<_>>();
        public_inputs.extend(expected.into_iter().map(Challenge::from));
        runner.set_public_inputs(&public_inputs).unwrap();
        let traces = runner.run().unwrap();

        let table_packing = TablePacking::default();
        let preprocessors = vec![
            poseidon2_preprocessor::<P3Goldilocks>(),
            recompose_preprocessor::<P3Goldilocks>(false),
        ];
        let mut air_builders = poseidon2_air_builders::<GoldilocksConfig, 2>();
        air_builders.extend(recompose_air_builders::<GoldilocksConfig, 2>(1, false));
        let (airs_degrees, primitive_columns, non_primitive_columns) =
            get_airs_and_degrees_with_prep::<GoldilocksConfig, _, 2>(
                &circuit,
                &table_packing,
                &preprocessors,
                &air_builders,
                ConstraintProfile::Standard,
            )
            .unwrap();
        let (airs, degrees): (Vec<_>, Vec<_>) = airs_degrees.into_iter().unzip();
        let config = goldilocks_config();
        let prover_data = ProverData::from_airs_and_degrees(&config, &airs, &degrees);
        let circuit_prover_data =
            CircuitProverData::new(prover_data, primitive_columns, non_primitive_columns);

        let mut prover = BatchStarkProver::new(config).with_table_packing(table_packing);
        prover.register_poseidon2_table::<2>(p3_circuit::ops::Poseidon2Config::GOLDILOCKS_D2_W8);
        prover.register_recompose_table::<2>(false);
        let proof = prover
            .prove_all_tables(&traces, &circuit_prover_data)
            .unwrap();
        prover.verify_all_tables(&proof).unwrap();
    }
}
