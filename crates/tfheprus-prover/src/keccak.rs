use core::array;
use core::borrow::Borrow;

use p3_air::{Air, AirBuilder, BaseAir, WindowAccess};
use p3_field::{PrimeCharacteristicRing, PrimeField64};
use p3_goldilocks::Goldilocks as P3Goldilocks;
use p3_keccak_air::{generate_trace_rows, KeccakAir, KeccakCols, NUM_KECCAK_COLS, NUM_ROUNDS};
use p3_matrix::{dense::RowMajorMatrix, Matrix};
use p3_uni_stark::{prove, verify, Proof};

use crate::{base_goldilocks_config, GoldilocksConfig, ProofError, BASE_PROOF_FRI_LOG_BLOWUP};

const KECCAK_STATE_WORDS: usize = 25;
const KECCAK_U64_LIMBS: usize = 4;
const KECCAK_STATE_LIMBS: usize = KECCAK_STATE_WORDS * KECCAK_U64_LIMBS;
const KECCAK_PUBLIC_INPUTS: usize = 2 * KECCAK_STATE_LIMBS;
const KECCAK_MIN_DEGREE_BITS: usize = 5;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct KeccakF1600Statement {
    pub input_state: [u64; KECCAK_STATE_WORDS],
    pub output_state: [u64; KECCAK_STATE_WORDS],
}

impl KeccakF1600Statement {
    pub fn public_inputs(&self) -> Vec<P3Goldilocks> {
        let mut public_inputs = Vec::with_capacity(KECCAK_PUBLIC_INPUTS);
        public_inputs.extend(state_to_16_bit_limbs(self.input_state));
        public_inputs.extend(state_to_16_bit_limbs(self.output_state));
        public_inputs
    }
}

pub struct KeccakF1600Proof {
    pub statement: KeccakF1600Statement,
    pub public_inputs: Vec<P3Goldilocks>,
    pub proof: Proof<GoldilocksConfig>,
}

#[derive(Clone, Copy, Debug)]
struct PublicKeccakF1600Air;

impl<F> BaseAir<F> for PublicKeccakF1600Air {
    fn width(&self) -> usize {
        NUM_KECCAK_COLS
    }

    fn num_public_values(&self) -> usize {
        KECCAK_PUBLIC_INPUTS
    }
}

impl<AB: AirBuilder> Air<AB> for PublicKeccakF1600Air {
    fn eval(&self, builder: &mut AB) {
        KeccakAir {}.eval(builder);

        let main = builder.main();
        let local: &KeccakCols<AB::Var> = main.current_slice().borrow();
        debug_assert_eq!(builder.public_values().len(), KECCAK_PUBLIC_INPUTS);
        let public_input =
            array::from_fn::<_, KECCAK_STATE_LIMBS, _>(|index| builder.public_values()[index]);
        let public_output = array::from_fn::<_, KECCAK_STATE_LIMBS, _>(|index| {
            builder.public_values()[KECCAK_STATE_LIMBS + index]
        });

        builder
            .when_first_row()
            .assert_zeros::<KECCAK_STATE_LIMBS, _>(array::from_fn(|index| {
                input_state_limb(local, index).into() - public_input[index].into()
            }));

        let final_step = local.step_flags[NUM_ROUNDS - 1];
        builder
            .when(final_step)
            .assert_zeros::<KECCAK_STATE_LIMBS, _>(array::from_fn(|index| {
                output_state_limb(local, index).into() - public_output[index].into()
            }));
    }
}

pub fn prove_keccak_f1600(
    input_state: [u64; KECCAK_STATE_WORDS],
) -> Result<KeccakF1600Proof, ProofError> {
    let trace = generate_trace_rows::<P3Goldilocks>(vec![input_state], BASE_PROOF_FRI_LOG_BLOWUP);
    let output_state = extract_first_output_state(&trace)?;
    let statement = KeccakF1600Statement {
        input_state,
        output_state,
    };
    let public_inputs = statement.public_inputs();
    let config = base_goldilocks_config();
    let proof = prove(&config, &PublicKeccakF1600Air, trace, &public_inputs);

    Ok(KeccakF1600Proof {
        statement,
        public_inputs,
        proof,
    })
}

pub fn verify_keccak_f1600(proof: &KeccakF1600Proof) -> Result<(), ProofError> {
    if proof.proof.degree_bits < KECCAK_MIN_DEGREE_BITS {
        return Err(ProofError::StatementMismatch);
    }
    let expected_public_inputs = proof.statement.public_inputs();
    if proof.public_inputs != expected_public_inputs {
        return Err(ProofError::StatementMismatch);
    }
    let config = base_goldilocks_config();
    verify(
        &config,
        &PublicKeccakF1600Air,
        &proof.proof,
        &proof.public_inputs,
    )
    .map_err(|error| ProofError::Plonky3(format!("{error:?}")))
}

pub fn prove_and_verify_keccak_f1600(
    input_state: [u64; KECCAK_STATE_WORDS],
) -> Result<KeccakF1600Proof, ProofError> {
    let proof = prove_keccak_f1600(input_state)?;
    verify_keccak_f1600(&proof)?;
    Ok(proof)
}

fn state_to_16_bit_limbs(state: [u64; KECCAK_STATE_WORDS]) -> impl Iterator<Item = P3Goldilocks> {
    state.into_iter().flat_map(|word| {
        (0..KECCAK_U64_LIMBS)
            .map(move |limb| P3Goldilocks::from_u64((word >> (16 * limb)) & 0xffff))
    })
}

fn extract_first_output_state(
    trace: &RowMajorMatrix<P3Goldilocks>,
) -> Result<[u64; KECCAK_STATE_WORDS], ProofError> {
    if trace.width != NUM_KECCAK_COLS || trace.height() < NUM_ROUNDS {
        return Err(ProofError::StatementMismatch);
    }
    let (prefix, rows, suffix) = unsafe { trace.values.align_to::<KeccakCols<P3Goldilocks>>() };
    if !prefix.is_empty() || !suffix.is_empty() || rows.len() != trace.height() {
        return Err(ProofError::StatementMismatch);
    }

    let final_row = &rows[NUM_ROUNDS - 1];
    Ok(array::from_fn(|word_index| {
        let x = word_index % 5;
        let y = word_index / 5;
        (0..KECCAK_U64_LIMBS).fold(0u64, |acc, limb| {
            acc | (final_row.a_prime_prime_prime(y, x, limb).as_canonical_u64() << (16 * limb))
        })
    }))
}

fn input_state_limb<T: Copy>(row: &KeccakCols<T>, index: usize) -> T {
    let word_index = index / KECCAK_U64_LIMBS;
    let limb = index % KECCAK_U64_LIMBS;
    let x = word_index % 5;
    let y = word_index / 5;
    row.preimage[y][x][limb]
}

fn output_state_limb<T: Copy>(row: &KeccakCols<T>, index: usize) -> T {
    let word_index = index / KECCAK_U64_LIMBS;
    let limb = index % KECCAK_U64_LIMBS;
    let x = word_index % 5;
    let y = word_index / 5;
    row.a_prime_prime_prime(y, x, limb)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn proves_and_verifies_keccak_f1600_zero_state() {
        prove_and_verify_keccak_f1600([0; KECCAK_STATE_WORDS]).unwrap();
    }

    #[test]
    fn rejects_keccak_f1600_statement_mismatch() {
        let mut proof = prove_keccak_f1600([0; KECCAK_STATE_WORDS]).unwrap();
        proof.statement.output_state[0] ^= 1;

        assert_eq!(
            verify_keccak_f1600(&proof),
            Err(ProofError::StatementMismatch)
        );
    }

    #[test]
    fn rejects_keccak_f1600_trace_too_short_for_final_round() {
        let mut proof = prove_keccak_f1600([0; KECCAK_STATE_WORDS]).unwrap();
        proof.proof.degree_bits = KECCAK_MIN_DEGREE_BITS - 1;

        assert_eq!(
            verify_keccak_f1600(&proof),
            Err(ProofError::StatementMismatch)
        );
    }
}
