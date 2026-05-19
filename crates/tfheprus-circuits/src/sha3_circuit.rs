use p3_circuit::{CircuitBuilder, CircuitError, ExprId};
use p3_field::PrimeCharacteristicRing;
use p3_goldilocks::Goldilocks as P3Goldilocks;
use tfheprus_core::SHA3_256_DOMAIN_PREFIX;

const SHA3_256_RATE_BYTES: usize = 136;
const KECCAK_ROUNDS: usize = 24;
const KECCAK_LANE_BITS: usize = 64;

const RHO_OFFSETS: [[usize; 5]; 5] = [
    [0, 36, 3, 41, 18],
    [1, 44, 10, 45, 2],
    [62, 6, 43, 15, 61],
    [28, 55, 25, 21, 56],
    [27, 20, 39, 8, 14],
];

const ROUND_CONSTANTS: [u64; KECCAK_ROUNDS] = [
    0x0000_0000_0000_0001,
    0x0000_0000_0000_8082,
    0x8000_0000_0000_808a,
    0x8000_0000_8000_8000,
    0x0000_0000_0000_808b,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8009,
    0x0000_0000_0000_008a,
    0x0000_0000_0000_0088,
    0x0000_0000_8000_8009,
    0x0000_0000_8000_000a,
    0x0000_0000_8000_808b,
    0x8000_0000_0000_008b,
    0x8000_0000_0000_8089,
    0x8000_0000_0000_8003,
    0x8000_0000_0000_8002,
    0x8000_0000_0000_0080,
    0x0000_0000_0000_800a,
    0x8000_0000_8000_000a,
    0x8000_0000_8000_8081,
    0x8000_0000_0000_8080,
    0x0000_0000_8000_0001,
    0x8000_0000_8000_8008,
];

pub fn sha3_256_bytes_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    input_bytes: &[ExprId],
) -> Result<[ExprId; 8], CircuitError> {
    let input_byte_bits = input_bytes
        .iter()
        .map(|&byte| byte_bits(builder, byte))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(sha3_256_byte_bits_expr(builder, &input_byte_bits))
}

pub fn sha3_256_field_elements_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    domain: &[u8],
    values: &[ExprId],
) -> Result<[ExprId; 8], CircuitError> {
    let mut bytes = domain_separated_prefix_bits(builder, domain);
    for &value in values {
        bytes.extend(field_element_le_bytes_bits(builder, value)?);
    }
    Ok(sha3_256_byte_bits_expr(builder, &bytes))
}

pub fn sha3_256_chain_update_fields_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    domain: &[u8],
    previous: &[ExprId; 8],
    values: &[ExprId],
) -> Result<[ExprId; 8], CircuitError> {
    let mut bytes = domain_separated_prefix_bits(builder, domain);
    bytes.extend(const_bytes_bits(builder, b"chain-update"));
    for &word in previous {
        bytes.extend(u32_limb_le_bytes_bits(builder, word)?);
    }
    for &value in values {
        bytes.extend(field_element_le_bytes_bits(builder, value)?);
    }
    Ok(sha3_256_byte_bits_expr(builder, &bytes))
}

fn sha3_256_byte_bits_expr(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    input_bytes: &[[ExprId; 8]],
) -> [ExprId; 8] {
    let zero = builder.define_const(P3Goldilocks::ZERO);
    let mut state = vec![vec![vec![zero; KECCAK_LANE_BITS]; 5]; 5];
    let padded = padded_sha3_256_blocks(builder, input_bytes);

    for block in padded.chunks(SHA3_256_RATE_BYTES) {
        for (byte_index, byte_bits) in block.iter().enumerate() {
            let lane_index = byte_index / 8;
            let lane_byte = byte_index % 8;
            let x = lane_index % 5;
            let y = lane_index / 5;
            for (bit_index, &bit) in byte_bits.iter().enumerate() {
                let lane_bit = lane_byte * 8 + bit_index;
                state[x][y][lane_bit] = xor_bit(builder, state[x][y][lane_bit], bit);
            }
        }
        keccak_f1600(builder, &mut state);
    }

    let mut output_bytes = Vec::with_capacity(32);
    for byte_index in 0..32 {
        let lane_index = byte_index / 8;
        let lane_byte = byte_index % 8;
        let x = lane_index % 5;
        let y = lane_index / 5;
        output_bytes.push(state[x][y][lane_byte * 8..lane_byte * 8 + 8].to_vec());
    }

    core::array::from_fn(|word_index| {
        let mut bits = Vec::with_capacity(32);
        for byte_bits in &output_bytes[word_index * 4..word_index * 4 + 4] {
            bits.extend_from_slice(byte_bits);
        }
        pack_bits_le(builder, &bits)
    })
}

fn padded_sha3_256_blocks(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    input_bytes: &[[ExprId; 8]],
) -> Vec<[ExprId; 8]> {
    let mut bytes = input_bytes.to_vec();
    bytes.push(const_byte_bits(builder, 0x06));
    while bytes.len() % SHA3_256_RATE_BYTES != SHA3_256_RATE_BYTES - 1 {
        bytes.push(const_byte_bits(builder, 0));
    }
    bytes.push(const_byte_bits(builder, 0x80));
    bytes
}

fn keccak_f1600(builder: &mut CircuitBuilder<P3Goldilocks>, state: &mut [Vec<Vec<ExprId>>]) {
    for &round_constant in &ROUND_CONSTANTS {
        let mut c = vec![vec![ExprId::ZERO; KECCAK_LANE_BITS]; 5];
        for x in 0..5 {
            c[x] = xor_lanes(
                builder,
                &[
                    state[x][0].clone(),
                    state[x][1].clone(),
                    state[x][2].clone(),
                    state[x][3].clone(),
                    state[x][4].clone(),
                ],
            );
        }

        let mut d = vec![vec![ExprId::ZERO; KECCAK_LANE_BITS]; 5];
        for x in 0..5 {
            d[x] = xor_lane(builder, &c[(x + 4) % 5], &rotate_lane(&c[(x + 1) % 5], 1));
        }

        for x in 0..5 {
            for y in 0..5 {
                state[x][y] = xor_lane(builder, &state[x][y], &d[x]);
            }
        }

        let mut b = vec![vec![vec![ExprId::ZERO; KECCAK_LANE_BITS]; 5]; 5];
        for x in 0..5 {
            for y in 0..5 {
                b[y][(2 * x + 3 * y) % 5] = rotate_lane(&state[x][y], RHO_OFFSETS[x][y]);
            }
        }

        for x in 0..5 {
            for y in 0..5 {
                let not_next = not_lane(builder, &b[(x + 1) % 5][y]);
                let and_term = and_lane(builder, &not_next, &b[(x + 2) % 5][y]);
                state[x][y] = xor_lane(builder, &b[x][y], &and_term);
            }
        }

        let round_bits = const_u64_bits(builder, round_constant);
        state[0][0] = xor_lane(builder, &state[0][0], &round_bits);
    }
}

fn byte_bits(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    byte: ExprId,
) -> Result<[ExprId; 8], CircuitError> {
    let bits = builder.decompose_to_bits::<P3Goldilocks>(byte, 8)?;
    Ok(core::array::from_fn(|index| bits[index]))
}

fn field_element_le_bytes_bits(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    value: ExprId,
) -> Result<Vec<[ExprId; 8]>, CircuitError> {
    let bits = builder.decompose_to_bits::<P3Goldilocks>(value, 64)?;
    Ok(bits_to_le_bytes(&bits))
}

fn u32_limb_le_bytes_bits(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    value: ExprId,
) -> Result<Vec<[ExprId; 8]>, CircuitError> {
    let bits = builder.decompose_to_bits::<P3Goldilocks>(value, 32)?;
    Ok(bits_to_le_bytes(&bits))
}

fn bits_to_le_bytes(bits: &[ExprId]) -> Vec<[ExprId; 8]> {
    bits.chunks_exact(8)
        .map(|chunk| core::array::from_fn(|index| chunk[index]))
        .collect()
}

fn domain_separated_prefix_bits(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    domain: &[u8],
) -> Vec<[ExprId; 8]> {
    let mut bytes = const_bytes_bits(builder, SHA3_256_DOMAIN_PREFIX);
    bytes.extend(const_u32_le_bytes_bits(builder, domain.len() as u32));
    bytes.extend(const_bytes_bits(builder, domain));
    bytes
}

fn const_bytes_bits(builder: &mut CircuitBuilder<P3Goldilocks>, bytes: &[u8]) -> Vec<[ExprId; 8]> {
    bytes
        .iter()
        .map(|&byte| const_byte_bits(builder, byte))
        .collect()
}

fn const_u32_le_bytes_bits(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    value: u32,
) -> Vec<[ExprId; 8]> {
    value
        .to_le_bytes()
        .into_iter()
        .map(|byte| const_byte_bits(builder, byte))
        .collect()
}

fn const_byte_bits(builder: &mut CircuitBuilder<P3Goldilocks>, byte: u8) -> [ExprId; 8] {
    core::array::from_fn(|index| {
        builder.define_const(P3Goldilocks::from_u64(((byte >> index) & 1) as u64))
    })
}

fn const_u64_bits(builder: &mut CircuitBuilder<P3Goldilocks>, value: u64) -> Vec<ExprId> {
    (0..KECCAK_LANE_BITS)
        .map(|index| builder.define_const(P3Goldilocks::from_u64((value >> index) & 1)))
        .collect()
}

fn rotate_lane(lane: &[ExprId], offset: usize) -> Vec<ExprId> {
    (0..KECCAK_LANE_BITS)
        .map(|index| {
            lane[(index + KECCAK_LANE_BITS - (offset % KECCAK_LANE_BITS)) % KECCAK_LANE_BITS]
        })
        .collect()
}

fn xor_lanes(builder: &mut CircuitBuilder<P3Goldilocks>, lanes: &[Vec<ExprId>; 5]) -> Vec<ExprId> {
    let mut out = lanes[0].clone();
    for lane in &lanes[1..] {
        out = xor_lane(builder, &out, lane);
    }
    out
}

fn xor_lane(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    lhs: &[ExprId],
    rhs: &[ExprId],
) -> Vec<ExprId> {
    lhs.iter()
        .zip(rhs)
        .map(|(&a, &b)| xor_bit(builder, a, b))
        .collect()
}

fn and_lane(
    builder: &mut CircuitBuilder<P3Goldilocks>,
    lhs: &[ExprId],
    rhs: &[ExprId],
) -> Vec<ExprId> {
    lhs.iter()
        .zip(rhs)
        .map(|(&a, &b)| builder.mul(a, b))
        .collect()
}

fn not_lane(builder: &mut CircuitBuilder<P3Goldilocks>, lane: &[ExprId]) -> Vec<ExprId> {
    let one = builder.define_const(P3Goldilocks::ONE);
    lane.iter().map(|&bit| builder.sub(one, bit)).collect()
}

fn xor_bit(builder: &mut CircuitBuilder<P3Goldilocks>, lhs: ExprId, rhs: ExprId) -> ExprId {
    let sum = builder.add(lhs, rhs);
    let product = builder.mul(lhs, rhs);
    let two_product = builder.add(product, product);
    builder.sub(sum, two_product)
}

fn pack_bits_le(builder: &mut CircuitBuilder<P3Goldilocks>, bits: &[ExprId]) -> ExprId {
    bits.iter().enumerate().fold(
        builder.define_const(P3Goldilocks::ZERO),
        |acc, (index, &bit)| {
            let coeff = builder.define_const(P3Goldilocks::from_u64(1u64 << index));
            let term = builder.mul(bit, coeff);
            builder.add(acc, term)
        },
    )
}

#[cfg(test)]
mod tests {
    use p3_circuit::CircuitBuilder;
    use p3_field::PrimeCharacteristicRing;
    use tfheprus_core::{
        raw_sha3_256, sha3_256_chain_initial, sha3_256_chain_update_fields,
        sha3_256_field_elements, Goldilocks,
    };

    use super::*;

    #[test]
    fn sha3_256_empty_message_matches_test_vector() {
        run_sha3_256_case(b"");
    }

    #[test]
    fn sha3_256_short_message_matches_reference() {
        run_sha3_256_case(b"abc");
    }

    #[test]
    fn sha3_256_field_elements_match_native_commitment() {
        let domain = b"field-test";
        let values = [Goldilocks::from_u64(1), Goldilocks::from_u64(2)];
        let mut builder = CircuitBuilder::<P3Goldilocks>::new();
        let value_targets = builder.alloc_public_inputs(values.len(), "sha3_field_value");
        let digest_words = sha3_256_field_elements_expr(&mut builder, domain, &value_targets)
            .expect("field digest circuit builds");
        let expected_words = builder.alloc_public_inputs(8, "sha3_expected_word");
        for (&computed, &expected) in digest_words.iter().zip(&expected_words) {
            builder.connect(computed, expected);
        }
        let circuit = builder.build().unwrap();
        let mut public_inputs = values
            .iter()
            .map(|value| P3Goldilocks::from_u64(value.value()))
            .collect::<Vec<_>>();
        public_inputs.extend(
            sha3_256_field_elements(domain, values)
                .to_field_elements()
                .into_iter()
                .map(|value| P3Goldilocks::from_u64(value.value())),
        );
        let mut runner = circuit.runner();
        runner.set_public_inputs(&public_inputs).unwrap();
        runner.run().unwrap();
    }

    #[test]
    fn sha3_256_chain_update_fields_match_native_commitment() {
        let domain = b"chain-test";
        let previous = sha3_256_chain_initial(domain);
        let values = [Goldilocks::from_u64(7), Goldilocks::from_u64(9)];

        let mut builder = CircuitBuilder::<P3Goldilocks>::new();
        let previous_targets = builder.alloc_public_input_array::<8>("sha3_previous_word");
        let value_targets = builder.alloc_public_inputs(values.len(), "sha3_chain_value");
        let digest_words = sha3_256_chain_update_fields_expr(
            &mut builder,
            domain,
            &previous_targets,
            &value_targets,
        )
        .expect("chain update circuit builds");
        let expected_words = builder.alloc_public_inputs(8, "sha3_expected_word");
        for (&computed, &expected) in digest_words.iter().zip(&expected_words) {
            builder.connect(computed, expected);
        }
        let circuit = builder.build().unwrap();
        let mut public_inputs = previous
            .iter()
            .chain(values.iter())
            .map(|value| P3Goldilocks::from_u64(value.value()))
            .collect::<Vec<_>>();
        public_inputs.extend(
            sha3_256_chain_update_fields(domain, &previous, values)
                .into_iter()
                .map(|value| P3Goldilocks::from_u64(value.value())),
        );
        let mut runner = circuit.runner();
        runner.set_public_inputs(&public_inputs).unwrap();
        runner.run().unwrap();
    }

    fn run_sha3_256_case(message: &[u8]) {
        let mut builder = CircuitBuilder::<P3Goldilocks>::new();
        let input_bytes = builder.alloc_public_inputs(message.len(), "sha3_input_byte");
        let digest_words = sha3_256_bytes_expr(&mut builder, &input_bytes).unwrap();
        let expected_words = builder.alloc_public_inputs(8, "sha3_expected_word");
        for (&computed, &expected) in digest_words.iter().zip(&expected_words) {
            builder.connect(computed, expected);
        }
        let circuit = builder.build().unwrap();
        let mut public_inputs = message
            .iter()
            .copied()
            .map(|byte| P3Goldilocks::from_u64(byte as u64))
            .collect::<Vec<_>>();
        public_inputs.extend(
            digest_u32_words(raw_sha3_256(message))
                .into_iter()
                .map(|word| P3Goldilocks::from_u64(word as u64)),
        );
        let mut runner = circuit.runner();
        runner.set_public_inputs(&public_inputs).unwrap();
        runner.run().unwrap();
    }

    fn digest_u32_words(bytes: [u8; 32]) -> [u32; 8] {
        core::array::from_fn(|index| {
            let offset = 4 * index;
            u32::from_le_bytes([
                bytes[offset],
                bytes[offset + 1],
                bytes[offset + 2],
                bytes[offset + 3],
            ])
        })
    }
}
