use crate::field::Goldilocks;
#[cfg(test)]
use crate::field::GOLDILOCKS_MODULUS;
use crate::ggsw::{cmux, cmux_ntt};
use crate::glwe::{sample_extract_index_zero, GlweCiphertext};
use crate::keys::{EvaluationKey, EvaluationKeyNtt, GateEvaluationKey, GateEvaluationKeyNtt};
use crate::keyswitch::lwe_keyswitch;
use crate::lwe::{encode_bool, encode_message, LweCiphertext, BOOLEAN_MU};
use crate::params::Params;
use crate::poly::Polynomial;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TestPolynomial {
    pub poly: Polynomial,
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum HomGate {
    Nand,
    Nor,
    Xnor,
    And,
    Or,
    Xor,
    AndNotRight,
    AndNotLeft,
    OrNotRight,
    OrNotLeft,
}

impl TestPolynomial {
    /// Build a sparse test polynomial for one exact plaintext slot.
    ///
    /// This is the safest first test primitive because arbitrary LUTs must obey
    /// TFHE's negacyclic encoding constraints. The redundant LUT embedding from
    /// the paper will be added after the core blind-rotation semantics settle.
    pub fn single_slot(params: &Params, input_message: u64, output_message: u64) -> Self {
        let mut poly = Polynomial::zero(params.polynomial_size);
        let exponent = plaintext_exponent(params, input_message);
        let encoded = encode_message(params, output_message % params.plaintext_modulus);
        write_exponent_coefficient(&mut poly, exponent, encoded);
        Self { poly }
    }

    pub fn from_lut(params: &Params, lut: impl Fn(u64) -> u64) -> Self {
        let mut poly = Polynomial::zero(params.polynomial_size);
        for message in 0..params.plaintext_modulus {
            let exponent = plaintext_exponent(params, message);
            let encoded = encode_message(params, lut(message) % params.plaintext_modulus);
            write_exponent_coefficient(&mut poly, exponent, encoded);
        }
        Self { poly }
    }

    pub fn identity(params: &Params) -> Self {
        Self::from_lut(params, |message| message)
    }

    pub fn boolean_constant(params: &Params, message: bool) -> Self {
        Self {
            poly: Polynomial::from_coeffs(vec![encode_bool(message); params.polynomial_size]),
        }
    }

    pub fn to_le_bytes(&self) -> Vec<u8> {
        self.poly.to_le_bytes()
    }
}

impl HomGate {
    pub fn eval(self, lhs: bool, rhs: bool) -> bool {
        match self {
            Self::Nand => !(lhs & rhs),
            Self::Nor => !(lhs | rhs),
            Self::Xnor => lhs == rhs,
            Self::And => lhs & rhs,
            Self::Or => lhs | rhs,
            Self::Xor => lhs ^ rhs,
            Self::AndNotRight => lhs & !rhs,
            Self::AndNotLeft => !lhs & rhs,
            Self::OrNotRight => lhs | !rhs,
            Self::OrNotLeft => !lhs | rhs,
        }
    }

    fn affine_coefficients(self) -> (i64, i64, i64) {
        match self {
            Self::Nand => (-1, -1, 1),
            Self::Nor => (-1, -1, -1),
            Self::Xnor => (-2, -2, -2),
            Self::And => (1, 1, -1),
            Self::Or => (1, 1, 1),
            Self::Xor => (2, 2, 2),
            Self::AndNotRight => (1, -1, -1),
            Self::AndNotLeft => (-1, 1, -1),
            Self::OrNotRight => (1, -1, 1),
            Self::OrNotLeft => (-1, 1, 1),
        }
    }
}

pub fn bootstrap_without_keyswitch(
    params: &Params,
    ek: &EvaluationKey,
    input: &LweCiphertext,
    test_polynomial: &TestPolynomial,
) -> LweCiphertext {
    let acc = blind_rotate_with_key(params, &ek.bootstrapping_key, input, test_polynomial);
    sample_extract_index_zero(&acc)
}

pub fn bootstrap_without_keyswitch_ntt(
    params: &Params,
    ek: &EvaluationKeyNtt,
    input: &LweCiphertext,
    test_polynomial: &TestPolynomial,
) -> LweCiphertext {
    let acc = blind_rotate_ntt_with_key(params, &ek.bootstrapping_key, input, test_polynomial);
    sample_extract_index_zero(&acc)
}

pub fn bootstrap_with_keyswitch(
    params: &Params,
    ek: &GateEvaluationKey,
    input: &LweCiphertext,
    test_polynomial: &TestPolynomial,
) -> LweCiphertext {
    let acc = blind_rotate_with_key(params, &ek.bootstrapping_key, input, test_polynomial);
    let extracted = sample_extract_index_zero(&acc);
    lwe_keyswitch(params, &ek.key_switching_key, &extracted)
}

pub fn bootstrap_with_keyswitch_ntt(
    params: &Params,
    ek: &GateEvaluationKeyNtt,
    input: &LweCiphertext,
    test_polynomial: &TestPolynomial,
) -> LweCiphertext {
    let acc = blind_rotate_ntt_with_key(params, &ek.bootstrapping_key, input, test_polynomial);
    let extracted = sample_extract_index_zero(&acc);
    lwe_keyswitch(params, &ek.key_switching_key, &extracted)
}

pub fn bootstrap_boolean(
    params: &Params,
    ek: &GateEvaluationKey,
    input: &LweCiphertext,
) -> LweCiphertext {
    let test_polynomial = TestPolynomial::boolean_constant(params, true);
    bootstrap_with_keyswitch(params, ek, input, &test_polynomial)
}

pub fn bootstrap_boolean_ntt(
    params: &Params,
    ek: &GateEvaluationKeyNtt,
    input: &LweCiphertext,
) -> LweCiphertext {
    let test_polynomial = TestPolynomial::boolean_constant(params, true);
    bootstrap_with_keyswitch_ntt(params, ek, input, &test_polynomial)
}

pub fn hom_gate(
    params: &Params,
    ek: &GateEvaluationKey,
    gate: HomGate,
    lhs: &LweCiphertext,
    rhs: &LweCiphertext,
) -> LweCiphertext {
    let affine = hom_gate_affine_input(gate, lhs, rhs);
    bootstrap_boolean(params, ek, &affine)
}

pub fn hom_gate_ntt(
    params: &Params,
    ek: &GateEvaluationKeyNtt,
    gate: HomGate,
    lhs: &LweCiphertext,
    rhs: &LweCiphertext,
) -> LweCiphertext {
    let affine = hom_gate_affine_input(gate, lhs, rhs);
    bootstrap_boolean_ntt(params, ek, &affine)
}

pub fn hom_nand(
    params: &Params,
    ek: &GateEvaluationKey,
    lhs: &LweCiphertext,
    rhs: &LweCiphertext,
) -> LweCiphertext {
    hom_gate(params, ek, HomGate::Nand, lhs, rhs)
}

pub fn hom_nand_ntt(
    params: &Params,
    ek: &GateEvaluationKeyNtt,
    lhs: &LweCiphertext,
    rhs: &LweCiphertext,
) -> LweCiphertext {
    hom_gate_ntt(params, ek, HomGate::Nand, lhs, rhs)
}

pub fn blind_rotate(
    params: &Params,
    ek: &EvaluationKey,
    input: &LweCiphertext,
    test_polynomial: &TestPolynomial,
) -> GlweCiphertext {
    blind_rotate_with_key(params, &ek.bootstrapping_key, input, test_polynomial)
}

fn blind_rotate_with_key(
    params: &Params,
    bootstrapping_key: &[crate::ggsw::GgswCiphertext],
    input: &LweCiphertext,
    test_polynomial: &TestPolynomial,
) -> GlweCiphertext {
    assert_eq!(input.mask.len(), params.lwe_dimension);
    assert_eq!(bootstrapping_key.len(), params.lwe_dimension);
    let body_exponent = mod_switch_to_exponent(params, input.body);
    let initial_exponent = (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
    let mut acc = GlweCiphertext::trivial(
        test_polynomial.poly.mul_xai(initial_exponent),
        params.glwe_dimension,
    );
    for (mask_value, selector) in input.mask.iter().zip(bootstrapping_key.iter()) {
        let exponent = mod_switch_to_exponent(params, *mask_value);
        if exponent == 0 {
            continue;
        }
        let rotated = acc.mul_xai(exponent);
        acc = cmux(params, &acc, &rotated, selector);
    }
    acc
}

pub fn blind_rotate_ntt(
    params: &Params,
    ek: &EvaluationKeyNtt,
    input: &LweCiphertext,
    test_polynomial: &TestPolynomial,
) -> GlweCiphertext {
    blind_rotate_ntt_with_key(params, &ek.bootstrapping_key, input, test_polynomial)
}

fn blind_rotate_ntt_with_key(
    params: &Params,
    bootstrapping_key: &[crate::ggsw::GgswCiphertextNtt],
    input: &LweCiphertext,
    test_polynomial: &TestPolynomial,
) -> GlweCiphertext {
    assert_eq!(input.mask.len(), params.lwe_dimension);
    assert_eq!(bootstrapping_key.len(), params.lwe_dimension);
    let body_exponent = mod_switch_to_exponent(params, input.body);
    let initial_exponent = (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
    let mut acc = GlweCiphertext::trivial(
        test_polynomial.poly.mul_xai(initial_exponent),
        params.glwe_dimension,
    );
    for (mask_value, selector) in input.mask.iter().zip(bootstrapping_key.iter()) {
        let exponent = mod_switch_to_exponent(params, *mask_value);
        if exponent == 0 {
            continue;
        }
        let rotated = acc.mul_xai(exponent);
        acc = cmux_ntt(params, &acc, &rotated, selector);
    }
    acc
}

pub fn mod_switch_to_exponent(params: &Params, value: Goldilocks) -> usize {
    let modulus = params.exponent_modulus();
    assert!(modulus.is_power_of_two());
    let exponent_bits = modulus.trailing_zeros() as usize;
    let shift = 64 - exponent_bits;
    let rounded = (value.value() as u128 + (1u128 << (shift - 1))) >> shift;
    (rounded as usize) % modulus
}

fn hom_gate_affine_input(gate: HomGate, lhs: &LweCiphertext, rhs: &LweCiphertext) -> LweCiphertext {
    assert_eq!(lhs.mask.len(), rhs.mask.len());
    let (lhs_factor, rhs_factor, offset_factor) = gate.affine_coefficients();
    lhs.scale_signed(lhs_factor)
        .add(&rhs.scale_signed(rhs_factor))
        .add_plaintext(BOOLEAN_MU * Goldilocks::from_i64(offset_factor))
}

fn plaintext_exponent(params: &Params, message: u64) -> usize {
    let numerator = message as u128 * params.exponent_modulus() as u128;
    (numerator / params.plaintext_modulus as u128) as usize
}

fn write_exponent_coefficient(poly: &mut Polynomial, exponent: usize, value: Goldilocks) {
    let n = poly.len();
    let exponent = exponent % (2 * n);
    if exponent < n {
        poly[exponent] = value;
    } else {
        poly[exponent - n] = -value;
    }
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    use super::*;
    use crate::ggsw::{GgswCiphertext, GgswCiphertextNtt};
    use crate::keys::{EvaluationKey, GateEvaluationKey, GateEvaluationKeyNtt, SecretKey};
    use crate::keyswitch::LweKeySwitchKey;
    use crate::lwe::LweCiphertext;
    use crate::noise::sample_encryption_noise;

    #[test]
    fn mod_switch_rounds_against_power_of_two_torus() {
        for params in [
            Params::toy(),
            Params::moderate_toy(),
            Params::paper_v1(),
            Params::secure_128(),
        ] {
            let modulus = params.exponent_modulus();
            let step = GOLDILOCKS_MODULUS / modulus as u64;
            for exponent in 0..modulus {
                let value = Goldilocks::from_u64(step * exponent as u64);
                assert_eq!(mod_switch_to_exponent(&params, value), exponent);
            }
        }
    }

    #[test]
    fn nonzero_mask_bootstrap_applies_single_slot_test_polynomial() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(30);
        let sk = SecretKey::generate(&params, &mut rng);
        let ek = EvaluationKey::generate(&params, &sk, &mut rng);
        let input_message = 1;
        let output_message = 3;
        let test_poly = TestPolynomial::single_slot(&params, input_message, output_message);
        let mask_step = GOLDILOCKS_MODULUS / params.exponent_modulus() as u64;
        let mask = (0..params.lwe_dimension)
            .map(|index| Goldilocks::from_u64(mask_step * ((index as u64 % 15) + 1)))
            .collect();
        let input = LweCiphertext::encrypt_with_mask_and_default_noise(
            &params,
            &sk.input_lwe,
            input_message,
            mask,
            &mut rng,
        );
        let output = bootstrap_without_keyswitch(&params, &ek, &input, &test_poly);
        let output_ntt = bootstrap_without_keyswitch_ntt(&params, &ek.to_ntt(), &input, &test_poly);
        assert_eq!(output_ntt, output);
        assert_eq!(
            output.decrypt(&params, &sk.extracted_output_lwe_key()),
            output_message
        );
    }

    #[test]
    fn hom_nand_ntt_bootstraps_and_key_switches_to_input_key() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(31);
        let sk = SecretKey::generate(&params, &mut rng);
        let gate_key = GateEvaluationKey::generate_with_noise_bound(&params, &sk, 0, &mut rng);
        let gate_key_ntt = gate_key.to_ntt();

        for lhs_message in [false, true] {
            for rhs_message in [false, true] {
                let lhs = LweCiphertext::encrypt_bool_with_noise_bound(
                    &sk.input_lwe,
                    lhs_message,
                    0,
                    &mut rng,
                );
                let rhs = LweCiphertext::encrypt_bool_with_noise_bound(
                    &sk.input_lwe,
                    rhs_message,
                    0,
                    &mut rng,
                );
                let output = hom_nand_ntt(&params, &gate_key_ntt, &lhs, &rhs);
                assert_eq!(
                    output.decrypt_bool(&sk.input_lwe),
                    !(lhs_message & rhs_message)
                );
            }
        }
    }

    #[test]
    fn hom_gate_e2e_default_noise_all_boolean_gates() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(32);
        let sk = SecretKey::generate(&params, &mut rng);
        let gate_key = GateEvaluationKey::generate(&params, &sk, &mut rng);
        let gate_key_ntt = gate_key.to_ntt();
        let gates = [
            HomGate::Nand,
            HomGate::Nor,
            HomGate::Xnor,
            HomGate::And,
            HomGate::Or,
            HomGate::Xor,
            HomGate::AndNotRight,
            HomGate::AndNotLeft,
            HomGate::OrNotRight,
            HomGate::OrNotLeft,
        ];

        for gate in gates {
            for lhs_message in [false, true] {
                for rhs_message in [false, true] {
                    let lhs = LweCiphertext::encrypt_bool_with_params(
                        &params,
                        &sk.input_lwe,
                        lhs_message,
                        &mut rng,
                    );
                    let rhs = LweCiphertext::encrypt_bool_with_params(
                        &params,
                        &sk.input_lwe,
                        rhs_message,
                        &mut rng,
                    );
                    let expected = gate.eval(lhs_message, rhs_message);
                    let output = hom_gate(&params, &gate_key, gate, &lhs, &rhs);
                    let output_ntt = hom_gate_ntt(&params, &gate_key_ntt, gate, &lhs, &rhs);
                    assert_eq!(output.decrypt_bool(&sk.input_lwe), expected);
                    assert_eq!(output_ntt.decrypt_bool(&sk.input_lwe), expected);
                }
            }
        }
    }

    #[test]
    fn hom_gate_e2e_secure_128_parameter_sparse_rotation() {
        let params = Params::secure_128();
        let mut rng = ChaCha20Rng::seed_from_u64(33);
        let sk = SecretKey::generate(&params, &mut rng);
        let selected_index = sk
            .input_lwe
            .coeffs()
            .iter()
            .position(|&coeff| coeff == Goldilocks::ONE)
            .expect("secure test seed should contain a nonzero input-key coefficient");

        let mut bootstrapping_key =
            vec![GgswCiphertextNtt { rows: Vec::new() }; params.lwe_dimension];
        bootstrapping_key[selected_index] =
            GgswCiphertext::encrypt_constant(&params, &sk.glwe, Goldilocks::ONE, &mut rng).to_ntt();
        let key_switching_key = LweKeySwitchKey::generate(
            &params,
            &sk.extracted_output_lwe_key(),
            &sk.input_lwe,
            &mut rng,
        );
        let gate_key = GateEvaluationKeyNtt {
            bootstrapping_key,
            key_switching_key,
        };

        let mask_step = GOLDILOCKS_MODULUS / params.exponent_modulus() as u64;
        let sparse_mask_value = Goldilocks::from_u64(mask_step * 17);
        let lhs = secure_sparse_mask_boolean_ciphertext(
            &params,
            &sk,
            selected_index,
            sparse_mask_value,
            true,
            &mut rng,
        );
        let rhs = secure_sparse_mask_boolean_ciphertext(
            &params,
            &sk,
            selected_index,
            sparse_mask_value,
            true,
            &mut rng,
        );

        let output = hom_gate_ntt(&params, &gate_key, HomGate::Nand, &lhs, &rhs);
        assert!(!output.decrypt_bool(&sk.input_lwe));
    }

    fn secure_sparse_mask_boolean_ciphertext(
        params: &Params,
        sk: &SecretKey,
        selected_index: usize,
        selected_mask_value: Goldilocks,
        message: bool,
        rng: &mut ChaCha20Rng,
    ) -> LweCiphertext {
        let mut mask = vec![Goldilocks::ZERO; params.lwe_dimension];
        mask[selected_index] = selected_mask_value;
        let noise = sample_encryption_noise(params, rng);
        LweCiphertext::encrypt_encoded_with_mask_and_noise(
            &sk.input_lwe,
            encode_bool(message),
            mask,
            noise,
        )
    }
}
