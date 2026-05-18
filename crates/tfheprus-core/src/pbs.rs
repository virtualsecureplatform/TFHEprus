use crate::field::{Goldilocks, GOLDILOCKS_MODULUS};
use crate::ggsw::{cmux, cmux_ntt};
use crate::glwe::{sample_extract_index_zero, GlweCiphertext};
use crate::keys::{EvaluationKey, EvaluationKeyNtt};
use crate::lwe::{encode_message, LweCiphertext};
use crate::params::Params;
use crate::poly::Polynomial;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct TestPolynomial {
    pub poly: Polynomial,
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

    pub fn to_le_bytes(&self) -> Vec<u8> {
        self.poly.to_le_bytes()
    }
}

pub fn bootstrap_without_keyswitch(
    params: &Params,
    ek: &EvaluationKey,
    input: &LweCiphertext,
    test_polynomial: &TestPolynomial,
) -> LweCiphertext {
    let acc = blind_rotate(params, ek, input, test_polynomial);
    sample_extract_index_zero(&acc)
}

pub fn bootstrap_without_keyswitch_ntt(
    params: &Params,
    ek: &EvaluationKeyNtt,
    input: &LweCiphertext,
    test_polynomial: &TestPolynomial,
) -> LweCiphertext {
    let acc = blind_rotate_ntt(params, ek, input, test_polynomial);
    sample_extract_index_zero(&acc)
}

pub fn blind_rotate(
    params: &Params,
    ek: &EvaluationKey,
    input: &LweCiphertext,
    test_polynomial: &TestPolynomial,
) -> GlweCiphertext {
    assert_eq!(input.mask.len(), params.lwe_dimension);
    assert_eq!(ek.bootstrapping_key.len(), params.lwe_dimension);
    let body_exponent = mod_switch_to_exponent(params, input.body);
    let initial_exponent = (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
    let mut acc = GlweCiphertext::trivial(
        test_polynomial.poly.mul_xai(initial_exponent),
        params.glwe_dimension,
    );
    for (mask_value, selector) in input.mask.iter().zip(ek.bootstrapping_key.iter()) {
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
    assert_eq!(input.mask.len(), params.lwe_dimension);
    assert_eq!(ek.bootstrapping_key.len(), params.lwe_dimension);
    let body_exponent = mod_switch_to_exponent(params, input.body);
    let initial_exponent = (params.exponent_modulus() - body_exponent) % params.exponent_modulus();
    let mut acc = GlweCiphertext::trivial(
        test_polynomial.poly.mul_xai(initial_exponent),
        params.glwe_dimension,
    );
    for (mask_value, selector) in input.mask.iter().zip(ek.bootstrapping_key.iter()) {
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
    let numerator = value.value() as u128 * params.exponent_modulus() as u128;
    let rounded = (numerator + (GOLDILOCKS_MODULUS as u128 / 2)) / GOLDILOCKS_MODULUS as u128;
    (rounded as usize) % params.exponent_modulus()
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
    use crate::keys::{EvaluationKey, SecretKey};
    use crate::lwe::LweCiphertext;

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
        let input = LweCiphertext::encrypt_with_mask(&params, &sk.input_lwe, input_message, mask);
        let output = bootstrap_without_keyswitch(&params, &ek, &input, &test_poly);
        let output_ntt = bootstrap_without_keyswitch_ntt(&params, &ek.to_ntt(), &input, &test_poly);
        assert_eq!(output_ntt, output);
        assert_eq!(
            output.decrypt(&params, &sk.extracted_output_lwe_key()),
            output_message
        );
    }
}
