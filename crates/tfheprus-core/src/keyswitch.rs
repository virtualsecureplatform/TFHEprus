use rand::RngCore;

use crate::field::Goldilocks;
use crate::glev::{
    decompose_scalar, decomposition_gadget_factor, GlevCiphertext, GlevCiphertextNtt,
};
use crate::glwe::{GlweCiphertext, GlweSecretKey};
use crate::lwe::{LweCiphertext, LweSecretKey};
use crate::params::Params;
use crate::poly::Polynomial;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlweKeySwitchKey {
    pub rows: Vec<GlevCiphertext>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlweKeySwitchKeyNtt {
    pub rows: Vec<GlevCiphertextNtt>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LweKeySwitchKey {
    pub rows: Vec<Vec<LweCiphertext>>,
}

impl GlweKeySwitchKey {
    pub fn generate<R: RngCore + ?Sized>(
        params: &Params,
        source_key: &GlweSecretKey,
        target_key: &GlweSecretKey,
        rng: &mut R,
    ) -> Self {
        assert_eq!(source_key.dimension(), params.glwe_dimension);
        assert_eq!(source_key.polynomial_size(), params.polynomial_size);
        assert_eq!(target_key.polynomial_size(), params.polynomial_size);
        let rows = source_key
            .polys()
            .iter()
            .map(|poly| GlevCiphertext::encrypt(params, target_key, poly, rng))
            .collect();
        Self { rows }
    }

    pub fn generate_with_noise_bound<R: RngCore + ?Sized>(
        params: &Params,
        source_key: &GlweSecretKey,
        target_key: &GlweSecretKey,
        noise_bound: u64,
        rng: &mut R,
    ) -> Self {
        assert_eq!(source_key.dimension(), params.glwe_dimension);
        assert_eq!(source_key.polynomial_size(), params.polynomial_size);
        assert_eq!(target_key.polynomial_size(), params.polynomial_size);
        let rows = source_key
            .polys()
            .iter()
            .map(|poly| {
                GlevCiphertext::encrypt_with_noise_bound(params, target_key, poly, noise_bound, rng)
            })
            .collect();
        Self { rows }
    }

    pub fn to_ntt(&self) -> GlweKeySwitchKeyNtt {
        GlweKeySwitchKeyNtt {
            rows: self.rows.iter().map(GlevCiphertext::to_ntt).collect(),
        }
    }
}

impl LweKeySwitchKey {
    pub fn generate<R: RngCore + ?Sized>(
        params: &Params,
        source_key: &LweSecretKey,
        target_key: &LweSecretKey,
        rng: &mut R,
    ) -> Self {
        let rows = source_key
            .coeffs()
            .iter()
            .map(|&source_coeff| {
                (0..params.decomposition_level_count)
                    .map(|level_index| {
                        let gadget = decomposition_gadget_factor(params, level_index);
                        let encoded = source_coeff * gadget;
                        LweCiphertext::encrypt_encoded_with_params(params, target_key, encoded, rng)
                    })
                    .collect()
            })
            .collect();
        Self { rows }
    }

    pub fn generate_with_noise_bound<R: RngCore + ?Sized>(
        params: &Params,
        source_key: &LweSecretKey,
        target_key: &LweSecretKey,
        noise_bound: u64,
        rng: &mut R,
    ) -> Self {
        let rows = source_key
            .coeffs()
            .iter()
            .map(|&source_coeff| {
                (0..params.decomposition_level_count)
                    .map(|level_index| {
                        let gadget = decomposition_gadget_factor(params, level_index);
                        let encoded = source_coeff * gadget;
                        LweCiphertext::encrypt_encoded_with_noise_bound(
                            target_key,
                            encoded,
                            noise_bound,
                            rng,
                        )
                    })
                    .collect()
            })
            .collect();
        Self { rows }
    }

    pub fn target_dimension(&self) -> usize {
        self.rows
            .first()
            .and_then(|row| row.first())
            .map(|ct| ct.mask.len())
            .expect("LWE key switch key must contain at least one row")
    }
}

pub fn glwe_keyswitch(
    params: &Params,
    ksk: &GlweKeySwitchKey,
    input: &GlweCiphertext,
) -> GlweCiphertext {
    assert_eq!(ksk.rows.len(), input.mask.len());
    let target_dimension = ksk.rows[0].levels[0].mask.len();
    let mut output = GlweCiphertext::trivial(input.body.clone(), target_dimension);
    for (mask_poly, row) in input.mask.iter().zip(ksk.rows.iter()) {
        output = output.sub(&row.external_product_by_plain_poly(params, mask_poly));
    }
    output
}

pub fn glwe_keyswitch_ntt(
    params: &Params,
    ksk: &GlweKeySwitchKeyNtt,
    input: &GlweCiphertext,
) -> GlweCiphertext {
    assert_eq!(ksk.rows.len(), input.mask.len());
    let target_dimension = ksk.rows[0].levels[0].mask.len();
    let mut output = GlweCiphertext::trivial(input.body.clone(), target_dimension);
    for (mask_poly, row) in input.mask.iter().zip(ksk.rows.iter()) {
        output = output.sub(&row.external_product_by_plain_poly(params, mask_poly));
    }
    output
}

pub fn lwe_keyswitch(
    params: &Params,
    ksk: &LweKeySwitchKey,
    input: &LweCiphertext,
) -> LweCiphertext {
    assert_eq!(ksk.rows.len(), input.mask.len());
    let target_dimension = ksk.target_dimension();
    let mut output = LweCiphertext::trivial(target_dimension, input.body);
    for (mask_value, row) in input.mask.iter().zip(ksk.rows.iter()) {
        assert_eq!(row.len(), params.decomposition_level_count);
        let digits = decompose_scalar(params, *mask_value);
        for (digit, level_ct) in digits.iter().zip(row.iter()) {
            output = output.sub(&level_ct.scale(*digit));
        }
    }
    output
}

pub fn trivial_lwe_extraction_key(params: &Params, lwe_key: &LweSecretKey) -> GlweSecretKey {
    assert_eq!(params.glwe_dimension, 1);
    assert!(lwe_key.dimension() <= params.polynomial_size);

    let mut coeffs = vec![Goldilocks::ZERO; params.polynomial_size];
    for (index, &coeff) in lwe_key.coeffs().iter().enumerate() {
        if index == 0 {
            coeffs[0] = coeff;
        } else {
            coeffs[params.polynomial_size - index] = -coeff;
        }
    }
    GlweSecretKey::from_polys(vec![Polynomial::from_coeffs(coeffs)])
}

pub fn extract_trivial_lwe_prefix(input: &GlweCiphertext, dimension: usize) -> LweCiphertext {
    assert_eq!(input.mask.len(), 1);
    assert!(dimension <= input.body.len());
    LweCiphertext {
        mask: input.mask[0].coeffs()[..dimension].to_vec(),
        body: input.body[0],
    }
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    use super::*;
    use crate::{
        blind_rotate_ntt, bootstrap_without_keyswitch_ntt, encode_message, EvaluationKey,
        SecretKey, TestPolynomial, GOLDILOCKS_MODULUS,
    };

    #[test]
    fn trivial_lwe_extraction_key_matches_raw_mask_prefix() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(201);
        let lwe_key = LweSecretKey::generate_binary(params.lwe_dimension, &mut rng);
        let glwe_key = trivial_lwe_extraction_key(&params, &lwe_key);
        let message = Polynomial::constant(params.polynomial_size, encode_message(&params, 2));
        let mask = vec![Polynomial::random(params.polynomial_size, &mut rng)];
        let glwe = GlweCiphertext::encrypt_with_mask_and_default_noise(
            &params, &glwe_key, &message, mask, &mut rng,
        );
        let lwe = extract_trivial_lwe_prefix(&glwe, params.lwe_dimension);
        assert_eq!(lwe.decrypt(&params, &lwe_key), 2);
    }

    #[test]
    fn glwe_keyswitch_preserves_phase_under_trivial_extraction_key() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(202);
        let sk = SecretKey::generate(&params, &mut rng);
        let target_key = trivial_lwe_extraction_key(&params, &sk.input_lwe);
        let ksk = GlweKeySwitchKey::generate_with_noise_bound(
            &params,
            &sk.glwe,
            &target_key,
            0,
            &mut rng,
        );
        let message = Polynomial::from_coeffs(
            (0..params.polynomial_size)
                .map(|index| {
                    Goldilocks::from_u64(
                        ((index as u128 * GOLDILOCKS_MODULUS as u128) / 257) as u64,
                    )
                })
                .collect(),
        );
        let input =
            GlweCiphertext::encrypt_with_noise_bound(&params, &sk.glwe, &message, 0, &mut rng);
        let switched = glwe_keyswitch(&params, &ksk, &input);
        assert_eq!(switched.phase(&target_key), input.phase(&sk.glwe));
    }

    #[test]
    fn lwe_keyswitch_preserves_boolean_phase_under_target_key() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(204);
        let sk = SecretKey::generate(&params, &mut rng);
        let source_key = sk.extracted_output_lwe_key();
        let ksk = LweKeySwitchKey::generate_with_noise_bound(
            &params,
            &source_key,
            &sk.input_lwe,
            0,
            &mut rng,
        );
        for message in [false, true] {
            let input =
                LweCiphertext::encrypt_bool_with_noise_bound(&source_key, message, 0, &mut rng);
            let output = lwe_keyswitch(&params, &ksk, &input);
            assert_eq!(output.decrypt_bool(&sk.input_lwe), message);
        }
    }

    #[test]
    fn bootstrapping_glwe_keyswitch_outputs_under_input_lwe_key() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(203);
        let sk = SecretKey::generate(&params, &mut rng);
        let evaluation_key = EvaluationKey::generate(&params, &sk, &mut rng);
        let target_key = trivial_lwe_extraction_key(&params, &sk.input_lwe);
        let ksk = GlweKeySwitchKey::generate(&params, &sk.glwe, &target_key, &mut rng);
        let input_message = 1;
        let output_message = 3;
        let test_polynomial = TestPolynomial::single_slot(&params, input_message, output_message);
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
        let accumulator =
            blind_rotate_ntt(&params, &evaluation_key.to_ntt(), &input, &test_polynomial);
        let switched = glwe_keyswitch_ntt(&params, &ksk.to_ntt(), &accumulator);
        let output = extract_trivial_lwe_prefix(&switched, params.lwe_dimension);
        let without_keyswitch = bootstrap_without_keyswitch_ntt(
            &params,
            &evaluation_key.to_ntt(),
            &input,
            &test_polynomial,
        );
        assert_eq!(
            without_keyswitch.decrypt(&params, &sk.extracted_output_lwe_key()),
            output_message
        );
        assert_eq!(output.decrypt(&params, &sk.input_lwe), output_message);
    }
}
