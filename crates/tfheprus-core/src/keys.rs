use rand::RngCore;

use crate::field::Goldilocks;
use crate::ggsw::{GgswCiphertext, GgswCiphertextNtt};
use crate::glwe::GlweSecretKey;
use crate::lwe::LweSecretKey;
use crate::params::Params;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SecretKey {
    pub input_lwe: LweSecretKey,
    pub glwe: GlweSecretKey,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvaluationKey {
    pub bootstrapping_key: Vec<GgswCiphertext>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct EvaluationKeyNtt {
    pub bootstrapping_key: Vec<GgswCiphertextNtt>,
}

impl SecretKey {
    pub fn generate<R: RngCore + ?Sized>(params: &Params, rng: &mut R) -> Self {
        Self {
            input_lwe: LweSecretKey::generate_binary(params.lwe_dimension, rng),
            glwe: GlweSecretKey::generate_binary(params, rng),
        }
    }

    pub fn extracted_output_lwe_key(&self) -> LweSecretKey {
        self.glwe.extracted_lwe_secret_key()
    }
}

impl EvaluationKey {
    pub fn generate<R: RngCore + ?Sized>(params: &Params, sk: &SecretKey, rng: &mut R) -> Self {
        let bootstrapping_key = sk
            .input_lwe
            .coeffs()
            .iter()
            .map(|&bit| {
                debug_assert!(bit == Goldilocks::ZERO || bit == Goldilocks::ONE);
                GgswCiphertext::encrypt_constant(params, &sk.glwe, bit, rng)
            })
            .collect();
        Self { bootstrapping_key }
    }

    pub fn generate_with_noise_bound<R: RngCore + ?Sized>(
        params: &Params,
        sk: &SecretKey,
        noise_bound: u64,
        rng: &mut R,
    ) -> Self {
        let bootstrapping_key = sk
            .input_lwe
            .coeffs()
            .iter()
            .map(|&bit| {
                debug_assert!(bit == Goldilocks::ZERO || bit == Goldilocks::ONE);
                GgswCiphertext::encrypt_constant_with_noise_bound(
                    params,
                    &sk.glwe,
                    bit,
                    noise_bound,
                    rng,
                )
            })
            .collect();
        Self { bootstrapping_key }
    }

    pub fn bootstrapping_key_hash_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for ggsw in &self.bootstrapping_key {
            for row in &ggsw.rows {
                for level in &row.levels {
                    out.extend_from_slice(&level.to_le_bytes());
                }
            }
        }
        out
    }

    pub fn to_ntt(&self) -> EvaluationKeyNtt {
        EvaluationKeyNtt {
            bootstrapping_key: self
                .bootstrapping_key
                .iter()
                .map(GgswCiphertext::to_ntt)
                .collect(),
        }
    }
}
