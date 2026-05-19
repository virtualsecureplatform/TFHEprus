use rand::RngCore;

use crate::field::{Goldilocks, GOLDILOCKS_MODULUS};
use crate::noise::{sample_uniform_bounded_noise, DEFAULT_ENCRYPTION_NOISE_BOUND};
use crate::params::Params;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LweSecretKey {
    coeffs: Vec<Goldilocks>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct LweCiphertext {
    pub mask: Vec<Goldilocks>,
    pub body: Goldilocks,
}

impl LweSecretKey {
    pub fn generate_binary<R: RngCore + ?Sized>(dimension: usize, rng: &mut R) -> Self {
        let coeffs = (0..dimension)
            .map(|_| Goldilocks::from_u64((rng.next_u32() & 1) as u64))
            .collect();
        Self { coeffs }
    }

    pub fn from_coeffs(coeffs: Vec<Goldilocks>) -> Self {
        assert!(!coeffs.is_empty());
        Self { coeffs }
    }

    pub fn coeffs(&self) -> &[Goldilocks] {
        &self.coeffs
    }

    pub fn dimension(&self) -> usize {
        self.coeffs.len()
    }
}

impl LweCiphertext {
    pub fn encrypt<R: RngCore + ?Sized>(
        params: &Params,
        sk: &LweSecretKey,
        message: u64,
        rng: &mut R,
    ) -> Self {
        Self::encrypt_with_noise_bound(params, sk, message, DEFAULT_ENCRYPTION_NOISE_BOUND, rng)
    }

    pub fn encrypt_with_noise_bound<R: RngCore + ?Sized>(
        params: &Params,
        sk: &LweSecretKey,
        message: u64,
        noise_bound: u64,
        rng: &mut R,
    ) -> Self {
        let mask = (0..sk.dimension())
            .map(|_| Goldilocks::random(rng))
            .collect::<Vec<_>>();
        let noise = sample_uniform_bounded_noise(noise_bound, rng);
        Self::encrypt_with_mask_and_noise(params, sk, message, mask, noise)
    }

    pub fn encrypt_trivial(params: &Params, sk: &LweSecretKey, message: u64) -> Self {
        Self::encrypt_with_mask_and_noise(
            params,
            sk,
            message,
            vec![Goldilocks::ZERO; sk.dimension()],
            Goldilocks::ZERO,
        )
    }

    pub fn encrypt_with_mask(
        params: &Params,
        sk: &LweSecretKey,
        message: u64,
        mask: Vec<Goldilocks>,
    ) -> Self {
        Self::encrypt_with_mask_and_noise(params, sk, message, mask, Goldilocks::ONE)
    }

    pub fn encrypt_with_mask_and_noise_bound<R: RngCore + ?Sized>(
        params: &Params,
        sk: &LweSecretKey,
        message: u64,
        mask: Vec<Goldilocks>,
        noise_bound: u64,
        rng: &mut R,
    ) -> Self {
        let noise = sample_uniform_bounded_noise(noise_bound, rng);
        Self::encrypt_with_mask_and_noise(params, sk, message, mask, noise)
    }

    pub fn encrypt_with_mask_and_noise(
        params: &Params,
        sk: &LweSecretKey,
        message: u64,
        mask: Vec<Goldilocks>,
        noise: Goldilocks,
    ) -> Self {
        assert_eq!(mask.len(), sk.dimension());
        let encoded = encode_message(params, message);
        let body = mask
            .iter()
            .zip(sk.coeffs())
            .map(|(&a, &s)| a * s)
            .sum::<Goldilocks>()
            + encoded
            + noise;
        Self { mask, body }
    }

    pub fn phase(&self, sk: &LweSecretKey) -> Goldilocks {
        assert_eq!(self.mask.len(), sk.dimension());
        self.body
            - self
                .mask
                .iter()
                .zip(sk.coeffs())
                .map(|(&a, &s)| a * s)
                .sum::<Goldilocks>()
    }

    pub fn decrypt(&self, params: &Params, sk: &LweSecretKey) -> u64 {
        decode_message(params, self.phase(sk))
    }

    pub fn to_le_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity((self.mask.len() + 1) * 8);
        for value in &self.mask {
            out.extend_from_slice(&value.to_le_bytes());
        }
        out.extend_from_slice(&self.body.to_le_bytes());
        out
    }
}

pub fn encode_message(params: &Params, message: u64) -> Goldilocks {
    assert!(message < params.plaintext_modulus);
    let delta = GOLDILOCKS_MODULUS / params.plaintext_modulus;
    Goldilocks::from_u64(message * delta)
}

pub fn decode_message(params: &Params, phase: Goldilocks) -> u64 {
    (0..params.plaintext_modulus)
        .min_by_key(|&message| phase.wrapping_distance(encode_message(params, message)))
        .expect("plaintext modulus is validated to be nonzero")
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    use super::*;

    #[test]
    fn lwe_round_trips_messages() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(7);
        let sk = LweSecretKey::generate_binary(params.lwe_dimension, &mut rng);
        for message in 0..params.plaintext_modulus {
            let ct = LweCiphertext::encrypt(&params, &sk, message, &mut rng);
            assert_eq!(ct.decrypt(&params, &sk), message);
        }
    }

    #[test]
    fn lwe_round_trips_messages_with_bounded_noise() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(8);
        let sk = LweSecretKey::generate_binary(params.lwe_dimension, &mut rng);
        for message in 0..params.plaintext_modulus {
            let ct = LweCiphertext::encrypt_with_noise_bound(&params, &sk, message, 3, &mut rng);
            assert_eq!(ct.decrypt(&params, &sk), message);
        }
    }
}
