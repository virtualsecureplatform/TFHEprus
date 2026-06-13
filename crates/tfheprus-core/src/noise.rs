use rand::RngCore;

use crate::field::Goldilocks;
#[cfg(test)]
use crate::field::GOLDILOCKS_MODULUS;
use crate::params::{EncryptionNoise, Params};
use crate::poly::Polynomial;

pub const DEFAULT_ENCRYPTION_NOISE_BOUND: u64 = 1;
pub const DEFAULT_ENCRYPTION_CBD_TERMS: usize = 32;
pub const DEFAULT_ENCRYPTION_NOISE_DESCRIPTION: &str = "centered_binomial_terms=32";

pub fn sample_default_encryption_noise<R: RngCore + ?Sized>(rng: &mut R) -> Goldilocks {
    sample_centered_binomial_noise(DEFAULT_ENCRYPTION_CBD_TERMS, rng)
}

pub fn sample_encryption_noise<R: RngCore + ?Sized>(params: &Params, rng: &mut R) -> Goldilocks {
    match params.encryption_noise {
        EncryptionNoise::CenteredBinomial { terms } => sample_centered_binomial_noise(terms, rng),
        EncryptionNoise::DiscreteGaussianStddev { stddev } => {
            sample_discrete_gaussian_noise(stddev, rng)
        }
    }
}

pub fn sample_default_encryption_noise_polynomial<R: RngCore + ?Sized>(
    size: usize,
    rng: &mut R,
) -> Polynomial {
    sample_centered_binomial_noise_polynomial(size, DEFAULT_ENCRYPTION_CBD_TERMS, rng)
}

pub fn sample_encryption_noise_polynomial<R: RngCore + ?Sized>(
    params: &Params,
    size: usize,
    rng: &mut R,
) -> Polynomial {
    Polynomial::from_coeffs(
        (0..size)
            .map(|_| sample_encryption_noise(params, rng))
            .collect(),
    )
}

pub fn sample_centered_binomial_noise<R: RngCore + ?Sized>(
    terms: usize,
    rng: &mut R,
) -> Goldilocks {
    assert!(terms <= i64::MAX as usize);
    let mut remaining = terms;
    let mut signed = 0i64;
    while remaining > 0 {
        let bits = rng.next_u64();
        let take = remaining.min(32);
        let mask = if take == 32 {
            u32::MAX
        } else {
            (1u32 << take) - 1
        };
        let positive = ((bits as u32) & mask).count_ones() as i64;
        let negative = (((bits >> 32) as u32) & mask).count_ones() as i64;
        signed += positive - negative;
        remaining -= take;
    }
    goldilocks_from_signed(signed)
}

pub fn sample_centered_binomial_noise_polynomial<R: RngCore + ?Sized>(
    size: usize,
    terms: usize,
    rng: &mut R,
) -> Polynomial {
    Polynomial::from_coeffs(
        (0..size)
            .map(|_| sample_centered_binomial_noise(terms, rng))
            .collect(),
    )
}

pub fn sample_discrete_gaussian_noise<R: RngCore + ?Sized>(stddev: u64, rng: &mut R) -> Goldilocks {
    assert!(stddev > 0);
    let radius = (-2.0 * uniform_open01(rng).ln()).sqrt();
    let angle = core::f64::consts::TAU * uniform_open01(rng);
    let sample = (radius * angle.cos() * stddev as f64).round();
    assert!(sample >= i64::MIN as f64 && sample <= i64::MAX as f64);
    goldilocks_from_signed(sample as i64)
}

pub fn sample_uniform_bounded_noise<R: RngCore + ?Sized>(bound: u64, rng: &mut R) -> Goldilocks {
    if bound == 0 {
        return Goldilocks::ZERO;
    }
    assert!(bound <= u64::MAX / 2);
    let width = 2 * bound + 1;
    let sample = rng.next_u64() % width;
    goldilocks_from_signed(sample as i64 - bound as i64)
}

pub fn sample_uniform_bounded_noise_polynomial<R: RngCore + ?Sized>(
    size: usize,
    bound: u64,
    rng: &mut R,
) -> Polynomial {
    Polynomial::from_coeffs(
        (0..size)
            .map(|_| sample_uniform_bounded_noise(bound, rng))
            .collect(),
    )
}

fn goldilocks_from_signed(value: i64) -> Goldilocks {
    Goldilocks::from_i64(value)
}

fn uniform_open01<R: RngCore + ?Sized>(rng: &mut R) -> f64 {
    const DENOMINATOR: f64 = (1u64 << 53) as f64;
    let value = rng.next_u64() >> 11;
    (value as f64 + 0.5) / DENOMINATOR
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    use super::*;

    #[test]
    fn centered_binomial_noise_is_bounded_and_signed() {
        let mut rng = ChaCha20Rng::seed_from_u64(44);
        let mut saw_positive = false;
        let mut saw_negative = false;
        for _ in 0..512 {
            let sample = sample_centered_binomial_noise(DEFAULT_ENCRYPTION_CBD_TERMS, &mut rng);
            let value = sample.value();
            saw_positive |= value <= DEFAULT_ENCRYPTION_CBD_TERMS as u64 && value != 0;
            saw_negative |=
                value >= Goldilocks::from_i64(-(DEFAULT_ENCRYPTION_CBD_TERMS as i64)).value();
        }
        assert!(saw_positive);
        assert!(saw_negative);
    }

    #[test]
    fn discrete_gaussian_noise_is_signed_and_nontrivial() {
        let mut rng = ChaCha20Rng::seed_from_u64(45);
        let mut saw_positive = false;
        let mut saw_negative = false;
        for _ in 0..512 {
            let sample = sample_discrete_gaussian_noise(1 << 13, &mut rng).value();
            saw_positive |= sample != 0 && sample < GOLDILOCKS_MODULUS / 2;
            saw_negative |= sample > GOLDILOCKS_MODULUS / 2;
        }
        assert!(saw_positive);
        assert!(saw_negative);
    }
}
