use rand::RngCore;

use crate::field::Goldilocks;
use crate::poly::Polynomial;

pub const DEFAULT_ENCRYPTION_NOISE_BOUND: u64 = 1;

pub fn sample_uniform_bounded_noise<R: RngCore + ?Sized>(bound: u64, rng: &mut R) -> Goldilocks {
    if bound == 0 {
        return Goldilocks::ZERO;
    }
    assert!(bound <= u64::MAX / 2);
    let width = 2 * bound + 1;
    let sample = rng.next_u64() % width;
    if sample <= bound {
        Goldilocks::ZERO - Goldilocks::from_u64(bound - sample)
    } else {
        Goldilocks::from_u64(sample - bound)
    }
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
