use rand::RngCore;

use crate::field::{Goldilocks, GOLDILOCKS_MODULUS};
use crate::glwe::{GlweCiphertext, GlweCiphertextNtt, GlweSecretKey};
use crate::params::Params;
use crate::poly::Polynomial;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlevCiphertext {
    pub levels: Vec<GlweCiphertext>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlevCiphertextNtt {
    pub levels: Vec<GlweCiphertextNtt>,
}

impl GlevCiphertext {
    pub fn encrypt<R: RngCore + ?Sized>(
        params: &Params,
        sk: &GlweSecretKey,
        message: &Polynomial,
        rng: &mut R,
    ) -> Self {
        let mut levels = Vec::with_capacity(params.decomposition_level_count);
        for level_index in 0..params.decomposition_level_count {
            let gadget = decomposition_gadget_factor(params, level_index);
            let scaled = message.scale(gadget);
            levels.push(GlweCiphertext::encrypt(params, sk, &scaled, rng));
        }
        Self { levels }
    }

    pub fn encrypt_with_noise_bound<R: RngCore + ?Sized>(
        params: &Params,
        sk: &GlweSecretKey,
        message: &Polynomial,
        noise_bound: u64,
        rng: &mut R,
    ) -> Self {
        let mut levels = Vec::with_capacity(params.decomposition_level_count);
        for level_index in 0..params.decomposition_level_count {
            let gadget = decomposition_gadget_factor(params, level_index);
            let scaled = message.scale(gadget);
            levels.push(GlweCiphertext::encrypt_with_noise_bound(
                params,
                sk,
                &scaled,
                noise_bound,
                rng,
            ));
        }
        Self { levels }
    }

    pub fn external_product_by_plain_poly(
        &self,
        params: &Params,
        poly: &Polynomial,
    ) -> GlweCiphertext {
        let digits = decompose_polynomial(params, poly);
        let mut acc = GlweCiphertext::trivial(
            Polynomial::zero(params.polynomial_size),
            params.glwe_dimension,
        );
        for (digit_poly, level_ct) in digits.iter().zip(self.levels.iter()) {
            acc = acc.add(&level_ct.mul_by_plain_poly(digit_poly));
        }
        acc
    }

    pub fn to_ntt(&self) -> GlevCiphertextNtt {
        GlevCiphertextNtt {
            levels: self.levels.iter().map(GlweCiphertext::to_ntt).collect(),
        }
    }
}

impl GlevCiphertextNtt {
    pub fn external_product_by_plain_poly(
        &self,
        params: &Params,
        poly: &Polynomial,
    ) -> GlweCiphertext {
        let digits = decompose_polynomial(params, poly);
        let mut acc = GlweCiphertext::trivial(
            Polynomial::zero(params.polynomial_size),
            params.glwe_dimension,
        );
        for (digit_poly, level_ct) in digits.iter().zip(self.levels.iter()) {
            acc = acc.add(&level_ct.mul_by_plain_poly(digit_poly));
        }
        acc
    }
}

pub fn decompose_polynomial(params: &Params, poly: &Polynomial) -> Vec<Polynomial> {
    let mut levels = vec![Polynomial::zero(poly.len()); params.decomposition_level_count];
    for (coeff_index, coeff) in poly.coeffs().iter().enumerate() {
        let digits = decompose_scalar(params, *coeff);
        for (level, digit) in levels.iter_mut().zip(digits) {
            level[coeff_index] = digit;
        }
    }
    levels
}

pub fn decompose_scalar(params: &Params, coeff: Goldilocks) -> Vec<Goldilocks> {
    if uses_exact_binary_decomposition(params) {
        decompose_scalar_exact(params, coeff)
    } else {
        decompose_scalar_approx(params, coeff)
    }
}

pub fn decomposition_gadget_factor(params: &Params, level_index: usize) -> Goldilocks {
    assert!(level_index < params.decomposition_level_count);
    if uses_exact_binary_decomposition(params) {
        Goldilocks::from_u64(1u64 << (params.decomposition_base_log * level_index))
    } else {
        let denominator = 1u128 << (params.decomposition_base_log * (level_index + 1));
        let rounded = (GOLDILOCKS_MODULUS as u128 + denominator / 2) / denominator;
        Goldilocks::from_u64(rounded as u64)
    }
}

fn uses_exact_binary_decomposition(params: &Params) -> bool {
    params.decomposition_base_log * params.decomposition_level_count == 64
}

fn decompose_scalar_exact(params: &Params, coeff: Goldilocks) -> Vec<Goldilocks> {
    let base_mask = params.gadget_base() - 1;
    let mut value = coeff.value();
    let mut digits = Vec::with_capacity(params.decomposition_level_count);
    for _ in 0..params.decomposition_level_count {
        digits.push(Goldilocks::from_u64(value & base_mask));
        value >>= params.decomposition_base_log;
    }
    digits
}

fn decompose_scalar_approx(params: &Params, coeff: Goldilocks) -> Vec<Goldilocks> {
    let total_bits = params.decomposition_base_log * params.decomposition_level_count;
    assert!(total_bits < 64);

    let modulus = 1u128 << total_bits;
    let q = GOLDILOCKS_MODULUS as u128;
    let rounded = ((coeff.value() as u128 * modulus + q / 2) / q) % modulus;

    let base = 1i128 << params.decomposition_base_log;
    let half_base = base / 2;
    let mask = (base - 1) as u128;
    let mut carry = 0i128;
    let mut low_to_high = Vec::with_capacity(params.decomposition_level_count);
    for level_index in 0..params.decomposition_level_count {
        let shift = params.decomposition_base_log * level_index;
        let limb = (((rounded >> shift) & mask) as i128) + carry;
        if limb >= half_base {
            low_to_high.push(limb - base);
            carry = 1;
        } else {
            low_to_high.push(limb);
            carry = 0;
        }
    }

    low_to_high
        .into_iter()
        .rev()
        .map(|digit| Goldilocks::from_i64(digit as i64))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::poly::Polynomial;

    #[test]
    fn exact_toy_decomposition_reconstructs_coefficients() {
        let params = Params::toy();
        let poly = Polynomial::from_coeffs(vec![
            0u64.into(),
            1u64.into(),
            0x1234_5678_9abc_def0u64.into(),
            0xffff_fffe_ffff_fffeu64.into(),
            7u64.into(),
            8u64.into(),
            9u64.into(),
            10u64.into(),
        ]);
        let digits = decompose_polynomial(&params, &poly);
        for i in 0..poly.len() {
            let mut reconstructed = Goldilocks::ZERO;
            for (level_index, digit_poly) in digits.iter().enumerate() {
                reconstructed += digit_poly[i] * decomposition_gadget_factor(&params, level_index);
            }
            assert_eq!(reconstructed, poly[i]);
        }
    }

    #[test]
    fn paper_decomposition_reconstructs_with_expected_approximation_error() {
        let params = Params::paper_v1();
        let low_weight =
            decomposition_gadget_factor(&params, params.decomposition_level_count - 1).value();
        let tolerance = low_weight * 2;
        let samples = [
            0,
            1,
            31,
            low_weight - 1,
            low_weight,
            GOLDILOCKS_MODULUS / 2 - 1,
            GOLDILOCKS_MODULUS / 2,
            GOLDILOCKS_MODULUS - low_weight,
            GOLDILOCKS_MODULUS - 2,
            GOLDILOCKS_MODULUS - 1,
        ];

        for value in samples {
            let coeff = Goldilocks::from_u64(value);
            let digits = decompose_scalar(&params, coeff);
            assert_eq!(digits.len(), params.decomposition_level_count);
            for digit in &digits {
                let canonical = digit.value();
                assert!(
                    canonical <= params.gadget_base() / 2
                        || canonical >= GOLDILOCKS_MODULUS - params.gadget_base() / 2
                );
            }

            let reconstructed =
                digits
                    .iter()
                    .enumerate()
                    .fold(Goldilocks::ZERO, |acc, (level_index, digit)| {
                        acc + *digit * decomposition_gadget_factor(&params, level_index)
                    });
            assert!(
                coeff.wrapping_distance(reconstructed) <= tolerance,
                "value={value}, reconstructed={}, tolerance={tolerance}",
                reconstructed.value()
            );
        }
    }
}
