use rand::RngCore;

use crate::field::Goldilocks;
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
        let base = Goldilocks::from_u64(params.gadget_base());
        let mut gadget = Goldilocks::ONE;
        let mut levels = Vec::with_capacity(params.decomposition_level_count);
        for _ in 0..params.decomposition_level_count {
            let scaled = message.scale(gadget);
            levels.push(GlweCiphertext::encrypt(params, sk, &scaled, rng));
            gadget *= base;
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
    let base_mask = params.gadget_base() - 1;
    let mut levels = vec![Polynomial::zero(poly.len()); params.decomposition_level_count];
    for (coeff_index, coeff) in poly.coeffs().iter().enumerate() {
        let mut value = coeff.value();
        for level in &mut levels {
            let digit = value & base_mask;
            level[coeff_index] = Goldilocks::from_u64(digit);
            value >>= params.decomposition_base_log;
        }
    }
    levels
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
            let mut scale = Goldilocks::ONE;
            let mut reconstructed = Goldilocks::ZERO;
            for digit_poly in &digits {
                reconstructed += digit_poly[i] * scale;
                scale *= Goldilocks::from_u64(params.gadget_base());
            }
            assert_eq!(reconstructed, poly[i]);
        }
    }
}
