use core::ops::{Index, IndexMut};

use rand::RngCore;

use crate::field::Goldilocks;
use crate::ntt;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Polynomial {
    coeffs: Vec<Goldilocks>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct NttPolynomial {
    evals: Vec<Goldilocks>,
}

impl Polynomial {
    pub fn zero(size: usize) -> Self {
        Self {
            coeffs: vec![Goldilocks::ZERO; size],
        }
    }

    pub fn from_coeffs(coeffs: Vec<Goldilocks>) -> Self {
        assert!(!coeffs.is_empty());
        assert!(coeffs.len().is_power_of_two());
        Self { coeffs }
    }

    pub fn constant(size: usize, value: Goldilocks) -> Self {
        let mut poly = Self::zero(size);
        poly[0] = value;
        poly
    }

    pub fn random<R: RngCore + ?Sized>(size: usize, rng: &mut R) -> Self {
        let coeffs = (0..size).map(|_| Goldilocks::random(rng)).collect();
        Self { coeffs }
    }

    pub fn len(&self) -> usize {
        self.coeffs.len()
    }

    pub fn is_empty(&self) -> bool {
        self.coeffs.is_empty()
    }

    pub fn coeffs(&self) -> &[Goldilocks] {
        &self.coeffs
    }

    pub fn coeffs_mut(&mut self) -> &mut [Goldilocks] {
        &mut self.coeffs
    }

    pub fn add(&self, rhs: &Self) -> Self {
        self.zip_map(rhs, |a, b| a + b)
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        self.zip_map(rhs, |a, b| a - b)
    }

    pub fn neg(&self) -> Self {
        Self::from_coeffs(self.coeffs.iter().map(|&c| -c).collect())
    }

    pub fn scale(&self, scalar: Goldilocks) -> Self {
        Self::from_coeffs(self.coeffs.iter().map(|&c| c * scalar).collect())
    }

    pub fn mul_naive(&self, rhs: &Self) -> Self {
        assert_eq!(self.len(), rhs.len());
        let n = self.len();
        let mut out = vec![Goldilocks::ZERO; n];
        for i in 0..n {
            for j in 0..n {
                let product = self[i] * rhs[j];
                let degree = i + j;
                if degree < n {
                    out[degree] += product;
                } else {
                    out[degree - n] -= product;
                }
            }
        }
        Self::from_coeffs(out)
    }

    pub fn mul(&self, rhs: &Self) -> Self {
        self.mul_ntt(rhs)
    }

    pub fn mul_ntt(&self, rhs: &Self) -> Self {
        Self::from_coeffs(ntt::negacyclic_mul(&self.coeffs, &rhs.coeffs))
    }

    pub fn to_ntt(&self) -> NttPolynomial {
        NttPolynomial::from_polynomial(self)
    }

    pub fn mul_xai(&self, exponent: usize) -> Self {
        let n = self.len();
        let modulus = 2 * n;
        let exponent = exponent % modulus;
        let mut out = vec![Goldilocks::ZERO; n];
        for (i, &coeff) in self.coeffs.iter().enumerate() {
            let target = (i + exponent) % modulus;
            if target < n {
                out[target] += coeff;
            } else {
                out[target - n] -= coeff;
            }
        }
        Self::from_coeffs(out)
    }

    pub fn to_le_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.len() * 8);
        for coeff in &self.coeffs {
            out.extend_from_slice(&coeff.to_le_bytes());
        }
        out
    }

    fn zip_map(&self, rhs: &Self, f: impl Fn(Goldilocks, Goldilocks) -> Goldilocks) -> Self {
        assert_eq!(self.len(), rhs.len());
        Self::from_coeffs(
            self.coeffs
                .iter()
                .zip(rhs.coeffs.iter())
                .map(|(&a, &b)| f(a, b))
                .collect(),
        )
    }
}

impl NttPolynomial {
    pub fn from_polynomial(poly: &Polynomial) -> Self {
        Self {
            evals: ntt::negacyclic_ntt(poly.coeffs()),
        }
    }

    pub fn from_evals(evals: Vec<Goldilocks>) -> Self {
        assert!(!evals.is_empty());
        assert!(evals.len().is_power_of_two());
        Self { evals }
    }

    pub fn evals(&self) -> &[Goldilocks] {
        &self.evals
    }

    pub fn mul_polynomial(&self, rhs: &Polynomial) -> Polynomial {
        let rhs_ntt = rhs.to_ntt();
        self.mul_ntt(&rhs_ntt)
    }

    pub fn mul_ntt(&self, rhs: &Self) -> Polynomial {
        Polynomial::from_coeffs(ntt::negacyclic_mul_ntt(&self.evals, &rhs.evals))
    }
}

impl Index<usize> for Polynomial {
    type Output = Goldilocks;

    fn index(&self, index: usize) -> &Self::Output {
        &self.coeffs[index]
    }
}

impl IndexMut<usize> for Polynomial {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        &mut self.coeffs[index]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn x_power_wraps_negacyclically() {
        let p = Polynomial::from_coeffs(vec![
            1u64.into(),
            2u64.into(),
            3u64.into(),
            4u64.into(),
            5u64.into(),
            6u64.into(),
            7u64.into(),
            8u64.into(),
        ]);
        let rotated = p.mul_xai(8);
        assert_eq!(rotated, p.neg());
        assert_eq!(p.mul_xai(16), p);
    }

    #[test]
    fn multiplication_respects_xn_plus_one() {
        let x = Polynomial::from_coeffs(vec![
            Goldilocks::ZERO,
            Goldilocks::ONE,
            Goldilocks::ZERO,
            Goldilocks::ZERO,
        ]);
        assert_eq!(
            x.mul_naive(&x).mul_naive(&x).mul_naive(&x),
            Polynomial::constant(4, -Goldilocks::ONE)
        );
    }

    #[test]
    fn ntt_multiplication_matches_naive() {
        for size in [4, 8, 16, 1024] {
            let lhs = Polynomial::from_coeffs(
                (0..size)
                    .map(|value| Goldilocks::from_u64((value * 3 + 1) as u64))
                    .collect(),
            );
            let rhs = Polynomial::from_coeffs(
                (0..size)
                    .map(|value| Goldilocks::from_u64((value * 5 + 7) as u64))
                    .collect(),
            );
            assert_eq!(lhs.mul_ntt(&rhs), lhs.mul_naive(&rhs));
        }
    }
}
