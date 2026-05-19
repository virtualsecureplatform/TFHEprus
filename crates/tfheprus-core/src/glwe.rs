use rand::RngCore;

use crate::field::Goldilocks;
use crate::lwe::{LweCiphertext, LweSecretKey};
use crate::noise::{sample_uniform_bounded_noise_polynomial, DEFAULT_ENCRYPTION_NOISE_BOUND};
use crate::params::Params;
use crate::poly::{NttPolynomial, Polynomial};

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlweSecretKey {
    polys: Vec<Polynomial>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlweCiphertext {
    pub mask: Vec<Polynomial>,
    pub body: Polynomial,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GlweCiphertextNtt {
    pub mask: Vec<NttPolynomial>,
    pub body: NttPolynomial,
}

impl GlweSecretKey {
    pub fn generate_binary<R: RngCore + ?Sized>(params: &Params, rng: &mut R) -> Self {
        let polys = (0..params.glwe_dimension)
            .map(|_| {
                Polynomial::from_coeffs(
                    (0..params.polynomial_size)
                        .map(|_| Goldilocks::from_u64((rng.next_u32() & 1) as u64))
                        .collect(),
                )
            })
            .collect();
        Self { polys }
    }

    pub fn from_polys(polys: Vec<Polynomial>) -> Self {
        assert!(!polys.is_empty());
        Self { polys }
    }

    pub fn polys(&self) -> &[Polynomial] {
        &self.polys
    }

    pub fn dimension(&self) -> usize {
        self.polys.len()
    }

    pub fn polynomial_size(&self) -> usize {
        self.polys[0].len()
    }

    pub fn extracted_lwe_secret_key(&self) -> LweSecretKey {
        let mut coeffs = Vec::with_capacity(self.dimension() * self.polynomial_size());
        for poly in &self.polys {
            coeffs.extend_from_slice(poly.coeffs());
        }
        LweSecretKey::from_coeffs(coeffs)
    }
}

impl GlweCiphertext {
    pub fn trivial(message: Polynomial, glwe_dimension: usize) -> Self {
        let size = message.len();
        Self {
            mask: vec![Polynomial::zero(size); glwe_dimension],
            body: message,
        }
    }

    pub fn encrypt_zero<R: RngCore + ?Sized>(
        params: &Params,
        sk: &GlweSecretKey,
        rng: &mut R,
    ) -> Self {
        Self::encrypt(params, sk, &Polynomial::zero(params.polynomial_size), rng)
    }

    pub fn encrypt<R: RngCore + ?Sized>(
        params: &Params,
        sk: &GlweSecretKey,
        message: &Polynomial,
        rng: &mut R,
    ) -> Self {
        Self::encrypt_with_noise_bound(params, sk, message, DEFAULT_ENCRYPTION_NOISE_BOUND, rng)
    }

    pub fn encrypt_with_noise_bound<R: RngCore + ?Sized>(
        params: &Params,
        sk: &GlweSecretKey,
        message: &Polynomial,
        noise_bound: u64,
        rng: &mut R,
    ) -> Self {
        assert_eq!(message.len(), params.polynomial_size);
        assert_eq!(sk.dimension(), params.glwe_dimension);
        let mask = (0..params.glwe_dimension)
            .map(|_| Polynomial::random(params.polynomial_size, rng))
            .collect::<Vec<_>>();
        let noise =
            sample_uniform_bounded_noise_polynomial(params.polynomial_size, noise_bound, rng);
        Self::encrypt_with_mask_and_noise(params, sk, message, mask, noise)
    }

    pub fn encrypt_with_mask(
        params: &Params,
        sk: &GlweSecretKey,
        message: &Polynomial,
        mask: Vec<Polynomial>,
    ) -> Self {
        let noise = Polynomial::from_coeffs(vec![Goldilocks::ONE; params.polynomial_size]);
        Self::encrypt_with_mask_and_noise(params, sk, message, mask, noise)
    }

    pub fn encrypt_with_mask_and_noise_bound<R: RngCore + ?Sized>(
        params: &Params,
        sk: &GlweSecretKey,
        message: &Polynomial,
        mask: Vec<Polynomial>,
        noise_bound: u64,
        rng: &mut R,
    ) -> Self {
        let noise =
            sample_uniform_bounded_noise_polynomial(params.polynomial_size, noise_bound, rng);
        Self::encrypt_with_mask_and_noise(params, sk, message, mask, noise)
    }

    pub fn encrypt_with_mask_and_noise(
        params: &Params,
        sk: &GlweSecretKey,
        message: &Polynomial,
        mask: Vec<Polynomial>,
        noise: Polynomial,
    ) -> Self {
        assert_eq!(mask.len(), sk.dimension());
        assert_eq!(noise.len(), params.polynomial_size);
        let mut body = message.clone();
        for (a, s) in mask.iter().zip(sk.polys()) {
            body = body.add(&a.mul(s));
        }
        body = body.add(&noise);
        assert_eq!(body.len(), params.polynomial_size);
        Self { mask, body }
    }

    pub fn phase(&self, sk: &GlweSecretKey) -> Polynomial {
        assert_eq!(self.mask.len(), sk.dimension());
        let mut phase = self.body.clone();
        for (a, s) in self.mask.iter().zip(sk.polys()) {
            phase = phase.sub(&a.mul(s));
        }
        phase
    }

    pub fn add(&self, rhs: &Self) -> Self {
        assert_eq!(self.mask.len(), rhs.mask.len());
        Self {
            mask: self
                .mask
                .iter()
                .zip(rhs.mask.iter())
                .map(|(a, b)| a.add(b))
                .collect(),
            body: self.body.add(&rhs.body),
        }
    }

    pub fn sub(&self, rhs: &Self) -> Self {
        assert_eq!(self.mask.len(), rhs.mask.len());
        Self {
            mask: self
                .mask
                .iter()
                .zip(rhs.mask.iter())
                .map(|(a, b)| a.sub(b))
                .collect(),
            body: self.body.sub(&rhs.body),
        }
    }

    pub fn mul_by_plain_poly(&self, poly: &Polynomial) -> Self {
        Self {
            mask: self.mask.iter().map(|a| a.mul(poly)).collect(),
            body: self.body.mul(poly),
        }
    }

    pub fn to_ntt(&self) -> GlweCiphertextNtt {
        GlweCiphertextNtt {
            mask: self.mask.iter().map(Polynomial::to_ntt).collect(),
            body: self.body.to_ntt(),
        }
    }

    pub fn mul_xai(&self, exponent: usize) -> Self {
        Self {
            mask: self.mask.iter().map(|a| a.mul_xai(exponent)).collect(),
            body: self.body.mul_xai(exponent),
        }
    }

    pub fn to_le_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        for poly in &self.mask {
            out.extend_from_slice(&poly.to_le_bytes());
        }
        out.extend_from_slice(&self.body.to_le_bytes());
        out
    }
}

impl GlweCiphertextNtt {
    pub fn mul_by_plain_poly(&self, poly: &Polynomial) -> GlweCiphertext {
        let poly_ntt = poly.to_ntt();
        GlweCiphertext {
            mask: self
                .mask
                .iter()
                .map(|ntt_poly| ntt_poly.mul_ntt(&poly_ntt))
                .collect(),
            body: self.body.mul_ntt(&poly_ntt),
        }
    }
}

pub fn sample_extract_index_zero(ct: &GlweCiphertext) -> LweCiphertext {
    let n = ct.body.len();
    let mut mask = Vec::with_capacity(ct.mask.len() * n);
    for poly in &ct.mask {
        mask.push(poly[0]);
        for i in 1..n {
            mask.push(-poly[n - i]);
        }
    }
    LweCiphertext {
        mask,
        body: ct.body[0],
    }
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    use super::*;

    #[test]
    fn glwe_round_trips_polynomial_messages() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(11);
        let sk = GlweSecretKey::generate_binary(&params, &mut rng);
        let msg = Polynomial::from_coeffs(
            (0..params.polynomial_size)
                .map(|value| Goldilocks::from_u64(value as u64))
                .collect(),
        );
        let mask = (0..params.glwe_dimension)
            .map(|_| Polynomial::random(params.polynomial_size, &mut rng))
            .collect();
        let ct = GlweCiphertext::encrypt_with_mask_and_noise(
            &params,
            &sk,
            &msg,
            mask,
            Polynomial::zero(params.polynomial_size),
        );
        assert_eq!(ct.phase(&sk), msg);
    }

    #[test]
    fn glwe_encrypt_with_bounded_noise_adds_phase_noise() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(13);
        let sk = GlweSecretKey::generate_binary(&params, &mut rng);
        let msg = Polynomial::from_coeffs(
            (0..params.polynomial_size)
                .map(|value| Goldilocks::from_u64(value as u64))
                .collect(),
        );
        let noise = Polynomial::from_coeffs(vec![Goldilocks::ONE; params.polynomial_size]);
        let mask = (0..params.glwe_dimension)
            .map(|_| Polynomial::random(params.polynomial_size, &mut rng))
            .collect();
        let ct = GlweCiphertext::encrypt_with_mask_and_noise(&params, &sk, &msg, mask, noise);
        assert_eq!(
            ct.phase(&sk),
            msg.add(&Polynomial::from_coeffs(vec![
                Goldilocks::ONE;
                params.polynomial_size
            ]))
        );
    }

    #[test]
    fn sample_extraction_decrypts_constant_coefficient() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(12);
        let sk = GlweSecretKey::generate_binary(&params, &mut rng);
        let msg = Polynomial::from_coeffs((10..18).map(Goldilocks::from_u64).collect());
        let mask = (0..params.glwe_dimension)
            .map(|_| Polynomial::random(params.polynomial_size, &mut rng))
            .collect();
        let ct = GlweCiphertext::encrypt_with_mask_and_noise(
            &params,
            &sk,
            &msg,
            mask,
            Polynomial::zero(params.polynomial_size),
        );
        let lwe = sample_extract_index_zero(&ct);
        assert_eq!(lwe.phase(&sk.extracted_lwe_secret_key()), msg[0]);
    }
}
