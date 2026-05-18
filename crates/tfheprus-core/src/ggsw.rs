use rand::RngCore;

use crate::field::Goldilocks;
use crate::glev::{GlevCiphertext, GlevCiphertextNtt};
use crate::glwe::{GlweCiphertext, GlweSecretKey};
use crate::params::Params;
use crate::poly::Polynomial;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GgswCiphertext {
    pub rows: Vec<GlevCiphertext>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct GgswCiphertextNtt {
    pub rows: Vec<GlevCiphertextNtt>,
}

impl GgswCiphertext {
    pub fn encrypt_constant<R: RngCore + ?Sized>(
        params: &Params,
        sk: &GlweSecretKey,
        message: Goldilocks,
        rng: &mut R,
    ) -> Self {
        Self::encrypt_polynomial(
            params,
            sk,
            &Polynomial::constant(params.polynomial_size, message),
            rng,
        )
    }

    pub fn encrypt_polynomial<R: RngCore + ?Sized>(
        params: &Params,
        sk: &GlweSecretKey,
        message: &Polynomial,
        rng: &mut R,
    ) -> Self {
        let mut rows = Vec::with_capacity(params.glwe_dimension + 1);
        for sk_poly in sk.polys() {
            rows.push(GlevCiphertext::encrypt(
                params,
                sk,
                &message.mul(sk_poly).neg(),
                rng,
            ));
        }
        rows.push(GlevCiphertext::encrypt(params, sk, message, rng));
        Self { rows }
    }

    pub fn to_ntt(&self) -> GgswCiphertextNtt {
        GgswCiphertextNtt {
            rows: self.rows.iter().map(GlevCiphertext::to_ntt).collect(),
        }
    }
}

pub fn external_product(
    params: &Params,
    ct: &GlweCiphertext,
    ggsw: &GgswCiphertext,
) -> GlweCiphertext {
    assert_eq!(ggsw.rows.len(), params.glwe_dimension + 1);
    let mut acc = GlweCiphertext::trivial(
        Polynomial::zero(params.polynomial_size),
        params.glwe_dimension,
    );
    for (mask_poly, row) in ct.mask.iter().zip(ggsw.rows.iter()) {
        acc = acc.add(&row.external_product_by_plain_poly(params, mask_poly));
    }
    acc.add(&ggsw.rows[params.glwe_dimension].external_product_by_plain_poly(params, &ct.body))
}

pub fn external_product_ntt(
    params: &Params,
    ct: &GlweCiphertext,
    ggsw: &GgswCiphertextNtt,
) -> GlweCiphertext {
    assert_eq!(ggsw.rows.len(), params.glwe_dimension + 1);
    let mut acc = GlweCiphertext::trivial(
        Polynomial::zero(params.polynomial_size),
        params.glwe_dimension,
    );
    for (mask_poly, row) in ct.mask.iter().zip(ggsw.rows.iter()) {
        acc = acc.add(&row.external_product_by_plain_poly(params, mask_poly));
    }
    acc.add(&ggsw.rows[params.glwe_dimension].external_product_by_plain_poly(params, &ct.body))
}

pub fn cmux(
    params: &Params,
    c0: &GlweCiphertext,
    c1: &GlweCiphertext,
    selector: &GgswCiphertext,
) -> GlweCiphertext {
    let diff = c1.sub(c0);
    external_product(params, &diff, selector).add(c0)
}

pub fn cmux_ntt(
    params: &Params,
    c0: &GlweCiphertext,
    c1: &GlweCiphertext,
    selector: &GgswCiphertextNtt,
) -> GlweCiphertext {
    let diff = c1.sub(c0);
    external_product_ntt(params, &diff, selector).add(c0)
}

#[cfg(test)]
mod tests {
    use rand::SeedableRng;
    use rand_chacha::ChaCha20Rng;

    use super::*;

    #[test]
    fn cmux_selects_expected_branch() {
        let params = Params::toy();
        let mut rng = ChaCha20Rng::seed_from_u64(20);
        let sk = GlweSecretKey::generate_binary(&params, &mut rng);
        let msg0 = Polynomial::constant(params.polynomial_size, 3u64.into());
        let msg1 = Polynomial::constant(params.polynomial_size, 9u64.into());
        let c0 = GlweCiphertext::encrypt(&params, &sk, &msg0, &mut rng);
        let c1 = GlweCiphertext::encrypt(&params, &sk, &msg1, &mut rng);

        let zero = GgswCiphertext::encrypt_constant(&params, &sk, Goldilocks::ZERO, &mut rng);
        let one = GgswCiphertext::encrypt_constant(&params, &sk, Goldilocks::ONE, &mut rng);

        assert_eq!(cmux(&params, &c0, &c1, &zero).phase(&sk), msg0);
        assert_eq!(cmux(&params, &c0, &c1, &one).phase(&sk), msg1);
        assert_eq!(cmux_ntt(&params, &c0, &c1, &zero.to_ntt()).phase(&sk), msg0);
        assert_eq!(cmux_ntt(&params, &c0, &c1, &one.to_ntt()).phase(&sk), msg1);
    }
}
