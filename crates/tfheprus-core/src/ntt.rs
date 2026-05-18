use crate::field::{Goldilocks, GOLDILOCKS_MODULUS};

pub const GOLDILOCKS_TWO_ADICITY: usize = 32;

pub fn primitive_power_of_two_root(order: usize) -> Goldilocks {
    assert!(order.is_power_of_two());
    assert!(order <= (1usize << GOLDILOCKS_TWO_ADICITY));
    Goldilocks::from_u64(7).pow((GOLDILOCKS_MODULUS - 1) / order as u64)
}

pub fn ntt(values: &mut [Goldilocks], inverse: bool) {
    let n = values.len();
    assert!(n.is_power_of_two());
    bit_reverse(values);

    let mut len = 2;
    while len <= n {
        let mut root = primitive_power_of_two_root(len);
        if inverse {
            root = root.inverse().expect("root of unity is nonzero");
        }

        for chunk in values.chunks_exact_mut(len) {
            let mut twiddle = Goldilocks::ONE;
            let half = len / 2;
            for j in 0..half {
                let u = chunk[j];
                let v = chunk[j + half] * twiddle;
                chunk[j] = u + v;
                chunk[j + half] = u - v;
                twiddle *= root;
            }
        }

        len *= 2;
    }

    if inverse {
        let inv_n = Goldilocks::from_u64(n as u64)
            .inverse()
            .expect("NTT length is nonzero");
        for value in values {
            *value *= inv_n;
        }
    }
}

pub fn negacyclic_mul(lhs: &[Goldilocks], rhs: &[Goldilocks]) -> Vec<Goldilocks> {
    assert_eq!(lhs.len(), rhs.len());

    let lhs_eval = negacyclic_ntt(lhs);
    let rhs_eval = negacyclic_ntt(rhs);
    negacyclic_mul_ntt(&lhs_eval, &rhs_eval)
}

pub fn negacyclic_mul_ntt(lhs_ntt: &[Goldilocks], rhs_ntt: &[Goldilocks]) -> Vec<Goldilocks> {
    assert_eq!(lhs_ntt.len(), rhs_ntt.len());

    let mut product = lhs_ntt.to_vec();

    for (lhs_value, rhs_value) in product.iter_mut().zip(rhs_ntt.iter()) {
        *lhs_value *= *rhs_value;
    }

    negacyclic_intt(&product)
}

pub fn negacyclic_ntt(values: &[Goldilocks]) -> Vec<Goldilocks> {
    let n = values.len();
    assert!(n.is_power_of_two());
    assert!(2 * n <= (1usize << GOLDILOCKS_TWO_ADICITY));

    let psi = primitive_power_of_two_root(2 * n);
    let mut evals = twist(values, psi);
    ntt(&mut evals, false);
    evals
}

pub fn negacyclic_intt(values: &[Goldilocks]) -> Vec<Goldilocks> {
    let n = values.len();
    assert!(n.is_power_of_two());
    assert!(2 * n <= (1usize << GOLDILOCKS_TWO_ADICITY));

    let psi = primitive_power_of_two_root(2 * n);
    let psi_inv = psi.inverse().expect("root of unity is nonzero");
    let mut coeffs = values.to_vec();
    ntt(&mut coeffs, true);
    untwist(&mut coeffs, psi_inv);
    coeffs
}

fn twist(values: &[Goldilocks], psi: Goldilocks) -> Vec<Goldilocks> {
    let mut twiddle = Goldilocks::ONE;
    values
        .iter()
        .map(|&value| {
            let out = value * twiddle;
            twiddle *= psi;
            out
        })
        .collect()
}

fn untwist(values: &mut [Goldilocks], psi_inv: Goldilocks) {
    let mut twiddle = Goldilocks::ONE;
    for value in values {
        *value *= twiddle;
        twiddle *= psi_inv;
    }
}

fn bit_reverse(values: &mut [Goldilocks]) {
    let n = values.len();
    let bits = n.trailing_zeros();
    for i in 0..n {
        let j = i.reverse_bits() >> (usize::BITS - bits);
        if i < j {
            values.swap(i, j);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn root_has_exact_requested_order() {
        for order in [2, 4, 8, 16, 1024, 1 << GOLDILOCKS_TWO_ADICITY] {
            let root = primitive_power_of_two_root(order);
            assert_eq!(root.pow(order as u64), Goldilocks::ONE);
            if order > 1 {
                assert_ne!(root.pow((order / 2) as u64), Goldilocks::ONE);
            }
        }
    }

    #[test]
    fn ntt_round_trips() {
        let mut values = (0..16).map(Goldilocks::from_u64).collect::<Vec<_>>();
        let original = values.clone();
        ntt(&mut values, false);
        ntt(&mut values, true);
        assert_eq!(values, original);
    }

    #[test]
    fn negacyclic_ntt_round_trips() {
        let values = (0..16).map(Goldilocks::from_u64).collect::<Vec<_>>();
        let evals = negacyclic_ntt(&values);
        assert_eq!(negacyclic_intt(&evals), values);
    }
}
