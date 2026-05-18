use core::fmt;
use core::iter::Sum;
use core::ops::{Add, AddAssign, Mul, MulAssign, Neg, Sub, SubAssign};

use rand::RngCore;

pub const GOLDILOCKS_MODULUS: u64 = 0xffff_ffff_0000_0001;

#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct Goldilocks(u64);

impl Goldilocks {
    pub const ZERO: Self = Self(0);
    pub const ONE: Self = Self(1);

    pub const fn new_canonical(value: u64) -> Self {
        assert!(value < GOLDILOCKS_MODULUS);
        Self(value)
    }

    pub fn new(value: u64) -> Self {
        Self(value % GOLDILOCKS_MODULUS)
    }

    pub const fn value(self) -> u64 {
        self.0
    }

    pub fn from_u64(value: u64) -> Self {
        Self::new(value)
    }

    pub fn from_i64(value: i64) -> Self {
        if value >= 0 {
            Self::from_u64(value as u64)
        } else {
            -Self::from_u64(value.unsigned_abs())
        }
    }

    pub fn random<R: RngCore + ?Sized>(rng: &mut R) -> Self {
        loop {
            let value = rng.next_u64();
            if value < GOLDILOCKS_MODULUS {
                return Self(value);
            }
        }
    }

    pub fn pow(self, mut exponent: u64) -> Self {
        let mut base = self;
        let mut acc = Self::ONE;
        while exponent != 0 {
            if exponent & 1 == 1 {
                acc *= base;
            }
            base *= base;
            exponent >>= 1;
        }
        acc
    }

    pub fn inverse(self) -> Option<Self> {
        if self == Self::ZERO {
            None
        } else {
            Some(self.pow(GOLDILOCKS_MODULUS - 2))
        }
    }

    pub fn wrapping_distance(self, other: Self) -> u64 {
        let a = self.value();
        let b = other.value();
        let forward = a.abs_diff(b);
        forward.min(GOLDILOCKS_MODULUS - forward)
    }

    pub fn to_le_bytes(self) -> [u8; 8] {
        self.0.to_le_bytes()
    }
}

impl From<u64> for Goldilocks {
    fn from(value: u64) -> Self {
        Self::from_u64(value)
    }
}

impl fmt::Debug for Goldilocks {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "Goldilocks({})", self.0)
    }
}

impl Add for Goldilocks {
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self(((self.0 as u128 + rhs.0 as u128) % GOLDILOCKS_MODULUS as u128) as u64)
    }
}

impl AddAssign for Goldilocks {
    fn add_assign(&mut self, rhs: Self) {
        *self = *self + rhs;
    }
}

impl Sub for Goldilocks {
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        if self.0 >= rhs.0 {
            Self(self.0 - rhs.0)
        } else {
            Self(GOLDILOCKS_MODULUS - (rhs.0 - self.0))
        }
    }
}

impl SubAssign for Goldilocks {
    fn sub_assign(&mut self, rhs: Self) {
        *self = *self - rhs;
    }
}

impl Mul for Goldilocks {
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        Self(((self.0 as u128 * rhs.0 as u128) % GOLDILOCKS_MODULUS as u128) as u64)
    }
}

impl MulAssign for Goldilocks {
    fn mul_assign(&mut self, rhs: Self) {
        *self = *self * rhs;
    }
}

impl Neg for Goldilocks {
    type Output = Self;

    fn neg(self) -> Self::Output {
        if self == Self::ZERO {
            self
        } else {
            Self(GOLDILOCKS_MODULUS - self.0)
        }
    }
}

impl Sum for Goldilocks {
    fn sum<I: Iterator<Item = Self>>(iter: I) -> Self {
        iter.fold(Self::ZERO, |acc, value| acc + value)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn field_arithmetic_wraps_mod_goldilocks() {
        let minus_one = Goldilocks::from_u64(GOLDILOCKS_MODULUS - 1);
        assert_eq!((minus_one + Goldilocks::ONE).value(), 0);
        assert_eq!(
            (Goldilocks::ZERO - Goldilocks::ONE).value(),
            GOLDILOCKS_MODULUS - 1
        );
        assert_eq!(
            (Goldilocks::from_u64(GOLDILOCKS_MODULUS - 1) * Goldilocks::from_u64(2)).value(),
            GOLDILOCKS_MODULUS - 2
        );
    }
}
