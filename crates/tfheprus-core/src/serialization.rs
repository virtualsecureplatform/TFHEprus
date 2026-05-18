use crate::field::Goldilocks;

pub trait CanonicalBytes {
    fn canonical_bytes(&self) -> Vec<u8>;
}

impl CanonicalBytes for Goldilocks {
    fn canonical_bytes(&self) -> Vec<u8> {
        self.to_le_bytes().to_vec()
    }
}
