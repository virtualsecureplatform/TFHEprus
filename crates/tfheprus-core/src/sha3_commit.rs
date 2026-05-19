use serde::{Deserialize, Serialize};
use sha3::{Digest, Sha3_256};

use crate::Goldilocks;

pub const SHA3_256_DIGEST_BYTES: usize = 32;
pub const SHA3_256_DIGEST_U32_WORDS: usize = 8;
pub const SHA3_256_DIGEST_FIELD_ELEMENTS: usize = SHA3_256_DIGEST_U32_WORDS;

const DOMAIN_PREFIX: &[u8] = b"TFHEprus-SHA3-256-v1";

#[derive(Clone, Copy, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Sha3DigestWords(pub [u32; SHA3_256_DIGEST_U32_WORDS]);

impl Sha3DigestWords {
    pub fn as_words(&self) -> &[u32; SHA3_256_DIGEST_U32_WORDS] {
        &self.0
    }

    pub fn to_field_elements(self) -> [Goldilocks; SHA3_256_DIGEST_FIELD_ELEMENTS] {
        self.0.map(|word| Goldilocks::from_u64(word as u64))
    }

    pub fn from_field_elements(values: &[Goldilocks]) -> Option<[u32; SHA3_256_DIGEST_U32_WORDS]> {
        if values.len() != SHA3_256_DIGEST_FIELD_ELEMENTS {
            return None;
        }
        let mut words = [0u32; SHA3_256_DIGEST_U32_WORDS];
        for (word, value) in words.iter_mut().zip(values) {
            let value = value.value();
            if value > u32::MAX as u64 {
                return None;
            }
            *word = value as u32;
        }
        Some(words)
    }
}

pub fn raw_sha3_256(bytes: &[u8]) -> [u8; SHA3_256_DIGEST_BYTES] {
    Sha3_256::digest(bytes).into()
}

pub fn sha3_256_bytes(domain: &[u8], bytes: &[u8]) -> Sha3DigestWords {
    let mut hasher = domain_separated_hasher(domain);
    hasher.update((bytes.len() as u64).to_le_bytes());
    hasher.update(bytes);
    Sha3DigestWords(bytes_to_u32_words(hasher.finalize().into()))
}

pub fn sha3_256_field_elements(
    domain: &[u8],
    values: impl IntoIterator<Item = Goldilocks>,
) -> Sha3DigestWords {
    let mut hasher = domain_separated_hasher(domain);
    for value in values {
        hasher.update(value.to_le_bytes());
    }
    Sha3DigestWords(bytes_to_u32_words(hasher.finalize().into()))
}

pub fn sha3_256_field_element_digest(
    domain: &[u8],
    values: impl IntoIterator<Item = Goldilocks>,
) -> [Goldilocks; SHA3_256_DIGEST_FIELD_ELEMENTS] {
    sha3_256_field_elements(domain, values).to_field_elements()
}

pub fn sha3_256_chain_initial(domain: &[u8]) -> [Goldilocks; SHA3_256_DIGEST_FIELD_ELEMENTS] {
    sha3_256_bytes(domain, b"init").to_field_elements()
}

pub fn sha3_256_chain_update_fields(
    domain: &[u8],
    previous: &[Goldilocks; SHA3_256_DIGEST_FIELD_ELEMENTS],
    values: impl IntoIterator<Item = Goldilocks>,
) -> [Goldilocks; SHA3_256_DIGEST_FIELD_ELEMENTS] {
    let mut hasher = domain_separated_hasher(domain);
    hasher.update(b"chain-update");
    for word in Sha3DigestWords::from_field_elements(previous)
        .expect("SHA3 digest field elements must be u32 limbs")
    {
        hasher.update(word.to_le_bytes());
    }
    for value in values {
        hasher.update(value.to_le_bytes());
    }
    Sha3DigestWords(bytes_to_u32_words(hasher.finalize().into())).to_field_elements()
}

fn domain_separated_hasher(domain: &[u8]) -> Sha3_256 {
    let mut hasher = Sha3_256::new();
    hasher.update(DOMAIN_PREFIX);
    hasher.update((domain.len() as u32).to_le_bytes());
    hasher.update(domain);
    hasher
}

fn bytes_to_u32_words(bytes: [u8; SHA3_256_DIGEST_BYTES]) -> [u32; SHA3_256_DIGEST_U32_WORDS] {
    core::array::from_fn(|index| {
        let offset = 4 * index;
        u32::from_le_bytes([
            bytes[offset],
            bytes[offset + 1],
            bytes[offset + 2],
            bytes[offset + 3],
        ])
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn raw_sha3_256_matches_empty_test_vector() {
        let digest = raw_sha3_256(b"");
        let expected = [
            0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66, 0x51, 0xc1, 0x47, 0x56, 0xa0, 0x61,
            0xd6, 0x62, 0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa, 0x82, 0xd8, 0x0a, 0x4b,
            0x80, 0xf8, 0x43, 0x4a,
        ];
        assert_eq!(digest, expected);
    }

    #[test]
    fn field_digest_round_trips_through_u32_limbs() {
        let digest = sha3_256_field_element_digest(
            b"test",
            [Goldilocks::from_u64(1), Goldilocks::from_u64(2)],
        );
        let words = Sha3DigestWords::from_field_elements(&digest).unwrap();
        assert_eq!(words.len(), SHA3_256_DIGEST_U32_WORDS);
    }

    #[test]
    fn chain_update_depends_on_previous_digest() {
        let initial = sha3_256_chain_initial(b"chain-a");
        let other_initial = sha3_256_chain_initial(b"chain-b");
        let update = sha3_256_chain_update_fields(b"chain-a", &initial, [Goldilocks::from_u64(7)]);
        let other_update =
            sha3_256_chain_update_fields(b"chain-a", &other_initial, [Goldilocks::from_u64(7)]);
        assert_ne!(update, other_update);
    }
}
