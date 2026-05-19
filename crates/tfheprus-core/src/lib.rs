//! Native, Plonky3-friendly TFHE building blocks over the Goldilocks field.
//!
//! This crate intentionally implements only the TFHE subset needed by the
//! programmable-bootstrapping proof of concept. It is not a full TFHE library.

pub mod field;
pub mod ggsw;
pub mod glev;
pub mod glwe;
pub mod keys;
pub mod lwe;
pub mod ntt;
pub mod params;
pub mod pbs;
pub mod poly;
pub mod serialization;
pub mod sha3_commit;

pub use field::{Goldilocks, GOLDILOCKS_MODULUS};
pub use ggsw::{external_product, external_product_ntt, GgswCiphertext, GgswCiphertextNtt};
pub use glev::{
    decompose_polynomial, decompose_scalar, decomposition_gadget_factor, GlevCiphertext,
    GlevCiphertextNtt,
};
pub use glwe::{sample_extract_index_zero, GlweCiphertext, GlweCiphertextNtt, GlweSecretKey};
pub use keys::{EvaluationKey, EvaluationKeyNtt, SecretKey};
pub use lwe::{decode_message, encode_message, LweCiphertext, LweSecretKey};
pub use ntt::{
    negacyclic_intt, negacyclic_mul_ntt, negacyclic_ntt, ntt, primitive_power_of_two_root,
    GOLDILOCKS_TWO_ADICITY,
};
pub use params::Params;
pub use pbs::{
    blind_rotate, blind_rotate_ntt, bootstrap_without_keyswitch, bootstrap_without_keyswitch_ntt,
    mod_switch_to_exponent, TestPolynomial,
};
pub use poly::{NttPolynomial, Polynomial};
pub use sha3_commit::{
    raw_sha3_256, sha3_256_bytes, sha3_256_chain_initial, sha3_256_chain_update_fields,
    sha3_256_field_element_digest, sha3_256_field_elements, Sha3DigestWords, SHA3_256_DIGEST_BYTES,
    SHA3_256_DIGEST_FIELD_ELEMENTS, SHA3_256_DIGEST_U32_WORDS,
};
