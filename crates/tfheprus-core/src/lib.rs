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
pub mod params;
pub mod pbs;
pub mod poly;
pub mod serialization;

pub use field::{Goldilocks, GOLDILOCKS_MODULUS};
pub use ggsw::{external_product, GgswCiphertext};
pub use glev::{decompose_polynomial, GlevCiphertext};
pub use glwe::{sample_extract_index_zero, GlweCiphertext, GlweSecretKey};
pub use keys::{EvaluationKey, SecretKey};
pub use lwe::{decode_message, encode_message, LweCiphertext, LweSecretKey};
pub use params::Params;
pub use pbs::{blind_rotate, bootstrap_without_keyswitch, mod_switch_to_exponent, TestPolynomial};
pub use poly::Polynomial;
