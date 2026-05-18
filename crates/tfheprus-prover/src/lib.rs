//! Recursive prove/verify proof-of-concept entry points.
//!
//! The first implementation milestone is native correctness in
//! `tfheprus-core`; Plonky3 recursion will be added here after the circuit
//! kernels exist.

pub fn crate_ready() -> bool {
    tfheprus_circuits::crate_ready()
}
