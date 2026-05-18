# TFHEprus

TFHEprus is a Rust implementation of the TFHE subset needed for a
Plonky3-friendly programmable-bootstrapping proof of concept.

The project is intentionally not a full TFHE replacement. The native core uses
the Goldilocks modulus `2^64 - 2^32 + 1` and keeps the implementation simple
enough to mirror in Plonky3 circuits.

## Workspace

- `tfheprus-core`: native TFHE semantics over Goldilocks.
- `tfheprus-circuits`: Plonky3 circuit mirrors.
- `tfheprus-prover`: Plonky3 prove/verify PoC.
- `tfheprus-cli`: small command-line scaffold.

## Current Core Coverage

- Goldilocks field arithmetic.
- Negacyclic polynomial arithmetic in `F_q[X] / (X^N + 1)`.
- LWE and GLWE encryption/decryption with zero-noise semantics for now.
- GLev/GGSW structures for exact toy decomposition.
- External product and CMUX.
- Blind rotation and `bootstrap_without_keyswitch`.
- Sample extraction to an LWE ciphertext under the extracted GLWE key.

`bootstrap_without_keyswitch` deliberately stops before the final TFHE
key-switch. The output decrypts under `SecretKey::extracted_output_lwe_key()`.

## Current Proof Coverage

- Plonky3 circuit for public negacyclic polynomial multiplication over
  Goldilocks.
- Plonky3 circuit for public `mul_xai`, the negacyclic monomial rotation used
  by blind rotation.
- Plonky3 circuit for public GLWE index-zero sample extraction to LWE.
- Plonky3 PBS PoC for the native trivial-mask `bootstrap_without_keyswitch`
  path. This proves the all-zero LWE mask path that rotates the test polynomial
  by the body-derived exponent and sample-extracts the accumulator.
- Batch STARK prove/verify wrappers for these circuits.
- CLI smoke test:

```bash
cargo run -p tfheprus-cli -- prove-poly-mul
cargo run -p tfheprus-cli -- prove-mul-xai
cargo run -p tfheprus-cli -- prove-sample-extract
cargo run -p tfheprus-cli -- prove-trivial-pbs
cargo run -p tfheprus-cli -- prove-paper-pbs
```

`prove-paper-pbs` uses `Params::paper_v1()` and reports measured prove/verify
times. The reference paper reports 18 minutes prover time and 8 ms verifier time
on an Hpc7a.96xlarge for its full PBS implementation. This command is the
current trivial-mask PBS PoC at the same parameter shape; on the current runner,
`cargo run --release -p tfheprus-cli -- prove-paper-pbs` completed with
`prove_ms=125` and `verify_ms=6`.

## Validation

Run:

```bash
cargo fmt --check
cargo check --workspace
cargo test
cargo clippy --workspace --all-targets -- -D warnings
```
