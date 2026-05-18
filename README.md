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
- Batch STARK prove/verify wrapper for the polynomial multiplication circuit.
- CLI smoke test:

```bash
cargo run -p tfheprus-cli -- prove-poly-mul
```

## Validation

Run:

```bash
cargo fmt --check
cargo check --workspace
cargo test
cargo clippy --workspace --all-targets -- -D warnings
```
