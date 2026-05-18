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
- Negacyclic polynomial arithmetic in `F_q[X] / (X^N + 1)`, including a
  twisted Goldilocks NTT path.
- LWE and GLWE encryption/decryption with zero-noise semantics for now.
- GLev/GGSW structures for exact toy decomposition.
- External product and CMUX, with coefficient-key and NTT-key variants.
- Blind rotation and `bootstrap_without_keyswitch`, including an
  NTT-domain bootstrapping-key path.
- Sample extraction to an LWE ciphertext under the extracted GLWE key.

`bootstrap_without_keyswitch` deliberately stops before the final TFHE
key-switch. The output decrypts under `SecretKey::extracted_output_lwe_key()`.

## Current Proof Coverage

- Plonky3 circuit for public negacyclic polynomial multiplication over
  Goldilocks.
- Plonky3 circuit for public `mul_xai`, the negacyclic monomial rotation used
  by blind rotation.
- Plonky3 circuit for public GLWE index-zero sample extraction to LWE.
- Plonky3 PBS PoC for the native nonzero-mask `bootstrap_without_keyswitch`
  path. This includes `mul_xai`, CMUX, GGSW external product, exact gadget
  decomposition with in-circuit bit range checks, and sample extraction.
- The PBS circuit consumes the bootstrapping key in twisted NTT form, matching
  the TFHEpp-style transformed-key path and avoiding a key-side NTT inside each
  polynomial product.
- Batch STARK prove/verify wrappers for these circuits.
- CLI smoke test:

```bash
cargo run -p tfheprus-cli -- prove-poly-mul
cargo run -p tfheprus-cli -- prove-mul-xai
cargo run -p tfheprus-cli -- prove-sample-extract
cargo run -p tfheprus-cli -- run-actual-pbs-native
cargo run -p tfheprus-cli -- prove-actual-pbs
```

The current actual PBS proof uses `Params::toy()` while exercising every LWE
mask rotation. The previous all-zero-mask proof path was removed because it
skipped CMUX/external-product work.

On the current runner, `cargo run --release -p tfheprus-cli --
run-actual-pbs-native` completed the coefficient-key PBS in
`native_coeff_us=746`, converted the bootstrapping key to NTT form in
`key_ntt_precompute_us=189`, and completed the online NTT-key PBS in
`native_ntt_us=557`. `cargo run --release -p tfheprus-cli --
prove-actual-pbs` completed with `prove_us=725007` and `verify_us=7742`.
These are still `Params::toy()` timings; at degree 8, NTT overhead dominates
the native run, while the proof circuit already benefits from removing the
key-side transform.

## Validation

Run:

```bash
cargo fmt --check
cargo check --workspace
cargo test
cargo clippy --workspace --all-targets -- -D warnings
```
