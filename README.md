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
- GLev/GGSW structures for exact toy decomposition and native paper-style
  approximate decomposition (`B=2^5, l=4` in `Params::paper_v1()`).
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
  decomposition, paper-style approximate gadget decomposition with bounded
  reconstruction error, table-backed range checks, and sample extraction.
- Plonky3 PBS-step PoC for a single blind-rotation CMUX iteration. This is the
  current leaf circuit for the recursive/chunked PBS direction.
- Plonky3 private-selector PBS-step PoC. The selected GGSW ciphertext is now a
  private witness in this leaf, with a small public algebraic digest binding the
  NTT-domain selector used by CMUX. This matches the paper direction of keeping
  bootstrapping-key material private behind compact public commitments, although
  it is not yet the final recursive Poseidon/hash-chain construction.
- The PBS circuit derives the rounded mod-switch rotation bits from the public
  LWE body and mask values in-circuit; these values are no longer only
  statement-specific compile-time rotation constants.
- The PBS circuit consumes the bootstrapping key in twisted NTT form, matching
  the TFHEpp-style transformed-key path and avoiding a key-side NTT inside each
  polynomial product.
- Circuit public inputs are bound into the batch-STARK Fiat-Shamir transcript
  through the primitive Public table, and verifier wrappers check that the
  embedded public statement matches the requested TFHEprus instance.
- Batch STARK prove/verify wrappers for these circuits.
- CLI smoke test:

```bash
cargo run -p tfheprus-cli -- prove-poly-mul
cargo run -p tfheprus-cli -- prove-mul-xai
cargo run -p tfheprus-cli -- prove-sample-extract
cargo run -p tfheprus-cli -- prove-pbs-step paper-v1
cargo run -p tfheprus-cli -- prove-pbs-step-private paper-v1
cargo run -p tfheprus-cli -- run-actual-pbs-native
cargo run -p tfheprus-cli -- profile-actual-pbs moderate
cargo run -p tfheprus-cli -- run-actual-pbs-native moderate
cargo run -p tfheprus-cli -- profile-actual-pbs paper-v1
cargo run -p tfheprus-cli -- run-actual-pbs-native paper-v1
cargo run -p tfheprus-cli -- prove-actual-pbs
```

The current actual PBS proof uses `Params::toy()` while exercising every LWE
mask rotation. The previous all-zero-mask proof path was removed because it
skipped CMUX/external-product work.

On the current runner, `cargo run --release -p tfheprus-cli --
run-actual-pbs-native` completed the coefficient-key PBS in
`native_coeff_us=826`, converted the bootstrapping key to NTT form in
`key_ntt_precompute_us=209`, and completed the online NTT-key PBS in
`native_ntt_us=515`. `cargo run --release -p tfheprus-cli --
prove-actual-pbs` completed with `prove_us=504195` and `verify_us=11456`.
These are still `Params::toy()` timings; at degree 8, NTT overhead dominates
the native run, while the proof circuit already benefits from removing the
key-side transform.

`Params::moderate_toy()` is available for native bottleneck checks. It uses
`n=32, N=64, k=1, B=2^16, l=4, p=4`, which is still an exact-decomposition
toy preset rather than a secure TFHE parameter set. On the current runner,
`profile-actual-pbs moderate` reports `public_inputs=32930` and
`private_inputs=18496`. `run-actual-pbs-native moderate` completed with
`eval_keygen_us=4631`, `native_coeff_us=7972`, `key_ntt_precompute_us=2239`,
and `native_ntt_us=4747`. The moderate proof command is intentionally not
enabled by default; this preset is for measuring native and statement-size
growth before attempting a much larger proof.

`Params::paper_v1()` exposes the paper-shaped PBS preset
`n=728, N=1024, k=1, B=2^5, l=4, p=4`. `profile-actual-pbs paper-v1` is a
lightweight estimator, so it does not allocate the full key just to count
wires. On the current runner it reports `bsk_public_inputs=11927552`,
`public_inputs=11930330`, `private_inputs=8992320`, and
`private_inputs_per_coeff=6` for approximate decomposition digits plus
error/sign witnesses. `run-actual-pbs-native paper-v1` skips the coefficient
reference run and completed the NTT-key native PBS with
`eval_keygen_us=942965`, `key_ntt_precompute_us=471961`, and
`native_ntt_us=842314`, decrypting the output message as expected. The
paper-v1 proof command remains disabled until the monolithic PBS circuit is
split into recursive/chunked proofs.

The single-step proof is available at paper shape. On the current runner,
`cargo run --release -p tfheprus-cli -- prove-pbs-step paper-v1` verified one
blind-rotation CMUX step with `public_inputs=20481`, `prove_us=11879152`, and
`verify_us=18639`. This is not yet a full recursive PBS proof; it is the leaf
proof needed before adding recursive verification and hash-chain binding across
all 728 steps.

The private-selector step is the next leaf shape for paper-style recursion:
`cargo run --release -p tfheprus-cli -- prove-pbs-step-private paper-v1` makes
the selected GGSW ciphertext private and replaces its 16384 public NTT
coefficients with a 4-field public digest. On the current runner it verified
with `public_inputs=4101`, `private_inputs=28736`, `prove_us=23295556`, and
`verify_us=18995`. The digest is an in-circuit Goldilocks algebraic sponge used
to prove the statement shape and public-value binding. A production security
path still needs the recursive hash-chain design from the paper, preferably with
the Plonky3 recursion hash used by the verifier.

## Validation

Run:

```bash
cargo fmt --check
cargo check --workspace
cargo test
cargo clippy --workspace --all-targets -- -D warnings
```
