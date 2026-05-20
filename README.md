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
- LWE and GLWE encryption/decryption with centered-binomial noise by default
  (`centered_binomial_terms=32`). Exact/noise-zero constructors are kept only
  for trivial public ciphertexts and algebraic test fixtures.
- GLev/GGSW structures for exact toy decomposition and native paper-style
  approximate decomposition (`B=2^5, l=4` in `Params::paper_v1()`).
- External product and CMUX, with coefficient-key and NTT-key variants.
- Blind rotation and `bootstrap_without_keyswitch`, including an
  NTT-domain bootstrapping-key path.
- Sample extraction to an LWE ciphertext under the extracted GLWE key, plus a
  paper-style GLWE key switch whose target key makes the first `n` GLWE mask
  coefficients a ciphertext under the original input LWE key.

`bootstrap_without_keyswitch` deliberately exposes the pre-key-switch PBS
output under `SecretKey::extracted_output_lwe_key()`. The native key-switch
helpers can then switch the final accumulator to an extraction-compatible GLWE
key derived from `SecretKey::input_lwe`.

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
  the chained PBS path below is the preferred Poseidon2 hash-chain statement.
- Plonky3 chained PBS-step PoC. The selected GGSW ciphertext and the LWE mask
  element are private witnesses, and the public statement carries Plonky3-native
  Goldilocks Poseidon2 BSK-chain and ciphertext-mask-chain digest transitions
  plus accumulator endpoints.
- Plonky3 chained PBS chunk PoC. Multiple consecutive blind-rotation steps can
  be composed inside one proof with only the chunk input/output accumulator and
  digest endpoints public.
- Plonky3 recursive verifier PoC for a chained PBS chunk proof. This proves and
  verifies the verifier for a real private-mask/private-selector PBS chunk
  proof, using a TFHEprus-local Goldilocks STARK config with capped Merkle
  commitments.
- Chunked recursive PBS prefix driver. Consecutive chunks carry forward the
  accumulator, BSK digest, and ciphertext-mask digest, so the proof list can
  cover a prefix or the full blind rotation without regenerating keys per chunk.
- Public-statement verifier path for recursive PBS chunks. Verification of the
  chunk proof no longer needs the private selected GGSW ciphertexts or mask
  values; it checks params, chunk length, public accumulator endpoints, and
  digest-chain endpoints. The verifier rebuilds the expected chunk circuit from
  params and chunk length and rejects proofs with mismatched circuit metadata.
- Recursive aggregation for PBS chunks. Recursive chunk proofs can be reduced
  through a carry-up aggregation tree, including non-power-of-two chunk counts
  needed by practical paper-v1 schedules.
- Root-summary verification for recursive PBS aggregation. The tree wrapper can
  be consumed into a root proof plus the public PBS-chain summary, letting the
  verifier check the aggregate root without receiving all leaf and intermediate
  proofs.
- Postcard serialization for the recursive PBS root proof. The tree CLI
  round-trips the root artifact through bytes before root verification and
  reports the serialized size.
- Checkpoint artifacts for recursive PBS proving. Individual recursive chunk
  leaves can be written to disk, later aggregated into a serialized root proof,
  and verified independently from the root artifact.
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
cargo run --release -p tfheprus-cli -- prove-glwe-keyswitch paper-v1
cargo run --release -p tfheprus-cli -- prove-compact-root-keyswitch target/pbs-checkpoints-paper-v1-private-compact-current-c8/compact/root.bin
cargo run -p tfheprus-cli -- prove-pbs-step paper-v1
cargo run -p tfheprus-cli -- prove-pbs-step-private paper-v1
cargo run -p tfheprus-cli -- prove-pbs-step-chain paper-v1
cargo run -p tfheprus-cli -- prove-pbs-chain-chunk paper-v1 2
cargo run --release -p tfheprus-cli -- prove-pbs-chain-chunk-recursive toy 1
cargo run --release -p tfheprus-cli -- prove-pbs-chain-prefix-recursive toy 2
cargo run --release -p tfheprus-cli -- prove-pbs-chain-prefix-recursive paper-v1 2 4
cargo run --release -p tfheprus-cli -- prove-pbs-chain-pair-aggregate-recursive toy 2
cargo run --release -p tfheprus-cli -- prove-pbs-chain-pair-aggregate-recursive paper-v1 1
cargo run --release -p tfheprus-cli -- prove-pbs-chain-tree-aggregate-recursive toy 2 4
cargo run --release -p tfheprus-cli -- prove-pbs-chain-tree-aggregate-recursive paper-v1 1 3
mkdir -p target/pbs-checkpoints
cargo run --release -p tfheprus-cli -- prove-pbs-chain-leaves-recursive toy 2 2 target/pbs-checkpoints
cargo run --release -p tfheprus-cli -- prove-pbs-chain-leaf-recursive toy 2 0 target/pbs-checkpoints/toy-leaf-0.bin
cargo run --release -p tfheprus-cli -- prove-pbs-chain-leaf-recursive toy 2 1 target/pbs-checkpoints/toy-leaf-1.bin
cargo run --release -p tfheprus-cli -- aggregate-pbs-chain-leaves-recursive target/pbs-checkpoints/toy-root.bin target/pbs-checkpoints/toy-leaf-0.bin target/pbs-checkpoints/toy-leaf-1.bin
cargo run --release -p tfheprus-cli -- aggregate-pbs-chain-leaf-dir-recursive target/pbs-checkpoints/toy-root-from-dir.bin target/pbs-checkpoints 2
cargo run --release -p tfheprus-cli -- verify-pbs-chain-root-artifact-recursive target/pbs-checkpoints/toy-root.bin
cargo run --release -p tfheprus-cli -- profile-pbs-chain-leaf-cost paper-v1 8 shape
cargo run --release -p tfheprus-cli -- profile-pbs-chain-leaf-cost paper-v1 8 prove
cargo run -p tfheprus-cli -- profile-pbs-chain-tree paper-v1 8 728
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
`eval_keygen_us=930982`, `key_ntt_precompute_us=489200`,
`native_ntt_us=882475`, `glwe_ks_keygen_us=889`, and
`glwe_keyswitch_us=632` under the centered-binomial default noise, decrypting
both the extracted-key output and the key-switched original-key output to
message `3`. The paper-v1 monolithic proof command remains disabled because
the PBS proof path is split into recursive/chunked proofs.

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
to prove the statement shape and public-value binding. The chained PBS path now
uses the same Plonky3-friendly Poseidon2 family as the recursive verifier, so
the high-volume BSK/mask commitment chain no longer depends on the older
algebraic selector digest.

The chained step moves closer to the IVC statement in the paper:
`cargo run --release -p tfheprus-cli -- prove-pbs-step-chain paper-v1` keeps
both the selected GGSW ciphertext and the LWE mask element private, while public
inputs carry the input/output accumulator and BSK/ciphertext digest transitions.
On the current runner it verified with `public_inputs=4112`,
`private_inputs=28737`, `prove_us=23380094`, and `verify_us=19191`.

The chained chunk proof composes consecutive private-mask/private-selector
steps while keeping only the chunk endpoints public. On the current runner,
`cargo run --release -p tfheprus-cli -- prove-pbs-chain-chunk paper-v1 2`
verified two paper-shaped steps with `public_inputs=4112`,
`private_inputs=57474`, `prove_us=47030295`, and `verify_us=19652`.

The recursive verifier path is live for the chained chunk statement:
`cargo run --release -p tfheprus-cli -- prove-pbs-chain-chunk-recursive toy 1`
proved and verified the recursive verifier for one actual PBS chunk step with
`base_public_inputs=48`, `base_private_inputs=257`,
`recursive_public_inputs=107`, `prove_us=5994080`, and `verify_us=93789`.
Paper-shaped recursive chunk proofs also run: `paper-v1 1` verified with
`recursive_public_inputs=8313`, `chain_summary_fields=4119`,
`prove_us=35046039`, and `verify_us=7745859`; `paper-v1 2` verified with
`base_private_inputs=57474`, `recursive_public_inputs=8313`,
`chain_summary_fields=4119`, `prove_us=58357036`, and
`verify_us=15467881`.

The chunked recursive prefix driver verifies consecutive recursive chunk proofs
while carrying accumulator and digest-chain state across chunk boundaries.
`cargo run --release -p tfheprus-cli -- prove-pbs-chain-prefix-recursive toy 2`
covered all 8 toy blind-rotation steps as 4 recursive chunks and matched the
native NTT PBS output, decrypting `full_prefix_output_message=3`. It took
`total_prove_us=24220579` and `total_verify_us=380389`. The paper-shaped prefix
smoke `paper-v1 2 4` covered 4 consecutive steps as 2 recursive chunks; after
adding the public PBS-chain summary suffix, each two-step paper chunk uses
`recursive_public_inputs=8313`, `chain_summary_fields=4119`, and
`base_private_inputs=57474`.
The recursive chunk CLI uses the public-statement verifier path, so the
verification step is based on public endpoints and digest commitments rather
than the private chunk witness. A larger `paper-v1 4` recursive chunk verified
with `base_private_inputs=114948`, `recursive_public_inputs=4204`,
`prove_us=106519302`, and `verify_us=299286`.

The first aggregation layer is live for recursive chunk proofs:
`cargo run --release -p tfheprus-cli --
prove-pbs-chain-pair-aggregate-recursive toy 2` covered steps `0..4` as two
recursive two-step chunks and aggregated them with `aggregate_public_inputs=871`,
`chain_summary_fields=55`, `aggregate_prove_us=11945243`, and
`verify_us=455298`. The same path works at paper shape: `paper-v1 1` covered
steps `0..2` as two one-step chunks and aggregated them with
`aggregate_public_inputs=37509`, `chain_summary_fields=4119`,
`aggregate_prove_us=13614488`, and `verify_us=15833332`.

The recursive aggregation tree now reduces more than two chunk proofs to one
root and carries odd nodes upward, so it does not require a power-of-two leaf
count. `cargo run --release -p tfheprus-cli --
prove-pbs-chain-tree-aggregate-recursive toy 2 4` covered all 8 toy PBS steps
as four two-step chunks, matched the native NTT PBS output with
`full_tree_output_message=3`, and produced a two-layer tree with
`layer_sizes=[2,1]`, `root_public_inputs=3677`, `chain_summary_fields=55`,
`aggregate_prove_us=35718963`, `verify_us=1131511`, `root_verify_us=16392`,
and `root_proof_bytes=974226`. The odd-leaf path also
works at paper shape: `paper-v1 1 3` covered three one-step chunks with
`layer_sizes=[1,1]`, `root_public_inputs=95906`,
`chain_summary_fields=4119`, `leaf_prove_us=105193825`,
`aggregate_prove_us=32714973`, `verify_us=24141059`,
`root_verify_us=38496`, and `root_proof_bytes=1743707`. Tree verification now
also checks that public chunk statements form one continuous PBS chain: matching
params, bounded total step count, accumulator handoff, BSK digest handoff, and
mask digest handoff. The recursive leaf and aggregate circuits expose this
PBS-chain summary as public inputs and constrain summary composition in-circuit.
The CLI also serializes the root-only package, decodes it, and verifies the
decoded aggregate root proof against the public chain summary without
re-verifying all children from the high-level wrapper.

The checkpoint path works on serialized recursive leaf artifacts. The
single-leaf command can prove an arbitrary chunk by index, while
`prove-pbs-chain-leaves-recursive` carries the accumulator and digest state
forward sequentially and reuses existing verified leaf files in the output
directory. On the current runner, a fresh `toy 2 2` leaf-directory run wrote two
artifacts for steps `0..2` and `2..4` with `total_artifact_bytes=3025994`,
`total_prove_us=12251458`, and `total_verify_us=267785`; the immediate rerun
reused both artifacts with `written=0`, `reused=2`, `total_prove_us=0`, and
`total_verify_us=338750`. Aggregating those two leaf files with
`aggregate-pbs-chain-leaves-recursive` produced a one-layer root with
`root_public_inputs=871`, `chain_summary_fields=55`,
`aggregate_us=11982676`, `verify_us=478890`, `root_verify_us=14925`, and
`root_artifact_bytes=906094`. The directory aggregator now writes recursive
aggregation checkpoints under `<leaf_dir>/aggregation`, so interrupted runs can
resume from the last completed layer node instead of rebuilding the whole tree.
It can consume the same checkpoint directory either with an explicit leaf count
or by scanning sorted `leaf-*.bin` files; the explicit-count smoke produced
`aggregate_us=12102511`, `root_verify_us=15051`, and
`root_artifact_bytes=906094`, and an immediate rerun reused the layer checkpoint
with `aggregate_us=0` and `root_verify_us=17725`.
`verify-pbs-chain-root-artifact-recursive` verified the resulting root artifact
from disk with `verify_us=15878`. The deserializer rehydrates lookup metadata
that Plonky3 native verification can rebuild internally but recursive verifier
circuit construction needs explicitly.

For planning full paper-v1 runs without allocating keys or proving, the tree
profiler reports the chunk schedule and leaf statement sizes. `cargo run -p
tfheprus-cli -- profile-pbs-chain-tree paper-v1 8 728` yields `chunk_count=91`,
`tree_depth=7`, `aggregation_nodes=90`, `layer_sizes=[45,23,11,6,3,1,1]`,
`chunk_public_inputs=4112`, `chain_summary_fields=4119`,
`step_private_inputs=28737`,
`full_chunk_private_inputs=229896`, and
`total_leaf_private_inputs=20920536`.

The full paper-v1 leaf checkpoint run completed for `chunk_steps=8` and
`chunk_count=91`, covering all 728 blind-rotation steps. It reused one existing
leaf, wrote 90 new leaves, and reported
`total_artifact_bytes=231710346`, `total_prove_us=18068542366`,
`total_verify_us=5668620773`, `max_base_private_inputs=229896`, and
`max_recursive_public_inputs=8318`. Binary recursive aggregation then completed
layers `[45,23,11,6]` and wrote 85 aggregate checkpoints, but the first
layer-4 node was killed after reaching about 28.5 GiB RSS. The practical
artifact for the current Plonky3-recursion path is therefore a frontier package:
`package-pbs-chain-frontier-dir-recursive
target/pbs-checkpoints-paper-v1-c8/frontier-layer3.bin
target/pbs-checkpoints-paper-v1-c8/aggregation/layer-003` packages the six
layer-3 proofs into an 82,002,970-byte artifact, and
`verify-pbs-chain-frontier-artifact-recursive` verifies it with `params_n=728`,
`total_steps=728`, `chain_summary_fields=4119`,
`total_public_inputs=13897142`, `max_public_inputs=2491473`, and
`verify_us=4083332`.

Current paper-style PBS IVC PoC: the compact-private recursive path proves
leaves and aggregates with summary-only public inputs, and the PBS BSK/mask
chain uses Plonky3-friendly Goldilocks Poseidon2 rather than SHA3. A fresh
post-NTT-accumulation run of
`bench-pbs-chain-private-compact paper-v1 16 46` with `RAYON_NUM_THREADS=16`
proved all 728 paper-v1 blind-rotation steps as 45 full 16-step leaves plus
one 8-step tail, matched the native NTT PBS output with
`full_compact_leaf_checkpoint_output_message=3`, aggregated 46 leaves through
45 compact recursive aggregate nodes, serialized
`target/pbs-checkpoints-paper-v1-private-compact-nttacc-c16/compact/root.bin`,
and verified the root artifact with `params_n=728`, `total_steps=728`,
`root_public_inputs=31`, `compact_summary_fields=31`, and `verify_us=3446`.
The run reported `total_us=1023183370`, leaf `total_prove_us=935140075`,
`aggregate_us=78855821`, `leaf_artifact_bytes=82194321`,
`aggregate_artifact_bytes=8062932`, and `root_artifact_bytes=178988`.
The leaf-cost profiler is available for the next optimization pass:
`profile-pbs-chain-leaf-cost paper-v1 8 shape` reports an 8-step leaf with
`total_ops=2760852`, `witness_count=2840740`, `private_inputs=229896`,
`alu_rows=2639920`, `digit_ntts=64`, `inverse_ntts=32`,
`digit_range_checks=65536`, and `error_range_checks=16384`.
`profile-pbs-chain-leaf-cost paper-v1 8 prove` verified the base 8-step leaf
with `build_us=947097`, `air_prep_us=528048`, `prover_data_us=2733711`,
`witness_run_us=209248`, `prove_us=7260047`, and `verify_us=25146`. Since
paper-v1 uses 91 same-shaped leaves, the compact recursive leaf batch path now
caches both the base leaf prover data and the private compact recursive-wrapper
prover data for newly written leaves.
A two-leaf cached paper-v1 smoke run
`prove-pbs-chain-private-leaves-compact-fast paper-v1 8 2` reported
`prove_us=18567713` for the first leaf, including one-time prover setup, and
`prove_us=12819439` for the second steady-state leaf. Extrapolated over 91
same-shaped leaves this is roughly 1172 seconds before aggregation, compared
with the previously recorded 2621-second leaf total.
Leaf checkpoint commands now accept a final partial chunk, so `paper-v1 16 46`
covers all 728 steps as 45 full 16-step leaves plus one 8-step tail. A
two-leaf `paper-v1 16 2` smoke run reported `prove_us=30410937` for the first
leaf and `prove_us=19847131` for the second steady-state leaf. The full c16
run above keeps the steady full-leaf cost near 20 seconds and the partial tail
at `prove_us=18582700`.
The recursive STARK configs use capped Merkle commitments
(`MERKLE_CAP_HEIGHT=2`), including a zero-depth capped MMCS verifier regression
test for the case where the cap covers the whole opening path.

The paper-style GLWE key-switch arithmetic is also proven as a standalone
paper-v1 proof:
`cargo run --release -p tfheprus-cli -- prove-glwe-keyswitch paper-v1`
verified on the noisy default material path with `public_inputs=10969`,
`private_inputs=6144`, `proof_bytes=1161034`, `prove_us=638110`,
`verify_us=21800`, and `keyswitched_output_message=3`. The private-KSK digest
variant
`cargo run --release -p tfheprus-cli -- bench-glwe-keyswitch-modes paper-v1`
reduced public inputs to `2781`, but increased proof size to
`1271582` bytes and was slower in this run (`prove_us=658246`), so the faster
combined path currently keeps the KSK public. The combined command
`prove-compact-root-keyswitch
target/pbs-checkpoints-paper-v1-private-compact-nttacc-c16/compact/root.bin`
verifies the compact recursive root, checks the key-switch input accumulator
against the root output-accumulator digest, proves and verifies the final GLWE
key switch, and decrypts the final ciphertext under the original input LWE key
with `key_switch_prove_us=674661`, `key_switch_verify_us=21813`, and
`keyswitched_output_message=3`.

The one-artifact recursive PBS-plus-key-switch path is:
`cargo run --release -p tfheprus-cli --
prove-compact-root-keyswitch-recursive
target/pbs-checkpoints-paper-v1-private-compact-nttacc-c16/compact/root.bin
target/pbs-checkpoints-paper-v1-private-compact-nttacc-c16/compact/root-keyswitch-final.bin`,
followed by `cargo run --release -p tfheprus-cli --
verify-compact-root-keyswitch-recursive
target/pbs-checkpoints-paper-v1-private-compact-nttacc-c16/compact/root-keyswitch-final.bin`.
This final recursive proof privately verifies the compact PBS root proof and the
GLWE key-switch proof, links the key-switch input accumulator digest to the PBS
root output digest in-circuit, and exposes only the compact PBS summary plus the
final output LWE fields. On the current runner it wrote a 228437-byte artifact
with `final_public_inputs=760`, `recursive_prove_us=9753048`,
`recursive_verify_us=4201`, standalone artifact `verify_us=6087`, and
`keyswitched_output_message=3`. Regenerate compact root artifacts after changes
to the default encryption material, because the root digest binds the exact
noisy ciphertext values.

## Validation

Run:

```bash
cargo fmt --check
cargo check --workspace
cargo test
cargo clippy --workspace --all-targets -- -D warnings
```

The compact-private recursive PBS smoke test is ignored by default because it
proves two recursive leaves plus one aggregate proof:

```bash
cargo test --release -p tfheprus-prover \
  compact_recursive_private_pbs_public_inputs_remain_summary_only -- --ignored --nocapture
cargo test -p tfheprus-prover \
  compact_pbs_root_and_keyswitch_are_one_recursive_proof -- --ignored --nocapture
```
