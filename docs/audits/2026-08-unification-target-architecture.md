# Unification target architecture — Phase 0 memo (measured 2026-08-28)

This memo is the Phase 0 deliverable of the semantics-gap closure campaign approved 2026-08-28.
The campaign's north star: **one unified, auditable AIR-ensemble model in Clean, with one spec
that genuinely implies a RISC-V (Sail) execution** — retiring the current native-53-table vs
exact-34+6 split. Recursion, ArkLib, and LogUp/GKR remain named crypto-boundary premises. This
memo records what the candidate target architecture actually is, what is measured fact versus
open decision, and the sequencing consequences for the campaign's three tracks.

Companion decisions taken with the owner in the same session (recorded here so later PRs cite one
place): halt modeling is **real-handler-first** (time-model unification, then a genuine
`ExecutableSyscallHandler` HALT arm; no invented native halt chip); public values widen in place
by `exit_code`, `is_execution_shard`, and `committed_value_digest`; the shard-level capstone stays
the headline theorem (shards need not halt; recursion composes shards), with the single-shard
boot→halt statement as a named corollary.

## 1. Measured facts (sibling `sp1` checkout, fetched 2026-08-28)

### 1.1 `v6.5.0` is public but carries no AIR change

- Tag `v6.5.0` = `92b8eabaea9ab7306da5826caa700adabf7445ba` (2026-08-26), **6 commits** over
  `v6.4.0`: SDK mTLS client-identity support and a dalek Edwards-arithmetic perf change.
- `git diff --stat v6.4.0..v6.5.0 -- crates/core crates/hypercube crates/machine`: 5 files,
  15 insertions — `utils/mod.rs` and `verifier/hashable_key.rs` housekeeping. **No chip, bus,
  interaction, or public-values change.** A re-pin `v6.4.0 → v6.5.0` would be a version bump with
  zero semantic content; it is not the "v6.5.0 architecture".

### 1.2 The Merkle architecture is real, but still private-only

- `sp1-private@main` = `b0ba1484e57c60f196dbf14c05d8bb68dab6ab14` (2026-08-26), 77 commits ahead
  of `v6.4.0`, and **contains `v6.5.0` as an ancestor** (upstream was merged into the private line
  2026-08-26). The Merkle-tree memory architecture exists only there; **no public release tag
  carries it.**
- Definitive supervisor-relevant `RiscvAir` variant delta `v6.4.0 → private/main`:
  - removed (9): `Global`, `MemoryGlobalInit`, `MemoryGlobalFinal`, `PageProtGlobalInit`,
    `PageProtGlobalFinal`, `SyscallCore`, `SyscallCoreUser`, `SyscallPrecompile`,
    `SyscallPrecompileUser`;
  - added (5): `MerkleTreeTraversal`, `LeafHash`, `LeafHashControl`, `HintRead`,
    `HintReadControl`.
- **`SyscallInstrsChip` is byte-identical** between `v6.4.0` and `private/main`
  (`git diff --stat` over `crates/core/machine/src/syscall/instructions/` is empty). The ECALL
  instruction-row AIR — the eventual halt/COMMIT source — is stable across both architectures.
- The 25 instruction chips and their four buses remain untouched (re-confirming the 2026-08-19
  drift measurement in `docs/agents/extraction.md`).

### 1.3 Cluster composition keeps the 34+6 shape, with cleaner contents

On `private/main` (`crates/core/machine/src/riscv/mod.rs`), supervisor mode:

- **Execution cluster (34 tables)** = preprocessed `{Program, ByteLookup, RangeLookup}` + the 25
  instruction chips + `SyscallInstrs` + `MemoryBump` + `StateBump` + `MemoryLocal` + `HintRead` +
  `HintReadControl`.
- **Memory cluster (6 tables)** = preprocessed `{Program, ByteLookup, RangeLookup}` +
  `LeafHash` + `LeafHashControl` + `MerkleTreeTraversal`.

The `Global` septic-accumulation table, the global memory/page-prot boundary chains, and the
syscall transcript tables are gone from both clusters. `InstructionFetch`/`InstructionDecode`
appear only in the user-mode (`mprotect`) cluster; the supervisor profile is unaffected.

### 1.4 Public-values record is redesigned

`crates/hypercube/src/air/public_values.rs`, `v6.4.0 → private/main`:

- **Added**: `prev_merkle_root`/`merkle_root` (`[T; POSEIDON_NUM_WORDS]` each — the memory
  boundary is now a Merkle root pair), and trace-chunk sharding fields (`trace_chunk_idx` +
  inverse + zero flag, `shard_index` + inverse + zero flag, `num_merkle_shard`,
  `num_execution_shard`, `inv_num_shards`); `is_first_execution_shard` becomes `is_first_shard`.
- **Removed**: the eight `previous/last_{init,finalize}_{addr,page_idx}` chain fields, the five
  `global_*_count` fields, `global_cumulative_sum : SepticDigest` (the septic-curve layer leaves
  the public surface entirely), and `initial_timestamp_inv`.
- **Survive unchanged**: `committed_value_digest` (+prev), `deferred_proofs_digest` (+prev),
  `exit_code`, `is_execution_shard`, `pc_start`/`next_pc`, the timestamp block, the
  `commit_syscall`/`commit_deferred_syscall` flags, `proof_nonce`.

Consequence for PR 2.2 (public-values widening): the three fields the campaign adds to the native
`SP1StateBoundary` — `exit_code`, `is_execution_shard`, `committed_value_digest` — **all survive
the redesign**. Only their flat `toBaseVector` indices move; the widening PR should route every
index through the pinned-layout anchor lemmas so a re-pin changes one file.

### 1.5 The Merkle cluster is in-AIR Poseidon2

`crates/core/machine/src/memory/merkle/{leaf_hash,leaf_hash_controller,tree_traversal}.rs`
(618/­~250/462 lines): both `LeafHash` and `MerkleTreeTraversal` are built on the shared
`Poseidon2Operation` gadget (`WIDTH`, `NUM_EXTERNAL_ROUNDS`, 8-word digests) that the Poseidon2
precompile also uses. A native port is one shared Poseidon2 operation gadget plus three chips —
a real verification load, but a bounded and conventional one (operation gadget + `Spec` +
faithfulness anchors, the standard chip recipe), not an open-ended cluster.

## 2. Consequences for the campaign tracks

- **Track 1 (statement clarity)** is fully drift-stable: it touches the conclusion shape, the
  boundary premise structure, and proof-artifact segregation — none of which reference the
  system tables. Proceed immediately.
- **Track 2 (model expansion)** is drift-stable end to end: the halt AIR source
  (`SyscallInstrs`) is byte-identical across architectures, and the three widening fields
  survive the public-values redesign. The time-model unification (PR 2.3) and handler work
  (PR 2.4) need no architecture decision.
- **Track 3 (ensemble unification)** is where the architecture decision bites; see §3.
- **What the Merkle cluster makes derivable** (to be confirmed in the PR 3.2 design): memory
  init/finalize *values* become in-AIR facts chained to `merkle_root` through Poseidon2 leaf
  hashes and tree traversal, and per-location *uniqueness* gets a tree-path mechanism instead of
  the retired strictly-increasing byte-address chain. That is exactly the shape of the four
  `ProviderBindingContracts` fields the native relation currently assumes; the root↔vkey binding
  joins `PreprocessedBinding` as a named crypto premise. The "per-8-byte-cell vs byte-address
  granularity" residual dissolves with the address chain that created it — the leaf granularity
  is the page/word structure of the tree, assessed concretely in the 3.2 design.

## 3. The open owner decision: pin base for Track 3

The extraction doctrine (`docs/agents/extraction.md`) requires a pin that is public, released,
and externally reproducible; `v6.4.0` qualifies. The Merkle architecture today exists only on
`sp1-private@main`, which is none of those things — and is still moving (13 commits between the
2026-08-19 drift measurement and 2026-08-26).

Options:

1. **Wait for the public release that ships the Merkle architecture** (recommended default).
   Track 3.1's re-pin lands then; meanwhile the PR 3.2 *design* (native chip shapes, `Spec`
   vocabulary, which provider contracts become theorems) is written against `private/main` and
   noted as provisional. Tracks 1–2 are unaffected either way.
2. **Pin to a committed `sp1-private` commit now.** Gets Track 3 moving immediately at the cost
   of the external-reproducibility property of the extraction gate — a change to the disclosed
   trust story (`docs/release-audit.md`), not just a config edit. Requires an explicit owner
   sign-off recorded in the release audit, and accepts re-derivation risk while the private line
   is still churning.
3. **Interim bump `v6.4.0 → v6.5.0`.** Nearly free (no AIR delta) but also nearly pointless;
   only worth folding into the next scheduled extraction-pin maintenance, not a campaign step.

Sequencing under option 1: Phase 0 (this memo) → Track 1 and Track 2 PRs proceed now →
PR 3.2 design doc against `private/main` → re-pin + re-extract (3.1) at the public release →
3.2/3.3 land. The go/no-go entry in `docs/roadmap.md` § 2 records this.

## 4. What this memo deliberately does not do

It does not modify any Lean statement, does not touch the extraction pin, and does not claim the
Merkle-line measurements are stable — they are dated observations of a private branch, and every
number here must be re-measured at the public release before Track 3.1 executes. The
authoritative finding trackers for the existing audit campaigns remain
`docs/audits/2026-08-pr110-external-report-disposition.md` and
`docs/audits/2026-08-independent-semantic-audit.md`; this memo adds the unification campaign's
architecture baseline without superseding either.
