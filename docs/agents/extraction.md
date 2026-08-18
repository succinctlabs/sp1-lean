# Constraint extraction (`update_extracted.py`)

How SP1's **complete table rows, `assertZero` lists, interaction lists, public-value block, machine
shape, and populate traces** enter this project. The stable AIR output is list-only: Lean gadgets and
circuits are proof-oriented implementation details under `Native/` and are never generated from Rust.
`update_extracted.py` still emits operation list modules during the chip-boundary migration, but those
are generator-private dependencies of current chip oracles, not public verification boundaries.

The upstream compiler emits field-generic Lean directly, so there is no Python rewriting of constraint
expressions. Python only selects targets, supplies reuse imports, wraps modules, and writes deterministic
files.

## The pipeline

```
RiscvAir::machine() ───────────────→ Extracted/CoreAIRManifest.lean
executor opcode.rs (semantic pin) ─→ Extracted/OpcodeTable.lean
Air::eval / eval_public_values ────→ Extracted/{ChipOracle,SystemOracle}/...
        (audited extraction branch)   (rows + ordered asserts/interactions only)

Native/ hand-written Clean circuits ─→ Faithful/<Chip>.lean (`ChipFaithful`)
Rust chip_traces (same pin) ────────→ export/sp1dump/<Chip>.dump.json
                                       (events + full generate_trace rows;
                                        sole writer scripts/update_sp1_dumps.sh)
```

Run it:

```sh
SP1_DIR=/path/to/extraction-branch-checkout python3 update_extracted.py
```

`SP1_DIR` must point at a **clean** checkout of the extraction branch pinned by `SP1_PINNED_COMMIT`
(`dtumad/lean-extraction` on `succinctlabs/sp1`, based directly on the v6.4.0 semantic tag) — every
extraction change is an ordinary commit on that branch; there is no uncommitted-patch mechanism. The
ordinary sibling `../sp1` checked out at that branch serves as both semantic source and extractor.
The generator verifies that the checkout's merge base with semantic revision
`f66b4bff51d0ccff51d152e0f7f66b2ffedf3529` (`v6.4.0`) is the semantic revision itself, that
machine-source changes are reflection metadata only against an explicit file allowlist, and that the
worktree is clean. `CHIPS` and `SYSTEM_TABLES` select AIR anchors; `OPERATIONS` is the
shared-substrate registry (the canonical reader modules + statement targets multiple chip anchors
reference; the whole-chip migration is complete, so it shrinks only when an anchor is actually
retired). This script emits **AIR artifacts only** — trace conformance lives in the dump-anchored
pipeline (`scripts/update_sp1_dumps.sh` + `scripts/witgenExport.lean --testdata` + the Rust
differential), not here. There is no circuit-output registry or circuit emitter. The output is
deterministic, so a full regeneration at the audited pin leaves all pre-existing anchors
byte-identical.

**Opcode table.** The `Opcode` enum's variant-name → `#[repr(u8)]`-discriminant table — the opcode
value every chip commits on the Program bus — is extracted unconditionally as
`SP1Clean/Extracted/OpcodeTable.lean` by a text-level parse (like the manifest writers, no cargo
run) of `crates/core/executor/src/opcode.rs` **at `SP1_SEMANTIC_COMMIT` via `git show`**, so it is
independent of the checkout's working state and reproducible at the pin. The parse fails
closed on shape drift (missing `pub enum Opcode` block or `#[repr(u8)]` attribute, no variants,
non-consecutive discriminants). The hand-maintained mirror `SP1Clean/Model/Opcode.lean` is
cross-checked against the extracted table by the kernel-`decide` theorem
`opcodeTable_matchesExtracted` (`SP1Clean/FormalModel/OpcodeTable.lean`): variant names (via the
adjacent `Opcode.name` string table — a derived `Repr` does not kernel-reduce), discriminants,
count, and order, so any mirror drift fails the build.

Profile extraction is unconditional, even under `EXTRACT_ONLY`: regeneration fails before writing AIR
files unless the baseline 34-table execution cluster, the 6-table memory-boundary cluster, every main
and preprocessed width, and the 160-cell public-value width match the audited manifest exactly. Requested
system tables, public values, and self-contained chip oracles are hard requirements; the script exits
nonzero rather than retaining a stale artifact.

## What the rust backend emits

For `--chip Add --format lean`, the compiler prints a whole-row fragment of this shape:

```lean
structure AddCols (F : Type) where
  state : CPUState F
  adapter : RTypeReader F
  add_operation : AddOperation F
  is_real : F

namespace AddCols

@[irreducible] def asserts {F : Type} [Field F] [CoeHead F ℕ]
    (cols : AddCols F) : List F :=
  helper.asserts … ++ reader.asserts … ++ [cols.is_real * (cols.is_real - 1), …]

@[irreducible] def interactions {F : Type} [Field F] [CoeHead F ℕ]
    (cols : AddCols F) : List (Interaction F) :=
  helper.interactions … ++ reader.interactions …

end AddCols
```

The two lists are the stable oracle. Calls to operation/reader helpers inside their generated bodies are
an emission detail; a chip anchor may unfold them locally. Canonical generated readers such as
`CPUState` and `RTypeReader` are imported once, including their generated helper functions; only
chip-private arithmetic helpers are embedded in the chip namespace. The goal is not to make any of
those Rust helpers match Lean gadgets.

### Audited Rust extraction branch

The extraction backend is not part of the semantic SP1 pin yet. Its exact review surface is the
**committed** delta of the pinned branch over the semantic revision (`f66b4bff5..b5616f908`,
`dtumad/lean-extraction` on `succinctlabs/sp1`): the reflection derives on the 26 machine files
(verified derive-line-only by `verify_extractor_overlay`), the field-generic Lean emission in the
hypercube IR, the whole-chip extraction modes in `main.rs`, and the `chip_traces` dump binary.
`Extracted/Provenance.lean` records the semantic revision and the branch revision. The series is
authored at upstream-PR quality; once it lands upstream, `SP1_PINNED_COMMIT` advances to an
upstream commit. The relevant changes are:

- **Field-generic, not `Fin KB`**. Every Lean-emission site writes the
  type token `F` instead of the concrete `Fin KB`:
  `crates/hypercube/src/ir/ast.rs` (let-step + call-output types),
  `expr.rs` / `var.rs` (`(… : F)⁻¹` inverse constants),
  `shape.rs` (`to_lean_type`: `F`, `(Word F)`, and struct types as `(<name> F)`),
  and the list renderers (`List F` / `List (Interaction F)`).
- **Two-list output.** `crates/hypercube/src/ir/ast.rs` (`to_lean_components`)
  returns the row constraints as **two** lists — `asserts` (field exprs, each `= 0`) and
  `interactions` (`⟨.send/.receive, <payload>, mult⟩`) — and `crates/core/compiler/src/main.rs`
  emits separate `asserts` and `interactions` definitions. This mirrors Clean's own
  `Operations.constraints` / `Operations.interactions` split.
- **Field binder.** `crates/core/compiler/src/main.rs` prints
  `[Field F] [CoeHead F ℕ]` on the generated definitions. `[CoeHead F ℕ]` backs the
  `ByteOpcode.ofNat opcode` coercion when the opcode is a
  dynamic field value (e.g. Bitwise); it is an unused-but-harmless hypothesis for
  constant-opcode operations (Add).
- **Struct emission.** Shape reflection synthesizes
  `structure <name> (F : Type) where …` from the chip's column shape (recursing nested structs,
  nested-first).
- **Flat system tables and public values.** Tables without reflection metadata are emitted as an exact
  `values : Vector F width`; `MachineRecord::eval_public_values` is emitted as its own complete ordered
  assertion/interaction block.
- **Machine manifest.** A separate mode reads `RiscvAir::machine().shape().chip_clusters` directly and
  reports runtime table names and widths. Python compares that output to the theorem profile before
  writing anything.
- **No circuit backend.** The transitional Rust-to-Clean-circuit format does not exist on the
  extraction branch. The extractor cannot manufacture a second implementation of a native gadget.

Large generated lists are split into opaque `assertsPartN`/`interactionsPartN` definitions and then
concatenated in order. This is only a Lean elaboration boundary: it follows Clean's advice to keep
expensive values folded and does not alter the extracted list.

The pinned `Global` table is the sole Core AIR exception to the default elaboration budget. One of its
output terms has a dependency closure of roughly 1,300 shared IR bindings, so splitting the surrounding
list cannot make that term smaller (and finer factoring duplicates the closure). Its generated module
therefore carries a module-local budget directive, named with its measured floor in
`scripts/option_escapes_allowlist.txt`; no other generated Core AIR module receives one. If the emitter
starts producing a module that needs a budget, right-size the emit in `update_extracted.py` — do not
allowlist the output.

## The Lean side

- **`Extracted/ExtractionDSL.lean` + `Model/SP1Constraint.lean`** — the generated interaction vocabulary
  and the shared byte/opcode definitions. `ByteOpcode.constrain` gives the real
  meaning for `Range` (byte range checks, used by Add) and AND/OR/XOR (used by Bitwise, via
  `byteOp`). A **scoped**
  `CoeHead (ZMod p) ℕ` instance + `coe_eq_val` simp lemma live under
  `SP1Clean.ConstraintCoe` (activated only by `open scoped …`), so the coercion never
  leaks into the heavy arithmetic proofs in `Native/Operations/`/`Proofs/`.
- **`Extracted/ChipOracle/<Chip>.lean`** — generated; never hand-edit. It owns the chip-namespaced Rust row and its complete
  `asserts`/`interactions` oracle, reusing canonical generated reader rows/functions instead of cloning
  them per chip.
- **`Extracted/SystemOracle/<Table>.lean`** — generated flat rows for the eleven non-instruction tables
  needed by the baseline execution and memory-boundary clusters, plus the machine-level `PublicValues`
  block. Flat indices are named only in the hand-audited adapter above this layer.
- **`Extracted/CoreAIRManifest.lean` / `Provenance.lean`** — generated fail-closed profile and source
  identity. `FormalModel/CoreProfile.lean` proves the readable hand-maintained enum is a permutation of
  the runtime manifest with identical widths.
- **`Native/Chips/<Chip>/Defs.lean`** — owns an independent native row. It need not reuse the extracted
  row or any Rust operation struct.
- **`Faithful/ChipOracle.lean` + `Faithful/<Chip>.lean`** — define the native→Rust row reconfiguration
  and prove `ChipFaithful`. The assertion theorem compares the complete evaluated Clean assertion list;
  the interaction theorem compares the complete projected four-bus multiset.
- **`export/sp1dump/` + the generation-time gate** — the dump-anchored trace-conformance pipeline
  (successor of the retired `native_decide` vector batteries, 2026-08). `chip_traces` (a committed
  binary at the extraction pin) dumps deterministic per-chip event batteries plus the full padded
  `generate_trace` matrix; `scripts/witgenExport.lean --testdata` recovers the native inputs from
  the dumped rows through the symbolic row maps, recomputes every event row via
  `FlatOperation.witgen` + row-map evaluation, and **fails closed on any cell mismatch** before
  writing the `export/testdata/` differential fixtures the Rust reference interpreter re-checks.
  This resolves the release-readiness audit finding F-R-01 (the legacy batteries' dumper never
  existed at any pinned revision): the dumper is now an ordinary commit at the pin, the dumps are
  reproducible byte-for-byte (`update_sp1_dumps.sh --check`), and the comparison re-runs in CI.

## Legacy operation-list outputs (retirement path)

The old `--format lean-circuit` mode and `CIRCUIT_OPERATIONS` registry are gone, and
`Extracted/Circuit/` has been deleted. The former generated circuit definitions now live as ordinary,
hand-maintained proof implementations under `Native/Operations/<Op>/Defs.lean`. Per-operation assertion/
interaction lists, witness vectors, and public `Faithful/<Operation>.lean` anchors still predate the chip
boundary; do not extend them. During migration a generated chip oracle may import
`Extracted.<Operation>` because the Rust list emitter factors its expression that way. A chip proof may
unfold that call locally but exposes only its `ChipFaithful` theorem.

For each migrated chip:

1. give the native chip its own row type;
2. define the simple native→Rust `reconfigure` map;
3. prove complete assertion and interaction equivalence;
4. retain/add the whole-chip trace-populate test;
5. remove any operation list, witness battery, or operation anchor no longer imported by another chip.

## Adding or refactoring a Lean gadget

Do not add it to extraction. Give it the smallest semantic contract useful to its consuming chips, prove
its soundness/completeness locally, and compose it as a true Clean subcircuit. Only the consuming chip's
row reconfiguration and `ChipFaithful` theorem must change if the chip row layout changes.

## Adding a new chip

Chip oracle modules (`Extracted/ChipOracle/<Chip>.lean`, the namespaced `<Chip>Cols` struct + the complete
`asserts`/`interactions`) are generated by the same tool from the chip's `Air::eval`. Three steps, the first
two in the **`$SP1_DIR`** checkout (extraction tooling — additive reflection derives + a dispatch line, *not*
a chip-semantics change):

1. **Compiler dispatch.** Add the chip to the `chip_cols_shape!` table in
   `crates/core/compiler/src/main.rs` (e.g. `"AluX0" => m::alu::alu_x0::AluX0Cols<ExprRef<F>, Sup>,`). The
   compiler extracts the **supervisor** (`Sup`) mode shape, so the user-mode mode-fields (`M::AdapterCols<T>`
   = `EmptyCols`, etc.) drop out of the emitted struct.
2. **Reflection derives.** The chip's `<Chip>Cols<T, M: TrustMode>` struct must derive `StructReflection,
   IntoShape` (add `use struct_reflection::{StructReflection, StructReflectionHelper};` and
   `use sp1_derive::{AlignedBorrow, IntoShape};`). The `IntoShape` derive handles the zero-width `EmptyCols`
   mode-fields fine (see `AddCols`).
3. **Generate.** Add `"<Chip>"` to `CHIPS` and `CHIP_ORACLES` in `update_extracted.py`, then run a *closed* group, e.g.
   `EXTRACT_ONLY=AluX0,CPUState,ALUTypeReader,RTypeReader python3 update_extracted.py` (closed under the
   chip's nested sub-structs, so the reuse/import wiring resolves). Sub-operation **methods** that are *not*
   `SP1Operation`s (e.g. `ALUTypeReader::eval_op_a_immutable`) are **inlined** in the chip's
   `asserts`/`interactions` rather than emitted as a `<Sub>.asserts` call — the `Faithful/<Chip>.lean` anchor
   then discharges them directly (see `Faithful/AluX0Chip.lean`).

## Generated helper factoring (sub-op `++`)

Operations that compose sub-operations (e.g. `AddwOperation`/`SubwOperation` calling
`U16MSBOperation`) emit parallel `<SubOp>.asserts … ++ [own…]` and
`<SubOp>.interactions … ++ [own…]` chains. The compiler re-emits the sub-op's column
**struct** inline (nested-first), which would clash with the sub-op's own standalone
`Extracted/<SubOp>.lean`. So `update_extracted.py` discovers struct ownership, asks the compiler to
reuse each owned sub-struct instead of re-emitting it, and adds `import SP1Clean.Extracted.<SubOp>`
to the header (so the
sub-op struct + list definitions come from its own module). Each `Extracted/` file therefore owns
exactly one struct. This factoring must remain invisible at the public proof boundary: a whole-chip
anchor may split/unfold the generated append chain as a local calculation, but it concludes with one
complete chip assertion/interactions theorem.

Two header details of the generated chip oracles: the module-doc reuse list names **every**
imported shared module (readers *and* struct carriers such as `MemoryAccess`), and imports that
another import already provides transitively are pruned (`_prune_transitive_imports` — e.g. a
load/store oracle reaches `RegisterAccessCols` through `ITypeReader`, whose module itself imports
`RTypeReader`, so no direct `RTypeReader` import is emitted).

## Future work

- Add `--elf` real-program dumps (`chip_traces --elf` now covers all 25 chip families; committing
  dumps and fixture rows from a real guest execution — and an `--elf` variant of the in-SP1
  conformance test — is deferred follow-up).
- Extend canonical generated reader reuse as each new chip oracle lands, while keeping chip-private
  Rust arithmetic helpers embedded as implementation details.
- Retire an entry of `OPERATIONS` / the operation-list modules whenever its last consuming
  anchor is retired (they are deliberate shared substrate, not migration debt — see `AGENTS.md`).
- Land the upstream sp1 PR from the pinned branch series (`dtumad/lean-extraction`), then advance
  `SP1_PINNED_COMMIT` to the upstream commit. The series now carries its own value proposition
  beyond extraction: `crates/core/compiler/conformance-check/` checks SP1's live
  `generate_trace` against the vendored formally-verified witness generators (see
  `docs/rust-integration-memo.md`). It is deliberately a **standalone opt-in package with zero
  CI footprint** for now — its own cargo workspace, excluded from SP1's, driven only by
  `scripts/run_sp1_conformance.sh` here — so nothing in SP1's `cargo build`/`cargo test
  --workspace` builds or runs it. Promoting it into SP1 CI is a later hardening step; only once
  it runs in authoritative SP1 CI do this repo's committed `export/sp1dump/` tree and its
  dump-anchored gate input become retirable (the gated seam-A retirement).
