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
Air::eval / eval_public_values ────→ Extracted/{ChipOracle,SystemOracle}/...
          (audited Rust overlay)      (rows + ordered asserts/interactions only)

Native/ hand-written Clean circuits ─→ Faithful/<Chip>.lean (`ChipFaithful`)
Rust generate_trace ────────────────→ SP1CleanTest/TraceGenTests/*Vectors.lean
```

Run it:

```sh
SP1_DIR=/path/to/audited-extractor-overlay EXTRACT_AIR_ONLY=1 python3 update_extracted.py
```

`SP1_DIR` must point at the exact extraction overlay checked by `SP1_PINNED_COMMIT` and the two patch
digests in `update_extracted.py`; the ordinary sibling `../sp1` remains the unmodified semantic source.
The generator verifies that the overlay's merge base is semantic revision
`a630089d9ff484ec6f2feade8d0afbb1447eed11` (`v6.3.1-8-ga630089d9`), that runtime-source changes are
reflection metadata only, and that the dirty exporter diff is byte-identical to the checked-in
list-only patches. `CHIPS` and `SYSTEM_TABLES` select AIR anchors; `TRACE_CHIPS` selects whole-chip
populate batteries. `OPERATIONS` and `WITNESS_OPERATIONS` are transitional registries. There is no
circuit-output registry or circuit emitter. The output is deterministic, so a full regeneration at
the audited overlay leaves all pre-existing anchors byte-identical.

Profile extraction is unconditional, even under `EXTRACT_ONLY`: regeneration fails before writing AIR
files unless the baseline 34-table execution cluster, the 6-table memory-boundary cluster, every main
and preprocessed width, and the 160-cell public-value width match the audited manifest exactly. Requested
system tables, public values, self-contained chip oracles, and whole-chip traces are hard requirements;
the script exits nonzero rather than retaining a stale artifact. `EXTRACT_AIR_ONLY=1` intentionally skips
the independent witness/trace batteries during a conservative Rust-pin audit.

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

### Audited Rust overlay

The extraction backend is not part of the semantic SP1 pin yet. Its exact review surface is committed
as `scripts/extractor-patches/core-air-lists.patch` and
`scripts/extractor-patches/core-air-manifest.patch`; `Extracted/Provenance.lean` records the semantic
revision, overlay revision, and combined diff hash. The relevant changes are:

- **Field-generic, not `Fin KB`.** Every Lean-emission site now writes the type token `F`
  instead of the concrete `Fin KB`:
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
- **No circuit backend.** The transitional Rust-to-Clean-circuit format was deleted from the audited
  patch. The extractor cannot manufacture a second implementation of a native gadget.

Large generated lists are split into opaque `assertsPartN`/`interactionsPartN` definitions and then
concatenated in order. This is only a Lean elaboration boundary: it follows Clean's advice to keep
expensive values folded and does not alter the extracted list.

The pinned `Global` table is the sole exception to the ordinary heartbeat budget. One of its output
terms has a dependency closure of roughly 1,300 shared IR bindings, so splitting the surrounding list
cannot make that term smaller (and finer factoring duplicates the closure). Its generated module carries
one module-local `set_option maxHeartbeats 1000000`, accounted for explicitly in
`scripts/heartbeats_baseline.txt`; no other generated Core AIR module receives a heartbeat override.

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
- **`SP1CleanTest/TraceGenTests/`** — compares rows generated from the native circuit with whole traces
  dumped by Rust.

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
   then discharges them directly (see `Faithful/AluX0.lean`).

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

## Future work

- Make every supported chip own a native row, a `ChipOracle`, a `ChipFaithful` proof, and a whole-trace
  conformance battery.
- Extend canonical generated reader reuse as each new chip oracle lands, while keeping chip-private
  Rust arithmetic helpers embedded as implementation details.
- Remove `WITNESS_OPERATIONS` and the remaining operation-list modules once their chip consumers migrate.
