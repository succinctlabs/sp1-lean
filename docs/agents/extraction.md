# Constraint extraction (`update_extracted.py`)

How SP1's **whole-chip rows, `assertZero` lists, interaction lists, and populate traces** enter this
project. The stable output is chip-level: Lean gadgets are proof-oriented implementation details and
are not required to mirror Rust operations. `update_extracted.py` also still emits a number of
operation modules during the migration, but those are generator-private dependencies of current chip
oracles, not public verification boundaries.

The upstream compiler emits field-generic Lean directly, so there is no Python rewriting of constraint
expressions. Python only selects targets, supplies reuse imports, wraps modules, and writes deterministic
files.

## The pipeline

```
sp1-constraint-compiler  --→  update_extracted.py  --→  Extracted/ChipOracle/<Chip>.lean
   (rust, field-generic)        (wrap + write)           (Rust row + asserts + interactions)
             Rust generate_trace  ────────────────────→  SP1CleanTest/TraceGenTests/*Vectors.lean
                                                                   ↑ compared by
                                                   Faithful/<Chip>.lean (`ChipFaithful`)
                                                   TraceGenTests/<Chip>TraceWitness.lean
```

Run it:

```
SP1_DIR=../sp1 python3 update_extracted.py
```

`SP1_DIR` must point at an sp1 checkout whose `sp1-constraint-compiler` builds; the default is
`../sp1` (a sibling sp1 checkout). `CHIPS` selects whole-chip AIR oracles and `TRACE_CHIPS` selects
whole-chip populate batteries. `OPERATIONS`, `WITNESS_OPERATIONS`, and `CIRCUIT_OPERATIONS` are
transitional registries: shrink them as chip anchors cease importing helper modules. The output is
deterministic, so re-running leaves a clean `git diff`.

Requested self-contained chip oracles and whole-chip traces are **hard requirements**: the script exits
nonzero if either fails, instead of silently leaving stale checked-in artifacts. Current 4.31 migration
blocker: the pinned local SP1 checkout's `witness_vectors` binary accepts only `--operation`; its former
`--chip`/`generate_trace` mode must be restored before any trace-vector regeneration can be claimed.
Existing checked-in trace anchors still elaborate, but that does not repair provenance/reproducibility.

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

### Rust changes that made this possible

All on the `field-generic-constraint-extraction` branch of the sp1 repo:

- **Field-generic, not `Fin KB`.** Every Lean-emission site now writes the type token `F`
  instead of the concrete `Fin KB`:
  `crates/hypercube/src/ir/ast.rs` (let-step + call-output types),
  `expr.rs` / `var.rs` (`(… : F)⁻¹` inverse constants),
  `shape.rs` (`to_lean_type`: `F`, `(Word F)`, and struct types as `(<name> F)`),
  `func.rs` (`to_output_lean_type`: `SP1Constraints F`).
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
- **Struct emission.** `Shape::collect_lean_struct_defs` (in `shape.rs`) synthesizes
  `structure <name> (F : Type) where …` from the chip's column shape (recursing nested structs,
  nested-first).

The old `Text`/`Json` emission formats were not preserved where they conflicted (the change to
field-generic types is intentionally destructive to the prior `Fin KB` text output).

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
- **`Native/Chips/<Chip>/Defs.lean`** — owns an independent native row. It need not reuse the extracted
  row or any Rust operation struct.
- **`Faithful/ChipOracle.lean` + `Faithful/<Chip>.lean`** — define the native→Rust row reconfiguration
  and prove `ChipFaithful`. The assertion theorem compares the complete evaluated Clean assertion list;
  the interaction theorem compares the complete projected four-bus multiset.
- **`SP1CleanTest/TraceGenTests/`** — compares rows generated from the native circuit with whole traces
  dumped by Rust.

## Legacy operation outputs (retirement path)

`--format lean-circuit`, `CIRCUIT_OPERATIONS`, per-operation witness vectors, and public
`Faithful/<Operation>.lean` anchors predate the chip boundary. Do not extend them. During migration a
generated chip oracle may still import `Extracted.<Operation>` because the Rust emitter factors its
expression that way; this is acceptable as an internal dependency. A chip proof should unfold that call
locally and expose only its `ChipFaithful` theorem.

For each migrated chip:

1. give the native chip its own row type;
2. define the simple native→Rust `reconfigure` map;
3. prove complete assertion and interaction equivalence;
4. retain/add the whole-chip trace-populate test;
5. remove any direct circuit, operation witness battery, or operation anchor no longer imported by another
   chip.

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
`U16MSBOperation`) emit a `let CSk := <SubOp>.constraints …` step and return `CSk ++ ⟨[own…], […]⟩`
(`++` is the componentwise `SP1Constraints` append). The compiler re-emits the sub-op's column
**struct** inline (nested-first), which would clash with the sub-op's own standalone
`Extracted/<SubOp>.lean`. So `update_extracted.py` post-processes a composed fragment: it
detects each `<SubOp>.constraints` call, **strips** the re-emitted `structure <SubOp> … deriving
ProvableStruct` block, and adds `import SP1Clean.Extracted.<SubOp>` to the header (so the
sub-op struct + `constraints` come from its own module). Each `Extracted/` file therefore owns
exactly one struct. This factoring must remain invisible at the public proof boundary: a whole-chip
anchor may split/unfold the generated append chain as a local calculation, but it concludes with one
complete chip assertion/interactions theorem.

## Future work

- Make every supported chip own a native row, a `ChipOracle`, a `ChipFaithful` proof, and a whole-trace
  conformance battery.
- Extend canonical generated reader reuse as each new chip oracle lands, while keeping chip-private
  Rust arithmetic helpers embedded as implementation details.
- Remove `CIRCUIT_OPERATIONS` and `WITNESS_OPERATIONS` once their remaining chip consumers migrate.
