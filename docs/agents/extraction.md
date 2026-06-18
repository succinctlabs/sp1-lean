# Constraint extraction (`update_extracted.py`)

How SP1's operation **structs + constraints** get into this project as the
`SP1Clean/Extracted/<Op>.lean` files that the faithfulness anchors (`Faithful/<Op>.lean`)
pin the native gadgets against. This is the clean-native analogue of sp1-lean's
`update_constraints.py`, but it regenerates whole self-contained files (struct *and*
constraints) and the upstream compiler was extended to emit field-generic, clean-native-ready
Lean directly — so there is **no** Python post-processing of the constraint text.

## The pipeline

```
sp1-constraint-compiler  --→  update_extracted.py  --→  SP1Clean/Extracted/<Op>.lean
   (rust, field-generic)        (wrap + write)            (struct + @[irreducible] constraints)
                                                                  ↑ imported by
                                                          Model/SP1Constraint.lean (shared datatype)
                                                          Faithful/<Op>.lean (anchor theorem)
```

Run it:

```
SP1_DIR=../sp1 python3 update_extracted.py
```

`SP1_DIR` must point at an sp1 checkout whose `sp1-constraint-compiler` builds; the default is
`../sp1` (a sibling sp1 checkout, on the `clean-native` extraction branch). The operations regenerated
are the `CONSTRAINTS_LIST` table at the top of
the script: `Add/AddOperation`, `Bitwise/BitwiseOperation`, `Sub/SubOperation`, and the
W-variants `Addw/U16MSBOperation`, `Addw/AddwOperation`, `Subw/SubwOperation`. The output is
deterministic, so re-running leaves a clean `git diff`.

Any op whose struct `#[derive(SP1OperationBuilder)]`s (and whose `*Input` derives
`InputParams`/`InputExpr`) is auto-registered by the compiler — adding it to `CONSTRAINTS_LIST`
is enough; no hand-written `impl SP1OperationBuilder` in the compiler's `builder.rs` is needed.

## What the rust backend emits

For `--chip <C> --operation <Op> --format lean`, the compiler now prints a self-contained
module fragment:

```lean
structure AddOperation (F : Type) where
  value : (Word F)

namespace AddOperation

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (a : (Word F)) (b : (Word F)) (cols : (AddOperation F)) (is_real : F)
  : SP1Constraints F :=
  …
  ⟨[ E1, … ], [ ⟨.send, .byte (ByteOpcode.ofNat 6) cols.value[0] 16 0, is_real⟩, … ]⟩

end AddOperation
```

`update_extracted.py` sandwiches this between a fixed header (imports of
`SP1Clean.Math.Word` + `…SP1Constraint`, `namespace SP1Clean.Extracted`,
`open SP1Clean`) and footer, giving e.g. `SP1Clean.Extracted.AddOperation.constraints`.

### Rust changes that made this possible

All on the `field-generic-constraint-extraction` branch of the sp1 repo:

- **Field-generic, not `Fin KB`.** Every Lean-emission site now writes the type token `F`
  instead of the concrete `Fin KB`:
  `crates/hypercube/src/ir/ast.rs` (let-step + call-output types),
  `expr.rs` / `var.rs` (`(… : F)⁻¹` inverse constants),
  `shape.rs` (`to_lean_type`: `F`, `(Word F)`, and struct types as `(<name> F)`),
  `func.rs` (`to_output_lean_type`: `SP1Constraints F`).
- **Two-list output (`SP1Constraints`).** `crates/hypercube/src/ir/ast.rs` (`to_lean_components`)
  returns the row constraints as **two** lists — `asserts` (field exprs, each `= 0`) and
  `interactions` (`⟨.send/.receive, <payload>, mult⟩`) — and `crates/core/compiler/src/main.rs`
  emits them as a `⟨[asserts], [interactions]⟩ : SP1Constraints F` literal (composed sub-ops chain
  with `++`, the componentwise append). This mirrors Clean's own `Operations.constraints` /
  `Operations.interactions` split and isolates arithmetic faithfulness from bus faithfulness.
- **Field binder.** `crates/core/compiler/src/main.rs` prints
  `@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]` for both operations and
  chips. `[CoeHead F ℕ]` backs the `ByteOpcode.ofNat opcode` coercion when the opcode is a
  dynamic field value (e.g. Bitwise); it is an unused-but-harmless hypothesis for
  constant-opcode operations (Add).
- **Struct emission.** `Shape::collect_lean_struct_defs` (in `shape.rs`) synthesizes
  `structure <name> (F : Type) where …` from the operation's `cols` input `Shape::Struct`
  (recursing nested structs, nested-first); `main.rs` prints these before the `constraints`
  def and wraps the def in `namespace <Op> … end <Op>`.

The old `Text`/`Json` emission formats were not preserved where they conflicted (the change to
field-generic types is intentionally destructive to the prior `Fin KB` text output).

## The Lean side

- **`Model/SP1Constraint.lean`** — the single, shared port of SP1's constraint datatype
  (`ByteOpcode` + `ofNat`, `AirInteraction`, `Interaction`, `SP1Constraints`, `allHold`,
  `allHold_append`), co-designed to match the emitted surface syntax. `ByteOpcode.constrain` gives the real
  meaning for `Range` (byte range checks, used by Add) and AND/OR/XOR (used by Bitwise, via
  `byteOp`); other opcodes are `True` stubs until exercised. A **scoped**
  `CoeHead (ZMod p) ℕ` instance + `coe_eq_val` simp lemma live under
  `SP1Clean.ConstraintCoe` (activated only by `open scoped …`), so the coercion never
  leaks into the heavy arithmetic proofs in `Operations/`/`Chips/`.
- **`Extracted/<Op>.lean`** — generated; never hand-edit. Field-generic; carries the struct +
  `@[irreducible] constraints`.
- **`Faithful/<Op>.lean`** — the anchor theorem only. Imports the shared datatype + the
  generated `Extracted` module, `open scoped SP1Clean.ConstraintCoe`, and proves the SP1
  constraint list's `allHold` equals the native gadget's spec (`RawSpec` / `byteOp` relation).

## Circuit form (`--format lean-circuit`)

For a **byte-bus, pure-assertion leaf** operation (Rust `eval` returns `Shape::Unit`, composes no
sub-ops), the compiler can additionally emit the **Clean-native circuit form** — the gadget's `Inputs`
struct, its `main : Var Inputs → Circuit Unit` do-block, and the `ElaboratedCircuit` instance +
`@[circuit_norm]` rfl-lemmas — instead of the two flat lists. `update_extracted.py` writes this to
`SP1Clean/Operations/<Op>/Extracted.lean` — the auto-generated member of the op's four-file
directory (alongside the hand-written `Populate.lean`, `RawSpec.lean`, `Formal.lean`) — for every op
in its `CIRCUIT_OPERATIONS` registry (`AddOperation`, `SubOperation`, `U16CompareOperation`,
`U16MSBOperation`, `BitwiseOperation`, the `IsZero`/`IsZeroWord`/`IsEqualWord` chain, `AddwOperation`,
`SubwOperation`, `AddrAddOperation`, `LtOperationUnsigned`, `LtOperationSigned`). The shared
`Extracted/<Op>.lean` (column struct + `asserts`/`interactions`) still lives in `Extracted/`; only the
circuit form moved into the per-op directory.

When an op composes **≥2 sub-circuits** (`LtOperationSigned`: two `U16MSBOperation` + one
`LtOperationUnsigned`), the nested `a ++ (b ++ c)` channel-list `⊆` goal does not close by the
`channelsLawful` *default* tactic, so the compiler emits an explicit
`channelsLawful := by simp [circuit_norm, main, <each sub>.circuit]` (unfolding the composed
`.circuit`s locally — never as global `@[circuit_norm]` lemmas, which would collapse the
`channelsWithRequirements = [] ∨ Assumptions` soundness requirement-tails of *every* composing chip).
A 0- or 1-sub op omits the field (the default closes it).

```lean
structure Inputs (F : Type) where           -- the `eval` params verbatim …
  a : (Word F)
  b : (Word F)
  cols : (AddOperation F)                    -- … the column struct nested as `cols`
  is_real : F
deriving ProvableStruct

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  …                                          -- the `let Eᵢ` SSA chain, then
  byteChannel.pullIf is_real ⟨6, is_real * cols.value[0], …⟩   -- byte send → gated pull (value folded)
  E1 === 0                                   -- each AssertZero → `=== 0`  (E1 = the `is_real` boolean gate)
  …
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where …
```

**Why this matters.** The emitted `main` *is* the extracted artifact, so the gadget's
soundness/completeness (`Operations/<Op>/Formal.lean`) run against SP1's constraints **by
construction** — there is no longer a hand-written `main` that a `Faithful/<Op>.lean` anchor must
reconcile against the extracted lists. The compiler-side translation bakes in the Clean conventions:
the field-generic `: F` becomes `ZMod p`, an `AssertZero` becomes `<e> === 0`, and a byte `send_byte`
becomes a `byteChannel.pullIf` (a *pull* of the preprocessed `ByteChip`, the value folded
`gate * value`). The `main` includes SP1's `is_real` boolean gate (`is_real * (is_real - 1) = 0`),
which the older hand-written gadgets dropped to a chip `Assumptions`.

**Migration shape** (per converted op): the generated `Operations/<Op>/Extracted.lean` owns
`Inputs`/`main`/`elaborated`; `FormalModel/Contracts/Operations.lean` drops the flat `Inputs` and imports the generated
module (the `Spec` reads `input.cols.value`); `Operations/<Op>/Formal.lean` runs its proofs against the
generated `main`; the hand-written `populate`/`spec_populate` live in `Operations/<Op>/Populate.lean`; and
each composing chip wraps the witnessed result word in the `cols` struct
(`assertion <Op>.circuit ⟨…, { value := value }, …⟩`). The op-level `Faithful/<Op>.lean` bridge and
the flat `Extracted/<Op>.{asserts,interactions}` defs **stay** — they remain load-bearing for the
not-yet-migrated **chip-level** faithfulness (`Faithful/<Chip>Chip.lean`, which still composes
`<Op>.asserts ↔ AssertSpec`). Only **byte-bus** leaves are supported so far; readers/CPUState
(State/Memory/Program buses) and the witnessing `FormalCircuit`s are future work.

## Adding a new operation

1. Add `("<Chip>", "<Op>")` to `CONSTRAINTS_LIST` in `update_extracted.py` and run it.
2. If `<Op>` emits a `ByteOpcode` not yet modelled, add its real meaning to
   `ByteOpcode.constrain` in `Model/SP1Constraint.lean` (replace the `True` stub).
3. Wire `SP1Clean.Extracted.<Op>` into the root index `SP1Clean.lean`.
4. Write `Faithful/<Op>.lean` anchoring `Extracted.<Op>.constraints` to the gadget's spec.

## Adding a new chip

Chip column structs (`Extracted/<Chip>Chip.lean`, the `<Chip>Cols` struct + the composed
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
3. **Generate.** Add `"<Chip>"` to `CHIPS` in `update_extracted.py` and run a *closed* group, e.g.
   `EXTRACT_ONLY=AluX0,CPUState,ALUTypeReader,RTypeReader python3 update_extracted.py` (closed under the
   chip's nested sub-structs, so the reuse/import wiring resolves). Sub-operation **methods** that are *not*
   `SP1Operation`s (e.g. `ALUTypeReader::eval_op_a_immutable`) are **inlined** in the chip's
   `asserts`/`interactions` rather than emitted as a `<Sub>.asserts` call — the `Faithful/<Chip>.lean` anchor
   then discharges them directly (see `Faithful/AluX0.lean`).

## Composed operations (sub-op `++`)

Operations that compose sub-operations (e.g. `AddwOperation`/`SubwOperation` calling
`U16MSBOperation`) emit a `let CSk := <SubOp>.constraints …` step and return `CSk ++ ⟨[own…], […]⟩`
(`++` is the componentwise `SP1Constraints` append). The compiler re-emits the sub-op's column
**struct** inline (nested-first), which would clash with the sub-op's own standalone
`Extracted/<SubOp>.lean`. So `update_extracted.py` post-processes a composed op's fragment: it
detects each `<SubOp>.constraints` call, **strips** the re-emitted `structure <SubOp> … deriving
ProvableStruct` block, and adds `import SP1Clean.Extracted.<SubOp>` to the header (so the
sub-op struct + `constraints` come from its own module). Each `Extracted/` file therefore owns
exactly one struct. The faithfulness anchor for a composed op splits the list at the `++` with
`SP1Constraints.allHold_append` and discharges the sub-op fragment via the sub-op's own anchor (see
`Faithful/Addw.lean`, `Faithful/Subw.lean`; the deeper `Faithful/LtOperationSigned.lean` and
`Faithful/IsZeroWordOperation.lean` collapse their sub-lists the same way).

## Future work

- Chip-level `asserts`/`interactions` are now generated and consumed (see *Adding a new chip* above; the
  native readers + CPU-state are in place). The remaining tooling gap is the `--format lean-circuit` chip
  form (the `Inputs` + `main` + `ElaboratedCircuit` shape) — currently operation-only; chips compose their
  sub-circuits by hand in `Chips/<Op>Chip/Defs.lean`.
