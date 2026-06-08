import Mathlib.Data.ZMod.Basic
import SP1Clean.Foundations.Bitwise

/-! # Shared SP1 opcode datatype (byte-interaction only)

The single, project-wide `ByteOpcode` / `Opcode` opcode datatypes (and the scoped
`CoeHead (ZMod p) ℕ` coercion), co-designed to match the surface syntax emitted by the
(field-generic) `sp1-constraint-compiler` `--format lean` backend (`.byte (ByteOpcode.ofNat n) …`,
`.program … (Opcode.ofNat n) …`).

The bus-interaction vocabulary built on these opcodes (`AirInteraction` / `Dir` / `Interaction` +
`Interaction.toProp`) and the two-list (`asserts` / `interactions`) constraint representation the
generated modules emit live in `SP1Clean/Extracted/ExtractionDSL.lean`.

The `ByteOpcode` here carries every SP1 opcode under a single unified `constrain` giving the
**real** meaning for every opcode — `Range` (byte range checks, used by Add), AND/OR/XOR (used by
Bitwise, via `byteOp`), and `U8Range`/`LTU`/`MSB` (used by the readers, Mul, Load, and Lt) — so
every per-chip faithfulness anchor shares one datatype.

The generated `constraints` defs are field-generic with a `[CoeHead F ℕ]` hypothesis, which
backs the `ByteOpcode.ofNat opcode` coercion when the opcode is a dynamic field value (e.g.
Bitwise). The `CoeHead (ZMod p) ℕ` instance needed to apply such a def at `ZMod p` is provided
below as a **scoped** instance (`open scoped SP1Clean.ConstraintCoe`) so it never leaks
into the heavy arithmetic proofs in `Operations/`/`Chips/`. -/

namespace SP1Clean

variable {p : ℕ}

/-! ## `ByteOpcode` (port of `SP1Foundations/ByteOpcode.lean`) -/

inductive ByteOpcode | AND | OR | XOR | U8Range | LTU | MSB | Range
  deriving DecidableEq

namespace ByteOpcode

/-! Lean auto-generates `ByteOpcode.ofNat : ℕ → ByteOpcode` for this enum, mapping by
constructor index — AND=0, OR=1, XOR=2, U8Range=3, LTU=4, MSB=5, Range=6 — which is exactly
SP1's `ByteOpcode` numbering and the inverse the `sp1-constraint-compiler` emitter targets
(`ByteOpcode.ofNat n`). The `@[simp]` lemmas below pin the cases the anchors use. -/

@[simp] lemma ofNat_zero  : ofNat 0 = .AND := rfl
@[simp] lemma ofNat_one   : ofNat 1 = .OR  := rfl
@[simp] lemma ofNat_two   : ofNat 2 = .XOR := rfl
@[simp] lemma ofNat_three : ofNat 3 = .U8Range := rfl
@[simp] lemma ofNat_four  : ofNat 4 = .LTU := rfl
@[simp] lemma ofNat_five  : ofNat 5 = .MSB := rfl
@[simp] lemma ofNat_six   : ofNat 6 = .Range := rfl

/-- The byte-opcode constraint. `Range` (used by Add's `slice_range_check_u16`) bounds
`a.val < 2 ^ b.val`; `U8Range` (used by CPUState's `clk_16_24` byte check) bounds all three
operands `< 256`; AND/OR/XOR (used by Bitwise) say `a` is the per-byte bitwise op of the
two byte operands, all bounded `< 256`; `MSB` (used by Mul/LoadByte/signed-Lt) says `a` is the
boolean top bit of `b` (`a = 1 ↔ 128 ≤ b.val`); `LTU` says `a` is the boolean `b.val < c.val`. -/
def constrain {p : ℕ} [NeZero p] (op : ByteOpcode) (a b c : ZMod p) : Prop :=
  match op with
  | AND => (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ a.val = b.val &&& c.val
  | OR  => (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ a.val = b.val ||| c.val
  | XOR => (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ a.val = b.val ^^^ c.val
  | U8Range => a.val < 256 ∧ b.val < 256 ∧ c.val < 256
  | LTU => (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b.val < c.val)
  | MSB => (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ 128 ≤ b.val)
  | Range => a.val < 2 ^ b.val

@[simp] lemma constrain_Range {p : ℕ} [NeZero p] (a b c : ZMod p) :
    ByteOpcode.Range.constrain a b c ↔ (a.val < 2 ^ b.val) := Iff.rfl

@[simp] lemma constrain_U8Range {p : ℕ} [NeZero p] (a b c : ZMod p) :
    ByteOpcode.U8Range.constrain a b c ↔ (a.val < 256 ∧ b.val < 256 ∧ c.val < 256) := Iff.rfl

@[simp] lemma constrain_LTU {p : ℕ} [NeZero p] (a b c : ZMod p) :
    ByteOpcode.LTU.constrain a b c ↔
      ((a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b.val < c.val)) :=
  Iff.rfl

@[simp] lemma constrain_MSB {p : ℕ} [NeZero p] (a b c : ZMod p) :
    ByteOpcode.MSB.constrain a b c ↔
      ((a.val < 256 ∧ b.val < 256 ∧ c.val < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ 128 ≤ b.val)) :=
  Iff.rfl

end ByteOpcode

/-! ## `Opcode` (placeholder for program-interaction opcodes)

SP1's RISC-V `Opcode` enum, emitted by the constraint compiler as `Opcode.ofNat n` inside
`.program` bus interactions (the chip adapters' instruction reads). The *semantics* of program
interactions are deferred (their `toProp` is `True`, see `Extracted/ExtractionDSL.lean`), so —
unlike the fully-modelled `ByteOpcode` — `Opcode` only needs to carry the numeric tag and elaborate.
It is
a thin `ℕ` wrapper with an `ofNat` that, like `ByteOpcode.ofNat`, composes with the
`[CoeHead F ℕ]` hypothesis so `Opcode.ofNat (opcode : F)` typechecks. -/
abbrev Opcode := ℕ

/-- Mirrors `ByteOpcode.ofNat`'s role for program interactions; identity on the numeric tag. -/
def Opcode.ofNat (n : ℕ) : Opcode := n

/-! ## Interaction vocabulary + two-list constraints → `Extracted/ExtractionDSL.lean`

The `AirInteraction` / `Dir` / `Interaction` (+ `Interaction.toProp`) bus vocabulary and the
two-list (`asserts : List F`, `interactions : List (Interaction F)`) constraint representation the
generated modules use live in `SP1Clean/Extracted/ExtractionDSL.lean` (the
`SP1Clean.Extracted` namespace), next to the generated files that consume them. This file
keeps only the shared `ByteOpcode` / `Opcode` opcode datatypes (above) and the scoped `CoeHead`
coercion (below) those interactions are built from. -/

/-! ## `CoeHead (ZMod p) ℕ` (scoped) -/

namespace ConstraintCoe

/-- Backs the `[CoeHead F ℕ]` hypothesis on generated `constraints` defs when they are applied
at `F = ZMod p` (the dynamic-opcode `ByteOpcode.ofNat opcode` coercion). `scoped` so it only
activates under `open scoped SP1Clean.ConstraintCoe` (the faithfulness anchors), never in
the arithmetic proofs that merely `open SP1Clean`. -/
scoped instance instCoeHeadZModNat {p : ℕ} : CoeHead (ZMod p) ℕ := ⟨ZMod.val⟩

/-- Normalize the scoped `ZMod p → ℕ` coercion to `ZMod.val`, so anchor proofs can rewrite the
generated `ByteOpcode.ofNat (CoeHead.coe opcode)` to `ByteOpcode.ofNat opcode.val`. Stated on
`CoeHead.coe` directly (rather than `↑`) so its LHS matches the coercion the compiler's
`[CoeHead F ℕ]` hypothesis leaves in the term. -/
@[simp] lemma coe_eq_val {p : ℕ} (x : ZMod p) : (CoeHead.coe x : ℕ) = x.val := rfl

end ConstraintCoe

end SP1Clean
