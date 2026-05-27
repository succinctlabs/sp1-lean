import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Operations.Operation.U16MSBOperation.Operation
import SP1Operations.Operation.U16MSBOperation.Constraints
import SP1Clean.ByteOpcodeTable
import SP1Clean.SP1Lookup
import SP1Clean.Operations.AddOperation

/-! # Tier 2a pilot: `U16MSBOperation` mirror

SP1's `U16MSBOperation` extracts the most-significant bit of a 16-bit value.
Its constraint list under `is_real = 1`:

- `msb * (msb - 1) = 0`                                  — boolean
- `send (.byte Range (2*a - msb*65536) 16 0) is_real`    — `(2*a - msb*65536).val < 2^16`

This is the smallest fragment that exercises one byte interaction. The Clean
mirror replaces the `send` with a single `lookup ByteOpcodeTable …` call
(see `SP1Clean/ByteOpcodeTable.lean`).

The principled Clean patch (drop the duplicate `Fin.foldl_eq_foldl_finRange`
in `Clean/Utils/Misc.lean`) means the `<==` / `===` operators are now
available — the circuit definition below uses them idiomatically. Promoting
to a full `FormalCircuit` (with soundness + completeness against the table's
`Spec`) is followup; the pilot ships the `iff_sp1` bridge.
-/

namespace SP1Clean.U16MSBOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)] [Fact (p > 65536)]

/-- Clean-side circuit. Witnesses `msb`, asserts boolean via `===`, then
performs the single byte-opcode lookup for `Range(2*a - msb*65536, 16, 0)`. -/
def main (a : Expression (ZMod p)) : Circuit (ZMod p) (Expression (ZMod p)) := do
  let msb ← witnessField (fun env =>
    if (a.eval env).val < 32768 then 0 else 1)
  msb * (msb - 1) === 0
  -- Row layout #v[opcode, a, b, c]; here opcode = Range.toNat = 6.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), 2 * a - msb * 65536, 16, 0] : Vector (Expression (ZMod p)) 4)
  return msb

/-- Pilot Spec: `msb` is boolean and `2*a - msb*65536` is a u16
(i.e. `< 65536`). -/
def Spec (a msb : ZMod p) : Prop :=
  msb * (msb - 1) = 0 ∧ (2 * a - msb * 65536).val < 65536

omit [Fact (p > 512)] in
/-- Helper: in `ZMod p` with `p > 65536`, `(16 : ZMod p).val = 16`. -/
lemma val_sixteen : ((16 : ZMod p) : ZMod p).val = 16 := by
  have hp : 65536 < p := (Fact.out : p > 65536)
  rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by norm_num,
      ZMod.val_natCast, Nat.mod_eq_of_lt]
  omega

omit [Fact (p > 512)] in
/-- Helper: `Range.constrain _ 16 _` reduces to `_.val < 65536`. -/
lemma range_at_sixteen (x : ZMod p) :
    ByteOpcode.Range.constrain x (16 : ZMod p) (0 : ZMod p) ↔ x.val < 65536 := by
  rw [ByteOpcode.constrain_Range, val_sixteen]
  norm_num

omit [Fact (p > 512)] in
/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. -/
theorem iff_sp1 (a : ZMod p) (cols : U16MSBOperation (ZMod p)) :
    (U16MSBOperation.constraints (F := ZMod p) a cols 1).allHold ↔
    Spec a cols.msb := by
  simp only [U16MSBOperation.constraints, SP1ConstraintList.allHold, List.Forall,
    SP1Constraint.toProp, Spec]
  simp only [ByteOpcode.ofNat_seven]  -- ByteOpcode.ofNat 6 = Range
  constructor
  · rintro ⟨_h_isreal, h_bool, h_range⟩
    refine ⟨?_, ?_⟩
    · linear_combination h_bool
    · have h1ne : ((1 : ZMod p) ≠ 0) := one_ne_zero
      have hr := h_range h1ne
      rw [range_at_sixteen] at hr
      exact hr
  · rintro ⟨h_bool, h_range⟩
    refine ⟨?_, ?_, ?_⟩
    · ring
    · linear_combination h_bool
    · intro _
      rw [range_at_sixteen]
      exact h_range

/-! ## Full `FormalAssertion` promotion (multiplicity-gated)

The top-level `main` above witnesses `msb` internally — it is a
`Circuit (ZMod p) (Expression (ZMod p))`, FormalCircuit-shape. For chip
composition we additionally want a pure-assertion form where `msb` is
supplied as a parameter (the chip provides it as a dedicated column). The
`Assertion.main` below mirrors `SP1Clean.AddOp.Assertion` exactly:
`is_real` gates both the msb-bool quadratic and the byte-range lookup,
so the contract is vacuous on padding rows and matches SP1's
`InteractionKind::Byte` per-row multiplicity contribution.

The assertion requires `Fact (2 ^ 17 < p)` (a strictly stronger field
hypothesis than the file's `Fact (p > 65536)`); chips that compose this
already supply it. -/

/-- Bundled FormalAssertion input: the operand `a` and the externally
supplied `msb` bit. -/
structure Inputs (F : Type) where
  a : F
  msb : F
deriving ProvableStruct

namespace Assertion

open Circuit

variable [Fact (2 ^ 17 < p)]

/-- Assertion-style `main`. Takes `msb` as a parameter rather than
witnessing it internally. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  input.msb * (input.msb - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)),
        2 * input.a - input.msb * 65536, 16, 0]
      : Vector (Expression (ZMod p)) 4)

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.U16MSBOp"
  main := main
  localLength _ := 0

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The FormalAssertion's spec, identical in shape to the top-level
`SP1Clean.U16MSBOp.Spec`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.msb * (input.msb - 1) = 0 ∧
  (2 * input.a - input.msb * 65536).val < 65536

omit [Fact (p > 512)] [Fact (p > 65536)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_msb_eq⟩ := h_input
  subst h_a_eq
  subst h_msb_eq
  simp only [circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_bool, h_range⟩ := h_holds
  simp only [sub_eq_add_neg]
  unfold id at *
  exact ⟨by linear_combination h_bool,
         SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_range⟩

omit [Fact (p > 512)] [Fact (p > 65536)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_msb_eq⟩ := h_input
  subst h_a_eq
  subst h_msb_eq
  simp only [sub_eq_add_neg] at h_spec
  obtain ⟨h_bool, h_range⟩ := h_spec
  simp only [circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  unfold id at *
  exact ⟨by linear_combination h_bool,
         SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_range⟩

end Assertion

/-- The full Clean `FormalAssertion` for `U16MSBOperation`: soundness +
completeness against the pure-assertion `Assertion.Spec`. Compose into a
chip's `main` via `U16MSBOp.assertion input`. -/
def assertion [Fact (2 ^ 17 < p)] : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-! ## Multiplicity-gated `AssertionGated` form

Parallel to the unconditional `Assertion` namespace above. The
`AssertionGated` form threads a multiplicity expression `is_real` and
gates both the msb-bool quadratic and the byte-range lookup by it, so
every emitted constraint vanishes on padding rows. Used by the new
`Chips/.../Multiplicity/` chip mirrors and by gated operation forms
landing in Phase 2 of the migration.

The `Assertion` form will be removed once all callers (current
`Aggregate.lean` chips + W-arith ops) migrate to this. -/

/-- Multiplicity-aware input: operand, externally-supplied msb bit, and
the gating multiplicity `is_real`. -/
structure InputsGated (F : Type) where
  a : F
  msb : F
  is_real : F
deriving ProvableStruct

namespace AssertionGated

open Circuit

variable [Fact (2 ^ 17 < p)]

/-- Multiplicity-gated `main`: gates both the msb-bool quadratic and the
byte-range lookup by `is_real`. -/
@[reducible]
def main (input : Var InputsGated (ZMod p)) : Circuit (ZMod p) Unit := do
  input.is_real * (input.msb * (input.msb - 1)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)),
         2 * input.a - input.msb * 65536, 16, 0], input.is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) InputsGated unit where
  name := "SP1Clean.U16MSBOpGated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

/-- Binarity of `is_real`. The chip-side `is_real * (is_real - 1) = 0`
gate establishes this externally. -/
def Assumptions (input : InputsGated (ZMod p)) : Prop :=
  input.is_real = 0 ∨ input.is_real = 1

/-- Semantic contract: vacuous on padding rows, asserts both the boolean
msb and the 16-bit range on real rows. -/
def Spec (input : InputsGated (ZMod p)) : Prop :=
  input.is_real = 1 →
    input.msb * (input.msb - 1) = 0 ∧
    (2 * input.a - input.msb * 65536).val < 65536

omit [Fact (p > 65536)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [AssertionGated.main]
  obtain ⟨h_a_eq, h_msb_eq, h_ir_eq⟩ := h_input
  subst h_a_eq; subst h_msb_eq; subst h_ir_eq
  obtain ⟨h_gbool, h_l_sub⟩ := h_holds
  intro h_is_real
  unfold id at *
  simp only [sub_eq_add_neg]
  have h_ir_ne_zero : Expression.eval env input_var_is_real ≠ 0 := by
    rw [h_is_real]; exact one_ne_zero
  have h_bool := (mul_eq_zero.mp h_gbool).resolve_left h_ir_ne_zero
  have h_range_spec := (h_l_sub trivial).resolve_left h_ir_ne_zero
  refine ⟨h_bool, SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ ?_⟩
  exact h_range_spec

omit [Fact (p > 65536)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [AssertionGated.main]
  obtain ⟨h_a_eq, h_msb_eq, h_ir_eq⟩ := h_input
  subst h_a_eq; subst h_msb_eq; subst h_ir_eq
  unfold id at *
  rcases h_assumptions with h_ir0 | h_ir1
  · -- Padding row: is_real = 0; both gated emissions trivialize.
    refine ⟨?_, ?_⟩
    · rw [h_ir0]; ring
    · exact ⟨trivial, Or.inl h_ir0⟩
  · -- Real row: recover msb-bool + range from Spec.
    simp only [sub_eq_add_neg] at h_spec
    obtain ⟨h_bool, h_range⟩ := h_spec h_ir1
    refine ⟨?_, ?_⟩
    · rw [h_ir1]; linear_combination h_bool
    · refine ⟨trivial, Or.inr ?_⟩
      exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_range

end AssertionGated

/-- Multiplicity-gated FormalAssertion for `U16MSBOperation`. Compose
via `U16MSBOp.assertionGated input` in `Chips/.../Multiplicity/` mirrors. -/
def assertionGated [Fact (2 ^ 17 < p)] : FormalAssertion (ZMod p) InputsGated :=
  { AssertionGated.elaborated with
    Assumptions := AssertionGated.Assumptions,
    Spec := AssertionGated.Spec,
    soundness := AssertionGated.soundness,
    completeness := AssertionGated.completeness }

end SP1Clean.U16MSBOp
