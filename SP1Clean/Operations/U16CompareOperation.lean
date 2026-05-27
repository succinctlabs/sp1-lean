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
import SP1Operations.Compare.U16CompareOperation.U16CompareOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.SP1Lookup
import SP1Clean.Operations.AddOperation

/-! # `U16CompareOperation` Clean mirror (scaffold)

SP1's `U16CompareOperation` compares two 16-bit values `a` and `b` and
asserts via a `bit : F` witness that:
- `bit` is boolean,
- `a - b + bit * 65536` is `< 65536` (i.e., `bit = 1 ↔ a < b`).

Rust source (proxy via SP1Operations):
`SP1Operations/Compare/U16CompareOperation/Constraints.lean`. The
constraint list under `is_real = 1` is:
```
[ .assertZero (bit*(bit-1))
, .send (.byte Range (a - b + bit*65536) 16 0) is_real ]
```
plus the chip-level `is_real * (is_real - 1)` gate (which lives at the
chip layer, not inside the wrapper).

This is the leaf atomic byte-comparison sub-op — no recursive sub-ops.
Proof bodies (`iff_sp1`, `soundness`, `completeness`) are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.U16CompareOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Takes the two compared values `a`, `b` and the
externally supplied compare bit; asserts `bit` is boolean and that the
shifted difference fits in `< 65536`. -/
def main (a b bit : Expression (ZMod p)) : Circuit (ZMod p) Unit := do
  bit * (bit - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), a - b + bit * 65536, 16, 0]
      : Vector (Expression (ZMod p)) 4)

/-- Pilot Spec: `bit` is boolean and the shifted difference is a u16. -/
def Spec (a b bit : ZMod p) : Prop :=
  bit * (bit - 1) = 0 ∧
  (a - b + bit * 65536).val < 65536

/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. Bridges the byte-send via the ByteOpcode Range opcode
contract (`x.val < 65536`). -/
theorem iff_sp1 (a b : ZMod p) (cols : U16CompareOperation (ZMod p)) :
    (U16CompareOperation.constraints (F := ZMod p) a b cols 1).allHold ↔
      Spec a b cols.bit := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  have h16_val : (16 : ZMod p).val = 16 := by
    rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  simp only [U16CompareOperation.constraints, SP1ConstraintList.allHold,
             List.Forall, SP1Constraint.toProp, SP1Constraint.toProp_send_byte,
             Spec, one_ne_zero, not_false_eq_true, true_imp_iff,
             ByteOpcode.ofNat_seven, ByteOpcode.constrain_Range, h16_val,
             show (2 ^ 16 : ℕ) = 65536 from rfl]
  -- After simplification:
  -- LHS:  1*(1-1)=0 ∧ bit*(bit-1)=0 ∧ (a-b+bit*65536).val < 65536
  -- RHS:  bit*(bit-1)=0 ∧ (a-b+bit*65536).val < 65536
  constructor
  · rintro ⟨_h_ir_bin, h_bit_bin, h_range⟩
    exact ⟨h_bit_bin, h_range one_ne_zero⟩
  · rintro ⟨h_bit_bin, h_range⟩
    exact ⟨by ring, h_bit_bin, fun _ => h_range⟩

/-! ## Full `FormalAssertion` promotion -/

/-- Bundled FormalAssertion input: the two compared values + the compare bit. -/
structure Inputs (F : Type) where
  a : F
  b : F
  bit : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Wrapper around `SP1Clean.U16CompareOp.main`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Clean.U16CompareOp.main input.a input.b input.bit

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.U16CompareOp"
  main := main
  localLength _ := 0

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The FormalAssertion's spec, identical in shape to the top-level
`SP1Clean.U16CompareOp.Spec`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.bit * (input.bit - 1) = 0 ∧
  (input.a - input.b + input.bit * 65536).val < 65536

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_bit_eq⟩ := h_input
  subst_eqs
  simp only [main, SP1Clean.U16CompareOp.main, circuit_norm,
             Lookup.Soundness, Table.toRaw, SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_bit_bin, h_send⟩ := h_holds
  simp only [Spec, sub_eq_add_neg]
  refine ⟨h_bit_bin, ?_⟩
  exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_send

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_bit_eq⟩ := h_input
  subst_eqs
  simp only [Spec, sub_eq_add_neg] at h_spec
  obtain ⟨h_bit_bin, h_range⟩ := h_spec
  simp only [main, SP1Clean.U16CompareOp.main, circuit_norm,
             Lookup.Completeness, Table.toRaw, SP1Clean.ByteOpcodeTable]
  refine ⟨h_bit_bin, ?_⟩
  exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_range

end Assertion

/-- The full Clean `FormalAssertion` for `U16CompareOperation`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-! ## Multiplicity-gated `AssertionGated` form

Parallel to the unconditional `Assertion` namespace above. The
`AssertionGated` form threads a multiplicity expression `is_real` and
gates both the bit-bool quadratic and the byte-range lookup by it. Used
by the new `Chips/.../Multiplicity/` chip mirrors and by gated operation
forms landing in later phases of the migration. -/

/-- Multiplicity-aware input: two compared values, the compare bit, and
the gating multiplicity `is_real`. -/
structure InputsGated (F : Type) where
  a : F
  b : F
  bit : F
  is_real : F
deriving ProvableStruct

namespace AssertionGated

open Circuit

/-- Multiplicity-gated `main`: gates both the bit-bool quadratic and the
byte-range lookup by `is_real`. -/
@[reducible]
def main (input : Var InputsGated (ZMod p)) : Circuit (ZMod p) Unit := do
  input.is_real * (input.bit * (input.bit - 1)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)),
         input.a - input.b + input.bit * 65536, 16, 0], input.is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) InputsGated unit where
  name := "SP1Clean.U16CompareOpGated"
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
bit and the 16-bit range on real rows. -/
def Spec (input : InputsGated (ZMod p)) : Prop :=
  input.is_real = 1 →
    input.bit * (input.bit - 1) = 0 ∧
    (input.a - input.b + input.bit * 65536).val < 65536

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [AssertionGated.main]
  obtain ⟨h_a_eq, h_b_eq, h_bit_eq, h_ir_eq⟩ := h_input
  subst h_a_eq; subst h_b_eq; subst h_bit_eq; subst h_ir_eq
  obtain ⟨h_gbool, h_l_sub⟩ := h_holds
  intro h_is_real
  unfold id at *
  simp only [sub_eq_add_neg]
  have h_ir_ne_zero : Expression.eval env input_var_is_real ≠ 0 := by
    rw [h_is_real]; exact one_ne_zero
  have h_bit_bool := (mul_eq_zero.mp h_gbool).resolve_left h_ir_ne_zero
  have h_range_spec := (h_l_sub trivial).resolve_left h_ir_ne_zero
  refine ⟨h_bit_bool, SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ ?_⟩
  exact h_range_spec

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [AssertionGated.main]
  obtain ⟨h_a_eq, h_b_eq, h_bit_eq, h_ir_eq⟩ := h_input
  subst h_a_eq; subst h_b_eq; subst h_bit_eq; subst h_ir_eq
  unfold id at *
  rcases h_assumptions with h_ir0 | h_ir1
  · -- Padding row: is_real = 0; both gated emissions trivialize.
    refine ⟨?_, ?_⟩
    · rw [h_ir0]; ring
    · exact ⟨trivial, Or.inl h_ir0⟩
  · -- Real row: recover bit-bool + range from Spec.
    simp only [sub_eq_add_neg] at h_spec
    obtain ⟨h_bit_bool, h_range⟩ := h_spec h_ir1
    refine ⟨?_, ?_⟩
    · rw [h_ir1]; linear_combination h_bit_bool
    · refine ⟨trivial, Or.inr ?_⟩
      exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_range

end AssertionGated

/-- Multiplicity-gated FormalAssertion for `U16CompareOperation`. Compose
via `U16CompareOp.assertionGated input` in `Chips/.../Multiplicity/` mirrors. -/
def assertionGated : FormalAssertion (ZMod p) InputsGated :=
  { AssertionGated.elaborated with
    Assumptions := AssertionGated.Assumptions,
    Spec := AssertionGated.Spec,
    soundness := AssertionGated.soundness,
    completeness := AssertionGated.completeness }

end SP1Clean.U16CompareOp
