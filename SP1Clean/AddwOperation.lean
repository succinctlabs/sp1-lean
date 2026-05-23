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
import SP1Operations.Operation.AddwOperation.AddwOperation
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.AddOperation

/-! # `AddwOperation` gadget mirror — Assertion style

SP1's `AddwOperation` is a 2-limb carry-chain 32-bit add plus a
`U16MSBOperation` sub-fragment on the high result limb. The natural-form
iff lemma `AddwOperation.allHold_constraints_iff` exposes both: a
`List.Forall ... U16MSBOperation.constraints` clause on `(cols.value[1],
cols.msb)` plus the carry+limb-bound clauses for the two result limbs.
-/

namespace SP1Clean.AddwOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Asserts the 2-limb carry chain, byte-bounds each
result limb, and emits the `U16MSBOperation` sub-fragment for `value[1]`
with witnessed `msb`. -/
def main (a b : Vector (Expression (ZMod p)) 4)
    (result : Vector (Expression (ZMod p)) 2)
    (msb : Expression (ZMod p)) : Circuit (ZMod p) Unit := do
  let c0 := (a[0] + b[0] - result[0]) * (65536 : ZMod p)⁻¹
  let c1 := (a[1] + b[1] - result[1] + c0) * (65536 : ZMod p)⁻¹
  c0 * (c0 - 1) === 0
  c1 * (c1 - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[0], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[1], 16, 0] : Vector (Expression (ZMod p)) 4)
  -- U16MSBOperation sub-fragment on `result[1]` with witness `msb`.
  msb * (msb - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)),
        (2 : Expression (ZMod p)) * result[1] - msb * 65536, 16, 0]
      : Vector (Expression (ZMod p)) 4)

/-- Pilot Spec, mirroring `AddwOperation.allHold_constraints_iff` RHS
verbatim: a `U16MSBOperation` constraints clause plus 2 natural-form
carries are boolean plus each result limb fits in `< 65536`. -/
def Spec (a b : Word (ZMod p)) (cols : _root_.AddwOperation (ZMod p)) : Prop :=
  let carry0 : ZMod p := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
  let carry1 : ZMod p := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
  List.Forall SP1Constraint.toProp
      (_root_.U16MSBOperation.constraints cols.value[1] { msb := cols.msb.msb } 1) ∧
  (carry0 = 0 ∨ carry0 = 1) ∧
  (carry1 = 0 ∨ carry1 = 1) ∧
  cols.value[0].val < 65536 ∧
  cols.value[1].val < 65536

/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. Direct re-export of
`AddwOperation.allHold_constraints_iff`. -/
theorem iff_sp1 (a b : Word (ZMod p)) (cols : _root_.AddwOperation (ZMod p)) :
    (_root_.AddwOperation.constraints a b cols 1).allHold ↔
      Spec a b cols :=
  _root_.AddwOperation.allHold_constraints_iff a b cols

/-! ## Full `FormalAssertion` promotion

Wraps the assertion-style `main` above (which already takes `msb` as a
parameter) into a Clean `FormalAssertion`. The `Assertion.Spec` inlines
the U16MSB clauses (`msb` boolean + the `2*result[1] - msb*65536` Range
bound) rather than re-using the `List.Forall SP1Constraint.toProp`
wrapping from the top-level `Spec` — this keeps the FormalAssertion
self-contained and avoids unwrapping the SP1 constraint list inside the
proofs. -/

/-- Bundled FormalAssertion input: the two operand words, the 2-limb
result, and the externally supplied msb bit. -/
structure Inputs (F : Type) where
  a : fields 4 F
  b : fields 4 F
  result : fields 2 F
  msb : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Wrapper around `SP1Clean.AddwOp.main` that destructures a `Var Inputs`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Clean.AddwOp.main input.a input.b input.result input.msb

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.AddwOp"
  main := main
  localLength _ := 0

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The FormalAssertion's spec, inlining the U16MSB clauses in natural
form: 2 carry-boolean clauses, 2 result-limb range bounds, the msb
boolean, and the `2*result[1] - msb*65536` Range bound. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let carry0 : ZMod p := (input.a[0] + input.b[0] - input.result[0]) * 65536⁻¹
  let carry1 : ZMod p :=
    (input.a[1] + input.b[1] - input.result[1] + carry0) * 65536⁻¹
  let msb_check : ZMod p := 2 * input.result[1] - input.msb * 65536
  (carry0 = 0 ∨ carry0 = 1) ∧
  (carry1 = 0 ∨ carry1 = 1) ∧
  input.result[0].val < 65536 ∧
  input.result[1].val < 65536 ∧
  input.msb * (input.msb - 1) = 0 ∧
  msb_check.val < 65536

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq, h_m_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  subst h_m_eq
  simp only [SP1Clean.AddwOp.main, circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_c0, h_c1, h_l0, h_l1, h_msb, h_lmsb⟩ := h_holds
  simp only [Vector.getElem_map, sub_eq_add_neg]
  unfold id at *
  refine ⟨?_, ?_,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l0,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l1,
          by linear_combination h_msb,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_lmsb⟩
  · obtain h | h := mul_eq_zero.mp h_c0
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · obtain h | h := mul_eq_zero.mp h_c1
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq, h_m_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  subst h_m_eq
  simp only [Vector.getElem_map, sub_eq_add_neg] at h_spec
  obtain ⟨hb0, hb1, hr0, hr1, hmsb, hlmsb⟩ := h_spec
  simp only [SP1Clean.AddwOp.main, circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  unfold id at *
  refine ⟨?_, ?_,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr0,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr1,
          by linear_combination hmsb,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hlmsb⟩
  · rcases hb0 with h | h <;> rw [h] <;> ring
  · rcases hb1 with h | h <;> rw [h] <;> ring

end Assertion

/-- The full Clean `FormalAssertion` for `AddwOperation`: soundness +
completeness against the inlined `Assertion.Spec`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.AddwOp
