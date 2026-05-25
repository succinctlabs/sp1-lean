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
import SP1Operations.Operation.SubOperation.SubOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.Operations.AddOperation

/-! # `SubOperation` gadget mirror — Assertion style

The borrow-chain twin of `SP1Clean.AddOperation`. SP1's `SubOperation` is a
4-limb borrow-chain 64-bit subtract; its auto-gen carries `d_i` are in
inverse/borrow form, while the natural-form iff lemma
`SubOperation.allHold_constraints_iff` re-phrases them as the
natural-form carries `c_i`.

The Clean-side `main` matches SP1's auto-gen RHS (borrow form) verbatim,
keeping the `iff_sp1` bridge a one-line re-export. The `Spec` uses the
natural-form carries so it reads symmetrically with `AddOp.Spec`.
-/

namespace SP1Clean.SubOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Asserts the borrow chain holds between the operand
limbs `a`, `b` and the result limbs `result`, and that each result limb
fits in `< 2^16`. The borrow expression matches SP1's auto-gen
`SubOperation.constraints` verbatim. -/
def main (a b result : Vector (Expression (ZMod p)) 4) : Circuit (ZMod p) Unit := do
  let k65536 : Expression (ZMod p) := 65536
  let k1 : Expression (ZMod p) := 1
  let d0 := (a[0] + k65536 - k1 - b[0] - result[0] + k1) * (65536 : ZMod p)⁻¹
  let d1 := (a[1] + k65536 - k1 - b[1] - result[1] + d0) * (65536 : ZMod p)⁻¹
  let d2 := (a[2] + k65536 - k1 - b[2] - result[2] + d1) * (65536 : ZMod p)⁻¹
  let d3 := (a[3] + k65536 - k1 - b[3] - result[3] + d2) * (65536 : ZMod p)⁻¹
  d0 * (d0 - 1) === 0
  d1 * (d1 - 1) === 0
  d2 * (d2 - 1) === 0
  d3 * (d3 - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[0], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[1], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[2], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[3], 16, 0] : Vector (Expression (ZMod p)) 4)

/-- Pilot Spec, mirroring `SubOperation.allHold_constraints_iff` RHS
verbatim: each of the 4 natural-form carries is boolean and each result
limb fits in `< 65536`. -/
def Spec (a b result : Word (ZMod p)) : Prop :=
  let carry0 : ZMod p := (b[0] + result[0] - a[0]) * 65536⁻¹
  let carry1 : ZMod p := (b[1] + result[1] - a[1] + carry0) * 65536⁻¹
  let carry2 : ZMod p := (b[2] + result[2] - a[2] + carry1) * 65536⁻¹
  let carry3 : ZMod p := (b[3] + result[3] - a[3] + carry2) * 65536⁻¹
  (carry0 = 0 ∨ carry0 = 1) ∧
  (carry1 = 0 ∨ carry1 = 1) ∧
  (carry2 = 0 ∨ carry2 = 1) ∧
  (carry3 = 0 ∨ carry3 = 1) ∧
  result[0].val < 65536 ∧
  result[1].val < 65536 ∧
  result[2].val < 65536 ∧
  result[3].val < 65536

/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. Direct re-export of
`SubOperation.allHold_constraints_iff`. -/
theorem iff_sp1 (a b : Word (ZMod p)) (cols : SubOperation (ZMod p)) :
    (SubOperation.constraints a b cols 1).allHold ↔
      Spec a b cols.value :=
  SubOperation.allHold_constraints_iff a b cols

/-! ## Full `FormalAssertion` promotion

Wraps the assertion-style `main` above into a Clean `FormalAssertion`. The
`Assertion.Spec` is stated in **borrow form** (matching `main` verbatim)
rather than the natural form used by the top-level `Spec` / `iff_sp1`. The
two forms are algebraically related by `d_i = 1 - c_i`; the top-level
chip's `iff_sp1` continues to consume the natural-form `Spec`. -/

/-- Bundled FormalAssertion input: the two operand words and the result
word. -/
structure Inputs (F : Type) where
  a : fields 4 F
  b : fields 4 F
  result : fields 4 F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Wrapper around `SP1Clean.SubOp.main` that destructures a `Var Inputs`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Clean.SubOp.main input.a input.b input.result

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.SubOp"
  main := main
  localLength _ := 0

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The FormalAssertion's spec, in **borrow form**: each of the 4 inverse
borrow values `d_i` is boolean, and each result limb fits in `< 65536`.
Matches `SP1Clean.SubOp.main` body verbatim. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let d0 : ZMod p :=
    (input.a[0] + 65536 - 1 - input.b[0] - input.result[0] + 1) * 65536⁻¹
  let d1 : ZMod p :=
    (input.a[1] + 65536 - 1 - input.b[1] - input.result[1] + d0) * 65536⁻¹
  let d2 : ZMod p :=
    (input.a[2] + 65536 - 1 - input.b[2] - input.result[2] + d1) * 65536⁻¹
  let d3 : ZMod p :=
    (input.a[3] + 65536 - 1 - input.b[3] - input.result[3] + d2) * 65536⁻¹
  (d0 = 0 ∨ d0 = 1) ∧
  (d1 = 0 ∨ d1 = 1) ∧
  (d2 = 0 ∨ d2 = 1) ∧
  (d3 = 0 ∨ d3 = 1) ∧
  input.result[0].val < 65536 ∧
  input.result[1].val < 65536 ∧
  input.result[2].val < 65536 ∧
  input.result[3].val < 65536

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  simp only [SP1Clean.SubOp.main, circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_d0, h_d1, h_d2, h_d3, h_l0, h_l1, h_l2, h_l3⟩ := h_holds
  simp only [Vector.getElem_map]
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l0,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l1,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l2,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l3⟩
  · obtain h | h := mul_eq_zero.mp h_d0
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · obtain h | h := mul_eq_zero.mp h_d1
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · obtain h | h := mul_eq_zero.mp h_d2
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · obtain h | h := mul_eq_zero.mp h_d3
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  simp only [Vector.getElem_map, sub_eq_add_neg] at h_spec
  obtain ⟨hb0, hb1, hb2, hb3, hr0, hr1, hr2, hr3⟩ := h_spec
  simp only [SP1Clean.SubOp.main, circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr0,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr1,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr2,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr3⟩
  · rcases hb0 with h | h <;> rw [h] <;> ring
  · rcases hb1 with h | h <;> rw [h] <;> ring
  · rcases hb2 with h | h <;> rw [h] <;> ring
  · rcases hb3 with h | h <;> rw [h] <;> ring

end Assertion

/-- The full Clean `FormalAssertion` for `SubOperation`: soundness +
completeness against the borrow-form `Assertion.Spec`, no internal
witnesses. Compose into a chip's `main` via `SubOp.assertion input`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.SubOp
