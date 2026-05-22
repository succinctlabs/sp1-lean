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
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Clean.ByteOpcodeTable

/-! # `AddOperation` gadget mirror — Assertion style

SP1's `AddOperation` is a 4-limb carry-chain 64-bit add. In SP1 Rust, the
gadget takes the two operand limb vectors `a`, `b` plus a `cols :
AddOperationCols<T>` (whose `cols.value` field holds the result limbs) and
emits constraints relating them — it does *not* witness the result columns
internally; those belong to the enclosing chip's column struct.

This Clean mirror adopts the same shape: `main` takes `(a, b, result)` and
emits the 4 inverse-form boolean carry asserts plus 4 `Range(16)` byte
lookups bounding each result limb. The Spec adopts SP1's
inverse-form RHS verbatim, so `iff_sp1` is a one-line re-export of
`AddOperation.allHold_constraints_iff`.
-/

namespace SP1Clean.AddOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Asserts the carry chain holds between the operand
limbs `a`, `b` and the result limbs `result`, and that each result limb
fits in `< 2^16`. No internal witnesses — `result` is supplied by the
caller (typically as a column-struct field). -/
def main (a b result : Vector (Expression (ZMod p)) 4) : Circuit (ZMod p) Unit := do
  let c0 := (a[0] + b[0] - result[0]) * (65536 : ZMod p)⁻¹
  let c1 := (a[1] + b[1] - result[1] + c0) * (65536 : ZMod p)⁻¹
  let c2 := (a[2] + b[2] - result[2] + c1) * (65536 : ZMod p)⁻¹
  let c3 := (a[3] + b[3] - result[3] + c2) * (65536 : ZMod p)⁻¹
  c0 * (c0 - 1) === 0
  c1 * (c1 - 1) === 0
  c2 * (c2 - 1) === 0
  c3 * (c3 - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[0], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[1], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[2], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[3], 16, 0] : Vector (Expression (ZMod p)) 4)

/-- Pilot Spec, matching SP1's `AddOperation.allHold_constraints_iff`
RHS verbatim: each of the 4 inverse-form carries is boolean and each
result limb fits in `< 65536`. -/
def Spec (a b result : Word (ZMod p)) : Prop :=
  let carry0 : ZMod p := (a[0] + b[0] - result[0]) * 65536⁻¹
  let carry1 : ZMod p := (a[1] + b[1] - result[1] + carry0) * 65536⁻¹
  let carry2 : ZMod p := (a[2] + b[2] - result[2] + carry1) * 65536⁻¹
  let carry3 : ZMod p := (a[3] + b[3] - result[3] + carry2) * 65536⁻¹
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
`AddOperation.allHold_constraints_iff`. -/
theorem iff_sp1 (a b : Word (ZMod p)) (cols : AddOperation (ZMod p)) :
    (AddOperation.constraints a b cols 1).allHold ↔
      Spec a b cols.value :=
  AddOperation.allHold_constraints_iff a b cols

/-! ## Full `FormalAssertion` promotion

Wraps the assertion-style `main` above into a Clean `FormalAssertion`. The
input is a `ProvableStruct` bundling the two operand words and the result
word; no internal witnesses are introduced (`localLength _ := 0`). The
sub-assertion soundness/completeness compose into the chip-level proof
without going through `iff_sp1`. -/

/-- Bundled input to the FormalAssertion: the two operand words and the
result word. -/
structure Inputs (F : Type) where
  a : fields 4 F
  b : fields 4 F
  result : fields 4 F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Wrapper around `SP1Clean.AddOp.main` that destructures a `Var Inputs`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Clean.AddOp.main input.a input.b input.result

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.AddOp"
  main := main
  localLength _ := 0

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The FormalAssertion's spec re-packages `SP1Clean.AddOp.Spec` on the
struct fields. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  SP1Clean.AddOp.Spec input.a input.b input.result

/-- Helper: unwrap a `ByteOpcodeSpec` row of the form `#v[6, x, 16, 0]` into
the range bound `x.val < 65536`. Used in soundness — the existential `bop`
is pinned to `Range` by `bop.toNat = 6` (the only opcode with toNat 6),
which is sound under `Fact (2^17 < p)`. -/
lemma byteOpcodeSpec_range16
    (x : ZMod p)
    (h : SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, 16, 0])) :
    x.val < 65536 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨bop, hbop, hconstr⟩ := h
  have h_eq : bop = .Range := by
    have h6 : (6 : ZMod p) = ((6 : ℕ) : ZMod p) := by push_cast; rfl
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at hbop
    rw [h6] at hbop
    apply_fun ZMod.val at hbop
    have h_lt : bop.toNat < 7 := by cases bop <;> simp [ByteOpcode.toNat]
    rw [ZMod.val_natCast, ZMod.val_natCast,
        Nat.mod_eq_of_lt (by omega : bop.toNat < p),
        Nat.mod_eq_of_lt (by omega : (6 : ℕ) < p)] at hbop
    cases bop <;> simp [ByteOpcode.toNat] at hbop
    rfl
  subst h_eq
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
             List.getElem_cons_zero, ByteOpcode.constrain_Range] at hconstr
  have h16 : (16 : ZMod p).val = 16 := by
    rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [h16] at hconstr
  exact hconstr

/-- Helper for completeness: given `x.val < 65536`, build a `ByteOpcodeSpec`
witnessed by `bop = Range`. -/
lemma byteOpcodeSpec_range16_of_lt
    (x : ZMod p) (hx : x.val < 65536) :
    SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, 16, 0]) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  refine ⟨.Range, ?_, ?_⟩
  · simp only [ByteOpcode.toNat, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, Nat.cast_ofNat]
  · simp only [ByteOpcode.constrain_Range, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    have h16 : (16 : ZMod p).val = 16 := by
      rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [h16]
    exact hx

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  simp only [SP1Clean.AddOp.main, circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_c0, h_c1, h_c2, h_c3, h_l0, h_l1, h_l2, h_l3⟩ := h_holds
  simp only [AddOp.Spec, Vector.getElem_map]
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_,
          byteOpcodeSpec_range16 _ h_l0,
          byteOpcodeSpec_range16 _ h_l1,
          byteOpcodeSpec_range16 _ h_l2,
          byteOpcodeSpec_range16 _ h_l3⟩
  · obtain h | h := mul_eq_zero.mp h_c0
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · obtain h | h := mul_eq_zero.mp h_c1
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · obtain h | h := mul_eq_zero.mp h_c2
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · obtain h | h := mul_eq_zero.mp h_c3
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  simp only [AddOp.Spec, Vector.getElem_map, sub_eq_add_neg] at h_spec
  obtain ⟨hb0, hb1, hb2, hb3, hr0, hr1, hr2, hr3⟩ := h_spec
  simp only [SP1Clean.AddOp.main, circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_,
          byteOpcodeSpec_range16_of_lt _ hr0,
          byteOpcodeSpec_range16_of_lt _ hr1,
          byteOpcodeSpec_range16_of_lt _ hr2,
          byteOpcodeSpec_range16_of_lt _ hr3⟩
  · rcases hb0 with h | h <;> rw [h] <;> ring
  · rcases hb1 with h | h <;> rw [h] <;> ring
  · rcases hb2 with h | h <;> rw [h] <;> ring
  · rcases hb3 with h | h <;> rw [h] <;> ring

end Assertion

/-- The full Clean `FormalAssertion` for `AddOperation`: soundness +
completeness against `Spec`, no internal witnesses. Compose into a chip's
`main` via `AddOp.assertion input` (the `CoeFun` from
`Clean.Circuit.Subcircuit` makes this a `Circuit Unit`). -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.AddOp
