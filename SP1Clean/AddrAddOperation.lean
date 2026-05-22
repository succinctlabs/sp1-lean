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
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Clean.ByteOpcodeTable

/-! # `AddrAddOperation` gadget mirror — Spec + iff_sp1 only

SP1's `AddrAddOperation` is the address-computation carry-chain used by
Load and Store chips: a 4-limb add `a + b` whose result fits in the
3-limb `cols.value` (the high 4th limb is constrained to be 0, since
SP1 addresses are 48-bit). Same shape as `AddOperation` (inverse-form
boolean carries + result-limb byte bounds), with the 4th carry forced
to absorb a zero high limb.

This mirror packages SP1's `allHold_constraints_iff` RHS as
`SP1Clean.AddrAddOp.Spec`, with `iff_sp1` a one-line re-export. Lets
the chip-level `SpecForIff` defs in
`LoadByte/LoadHalf/LoadWord/LoadDoubleChip.lean` and
`StoreHalf/StoreWord/StoreDoubleChip.lean` drop their inline
`(AddrAddOperation.constraints …).allHold` clauses for a named
predicate.

No `main` or `Assertion` bundle yet — those depend on Clean's
subcircuit DSL and add ~50 LoC of `ProvableStruct` plumbing.
Deferred to a follow-up iter; this minimal mirror is enough to clean
up the 10 chip SpecForIff defs that consume the operation today.
-/

namespace SP1Clean.AddrAddOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Asserts the address-add carry chain holds between
operand words `a, b` (4 limbs each) and a 3-limb result `value`. The 4th
carry uses `0` as the implicit high limb of the result, since SP1
addresses are 48-bit. -/
def main (a b : Vector (Expression (ZMod p)) 4)
    (value : Vector (Expression (ZMod p)) 3) : Circuit (ZMod p) Unit := do
  let c0 := (a[0] + b[0] - value[0]) * (65536 : ZMod p)⁻¹
  let c1 := (a[1] + b[1] - value[1] + c0) * (65536 : ZMod p)⁻¹
  let c2 := (a[2] + b[2] - value[2] + c1) * (65536 : ZMod p)⁻¹
  let c3 := (a[3] + b[3] - 0 + c2) * (65536 : ZMod p)⁻¹
  c0 * (c0 - 1) === 0
  c1 * (c1 - 1) === 0
  c2 * (c2 - 1) === 0
  c3 * (c3 - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), value[0], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), value[1], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), value[2], 16, 0] : Vector (Expression (ZMod p)) 4)

/-- Pilot Spec, matching SP1's `AddrAddOperation.allHold_constraints_iff`
RHS verbatim under `is_real = 1`. The carry chain is the same as
`AddOperation.Spec` but the 4th carry uses `0` as the high limb of
the result word (`cols.value` is 3 limbs since SP1 addresses are
48-bit), and there is no 4th result-limb bound. -/
def Spec (a b : Word (ZMod p)) (cols : _root_.AddrAddOperation (ZMod p)) : Prop :=
  let carry0 : ZMod p := (a[0] + b[0] - cols.value[0]) * 65536⁻¹
  let carry1 : ZMod p := (a[1] + b[1] - cols.value[1] + carry0) * 65536⁻¹
  let carry2 : ZMod p := (a[2] + b[2] - cols.value[2] + carry1) * 65536⁻¹
  let carry3 : ZMod p := (a[3] + b[3] - 0 + carry2) * 65536⁻¹
  (carry0 = 0 ∨ carry0 = 1) ∧
  (carry1 = 0 ∨ carry1 = 1) ∧
  (carry2 = 0 ∨ carry2 = 1) ∧
  (carry3 = 0 ∨ carry3 = 1) ∧
  cols.value[0].val < 65536 ∧
  cols.value[1].val < 65536 ∧
  cols.value[2].val < 65536

/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. Direct re-export of
`AddrAddOperation.allHold_constraints_iff`. -/
theorem iff_sp1 (a b : Word (ZMod p)) (cols : _root_.AddrAddOperation (ZMod p)) :
    (_root_.AddrAddOperation.constraints a b cols 1).allHold ↔
      Spec a b cols :=
  _root_.AddrAddOperation.allHold_constraints_iff a b cols

/-! ## Full `FormalAssertion` promotion

Wraps the assertion-style `main` above into a Clean `FormalAssertion`.
The input is a `ProvableStruct` bundling the two operand words and the
3-limb result vector; no internal witnesses are introduced. The
sub-assertion soundness/completeness compose into a chip-level proof
without going through `iff_sp1`. -/

/-- Bundled input to the FormalAssertion: the two operand words and the
3-limb result vector. -/
structure Inputs (F : Type) where
  a : fields 4 F
  b : fields 4 F
  value : fields 3 F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Wrapper around `SP1Clean.AddrAddOp.main` that destructures a `Var Inputs`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Clean.AddrAddOp.main input.a input.b input.value

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.AddrAddOp"
  main := main
  localLength _ := 0

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The FormalAssertion's spec re-packages `SP1Clean.AddrAddOp.Spec`
on the struct fields. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  SP1Clean.AddrAddOp.Spec input.a input.b { value := input.value }

/-- Helper: unwrap a `ByteOpcodeSpec` row of the form `#v[6, x, 16, 0]` into
the range bound `x.val < 65536`. -/
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

/-- Helper for completeness: given `x.val < 65536`, build a
`ByteOpcodeSpec` witnessed by `bop = Range`. -/
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
  obtain ⟨h_a_eq, h_b_eq, h_v_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_v_eq
  simp only [SP1Clean.AddrAddOp.main, circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_c0, h_c1, h_c2, h_c3, h_l0, h_l1, h_l2⟩ := h_holds
  simp only [AddrAddOp.Spec, Vector.getElem_map]
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_,
          byteOpcodeSpec_range16 _ h_l0,
          byteOpcodeSpec_range16 _ h_l1,
          byteOpcodeSpec_range16 _ h_l2⟩
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
  obtain ⟨h_a_eq, h_b_eq, h_v_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_v_eq
  simp only [AddrAddOp.Spec, Vector.getElem_map, sub_eq_add_neg] at h_spec
  obtain ⟨hb0, hb1, hb2, hb3, hr0, hr1, hr2⟩ := h_spec
  simp only [SP1Clean.AddrAddOp.main, circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_,
          byteOpcodeSpec_range16_of_lt _ hr0,
          byteOpcodeSpec_range16_of_lt _ hr1,
          byteOpcodeSpec_range16_of_lt _ hr2⟩
  · rcases hb0 with h | h <;> rw [h] <;> ring
  · rcases hb1 with h | h <;> rw [h] <;> ring
  · rcases hb2 with h | h <;> rw [h] <;> ring
  · rcases hb3 with h | h <;> rw [h] <;> ring

end Assertion

/-- The full Clean `FormalAssertion` for `AddrAddOperation`: soundness +
completeness against the carry-chain `Spec`, no internal witnesses.
Compose into a chip's `main` via `AddrAddOp.assertion input`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.AddrAddOp
