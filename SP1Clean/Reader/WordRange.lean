import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Foundations.Word
import SP1Clean.ByteOpcodeTable
import SP1Clean.SP1Lookup

/-! # `WordRange.assertion` — `Word.isU64` via 4 `Range 16` byte lookups

A leaf byte-bus primitive that range-checks each limb of a 4-limb `Word`
to be `< 2^16`. Composed by `OperandAccess` (alongside
`RegisterAccessTimestamp`) to provide the `Word.isU64 prev_value`
component of a memory operand's byte-bus content.

In Rust this corresponds to the `Word`-shaped `assert_word`/range-check
that fires alongside `eval_register_access_timestamp` — there is no
dedicated Rust helper that emits these 4 lookups in isolation, but
splitting them out on the Lean side gives a cleaner sub-circuit graph and
makes the `Word.isU64` Spec contract explicit. -/

namespace SP1Clean.WordRange

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

instance : Fact (p > 512) := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩

/-- Inputs for the gated Word range-check assertion. -/
structure Inputs (F : Type) where
  value : Vector F 4
  mult : F
deriving ProvableStruct

/-- Emit the 4 gated byte lookups (one per limb in `Range 16`). -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  SP1Lookup.byteOpcodeGated
    ⟨#v[(6 : Expression (ZMod p)), input.value[0], 16, 0], input.mult⟩
  SP1Lookup.byteOpcodeGated
    ⟨#v[(6 : Expression (ZMod p)), input.value[1], 16, 0], input.mult⟩
  SP1Lookup.byteOpcodeGated
    ⟨#v[(6 : Expression (ZMod p)), input.value[2], 16, 0], input.mult⟩
  SP1Lookup.byteOpcodeGated
    ⟨#v[(6 : Expression (ZMod p)), input.value[3], 16, 0], input.mult⟩

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.WordRange"
  main := main
  -- 4 byteOpcodeGated subcircuit calls × 4 witnesses each = 16.
  localLength _ := 16
  localLength_eq _ _ := by simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Gated spec: vacuous when `mult = 0`; otherwise `Word.isU64 value`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.mult = 0 ∨ Word.isU64 input.value

/-- Helper: `byteOpcodeSpec` row `#v[6, x, 16, 0]` ⇒ `x.val < 65536`.
Local copy of the same helper used in `RegisterAccessTimestamp` /
`OperandAccess` / `AddOperation` etc. -/
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

lemma byteOpcodeSpec_range16_of_lt
    (x : ZMod p) (hx : x.val < 65536) :
    SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, 16, 0]) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  refine ⟨.Range, ?_, ?_⟩
  · simp only [ByteOpcode.toNat, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, Nat.cast_ofNat]
  · simp only [ByteOpcode.constrain_Range, Vector.getElem_mk,
               List.getElem_toArray, List.getElem_cons_zero,
               List.getElem_cons_succ]
    have h16 : (16 : ZMod p).val = 16 := by
      rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [h16]
    exact hx

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_value_eq, h_mult_eq⟩ := h_input
  subst_eqs
  obtain ⟨d0, d1, d2, d3⟩ := h_holds
  simp only [SP1Lookup.ByteOpcodeGated.Spec, SP1Lookup.ByteOpcodeGated.Assumptions,
             forall_const] at d0 d1 d2 d3
  by_cases h_mult : Expression.eval env input_var_mult = 0
  · exact Or.inl h_mult
  right
  have r0 := d0.resolve_left h_mult
  have r1 := d1.resolve_left h_mult
  have r2 := d2.resolve_left h_mult
  have r3 := d3.resolve_left h_mult
  apply Word.isU64_of_cases
  · rw [Vector.getElem_map]; exact byteOpcodeSpec_range16 _ r0
  · rw [Vector.getElem_map]; exact byteOpcodeSpec_range16 _ r1
  · rw [Vector.getElem_map]; exact byteOpcodeSpec_range16 _ r2
  · rw [Vector.getElem_map]; exact byteOpcodeSpec_range16 _ r3

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_value_eq, h_mult_eq⟩ := h_input
  subst_eqs
  rcases h_spec with h_mult_zero | h_isU64
  · simp only [SP1Lookup.ByteOpcodeGated.Spec, SP1Lookup.ByteOpcodeGated.Assumptions,
               true_and]
    exact ⟨Or.inl h_mult_zero, Or.inl h_mult_zero,
           Or.inl h_mult_zero, Or.inl h_mult_zero⟩
  · obtain ⟨h_pv0, h_pv1, h_pv2, h_pv3⟩ := Word.lt_cases_of_isU64 h_isU64
    rw [Vector.getElem_map] at h_pv0 h_pv1 h_pv2 h_pv3
    simp only [SP1Lookup.ByteOpcodeGated.Spec, SP1Lookup.ByteOpcodeGated.Assumptions,
               true_and]
    refine ⟨?_, ?_, ?_, ?_⟩
    · right; exact byteOpcodeSpec_range16_of_lt _ h_pv0
    · right; exact byteOpcodeSpec_range16_of_lt _ h_pv1
    · right; exact byteOpcodeSpec_range16_of_lt _ h_pv2
    · right; exact byteOpcodeSpec_range16_of_lt _ h_pv3

end Assertion

/-- The Clean `FormalAssertion` for a 4-limb `Word.isU64` range check via
4 gated byte lookups. Composed by `OperandAccess.assertion` alongside
`RegisterAccessTimestamp.assertion`. -/
def assertion : FormalAssertion (ZMod p) Assertion.Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.WordRange
