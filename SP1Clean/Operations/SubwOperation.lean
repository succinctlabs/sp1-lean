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
import SP1Operations.Operation.SubwOperation.SubwOperation
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.Operations.AddOperation

/-! # `SubwOperation` gadget mirror — Assertion style

SP1's `SubwOperation` is a 2-limb borrow-chain 32-bit subtract plus a
`U16MSBOperation` sub-fragment that pins the msb of the second result limb.
The natural-form iff lemma `SubwOperation.allHold_constraints_iff`
exposes both: a `List.Forall ... U16MSBOperation.constraints` clause on
`(cols.value[1], cols.msb)` plus the carry+limb-bound clauses for the two
result limbs.

The Clean mirror keeps the same shape: `main` emits the borrow-form
asserts, the two Range(16) lookups, and inlines the `U16MSBOperation`
constraints — `iff_sp1` is then a one-line re-export of the SP1 lemma.
-/

namespace SP1Clean.SubwOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Asserts the 2-limb borrow chain, byte-bounds each
result limb, and emits the `U16MSBOperation` sub-fragment for `value[1]`
with witnessed `msb`. -/
def main (a b : Vector (Expression (ZMod p)) 4)
    (result : Vector (Expression (ZMod p)) 2)
    (msb : Expression (ZMod p)) : Circuit (ZMod p) Unit := do
  let k65536 : Expression (ZMod p) := 65536
  let k1 : Expression (ZMod p) := 1
  let d0 := (a[0] + k65536 - k1 - b[0] - result[0] + k1) * (65536 : ZMod p)⁻¹
  let d1 := (a[1] + k65536 - k1 - b[1] - result[1] + d0) * (65536 : ZMod p)⁻¹
  d0 * (d0 - 1) === 0
  d1 * (d1 - 1) === 0
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

/-- Pilot Spec, mirroring `SubwOperation.allHold_constraints_iff` RHS
verbatim: a `U16MSBOperation` constraints clause plus 2 natural-form
carries are boolean plus each result limb fits in `< 65536`. The
U16MSBOperation clause is left as `List.Forall ...` (matching the SP1
lemma) — promoting to the `SP1Clean.U16MSBOp.Spec` form is a follow-up. -/
def Spec (a b : Word (ZMod p)) (cols : _root_.SubwOperation (ZMod p)) : Prop :=
  let carry0 : ZMod p := (b[0] + cols.value[0] - a[0]) * 65536⁻¹
  let carry1 : ZMod p := (b[1] + cols.value[1] - a[1] + carry0) * 65536⁻¹
  List.Forall SP1Constraint.toProp
      (_root_.U16MSBOperation.constraints cols.value[1] { msb := cols.msb.msb } 1) ∧
  (carry0 = 0 ∨ carry0 = 1) ∧
  (carry1 = 0 ∨ carry1 = 1) ∧
  cols.value[0].val < 65536 ∧
  cols.value[1].val < 65536

/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. Direct re-export of
`SubwOperation.allHold_constraints_iff`. -/
theorem iff_sp1 (a b : Word (ZMod p)) (cols : _root_.SubwOperation (ZMod p)) :
    (_root_.SubwOperation.constraints a b cols 1).allHold ↔
      Spec a b cols :=
  _root_.SubwOperation.allHold_constraints_iff a b cols

/-! ## Full `FormalAssertion` promotion

Wraps the assertion-style `main` above (which already takes `msb` as a
parameter) into a Clean `FormalAssertion`. The `Assertion.Spec` is
stated in **borrow form** for the 2-limb chain (matching `main`'s `d_i`
expressions verbatim) plus inlined U16MSB clauses. -/

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

/-- Wrapper around `SP1Clean.SubwOp.main` that destructures a `Var Inputs`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Clean.SubwOp.main input.a input.b input.result input.msb

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.SubwOp"
  main := main
  localLength _ := 0

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The FormalAssertion's spec, in **borrow form** for the 2-limb chain
(matching `SP1Clean.SubwOp.main` verbatim), plus inlined U16MSB clauses. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let d0 : ZMod p :=
    (input.a[0] + 65536 - 1 - input.b[0] - input.result[0] + 1) * 65536⁻¹
  let d1 : ZMod p :=
    (input.a[1] + 65536 - 1 - input.b[1] - input.result[1] + d0) * 65536⁻¹
  let msb_check : ZMod p := 2 * input.result[1] - input.msb * 65536
  (d0 = 0 ∨ d0 = 1) ∧
  (d1 = 0 ∨ d1 = 1) ∧
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
  simp only [SP1Clean.SubwOp.main, circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_d0, h_d1, h_l0, h_l1, h_msb, h_lmsb⟩ := h_holds
  simp only [Vector.getElem_map, sub_eq_add_neg]
  unfold id at *
  refine ⟨?_, ?_,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l0,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l1,
          by linear_combination h_msb,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_lmsb⟩
  · obtain h | h := mul_eq_zero.mp h_d0
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · obtain h | h := mul_eq_zero.mp h_d1
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
  simp only [SP1Clean.SubwOp.main, circuit_norm, Lookup.Completeness, Table.toRaw,
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

/-- The full Clean `FormalAssertion` for `SubwOperation`: soundness +
completeness against the borrow-form `Assertion.Spec`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-- Bridge between the borrow-form `Assertion.Spec` (matching `main`'s `d_i`
expressions verbatim) and the natural-form `Spec` (which `iff_sp1` bridges
to SP1's allHold). Mirrors `SubwOperation.allHold_constraints_iff`'s
internal d↔c carry-swap + U16MSB conversion, but localized to Clean's
two Spec forms. -/
theorem Assertion_Spec_iff_Spec (a b : Word (ZMod p)) (value : Vector (ZMod p) 2)
    (msb : ZMod p) :
    Assertion.Spec ⟨a, b, value, msb⟩ ↔
      Spec a b { value := value, msb := { msb := msb } } := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hbridge : (65536 : ZMod p)⁻¹ * (65536 : ZMod p) = 1 :=
    inv_mul_cancel₀ val_65536_ne_zero
  refine ⟨?_, ?_⟩
  · rintro ⟨h_d0, h_d1, hr0, hr1, h_msb_bin, h_msb_check⟩
    refine ⟨?_, ?_, ?_, hr0, hr1⟩
    · -- U16MSB: bridge `(msb_bin ∧ msb_check_range)` to
      -- `List.Forall toProp (U16MSBOperation.constraints …)`.
      rw [_root_.U16MSBOperation.allHold_constraints_iff (is_real := 1)]
      refine ⟨Or.inr rfl, ?_, fun _ => h_msb_check⟩
      rcases mul_eq_zero.mp h_msb_bin with h | h
      · exact Or.inl h
      · exact Or.inr (by linear_combination h)
    · -- carry0 ∈ {0,1}: linear_combination on h_d0 and hbridge.
      rcases h_d0 with h | h
      · exact Or.inr (by linear_combination -h + hbridge)
      · exact Or.inl (by linear_combination -h + hbridge)
    · -- carry1 ∈ {0,1}: chained linear_combination (depends on carry0's bridge).
      rcases h_d1 with h | h
      · exact Or.inr (by
          linear_combination -h + (1 + (65536 : ZMod p)⁻¹) * hbridge)
      · exact Or.inl (by
          linear_combination -h + (1 + (65536 : ZMod p)⁻¹) * hbridge)
  · rintro ⟨h_u16, h_c0, h_c1, hr0, hr1⟩
    -- Extract borrow-form msb_bin + msb_check_range from the SP1-style
    -- U16MSB allHold clause via `U16MSBOperation.allHold_constraints_iff`.
    rw [_root_.U16MSBOperation.allHold_constraints_iff (is_real := 1)] at h_u16
    obtain ⟨_, h_msb_bin_or, h_msb_check_imp⟩ := h_u16
    have h_msb_check : (2 * value[1] - msb * 65536 : ZMod p).val < 65536 :=
      h_msb_check_imp one_ne_zero
    have h_msb_bin : msb * (msb - 1) = 0 := by
      -- h_msb_bin_or has the struct-projection form `{...}.msb.msb ∈ {0,1}`;
      -- reduce to bare `msb ∈ {0,1}` before substituting.
      have h_msb_bin_or' : msb = 0 ∨ msb = 1 := h_msb_bin_or
      rcases h_msb_bin_or' with h | h
      · rw [h]; ring
      · rw [h]; ring
    refine ⟨?_, ?_, hr0, hr1, h_msb_bin, h_msb_check⟩
    · -- d0 ∈ {0,1} from c0 ∈ {0,1} via reverse bridge.
      rcases h_c0 with h | h
      · exact Or.inr (by linear_combination -h + hbridge)
      · exact Or.inl (by linear_combination -h + hbridge)
    · -- d1 ∈ {0,1} from c1 ∈ {0,1} via reverse bridge.
      rcases h_c1 with h | h
      · exact Or.inr (by
          linear_combination -h + (1 + (65536 : ZMod p)⁻¹) * hbridge)
      · exact Or.inl (by
          linear_combination -h + (1 + (65536 : ZMod p)⁻¹) * hbridge)

end SP1Clean.SubwOp
