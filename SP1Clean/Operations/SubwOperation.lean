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
import SP1Clean.SP1Lookup
import SP1Clean.Operations.AddOperation
import SP1Clean.Operations.U16MSBOperation

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

/-! ## Multiplicity-gated `AssertionGated` form

Parallel to the unconditional `Assertion` namespace above. Adds an
`is_real` multiplicity gate that vanishes every emitted constraint on
padding rows, matching SP1's `SubwOperation.constraints` gating pattern.

The contract is **semantic-only**: `Spec` carries the BV32 + MSB
equation directly (matching `SubwOperation.iff_sp1_full`'s RHS verbatim)
under `is_real = 1`. The borrow-form decomposition stays an
implementation detail of `main`; the soundness/completeness proofs
route through the existing `Assertion_Spec_iff_Spec` bridge to swap
between borrow and natural-form carries, mirroring `AddwOp`'s gated
proof one level down. -/

/-- Multiplicity-aware input: two operand words, the 2-limb result, the
externally-supplied msb bit, and the gating multiplicity `is_real`. -/
structure InputsGated (F : Type) where
  a : fields 4 F
  b : fields 4 F
  result : fields 2 F
  msb : F
  is_real : F
deriving ProvableStruct

namespace AssertionGated

open Circuit

/-- Multiplicity-gated `main`: gates the binarity of `is_real`, the
2-limb borrow chain quadratics, both byte-range lookups, and the U16MSB
sub-circuit by `is_real`. The U16MSB sub-fragment is now a true gated
subcircuit (`U16MSBOp.assertionGated`) rather than inlined as in the
unconditional `Assertion.main`. -/
@[reducible]
def main (input : Var InputsGated (ZMod p)) : Circuit (ZMod p) Unit := do
  let k65536 : Expression (ZMod p) := 65536
  let k1 : Expression (ZMod p) := 1
  input.is_real * (input.is_real - 1) === 0
  let d0 := (input.a[0] + k65536 - k1 - input.b[0] - input.result[0] + k1)
              * (65536 : ZMod p)⁻¹
  let d1 := (input.a[1] + k65536 - k1 - input.b[1] - input.result[1] + d0)
              * (65536 : ZMod p)⁻¹
  input.is_real * (d0 * (d0 - 1)) === 0
  input.is_real * (d1 * (d1 - 1)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), input.result[0], 16, 0], input.is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), input.result[1], 16, 0], input.is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertionGated
    (⟨input.result[1], input.msb, input.is_real⟩ :
     Var SP1Clean.U16MSBOp.InputsGated (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) InputsGated unit where
  name := "SP1Clean.SubwOpGated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

/-- Binarity of `is_real` (asserted by chip side) plus the operand
`isU64` bounds needed to bridge the borrow-form Spec to the semantic
`SubwOperation.iff_sp1_full` RHS. -/
def Assumptions (input : InputsGated (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 → Word.isU64 input.a ∧ Word.isU64 input.b)

/-- Semantic contract mirroring `SubwOperation.iff_sp1_full`'s RHS:
on real rows, the 2-limb result is a u32, its 32-bit BitVec equals the
32-bit SUBW of the operands, and `msb` is the BitVec-msb-of-result bit. -/
def Spec (input : InputsGated (ZMod p)) : Prop :=
  input.is_real = 1 →
    HWord.isU32 input.result ∧
    HWord.toBitVec32 input.result =
      execute_RTYPEW_pure_32_w input.a input.b .SUBW ∧
    input.msb = (if (HWord.toBitVec32 input.result).msb then 1 else 0)

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [AssertionGated.main]
  obtain ⟨h_a_eq, h_b_eq, h_r_eq, h_m_eq, h_ir_eq⟩ := h_input
  subst h_a_eq; subst h_b_eq; subst h_r_eq; subst h_m_eq; subst h_ir_eq
  obtain ⟨h_ir_bin, h_gd0, h_gd1, h_l0_sub, h_l1_sub, h_u16_sub⟩ := h_holds
  obtain ⟨_h_ir_binary, h_bounds⟩ := h_assumptions
  intro h_is_real
  unfold id at *
  obtain ⟨h_isU64_a, h_isU64_b⟩ := h_bounds h_is_real
  haveI : NeZero p := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩
  have h_ir_ne_zero : Expression.eval env input_var_is_real ≠ 0 := by
    rw [h_is_real]; exact one_ne_zero
  -- Extract ungated borrow/range/U16MSB facts from gated emissions.
  have h_d0 := (mul_eq_zero.mp h_gd0).resolve_left h_ir_ne_zero
  have h_d1 := (mul_eq_zero.mp h_gd1).resolve_left h_ir_ne_zero
  have hr0 :=
    SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _
      ((h_l0_sub trivial).resolve_left h_ir_ne_zero)
  have hr1 :=
    SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _
      ((h_l1_sub trivial).resolve_left h_ir_ne_zero)
  have h_u16_assumps :
      Expression.eval env input_var_is_real = 0 ∨
      Expression.eval env input_var_is_real = 1 := Or.inr h_is_real
  have ⟨h_msb_bin, h_msb_check⟩ := (h_u16_sub h_u16_assumps) h_is_real
  -- Assemble the borrow-form `SubwOp.Assertion.Spec`.
  have h_subw_assertion : SP1Clean.SubwOp.Assertion.Spec
      ⟨Vector.map (Expression.eval env) input_var_a,
       Vector.map (Expression.eval env) input_var_b,
       Vector.map (Expression.eval env) input_var_result,
       Expression.eval env input_var_msb⟩ := by
    simp only [SP1Clean.SubwOp.Assertion.Spec, Vector.getElem_map, sub_eq_add_neg]
    refine ⟨?_, ?_, hr0, hr1, ?_, ?_⟩
    · rcases mul_eq_zero.mp h_d0 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    · rcases mul_eq_zero.mp h_d1 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    · linear_combination h_msb_bin
    · -- msb_check: bridge `↑2 + -y` (Spec goal after sub_eq_add_neg) to
      -- `2 - y` (the U16MSB subcircuit's exact form) via convert + ring.
      convert h_msb_check using 2
      push_cast
      ring
  -- Bridge borrow form → natural form → allHold → semantic triple.
  have h_subw_natural :=
    (SP1Clean.SubwOp.Assertion_Spec_iff_Spec _ _ _ _).mp h_subw_assertion
  have h_allHold :=
    (SP1Clean.SubwOp.iff_sp1 _ _ _).mpr h_subw_natural
  exact (_root_.SubwOperation.iff_sp1_full h_isU64_a h_isU64_b).mp h_allHold

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [AssertionGated.main]
  obtain ⟨h_a_eq, h_b_eq, h_r_eq, h_m_eq, h_ir_eq⟩ := h_input
  subst h_a_eq; subst h_b_eq; subst h_r_eq; subst h_m_eq; subst h_ir_eq
  obtain ⟨h_ir_binary, h_bounds⟩ := h_assumptions
  haveI : NeZero p := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩
  unfold id at *
  rcases h_ir_binary with h_ir0 | h_ir1
  · -- Padding row: is_real = 0; all gated emissions trivialize.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ir0]; ring
    · rw [h_ir0]; ring
    · rw [h_ir0]; ring
    · exact ⟨trivial, Or.inl h_ir0⟩
    · exact ⟨trivial, Or.inl h_ir0⟩
    · refine ⟨Or.inl h_ir0, fun h_contra => ?_⟩
      exact absurd (h_ir0.symm.trans h_contra) zero_ne_one
  · -- Real row: recover SubwOp.Assertion.Spec via spec_inv → iff_sp1.mp →
    -- Assertion_Spec_iff_Spec.mpr; disassemble; distribute `is_real`.
    obtain ⟨h_isU64_a, h_isU64_b⟩ := h_bounds h_ir1
    obtain ⟨h_isU32_v, h_bv, h_msb_eq⟩ := h_spec h_ir1
    have h_allHold :=
      _root_.SubwOperation.spec_inv
        (cols := { value := Vector.map (Expression.eval env) input_var_result,
                   msb := { msb := Expression.eval env input_var_msb } })
        h_isU64_a h_isU64_b h_isU32_v h_bv h_msb_eq
    have h_subw_natural := (SP1Clean.SubwOp.iff_sp1 _ _ _).mp h_allHold
    have h_subw_assertion :=
      (SP1Clean.SubwOp.Assertion_Spec_iff_Spec _ _ _ _).mpr h_subw_natural
    simp only [SP1Clean.SubwOp.Assertion.Spec, Vector.getElem_map, sub_eq_add_neg]
      at h_subw_assertion
    obtain ⟨hd0, hd1, hr0, hr1, h_msb_bin, h_msb_check⟩ := h_subw_assertion
    -- Normalize `↑65536`/`↑1`/`↑2` Nat-casts in the borrow-form hypotheses
    -- so the `rw [h]` on d0/d1 finds the goal's bare-literal pattern.
    push_cast at hd0 hd1 h_msb_check
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ir1]; ring
    · rw [h_ir1]; rcases hd0 with h | h <;> rw [h] <;> ring
    · rw [h_ir1]; rcases hd1 with h | h <;> rw [h] <;> ring
    · exact ⟨trivial,
             Or.inr (SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr0)⟩
    · exact ⟨trivial,
             Or.inr (SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr1)⟩
    · refine ⟨Or.inr h_ir1, fun _ => ⟨?_, ?_⟩⟩
      · linear_combination h_msb_bin
      · convert h_msb_check using 2
        push_cast
        ring

end AssertionGated

/-- Multiplicity-gated FormalAssertion for `SubwOperation`. Spec is the
semantic `SubwOperation.iff_sp1_full` RHS (gated on `is_real = 1`),
identical in shape to `SubOp.assertion`'s contract one level down. -/
def assertionGated : FormalAssertion (ZMod p) InputsGated :=
  { AssertionGated.elaborated with
    Assumptions := AssertionGated.Assumptions,
    Spec := AssertionGated.Spec,
    soundness := AssertionGated.soundness,
    completeness := AssertionGated.completeness }

end SP1Clean.SubwOp
