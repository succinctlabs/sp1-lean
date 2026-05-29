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
import SP1Foundations.Word
import SP1Clean.ByteOpcodeTable
import SP1Clean.MemoryBusTable
import SP1Clean.SP1Lookup
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.WordRange

/-! # `StoreMemoryAccessGated` sub-circuit

Mirror of `LoadMemoryAccessGated` for the store side. SP1's Store chips
emit the same memory-access shape as Load — boolean `flag`, clock-page
agreement when `flag = 1`, 65536-base timestamp equation, range bounds,
`Word.isU64` on the prior word — plus an explicit `write_value : Vector F 4`
(the bytes being written). The send/receive memory-bus pair on the store
side carries `write_value` in the receive (post-write state) instead of
`prev_value`.

## Status: real hint-witnessed circuit ("Avenue C")

Same promotion as `LoadMemoryAccessGated`: `main` emits the faithful
constraint content gated by `mult` (3 inline `mult`-gated `assertZero`s +
2 `byteOpcodeGated` range lookups + `WordRange` for `Word.isU64 prev_value`),
plus a second `WordRange` for `Word.isU64 write_value` (the store's extra
clause). `Assumptions := True`; `Spec := Contract` is proved from `h_holds`.
See `SP1Clean/Operations/LoadMemoryAccessGated.lean`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.StoreMemoryAccessGated

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Inputs: same as `LoadMemoryAccessGated` plus the explicit
`write_value` the store emits to the receive side. -/
structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  addr : Vector F 3
  prev_value : Vector F 4
  write_value : Vector F 4
  prev_high : F
  prev_low : F
  diff_low : F
  diff_high : F
  flag : F
  mult : F
deriving ProvableStruct

namespace Assertion

open Circuit

instance : Fact (p > 512) := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩

/-- Emit the faithful store-memory-access constraints, all gated by `mult`:
3 inline `mult`-gated `assertZero`s + 2 `byteOpcodeGated` range lookups +
`WordRange` for `Word.isU64 prev_value` + a second `WordRange` for
`Word.isU64 write_value`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  input.mult * (input.flag * (input.flag - 1)) === 0
  input.mult * (input.flag * (input.clk_high - input.prev_high)) === 0
  input.mult *
      (input.flag * (input.clk_low + 1) + (1 - input.flag) * input.clk_high -
        (input.flag * input.prev_low + (1 - input.flag) * input.prev_high) - 1 -
        (input.diff_low + input.diff_high * 65536)) === 0
  SP1Lookup.byteOpcodeGated
    ⟨#v[(6 : Expression (ZMod p)), input.diff_low, 16, 0], input.mult⟩
  SP1Lookup.byteOpcodeGated
    ⟨#v[(3 : Expression (ZMod p)), 0, input.diff_high, 0], input.mult⟩
  SP1Clean.WordRange.assertion
    (⟨input.prev_value, input.mult⟩ : Var SP1Clean.WordRange.Assertion.Inputs (ZMod p))
  SP1Clean.WordRange.assertion
    (⟨input.write_value, input.mult⟩ : Var SP1Clean.WordRange.Assertion.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.StoreMemoryAccessGated"
  main := main
  -- 3 inline gates (0) + 2 byteOpcodeGated (4 each) + 2 WordRange (16 each) = 40.
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The faithful store-memory-access contract, in disjunctive
(`mult = 0 ∨ …`) form so the assertion is vacuous on padding rows.
Mirrors `LoadMemoryAccessGated.Contract` plus an extra `Word.isU64 write_value`
clause for the bytes being written. -/
def Contract (input : Inputs (ZMod p)) : Prop :=
  input.mult = 0 ∨
    ((input.flag = 0 ∨ input.flag = 1) ∧
     (input.flag = 0 ∨ input.clk_high = input.prev_high) ∧
     input.flag * (input.clk_low + 1) + (1 - input.flag) * input.clk_high -
       (input.flag * input.prev_low + (1 - input.flag) * input.prev_high) - 1 =
       input.diff_low + input.diff_high * 65536 ∧
     input.diff_low.val < 65536 ∧
     input.diff_high < (256 : ZMod p) ∧
     Word.isU64 input.prev_value ∧
     Word.isU64 input.write_value)

/-- Spec is the contract — now *proved* from the in-circuit emissions. -/
def Spec (input : Inputs (ZMod p)) : Prop := Contract input

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_ch, h_cl, h_addr, h_pv, h_wv, h_phi, h_plo, h_dlo, h_dhi, h_flag,
          h_mult⟩ := h_input
  subst_eqs
  obtain ⟨g_bool, g_page, g_ts, d_diff, d_high, d_pv, d_wv⟩ := h_holds
  simp only [SP1Lookup.ByteOpcodeGated.Spec, SP1Lookup.ByteOpcodeGated.Assumptions,
             SP1Clean.WordRange.assertion, SP1Clean.WordRange.Assertion.Spec,
             SP1Clean.WordRange.Assertion.Assumptions,
             forall_const] at d_diff d_high d_pv d_wv
  by_cases h_mult0 : Expression.eval env input_var_mult = 0
  · exact Or.inl h_mult0
  right
  have r_diff := d_diff.resolve_left h_mult0
  have r_high := d_high.resolve_left h_mult0
  have r_pv := d_pv.resolve_left h_mult0
  have r_wv := d_wv.resolve_left h_mult0
  have g_bool' := (mul_eq_zero.mp g_bool).resolve_left h_mult0
  have g_page' := (mul_eq_zero.mp g_page).resolve_left h_mult0
  have g_ts' := (mul_eq_zero.mp g_ts).resolve_left h_mult0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases mul_eq_zero.mp g_bool' with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · rcases mul_eq_zero.mp g_page' with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · linear_combination g_ts'
  · exact SP1Clean.WordRange.Assertion.byteOpcodeSpec_range16 _ r_diff
  · exact SP1Clean.CPUState.Assertion.byteOpcodeSpec_u8range _ r_high
  · exact r_pv
  · exact r_wv

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_ch, h_cl, h_addr, h_pv, h_wv, h_phi, h_plo, h_dlo, h_dhi, h_flag,
          h_mult⟩ := h_input
  subst_eqs
  unfold id at *
  have h_spec' :
      Expression.eval env.toEnvironment input_var_mult = 0 ∨
        ((Expression.eval env.toEnvironment input_var_flag = 0 ∨
          Expression.eval env.toEnvironment input_var_flag = 1) ∧
         (Expression.eval env.toEnvironment input_var_flag = 0 ∨
          Expression.eval env.toEnvironment input_var_clk_high =
            Expression.eval env.toEnvironment input_var_prev_high) ∧
         Expression.eval env.toEnvironment input_var_flag *
             (Expression.eval env.toEnvironment input_var_clk_low + 1) +
           (1 - Expression.eval env.toEnvironment input_var_flag) *
             Expression.eval env.toEnvironment input_var_clk_high -
           (Expression.eval env.toEnvironment input_var_flag *
               Expression.eval env.toEnvironment input_var_prev_low +
             (1 - Expression.eval env.toEnvironment input_var_flag) *
               Expression.eval env.toEnvironment input_var_prev_high) - 1 =
           Expression.eval env.toEnvironment input_var_diff_low +
             Expression.eval env.toEnvironment input_var_diff_high * 65536 ∧
         (Expression.eval env.toEnvironment input_var_diff_low).val < 65536 ∧
         Expression.eval env.toEnvironment input_var_diff_high < (256 : ZMod p) ∧
         Word.isU64 (Vector.map (Expression.eval env.toEnvironment) input_var_prev_value) ∧
         Word.isU64 (Vector.map (Expression.eval env.toEnvironment) input_var_write_value)) :=
    h_spec
  rcases h_spec' with h_mult0 |
    ⟨h_flag01, h_page, h_tseq, h_dll, h_dhh, h_isU64_pv, h_isU64_wv⟩
  · refine ⟨?_, ?_, ?_, ⟨trivial, Or.inl h_mult0⟩, ⟨trivial, Or.inl h_mult0⟩,
            ⟨trivial, Or.inl h_mult0⟩, ⟨trivial, Or.inl h_mult0⟩⟩
    · rw [h_mult0]; ring
    · rw [h_mult0]; ring
    · rw [h_mult0]; ring
  · have h_flag0 : Expression.eval env.toEnvironment input_var_flag *
        (Expression.eval env.toEnvironment input_var_flag - 1) = 0 := by
      rcases h_flag01 with h | h <;> rw [h] <;> ring
    have h_page0 : Expression.eval env.toEnvironment input_var_flag *
        (Expression.eval env.toEnvironment input_var_clk_high -
          Expression.eval env.toEnvironment input_var_prev_high) = 0 := by
      rcases h_page with h | h <;> rw [h] <;> ring
    refine ⟨?_, ?_, ?_, ⟨trivial, Or.inr ?_⟩, ⟨trivial, Or.inr ?_⟩,
            ⟨trivial, Or.inr h_isU64_pv⟩, ⟨trivial, Or.inr h_isU64_wv⟩⟩
    · linear_combination Expression.eval env.toEnvironment input_var_mult * h_flag0
    · linear_combination Expression.eval env.toEnvironment input_var_mult * h_page0
    · linear_combination Expression.eval env.toEnvironment input_var_mult * h_tseq
    · exact (by simpa using SP1Clean.WordRange.Assertion.byteOpcodeSpec_range16_of_lt _ h_dll)
    · exact (by simpa using SP1Clean.CPUState.Assertion.byteOpcodeSpec_u8range_of_lt _ h_dhh)

end Assertion

def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.StoreMemoryAccessGated
