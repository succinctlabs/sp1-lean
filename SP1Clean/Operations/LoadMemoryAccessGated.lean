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

/-! # `LoadMemoryAccessGated` sub-circuit

Wraps the load-side RAM memory access SP1 emits in Load chips. The
underlying SP1 constraint compiler output (see e.g.
`SP1Chips/Load/LoadByte/Constraints.lean` for the canonical example) emits:

- `assertZero (flag * (flag - 1))` — boolean flag gate
- `assertZero (flag * (clk_high - prev_high))` — clock-page agreement
  (when `flag = 1`, the access is in the same 65536-clock page as the
  prior access, so the page-high bits agree)
- The 65536-base timestamp equation as a single `assertZero`:
  `flag*(clk_low+1) + (1-flag)*clk_high
   - (flag*prev_low + (1-flag)*prev_high) - 1 - (diff_low + diff_high*65536) = 0`
- `send .byte 6 diff_low 16 0` (Range(16) for `diff_low`)
- `send .byte 3 0 diff_high 0` (U8Range for `diff_high`)
- `Word.isU64 prev_value` (4 byte lookups, threaded via `WordRange`)
- `send .memory ...` + `receive .memory ...` (memory bus participation,
  gated by `mult`)

All emissions are gated by the chip's `is_real` (= `mult` here), so on
padding rows the constraint set collapses.

## Status: real hint-witnessed circuit ("Avenue C")

`main` emits the faithful constraint content, all gated by `mult` (= the
chip's `is_real`):
- the boolean `flag` gate, clock-page agreement, and the 65536-base
  timestamp equation as three inline `mult`-gated `assertZero`s;
- `diff_low` (Range 16) and `diff_high` (U8Range) via `SP1Lookup.byteOpcodeGated`;
- `Word.isU64 prev_value` via `SP1Clean.WordRange.assertion`.

The memory-bus `send`/`receive` participation is NOT emitted here — it is a
trace-level multiplicity-bus contribution aggregated by the
`Soundness/MemoryConsistency` pipeline, orthogonal to this per-row
constraint content.

`Assumptions := True`; `Spec := Contract` (the disjunctive `mult = 0 ∨ …`
form) is now *proved* from the in-circuit emissions rather than copied from
`Assumptions`. Canonical pattern: `OperandAccess.AssertionGated` at
`SP1Clean/Reader/OperandAccess.lean:224-310`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LoadMemoryAccessGated

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Inputs: clock components, address, prior-access value/timestamp,
diff witnesses, the in-page flag, and the gating multiplicity. -/
structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  addr : Vector F 3
  prev_value : Vector F 4
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

/-- Emit the faithful load-memory-access constraints, all gated by `mult`:
3 inline `mult`-gated `assertZero`s (boolean flag, clock-page agreement,
timestamp equation) + 2 `byteOpcodeGated` range lookups (`diff_low` in
Range 16, `diff_high` in U8Range) + `WordRange` (`Word.isU64 prev_value`). -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- `flag` boolean gate (gated by `mult`).
  input.mult * (input.flag * (input.flag - 1)) === 0
  -- Clock-page agreement: when `flag = 1`, `clk_high = prev_high` (gated).
  input.mult * (input.flag * (input.clk_high - input.prev_high)) === 0
  -- 65536-base timestamp equation (gated).
  input.mult *
      (input.flag * (input.clk_low + 1) + (1 - input.flag) * input.clk_high -
        (input.flag * input.prev_low + (1 - input.flag) * input.prev_high) - 1 -
        (input.diff_low + input.diff_high * 65536)) === 0
  -- `diff_low` in Range 16.
  SP1Lookup.byteOpcodeGated
    ⟨#v[(6 : Expression (ZMod p)), input.diff_low, 16, 0], input.mult⟩
  -- `diff_high` in U8Range.
  SP1Lookup.byteOpcodeGated
    ⟨#v[(3 : Expression (ZMod p)), 0, input.diff_high, 0], input.mult⟩
  -- `Word.isU64 prev_value`.
  SP1Clean.WordRange.assertion
    (⟨input.prev_value, input.mult⟩ : Var SP1Clean.WordRange.Assertion.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.LoadMemoryAccessGated"
  main := main
  -- 3 inline gates (0) + 2 byteOpcodeGated (4 each) + WordRange (16) = 24.
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The faithful load-memory-access contract, in disjunctive (`mult = 0 ∨ …`)
form so the assertion is vacuous on padding rows. Encodes:
- boolean flag,
- clock-page agreement when `flag = 1`,
- 65536-base timestamp equation,
- range bounds (`diff_low.val < 65536`, `diff_high < 256`),
- `Word.isU64 prev_value` for the loaded word. -/
def Contract (input : Inputs (ZMod p)) : Prop :=
  input.mult = 0 ∨
    ((input.flag = 0 ∨ input.flag = 1) ∧
     (input.flag = 0 ∨ input.clk_high = input.prev_high) ∧
     input.flag * (input.clk_low + 1) + (1 - input.flag) * input.clk_high -
       (input.flag * input.prev_low + (1 - input.flag) * input.prev_high) - 1 =
       input.diff_low + input.diff_high * 65536 ∧
     input.diff_low.val < 65536 ∧
     input.diff_high < (256 : ZMod p) ∧
     Word.isU64 input.prev_value)

/-- Spec is the contract — now *proved* from the in-circuit emissions. -/
def Spec (input : Inputs (ZMod p)) : Prop := Contract input

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_ch, h_cl, h_addr, h_pv, h_phi, h_plo, h_dlo, h_dhi, h_flag, h_mult⟩ :=
    h_input
  subst_eqs
  obtain ⟨g_bool, g_page, g_ts, d_diff, d_high, d_wr⟩ := h_holds
  simp only [SP1Lookup.ByteOpcodeGated.Spec, SP1Lookup.ByteOpcodeGated.Assumptions,
             SP1Clean.WordRange.assertion, SP1Clean.WordRange.Assertion.Spec,
             SP1Clean.WordRange.Assertion.Assumptions,
             forall_const] at d_diff d_high d_wr
  by_cases h_mult0 : Expression.eval env input_var_mult = 0
  · exact Or.inl h_mult0
  right
  -- Range / Word facts from the gated subcircuits.
  have r_diff := d_diff.resolve_left h_mult0
  have r_high := d_high.resolve_left h_mult0
  have r_wr := d_wr.resolve_left h_mult0
  -- Cancel `mult` from the three inline gates.
  have g_bool' := (mul_eq_zero.mp g_bool).resolve_left h_mult0
  have g_page' := (mul_eq_zero.mp g_page).resolve_left h_mult0
  have g_ts' := (mul_eq_zero.mp g_ts).resolve_left h_mult0
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rcases mul_eq_zero.mp g_bool' with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · rcases mul_eq_zero.mp g_page' with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · linear_combination g_ts'
  · exact SP1Clean.WordRange.Assertion.byteOpcodeSpec_range16 _ r_diff
  · exact SP1Clean.CPUState.Assertion.byteOpcodeSpec_u8range _ r_high
  · exact r_wr

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_ch, h_cl, h_addr, h_pv, h_phi, h_plo, h_dlo, h_dhi, h_flag, h_mult⟩ :=
    h_input
  subst_eqs
  unfold id at *
  -- Re-ascribe `h_spec` into canonical `Expression.eval env.toEnvironment …` form
  -- (defeq) so the downstream gate rewrites match syntactically.
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
         Word.isU64 (Vector.map (Expression.eval env.toEnvironment) input_var_prev_value)) :=
    h_spec
  rcases h_spec' with h_mult0 | ⟨h_flag01, h_page, h_tseq, h_dll, h_dhh, h_isU64⟩
  · -- `mult = 0`: every gate trivializes; lookups/WordRange take `Or.inl`.
    refine ⟨?_, ?_, ?_, ⟨trivial, Or.inl h_mult0⟩, ⟨trivial, Or.inl h_mult0⟩,
            ⟨trivial, Or.inl h_mult0⟩⟩
    · rw [h_mult0]; ring
    · rw [h_mult0]; ring
    · rw [h_mult0]; ring
  · -- `mult ≠ 0` branch: each fact forces the corresponding gate to hold.
    have h_flag0 : Expression.eval env.toEnvironment input_var_flag *
        (Expression.eval env.toEnvironment input_var_flag - 1) = 0 := by
      rcases h_flag01 with h | h <;> rw [h] <;> ring
    have h_page0 : Expression.eval env.toEnvironment input_var_flag *
        (Expression.eval env.toEnvironment input_var_clk_high -
          Expression.eval env.toEnvironment input_var_prev_high) = 0 := by
      rcases h_page with h | h <;> rw [h] <;> ring
    refine ⟨?_, ?_, ?_,
            ⟨trivial, Or.inr ?_⟩, ⟨trivial, Or.inr ?_⟩, ⟨trivial, Or.inr h_isU64⟩⟩
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

end SP1Clean.LoadMemoryAccessGated
