import SP1Clean.Chips.ALU.MulChip.Multiplicity.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.Reader.RTypeReader
import SP1Clean.Operations.MulOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `MulChip` Clean circuit + `FormalAssertion` (directory-form scaffold)

Composes the Rust subcircuit graph for `MulChip::eval`:
- `MulOp.assertion` (the 16-byte product carry-chain + sign-extend
  discipline — itself wrapping `U16toU8OpSafe.assertion` ×2 +
  `U16MSBOp.assertion` ×1),
- `CPUState.assertion`,
- `RTypeReader.assertion`,
- 7 trailing scalar gates (5 selector binaries + sum binary + op_a_0).

Opcode formula `is_mul·11 + is_mulh·12 + is_mulhu·13 + is_mulhsu·14 + is_mulw·24`.
`is_real = is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw`.

The default `subcircuitsConsistent` derivation exponentially times out on
this nesting depth (`MulOp.assertion` recursively composes 3 sub-circuits);
supply it as `sorry` for the scaffold along with the other proof
bodies. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.MulChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]

namespace Assertion

open Circuit

/-- Clean-side chip circuit. -/
@[reducible]
def main (cols : Var MulCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter,
       a_word, carry, product, b_low_bytes, c_low_bytes,
       b_msb, c_msb, product_msb, b_sign_extend, c_sign_extend,
       is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw, _adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  let is_real := is_mul + is_mulh + is_mulhu + is_mulhsu + is_mulw
  let opcode := is_mul * 11 + is_mulh * 12 + is_mulhu * 13 +
    is_mulhsu * 14 + is_mulw * 24
  SP1Clean.MulOp.assertion
    (⟨a_word, adapter.op_b_memory.prev_value, adapter.op_c_memory.prev_value,
       carry, product, b_low_bytes, c_low_bytes,
       b_msb, c_msb, product_msb, b_sign_extend, c_sign_extend,
       is_mul, is_mulh, is_mulhu, is_mulhsu, is_mulw⟩ :
      Var SP1Clean.MulOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.RTypeReader.assertion
    (⟨clk_high, clk_low, opcode, pc, a_word, adapter⟩ :
      Var SP1Clean.RTypeReader.Inputs (ZMod p))
  is_mul * (is_mul - 1) === 0
  is_mulh * (is_mulh - 1) === 0
  is_mulhu * (is_mulhu - 1) === 0
  is_mulhsu * (is_mulhsu - 1) === 0
  is_mulw * (is_mulw - 1) === 0
  is_real * (is_real - 1) === 0
  adapter.op_a_0 === 0

set_option maxHeartbeats 6400000 in
-- 3 subcircuits + 7 scalar gates; `MulOp.assertion` recursively composes
-- 3 sub-subcircuits, so default heartbeat budget is too tight for
-- `subcircuitsConsistent` / `localLength_eq` derivation. Matches the
-- parallel `Aggregate.lean:557` posture.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) MulCols unit where
  name := "SP1Clean.Mul"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp only [main, circuit_norm]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

/-- Two-part precondition (mirroring `SP1Clean/Chips/ALU/AddChip/Circuit.lean:99`):

- `is_trusted = is_real_sum` is a TrustMode-marker fact carried by the
  cols struct (`UserMode` variant); needed for the cols→Main→cols
  round-trip (`Lemmas.lean:fromMain_toMain`).
- `is_real_sum = 1` restricts the FormalAssertion to non-padding rows;
  the trace-soundness driver discharges this per row before invoking
  `MulChip.assertion`. -/
def Assumptions (cols : MulCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted =
    cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw ∧
  cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw = 1

/-- The unified chip Spec is defined in `Cols.lean`
(`SP1Clean.MulChip.FormalSpec`). -/
abbrev FormalSpec := @SP1Clean.MulChip.FormalSpec p

set_option maxHeartbeats 800000 in
-- Soundness mirrors `SP1Clean/Chips/ALU/AddChip/Circuit.lean:107` but for
-- the 5-variant fan-out: build the 14-conjunct `FormalSpec` from the three
-- sub-circuit Specs (`MulOp.Spec`, `cpuStateSpec`, `rtypeReaderSpec`), the
-- 7 in-circuit scalar gates, and the 5 trailing RV64 conditionals which
-- `MulOp.Spec` already delivers under `is_real_sum = 1`.
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨_h_trusted, h_is_real⟩ := h_assumptions
  obtain ⟨h_mulop_sub, h_cpu_sub, h_rtr_sub,
          h_mul_bin, h_mulh_bin, h_mulhu_bin, h_mulhsu_bin, h_mulw_bin,
          h_sum_bin, h_op_a_0⟩ := h_holds
  unfold id at *
  have h_cpu := h_cpu_sub trivial
  have h_rtr := h_rtr_sub trivial
  -- Pull `isU64 b/c` from rtypeReaderSpec. The rtypeReaderSpec states the
  -- isU64 facts as `Word.isU64 #v[mem.prev_value[0], ..[1], ..[2], ..[3]]`,
  -- which is the same Word as `mem.prev_value` only up to Vector eta.
  -- `Word.isU64_of_cases` extracts the underlying per-limb bounds we need.
  have h_isU64_b_vec := h_rtr.2.2.2.2.2.2.2.1.2.2.2.1
  have h_isU64_c_vec := h_rtr.2.2.2.2.2.2.2.1.2.2.2.2
  have h_isU64_b : Word.isU64 input_adapter_op_b_memory_prev_value :=
    Word.isU64_of_cases (h_isU64_b_vec ⟨0, by decide⟩) (h_isU64_b_vec ⟨1, by decide⟩)
      (h_isU64_b_vec ⟨2, by decide⟩) (h_isU64_b_vec ⟨3, by decide⟩)
  have h_isU64_c : Word.isU64 input_adapter_op_c_memory_prev_value :=
    Word.isU64_of_cases (h_isU64_c_vec ⟨0, by decide⟩) (h_isU64_c_vec ⟨1, by decide⟩)
      (h_isU64_c_vec ⟨2, by decide⟩) (h_isU64_c_vec ⟨3, by decide⟩)
  -- Discharge MulOp.assertion's Assumptions: aggregate-binary follows from
  -- `h_is_real : sum = 1` (use `Or.inr`); operand bounds come from h_rtr.
  have h_mulop := h_mulop_sub
    ⟨Or.inr h_is_real, fun _ => ⟨h_isU64_b, h_isU64_c⟩⟩
  -- MulOp.Spec at `is_real = 1` gives `(isU64 a ∧ 5 RV64 conditionals)`.
  obtain ⟨h_isU64_a, h_rv_mul, h_rv_mulh, h_rv_mulhu, h_rv_mulhsu, h_rv_mulw⟩ :=
    h_mulop h_is_real
  -- Refine the 14-conjunct FormalSpec. The 6 boolean gates from h_holds
  -- carry `+ -1` form vs FormalSpec's `- 1` form — `linear_combination`
  -- bridges these defeq variants.
  refine ⟨?_, h_cpu, h_rtr, ?_, ?_, ?_, ?_, ?_, ?_, h_op_a_0,
          h_rv_mul, h_rv_mulh, h_rv_mulhu, h_rv_mulhsu, h_rv_mulw⟩
  · intro _h_real
    exact ⟨h_isU64_a, h_rv_mul, h_rv_mulh, h_rv_mulhu, h_rv_mulhsu, h_rv_mulw⟩
  · linear_combination h_mul_bin
  · linear_combination h_mulh_bin
  · linear_combination h_mulhu_bin
  · linear_combination h_mulhsu_bin
  · linear_combination h_mulw_bin
  · linear_combination h_sum_bin

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `MulChip`. -/
def assertion : FormalAssertion (ZMod p) MulCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.MulChip
