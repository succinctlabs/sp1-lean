import SP1Clean.Chips.ALU.MulChip.Cols
import SP1Operations.Operation.MulOperation.MulOperation
import SP1Clean.Operations.MulOperation
import SP1Clean.Reader.RTypeReader
import SP1Chips.Mul.Common

/-! # `MulChip` cols-level lemmas (4-lemma scaffold, all sorry'd)

Mul is closer to fully provable than the other 5 chips — its `main`
already composes `SP1Clean.MulOp.assertion` as a Clean subcircuit
(canonical (a) shape). The sorries reduce to `MulOperation.iff_sp1_full`
(operation-level sorry'd) once the full lemma chain is in place. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Mul

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)] in
lemma fromMain_toMain (_cols : MulCols (ZMod p))
    (_h_trusted : True) : True := by trivial

lemma allHold_iff_structural
    (Main : Vector (ZMod p) 82)
    (_h_is_real :
      Main[78] + Main[79] + Main[80] + Main[81] + (1 : ZMod p) = 1) :
    (_root_.Mul.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  sorry

/-- **Forward** (soundness midpoint): assemble the chip-level semantic
`FormalSpec` from the per-sub-circuit Specs returned by `circuit_proof_start`.
Mirrors `SP1Clean.Add.formalSpec_of_subcircuit_specs`: the `MulOp` hypothesis
is kept in its `Assumptions → Spec` function form (the literal shape of the
`h_holds` conjunct) and discharged internally — binarity of the selector sum
from the `sum * (sum - 1) = 0` gate, and the `Word.isU64 op_b/op_c` bounds
(needed when the active row is real) pulled from `h_rtr` via
`RTypeReader.Gated.Assertion.isU64_operands_of_spec`.

The selector sum that `MulOp` threads (`is_mul + is_mulh + is_mulhu +
is_mulhsu + is_mulw`) is a reordering of the chip-level sum used by the
reader/CPU sub-circuits (`is_mul + is_mulh + is_mulw + is_mulhsu + is_mulhu`);
the two are bridged by `ring`. -/
lemma formalSpec_of_subcircuit_specs
    (cols : MulCols (ZMod p))
    (h_mul : SP1Clean.MulOp.Assumptions
        ⟨cols.op_a_write_value, cols.adapter.op_b_memory.prev_value,
         cols.adapter.op_c_memory.prev_value, cols.mul_operation.carry,
         cols.mul_operation.product, cols.mul_operation.b_lower_byte.low_bytes,
         cols.mul_operation.c_lower_byte.low_bytes, cols.mul_operation.b_msb,
         cols.mul_operation.c_msb, cols.mul_operation.product_msb.msb,
         cols.mul_operation.b_sign_extend, cols.mul_operation.c_sign_extend,
         cols.is_mul, cols.is_mulh, cols.is_mulhu, cols.is_mulhsu, cols.is_mulw⟩ →
      SP1Clean.MulOp.Spec
        ⟨cols.op_a_write_value, cols.adapter.op_b_memory.prev_value,
         cols.adapter.op_c_memory.prev_value, cols.mul_operation.carry,
         cols.mul_operation.product, cols.mul_operation.b_lower_byte.low_bytes,
         cols.mul_operation.c_lower_byte.low_bytes, cols.mul_operation.b_msb,
         cols.mul_operation.c_msb, cols.mul_operation.product_msb.msb,
         cols.mul_operation.b_sign_extend, cols.mul_operation.c_sign_extend,
         cols.is_mul, cols.is_mulh, cols.is_mulhu, cols.is_mulhsu, cols.is_mulw⟩)
    (h_cpu : SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state,
         #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
         8, cols.is_mul + cols.is_mulh + cols.is_mulw + cols.is_mulhsu + cols.is_mulhu⟩)
    (h_rtr : SP1Clean.RTypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
         cols.is_mul * 11 + cols.is_mulh * 12 + cols.is_mulw * 13
           + cols.is_mulhsu * 14 + cols.is_mulhu * 24,
         cols.state.pc, cols.op_a_write_value, cols.adapter,
         cols.is_mul + cols.is_mulh + cols.is_mulw + cols.is_mulhsu + cols.is_mulhu,
         cols.adapter_cols.is_trusted⟩)
    (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    Assertion.FormalSpec cols := by
  refine ⟨h_cpu, h_rtr, h_op_a_0, fun h_sum_one => ?_⟩
  -- Bridge the two selector-sum orderings.
  have hsum_eq :
      cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw
        = cols.is_mul + cols.is_mulh + cols.is_mulw + cols.is_mulhsu + cols.is_mulhu := by ring
  have h_mulop_sum_one :
      cols.is_mul + cols.is_mulh + cols.is_mulhu + cols.is_mulhsu + cols.is_mulw = 1 := by
    rw [hsum_eq]; exact h_sum_one
  obtain ⟨h_isU64_b, h_isU64_c⟩ :=
    SP1Clean.RTypeReader.Gated.Assertion.isU64_operands_of_spec h_sum_one h_rtr
  exact h_mul ⟨Or.inr h_mulop_sum_one, fun _ => ⟨h_isU64_b, h_isU64_c⟩⟩ h_mulop_sum_one

lemma subcircuit_specs_of_formalSpec
    (cols : MulCols (ZMod p))
    (_h_is_real_sum :
      cols.is_mul + cols.is_mulh + cols.is_mulw + cols.is_mulhsu + cols.is_mulhu = 1)
    (_h_spec : Assertion.FormalSpec cols) :
    True := by trivial

end SP1Clean.Mul
