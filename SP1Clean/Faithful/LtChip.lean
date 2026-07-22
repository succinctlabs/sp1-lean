import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Proofs.Chips.LtChip.Formal
import SP1Clean.Model.SP1Constraint
import SP1Clean.Faithful.ChipTactics
import SP1Clean.Extracted.LtChip
import SP1Clean.Faithful.LtOperationSigned
import SP1Clean.Faithful.CPUState
import SP1Clean.Faithful.ALUTypeReader

/-! # Chip-level faithfulness anchor — SP1's whole `Lt` chip constraint list ↔ the combined spec

Anchors the **entire** generated `Extracted.LtCols.{asserts,interactions}` lists (`Extracted/LtChip.lean`)
to the native combined spec. SP1's `Lt` chip constraints are `LtOperationSigned ++ CPUState ++
ALUTypeReader ++ [is_slt binary, is_sltu binary, sum binary, op_a_0]`, all gated by the row selector
`E0 = is_slt + is_sltu` (the SLT/SLTU one-hot). We split the two lists at each `++` (`forall_append_pair`),
reduce `E0` to `1` (the real-row hypothesis), and discharge each fragment by its combined anchor
(`ltSigned_`, `cpustate_`, `alutypereader_constraints_faithful`), leaving the two variant-flag booleans
(`is_slt`, `is_sltu`), the now-vacuous sum boolean, and the `op_a_0 = 0` register-index gate.

So a single theorem certifies that SP1's generated `Lt` chip constraint lists mean exactly: the
`LtOperationSigned` raw compare spec on the register-read operands, the two CPUState clock byte bounds,
the ALUTypeReader per-row well-formedness (the `op_a_0` zeroing on the compare bit, the `imm_c`
register/immediate multiplexer, and the three operands' timestamp byte bounds), the two variant-flag
booleans, and `op_a_0 = 0`. Composed from axiom-clean fragment anchors. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 2000000 in
/-- **Chip-level faithfulness anchor.** Under `is_slt + is_sltu = 1` (a real SLT/SLTU row), SP1's
generated `Lt` chip constraint lists hold iff the combined spec holds. -/
theorem ltcols_constraints_faithful (cols : Extracted.LtCols (ZMod p))
    (h_real : cols.is_slt + cols.is_sltu = 1) :
    (List.Forall (· = 0) (Extracted.LtCols.asserts cols) ∧
        List.Forall Interaction.toProp (Extracted.LtCols.interactions cols)) ↔
      ( ( LtOperationSigned.RawSpec
            #v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
              cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3]]
            #v[cols.adapter.op_c_memory.prev_value[0], cols.adapter.op_c_memory.prev_value[1],
              cols.adapter.op_c_memory.prev_value[2], cols.adapter.op_c_memory.prev_value[3]]
            { result :=
                { u16_compare_operation := cols.lt_operation.result.u16_compare_operation,
                  u16_flags :=
                    #v[cols.lt_operation.result.u16_flags[0], cols.lt_operation.result.u16_flags[1],
                      cols.lt_operation.result.u16_flags[2], cols.lt_operation.result.u16_flags[3]],
                  not_eq_inv := cols.lt_operation.result.not_eq_inv,
                  comparison_limbs :=
                    #v[cols.lt_operation.result.comparison_limbs[0],
                      cols.lt_operation.result.comparison_limbs[1]] },
              b_msb := cols.lt_operation.b_msb, c_msb := cols.lt_operation.c_msb }
            cols.is_slt
          ∧ ((cols.state.clk_0_16 - 1) * 8⁻¹).val < 2 ^ 13 ∧ cols.state.clk_16_24.val < 2 ^ 8 )
        ∧ cols.adapter.op_a_0 * cols.lt_operation.result.u16_compare_operation.bit = 0
        ∧ (1 - cols.adapter.imm_c) * (1 - cols.adapter.imm_c - 1) = 0
        ∧ ( cols.adapter.imm_c * (cols.adapter.op_c_memory.prev_value[0] - cols.adapter.op_c[0]) = 0 ∧
            cols.adapter.imm_c * (cols.adapter.op_c_memory.prev_value[1] - cols.adapter.op_c[1]) = 0 ∧
            cols.adapter.imm_c * (cols.adapter.op_c_memory.prev_value[2] - cols.adapter.op_c[2]) = 0 ∧
            cols.adapter.imm_c * (cols.adapter.op_c_memory.prev_value[3] - cols.adapter.op_c[3]) = 0 )
        ∧ ( cols.adapter.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
            ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 4
                - cols.adapter.op_a_memory.access_timestamp.prev_low - 1
                - cols.adapter.op_a_memory.access_timestamp.diff_low_limb) * 65536⁻¹).val < 2 ^ 8 )
        ∧ ( cols.adapter.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
            ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 3
                - cols.adapter.op_b_memory.access_timestamp.prev_low - 1
                - cols.adapter.op_b_memory.access_timestamp.diff_low_limb) * 65536⁻¹).val < 2 ^ 8 )
        ∧ (1 - cols.adapter.imm_c ≠ 0 →
            cols.adapter.op_c_memory.access_timestamp.diff_low_limb.val < 2 ^ 16)
        ∧ (1 - cols.adapter.imm_c ≠ 0 →
            ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 2
                - cols.adapter.op_c_memory.access_timestamp.prev_low - 1
                - cols.adapter.op_c_memory.access_timestamp.diff_low_limb) * 65536⁻¹).val < 2 ^ 8)
        ∧ cols.is_slt * (cols.is_slt - 1) = 0
        ∧ cols.is_sltu * (cols.is_sltu - 1) = 0
        ∧ cols.adapter.op_a_0 = 0 ) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.LtCols.asserts, Extracted.LtCols.interactions]
  rw [Extracted.forall_append_pair, Extracted.forall_append_pair, Extracted.forall_append_pair]
  simp only [h_real]
  rw [ltSigned_constraints_faithful, cpustate_constraints_faithful, alutypereader_constraints_faithful]
  simp only [List.Forall, sub_self, mul_zero, zero_add, true_and, and_true,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  tauto

end SP1Clean.Faithful
