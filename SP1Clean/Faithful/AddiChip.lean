import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Faithful.ChipTactics
import SP1Clean.Extracted.AddiChip
import SP1Clean.Faithful.AddOperation
import SP1Clean.Faithful.CPUState
import SP1Clean.Faithful.ITypeReader

/-! # Chip-level faithfulness anchor — SP1's whole `Addi` chip constraint list ↔ the combined spec

Anchors the **entire** generated `Extracted.AddiCols.{asserts,interactions}` lists to the native
combined spec. SP1's `Addi` chip constraints are `AddOperation ++ CPUState ++ ITypeReader ++ [binary
gate, op_a_0]`. Each fragment is discharged by its own anchor; a single theorem certifies the lists
mean **exactly**: the `AddOperation` raw arithmetic spec, the two CPUState clock byte bounds, the
ITypeReader per-row well-formedness, and `op_a_0 = 0`. Composed from axiom-clean fragment anchors. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 2000000 in
/-- **Chip-level faithfulness anchor.** Under `is_real = 1`, SP1's generated `Addi` chip constraint
lists hold iff the combined spec: the `AddOperation` assertion + interaction specs on the register-read
operand and immediate, the two CPUState clock bounds, the ITypeReader per-row well-formedness, and
`op_a_0 = 0`. -/
theorem addicols_constraints_faithful (cols : Extracted.AddiCols (ZMod p)) (h_real : cols.is_real = 1) :
    (List.Forall (· = 0) (Extracted.AddiCols.asserts cols) ∧
        List.Forall Interaction.toProp (Extracted.AddiCols.interactions cols)) ↔
      ( AddOperation.AssertSpec
          #v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
              cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3]]
          #v[cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
              cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3]]
          #v[cols.add_operation.value[0], cols.add_operation.value[1],
              cols.add_operation.value[2], cols.add_operation.value[3]]
        ∧ AddOperation.InteractSpec
            #v[cols.add_operation.value[0], cols.add_operation.value[1],
                cols.add_operation.value[2], cols.add_operation.value[3]]
        ∧ (((cols.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ cols.state.clk_16_24.val < 2 ^ 8)
        ∧ ( (cols.adapter.op_a_0 * cols.add_operation.value[0] = 0 ∧
              cols.adapter.op_a_0 * cols.add_operation.value[1] = 0 ∧
              cols.adapter.op_a_0 * cols.add_operation.value[2] = 0 ∧
              cols.adapter.op_a_0 * cols.add_operation.value[3] = 0) ∧
            (cols.adapter.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 4
                  - cols.adapter.op_a_memory.access_timestamp.prev_low - 1
                  - cols.adapter.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
            (cols.adapter.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 3
                  - cols.adapter.op_b_memory.access_timestamp.prev_low - 1
                  - cols.adapter.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8) )
        ∧ cols.adapter.op_a_0 = 0 ) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  faithful_chip Extracted.AddiCols.asserts Extracted.AddiCols.interactions h_real
    add_constraints_faithful itypereader_constraints_faithful

end SP1Clean.Faithful
