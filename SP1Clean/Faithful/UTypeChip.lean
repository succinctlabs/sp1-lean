import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Faithful.ChipTactics
import SP1Clean.Faithful.AddOperation
import SP1Clean.Faithful.JTypeReader
import SP1Clean.Extracted.UTypeChip

/-! # Chip-level faithfulness anchor for UType (LUI / AUIPC)

Anchors SP1's generated `Extracted.UTypeColumns.asserts` / `.interactions` lists
(`Extracted/UTypeChip.lean`, opcodes 48 = AUIPC, 49 = LUI) to the native combined spec. UType's
constraint lists are `CPUState ++ AddOperation ++ JTypeReader ++ [trailing scalar gates]`, in that
sub-call order — the straight-line state row, the single `pc + op_b_imm` add (the AUIPC offset; LUI
takes `addend = 0`), the destination-register write adapter, and the chip's own gates. We split at each
`++` (`forall_append_single` / `forall_append_interactions`), reduce the gated fragments to `1` (under
`is_real = 1`, `op_a_0 = 0`), and discharge each by its own anchor (`cpustate_*_faithful`,
`add_*_faithful`, `jtypereader_*_faithful`).

The trailing assertion gates collapse, under `is_real = 1 ∧ op_a_0 = 0`, to exactly: the `is_auipc`
binary gate and the three `addend[i] = is_auipc · pc[i]` definitions (the `addend = is_auipc ? pc : 0`
multiplexer). The `is_real` binary gate, the fourth-limb `0 = is_auipc·0`, and the `(is_real-1)·op_a_0`
padding gate are vacuous.

So under `is_real = 1 ∧ op_a_0 = 0` (the `rd ≠ x0` rows), SP1's generated UType constraint lists mean
exactly: the `AddOperation` carry-bool + range spec on the committed columns, the `is_auipc`
multiplexer that selects the PC addend, the CPUState clock-range bounds, and the JTypeReader timestamp
byte bounds. Composed from axiom-clean fragment anchors. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

set_option maxHeartbeats 2000000 in
/-- **Chip-level faithfulness anchor — assertion half.** Under `is_real = 1 ∧ op_a_0 = 0`, SP1's
generated UType `asserts` list holds iff: the `AddOperation` assertion spec (carry-bools for
`addend + op_b_imm`), the `is_auipc` binary gate, and the three `addend[i] = is_auipc · pc[i]`
multiplexer definitions. -/
theorem utypecols_asserts_faithful (cols : Extracted.UTypeColumns (ZMod p))
    (h_real : cols.is_real = 1) (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    List.Forall (· = 0) (Extracted.UTypeColumns.asserts cols) ↔
      ( AddOperation.AssertSpec
          #v[cols.addend[0], cols.addend[1], cols.addend[2], 0]
          #v[cols.adapter.op_b_imm[0], cols.adapter.op_b_imm[1],
              cols.adapter.op_b_imm[2], cols.adapter.op_b_imm[3]]
          #v[cols.add_operation.value[0], cols.add_operation.value[1],
              cols.add_operation.value[2], cols.add_operation.value[3]]
        ∧ (cols.is_auipc = 0 ∨ cols.is_auipc = 1)
        ∧ cols.addend[0] = cols.is_auipc * cols.state.pc[0]
        ∧ cols.addend[1] = cols.is_auipc * cols.state.pc[1]
        ∧ cols.addend[2] = cols.is_auipc * cols.state.pc[2] ) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.UTypeColumns.asserts]
  rw [Extracted.forall_append_single, Extracted.forall_append_single,
    Extracted.forall_append_single]
  simp only [h_real, h_op_a_0, sub_zero]
  rw [cpustate_asserts_faithful, add_asserts_faithful, jtypereader_asserts_faithful]
  simp only [List.Forall, true_and, and_true, sub_self, mul_zero, zero_mul, add_zero,
    sub_eq_zero, bool_iff]

set_option maxHeartbeats 2000000 in
/-- **Chip-level faithfulness anchor — interaction half.** Under `is_real = 1 ∧ op_a_0 = 0`, SP1's
generated UType `interactions` list holds iff: the CPUState clock-range bounds, the `AddOperation`
limb-range spec, and the JTypeReader `op_a` timestamp byte bounds. UType emits no chip-specific
interactions of its own. -/
theorem utypecols_interactions_faithful (cols : Extracted.UTypeColumns (ZMod p))
    (h_real : cols.is_real = 1) (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    List.Forall Interaction.toProp (Extracted.UTypeColumns.interactions cols) ↔
      ( (((cols.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
            cols.state.clk_16_24.val < 2 ^ 8)
        ∧ AddOperation.InteractSpec
            #v[cols.add_operation.value[0], cols.add_operation.value[1],
                cols.add_operation.value[2], cols.add_operation.value[3]]
        ∧ (cols.adapter.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
            ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 4
                - cols.adapter.op_a_memory.access_timestamp.prev_low - 1
                - cols.adapter.op_a_memory.access_timestamp.diff_low_limb)
              * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.UTypeColumns.interactions]
  rw [Extracted.forall_append_interactions, Extracted.forall_append_interactions,
    Extracted.forall_append_interactions]
  simp only [h_real, h_op_a_0, sub_zero]
  rw [cpustate_interactions_faithful, add_interactions_faithful, jtypereader_interactions_faithful]
  simp only [List.Forall, and_true]
  tauto

/-- **Faithfulness anchor (UType chip).** Under `is_real = 1 ∧ op_a_0 = 0`, SP1's generated UType
constraint lists hold iff the native combined spec — the conjunction of the two halves. -/
theorem utypecols_constraints_faithful (cols : Extracted.UTypeColumns (ZMod p))
    (h_real : cols.is_real = 1) (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    (List.Forall (· = 0) (Extracted.UTypeColumns.asserts cols) ∧
        List.Forall Interaction.toProp (Extracted.UTypeColumns.interactions cols)) ↔
      ( ( AddOperation.AssertSpec
            #v[cols.addend[0], cols.addend[1], cols.addend[2], 0]
            #v[cols.adapter.op_b_imm[0], cols.adapter.op_b_imm[1],
                cols.adapter.op_b_imm[2], cols.adapter.op_b_imm[3]]
            #v[cols.add_operation.value[0], cols.add_operation.value[1],
                cols.add_operation.value[2], cols.add_operation.value[3]]
          ∧ (cols.is_auipc = 0 ∨ cols.is_auipc = 1)
          ∧ cols.addend[0] = cols.is_auipc * cols.state.pc[0]
          ∧ cols.addend[1] = cols.is_auipc * cols.state.pc[1]
          ∧ cols.addend[2] = cols.is_auipc * cols.state.pc[2] )
        ∧ ( (((cols.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
              cols.state.clk_16_24.val < 2 ^ 8)
          ∧ AddOperation.InteractSpec
              #v[cols.add_operation.value[0], cols.add_operation.value[1],
                  cols.add_operation.value[2], cols.add_operation.value[3]]
          ∧ (cols.adapter.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 4
                  - cols.adapter.op_a_memory.access_timestamp.prev_low - 1
                  - cols.adapter.op_a_memory.access_timestamp.diff_low_limb)
                * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ) ) := by
  rw [utypecols_asserts_faithful cols h_real h_op_a_0,
    utypecols_interactions_faithful cols h_real h_op_a_0]

end SP1Clean.Faithful
