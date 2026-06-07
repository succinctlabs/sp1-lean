import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Faithful.ChipTactics
import SP1Clean.Extracted.JalrChip
import SP1Clean.Faithful.AddOperation
import SP1Clean.Faithful.CPUState

/-! # Chip-level faithfulness anchor for JALR — the assertion half

Anchors SP1's generated `Extracted.JalrColumns.asserts` list (opcode 47, `Extracted/JalrChip.lean`) to the
native combined spec. JALR's `asserts` list is the five-segment append chain
`AddOperation.asserts(rs1, op_c_imm, add_operation, is_real) ++ CPUState.asserts(…) ++
ITypeReader.asserts(…) ++ AddOperation.asserts(pc, #v[4,0,0,0], op_a_operation, is_real - op_a_0) ++ [the
binary/zeroing/lsb gates]`. We split at each `++` (`forall_append_single`), reduce the gates to `1` (under
`is_real = 1`, `op_a_0 = 0`), discharge each `AddOperation` fragment via `add_asserts_faithful`, and reduce
the `CPUState`/`ITypeReader` reader segments and the trailing gate list (all of whose entries vanish under
the two hypotheses except the two `value[3] = 0` 48-bit-fit facts and the `lsb` binary gate).

So under `is_real = 1 ∧ op_a_0 = 0` (the `rd ≠ x0` rows, matching the chip's completeness coverage), SP1's
generated JALR `asserts` list means **exactly**: the two `AddOperation` carry-bool specs (jump = `rs1 +
op_c_imm`, link = `pc + 4`) on the committed columns, plus the two 48-bit-fit facts and the `lsb` binary gate.

The interaction half (`jalrcols_interactions_faithful`) is proved directly: the two `AddOperation`
fragments discharge via `add_interactions_faithful`, the `CPUState` fragment via
`cpustate_interactions_faithful`, and the `ITypeReader` segment unfolds inline (as the assert proof does)
to its two operands' timestamp byte bounds; the trailing `Range((add_operation.value[0] - lsb)/4, 14)`
alignment send becomes the jump-target alignment bound. Both halves are `sorry`-free. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `(14 : ZMod p).val = 14` under `Fact (2^17 < p)`. -/
private lemma val_14 [NeZero p] : (14 : ZMod p).val = 14 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (14 : ℕ) < p by omega)

set_option maxHeartbeats 2000000 in
/-- **Chip-level faithfulness anchor — assertion half.** Under `is_real = 1 ∧ op_a_0 = 0`, SP1's generated
JALR `asserts` list holds iff: the two `AddOperation` assertion specs (carry-bools) for the jump target
(`rs1 + op_c_imm`) and the link address (`pc + 4`) on the committed columns, plus the two `value[3] = 0`
(48-bit-fit) facts and the `lsb` binary gate. -/
theorem jalrcols_asserts_faithful (cols : Extracted.JalrColumns (ZMod p))
    (h_real : cols.is_real = 1) (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    List.Forall (· = 0) (Extracted.JalrColumns.asserts cols) ↔
      ( AddOperation.AssertSpec
          #v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
              cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3]]
          #v[cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1],
              cols.adapter.op_c_imm[2], cols.adapter.op_c_imm[3]]
          #v[cols.add_operation.value[0], cols.add_operation.value[1],
              cols.add_operation.value[2], cols.add_operation.value[3]]
        ∧ AddOperation.AssertSpec
          #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]
          #v[4, 0, 0, 0]
          #v[cols.op_a_operation.value[0], cols.op_a_operation.value[1],
              cols.op_a_operation.value[2], cols.op_a_operation.value[3]]
        ∧ cols.add_operation.value[3] = 0
        ∧ cols.op_a_operation.value[3] = 0
        ∧ cols.lsb * (cols.lsb - 1) = 0 ) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.JalrColumns.asserts]
  rw [Extracted.forall_append_single, Extracted.forall_append_single,
    Extracted.forall_append_single, Extracted.forall_append_single]
  simp only [h_real, h_op_a_0, sub_zero]
  rw [add_asserts_faithful, add_asserts_faithful]
  simp only [Extracted.CPUState.asserts, Extracted.ITypeReader.asserts, List.Forall,
    sub_self, mul_zero, zero_mul, true_and, and_true]
  tauto

set_option maxHeartbeats 2000000 in
/-- **Chip-level faithfulness anchor — interaction half.** Under `is_real = 1 ∧ op_a_0 = 0`, SP1's
generated JALR `interactions` list holds iff: the two `AddOperation` limb-range specs (jump target and
link address), the two CPUState clock bounds, the `ITypeReader` `op_a`/`op_b` timestamp byte bounds, and
the jump-target alignment `Range((add_operation.value[0] - lsb)/4, 14)`. The state/program/memory sends
contribute `True`. -/
theorem jalrcols_interactions_faithful (cols : Extracted.JalrColumns (ZMod p))
    (h_real : cols.is_real = 1) (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    List.Forall Interaction.toProp (Extracted.JalrColumns.interactions cols) ↔
      ( AddOperation.InteractSpec
          #v[cols.add_operation.value[0], cols.add_operation.value[1],
              cols.add_operation.value[2], cols.add_operation.value[3]]
        ∧ (((cols.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ cols.state.clk_16_24.val < 2 ^ 8)
        ∧ (cols.adapter.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
            ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 4
                - cols.adapter.op_a_memory.access_timestamp.prev_low - 1
                - cols.adapter.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8)
        ∧ (cols.adapter.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
            ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 3
                - cols.adapter.op_b_memory.access_timestamp.prev_low - 1
                - cols.adapter.op_b_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8)
        ∧ AddOperation.InteractSpec
            #v[cols.op_a_operation.value[0], cols.op_a_operation.value[1],
                cols.op_a_operation.value[2], cols.op_a_operation.value[3]]
        ∧ ((cols.add_operation.value[0] - cols.lsb) * (4 : ZMod p)⁻¹).val < 2 ^ 14 ) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.JalrColumns.interactions]
  rw [Extracted.forall_append_interactions, Extracted.forall_append_interactions,
    Extracted.forall_append_interactions, Extracted.forall_append_interactions]
  simp only [h_real, h_op_a_0, sub_zero]
  rw [add_interactions_faithful, cpustate_interactions_faithful, add_interactions_faithful]
  simp only [Extracted.ITypeReader.interactions, List.Forall, Interaction.toProp_send_byte,
    Interaction.toProp_receive, Interaction.toProp_send_memory, Interaction.toProp_send_program,
    ByteOpcode.ofNat_six, ByteOpcode.ofNat_three, ByteOpcode.constrain_Range,
    ByteOpcode.constrain_U8Range, val_14, val_16, ZMod.val_zero, one_ne_zero, ne_eq,
    not_false_eq_true, true_implies, Nat.ofNat_pos, true_and, and_true,
    show (2 : ℕ) ^ 8 = 256 from by norm_num]
  tauto

end SP1Clean.Faithful
