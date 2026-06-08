import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Faithful.ChipTactics
import SP1Clean.Extracted.JalChip
import SP1Clean.Faithful.AddOperation

/-! # Chip-level faithfulness anchor for JAL — the assertion half

Anchors SP1's generated `Extracted.JalColumns.asserts` list (opcode 46, `Extracted/JalChip.lean`) to the
native combined spec. JAL's `asserts` list is `AddOperation.asserts(pc, op_b_imm, add_operation, is_real)
++ AddOperation.asserts(pc, #v[4,0,0,0], op_a_operation, is_real - op_a_0) ++ [the binary/zeroing
gates]` — two gated `AddOperation` fragments plus the trailing scalar gates. We split at each `++`
(`forall_append_single`), reduce both gates to `1` (under `is_real = 1`, `op_a_0 = 0`), and discharge each
add fragment by `add_asserts_faithful`; the trailing gates collapse to the two `value[3] = 0` (jump/link
targets fit in 48 bits) facts, the rest vanishing under the two hypotheses.

So under `is_real = 1 ∧ op_a_0 = 0` (the `rd ≠ x0` rows, matching the chip's completeness coverage), SP1's
generated JAL `asserts` list means **exactly**: the two `AddOperation` carry-bool specs (jump = `pc +
op_b_imm`, link = `pc + 4`) on the committed columns, plus the two 48-bit-fit facts.

The interaction half (`jalcols_interactions_faithful`) is proved directly: JAL inlines its
state/program/memory/timestamp sends (it does not compose `JTypeReader.interactions`), so the trailing
list reduces by the `Interaction.toProp_*` lemmas to the two `AddOperation` limb-range specs, the
`Range(add_operation.value[0]/4, 14)` jump-target alignment, the two CPUState clock bounds, and `op_a`'s
timestamp byte bounds. Composed from axiom-clean fragment anchors. -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `(13 : ZMod p).val = 13` under `Fact (2^17 < p)`. -/
private lemma val_13 [NeZero p] : (13 : ZMod p).val = 13 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (13 : ℕ) < p by omega)

/-- `(14 : ZMod p).val = 14` under `Fact (2^17 < p)`. -/
private lemma val_14 [NeZero p] : (14 : ZMod p).val = 14 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (14 : ℕ) < p by omega)

set_option maxHeartbeats 2000000 in
/-- **Chip-level faithfulness anchor — assertion half.** Under `is_real = 1 ∧ op_a_0 = 0`, SP1's generated
JAL `asserts` list holds iff: the two `AddOperation` assertion specs (carry-bools) for the jump target
(`pc + op_b_imm`) and the link address (`pc + 4`) on the committed columns, plus the two `value[3] = 0`
(48-bit-fit) facts. -/
theorem jalcols_asserts_faithful (cols : Extracted.JalColumns (ZMod p))
    (h_real : cols.is_real = 1) (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    List.Forall (· = 0) (Extracted.JalColumns.asserts cols) ↔
      ( AddOperation.AssertSpec
          #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]
          #v[cols.adapter.op_b_imm[0], cols.adapter.op_b_imm[1],
              cols.adapter.op_b_imm[2], cols.adapter.op_b_imm[3]]
          #v[cols.add_operation.value[0], cols.add_operation.value[1],
              cols.add_operation.value[2], cols.add_operation.value[3]]
        ∧ AddOperation.AssertSpec
          #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]
          #v[4, 0, 0, 0]
          #v[cols.op_a_operation.value[0], cols.op_a_operation.value[1],
              cols.op_a_operation.value[2], cols.op_a_operation.value[3]]
        ∧ cols.add_operation.value[3] = 0
        ∧ cols.op_a_operation.value[3] = 0 ) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.JalColumns.asserts]
  rw [Extracted.forall_append_single, Extracted.forall_append_single]
  simp only [h_real, h_op_a_0, sub_zero]
  rw [add_asserts_faithful, add_asserts_faithful]
  simp only [List.Forall, sub_self, mul_zero, zero_mul, true_and, and_true]
  tauto

set_option maxHeartbeats 2000000 in
/-- **Chip-level faithfulness anchor — interaction half.** Under `is_real = 1 ∧ op_a_0 = 0`, SP1's
generated JAL `interactions` list holds iff: the two `AddOperation` limb-range specs (jump target and
link address), the jump-target alignment `Range(add_operation.value[0]/4, 14)`, the two CPUState clock
bounds, and `op_a`'s timestamp byte bounds. The state/program/memory sends contribute `True`. -/
theorem jalcols_interactions_faithful (cols : Extracted.JalColumns (ZMod p))
    (h_real : cols.is_real = 1) (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    List.Forall Interaction.toProp (Extracted.JalColumns.interactions cols) ↔
      ( AddOperation.InteractSpec
          #v[cols.add_operation.value[0], cols.add_operation.value[1],
              cols.add_operation.value[2], cols.add_operation.value[3]]
        ∧ AddOperation.InteractSpec
            #v[cols.op_a_operation.value[0], cols.op_a_operation.value[1],
                cols.op_a_operation.value[2], cols.op_a_operation.value[3]]
        ∧ (cols.add_operation.value[0] * (4 : ZMod p)⁻¹).val < 2 ^ 14
        ∧ ((cols.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13
        ∧ cols.state.clk_16_24.val < 2 ^ 8
        ∧ cols.adapter.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16
        ∧ ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 4
              - cols.adapter.op_a_memory.access_timestamp.prev_low - 1
              - cols.adapter.op_a_memory.access_timestamp.diff_low_limb) * (65536 : ZMod p)⁻¹).val < 2 ^ 8 ) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.JalColumns.interactions]
  rw [Extracted.forall_append_interactions, Extracted.forall_append_interactions]
  simp only [h_real, h_op_a_0, sub_zero]
  rw [add_interactions_faithful, add_interactions_faithful]
  simp only [List.Forall, Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, Interaction.toProp_send_program, Interaction.toProp_send_state,
    ByteOpcode.ofNat_six, ByteOpcode.ofNat_three, ByteOpcode.constrain_Range,
    ByteOpcode.constrain_U8Range, val_13, val_14, val_16, ZMod.val_zero, one_ne_zero, ne_eq,
    not_false_eq_true, true_implies, Nat.ofNat_pos, true_and, and_true,
    show (2 : ℕ) ^ 8 = 256 from by norm_num]
  tauto

end SP1Clean.Faithful
