import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Model.SP1Constraint
import SP1Clean.Model.ByteTable
import SP1Clean.Extracted.LoadByteChip
import SP1Clean.Faithful.AddressOperation
import SP1Clean.Faithful.CPUState
import SP1Clean.Faithful.ITypeReader
import SP1Clean.Faithful.ChipTactics

/-! # Chip-level faithfulness anchor — SP1's whole `LoadByte` chip constraint list ↔ combined spec -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

set_option linter.unusedSimpArgs false in
set_option maxHeartbeats 4000000 in
theorem loadbytecols_constraints_faithful (cols : Extracted.LoadByteColumns (ZMod p))
    (h_real : cols.is_lb + cols.is_lbu = 1) :
    (List.Forall (· = 0) (Extracted.LoadByteColumns.asserts cols) ∧
      List.Forall Interaction.toProp (Extracted.LoadByteColumns.interactions cols)) ↔
      ((SP1Clean.AddressOperation.RawSpec
              #v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
                cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3]]
              #v[cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1], cols.adapter.op_c_imm[2],
                cols.adapter.op_c_imm[3]] cols.offset_bit[0] cols.offset_bit[1] cols.offset_bit[2]
              { addr_operation :=
                  { value := #v[cols.address_operation.addr_operation.value[0],
                      cols.address_operation.addr_operation.value[1],
                      cols.address_operation.addr_operation.value[2]] },
                top_two_limb_inv := cols.address_operation.top_two_limb_inv }
            ∧ ((cols.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13
                ∧ cols.state.clk_16_24.val < 256)
          ∧ (cols.adapter.op_a_0 * (cols.selected_byte + 65280 * cols.msb) = 0 ∧
              cols.adapter.op_a_0 * (65535 * cols.msb) = 0 ∧
              cols.adapter.op_a_0 * (65535 * cols.msb) = 0 ∧
              cols.adapter.op_a_0 * (65535 * cols.msb) = 0)
          ∧ (cols.adapter.op_a_memory.access_timestamp.diff_low_limb.val < 65536 ∧
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 4
                  - cols.adapter.op_a_memory.access_timestamp.prev_low - 1
                  - cols.adapter.op_a_memory.access_timestamp.diff_low_limb)
                    * (65536 : ZMod p)⁻¹).val < 256) ∧
            cols.adapter.op_b_memory.access_timestamp.diff_low_limb.val < 65536 ∧
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 3
                  - cols.adapter.op_b_memory.access_timestamp.prev_low - 1
                  - cols.adapter.op_b_memory.access_timestamp.diff_low_limb)
                    * (65536 : ZMod p)⁻¹).val < 256)
        ∧ ((cols.is_lb * (cols.is_lb - 1) = 0 ∧
              cols.is_lbu * (cols.is_lbu - 1) = 0 ∧
              cols.memory_access.access_timestamp.compare_low
                  * (cols.memory_access.access_timestamp.compare_low - 1) = 0 ∧
              cols.memory_access.access_timestamp.compare_low
                  * (cols.state.clk_high - cols.memory_access.access_timestamp.prev_high) = 0 ∧
              cols.memory_access.access_timestamp.compare_low
                        * (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 1) +
                      (1 - cols.memory_access.access_timestamp.compare_low) * cols.state.clk_high -
                    (cols.memory_access.access_timestamp.compare_low
                          * cols.memory_access.access_timestamp.prev_low +
                      (1 - cols.memory_access.access_timestamp.compare_low)
                        * cols.memory_access.access_timestamp.prev_high) -
                  1 -
                (cols.memory_access.access_timestamp.diff_low_limb +
                  cols.memory_access.access_timestamp.diff_high_limb * 65536) = 0 ∧
              cols.adapter.op_a_0 = 0 ∧
              (cols.offset_bit[1] - 1) * ((cols.offset_bit[2] - 1)
                  * (cols.selected_limb - cols.memory_access.prev_value[0])) = 0 ∧
              cols.offset_bit[1] * ((cols.offset_bit[2] - 1)
                  * (cols.selected_limb - cols.memory_access.prev_value[1])) = 0 ∧
              (cols.offset_bit[1] - 1) * (cols.offset_bit[2]
                  * (cols.selected_limb - cols.memory_access.prev_value[2])) = 0 ∧
              cols.offset_bit[1] * (cols.offset_bit[2]
                  * (cols.selected_limb - cols.memory_access.prev_value[3])) = 0 ∧
              cols.selected_byte - (cols.offset_bit[0]
                    * ((cols.selected_limb - cols.selected_limb_low_byte) * (256 : ZMod p)⁻¹) +
                  (1 - cols.offset_bit[0]) * cols.selected_limb_low_byte) = 0 ∧
              cols.is_lbu * cols.msb = 0) ∧
            cols.memory_access.access_timestamp.diff_low_limb.val < 65536 ∧
              cols.memory_access.access_timestamp.diff_high_limb.val < 256 ∧
              (cols.selected_limb_low_byte.val < 256 ∧
                  ((cols.selected_limb - cols.selected_limb_low_byte) * (256 : ZMod p)⁻¹).val < 256) ∧
                (¬cols.is_lb = 0 →
                  (cols.msb.val < 256 ∧ cols.selected_byte.val < 256) ∧
                    (cols.msb = 0 ∨ cols.msb = 1) ∧ (cols.msb = 1 ↔ 128 ≤ cols.selected_byte.val))) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.LoadByteColumns.asserts, Extracted.LoadByteColumns.interactions]
  rw [forall_append_pair, forall_append_pair, forall_append_pair]
  simp only [h_real]
  rw [address_constraints_faithful, cpustate_constraints_faithful, itypereader_constraints_faithful]
  simp only [List.Forall, Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, ByteOpcode.ofNat_six, ByteOpcode.ofNat_three,
    ByteOpcode.ofNat_five, ByteOpcode.constrain_Range, ByteOpcode.constrain_U8Range,
    ByteOpcode.constrain_MSB, val_16, ZMod.val_zero,
    one_ne_zero, ne_eq, not_false_eq_true, true_implies, one_mul, sub_self, mul_zero,
    Nat.ofNat_pos, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, true_and, and_true, Nat.cast_one, Nat.cast_ofNat,
    show (2 : ℕ) ^ 8 = 256 from by norm_num, show (2 : ℕ) ^ 16 = 65536 from by norm_num]

end SP1Clean.Faithful
