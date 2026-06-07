import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import SP1Clean.Foundations.SP1Constraint
import SP1Clean.Extracted.StoreWordChip
import SP1Clean.Faithful.AddressOperation
import SP1Clean.Faithful.CPUState
import SP1Clean.Faithful.ITypeReaderImmutable

/-! # Chip-level faithfulness anchor — SP1's whole `StoreWord` chip constraint list ↔ combined spec -/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

private lemma val_16 [NeZero p] : (16 : ZMod p).val = 16 := by
  have : (131072 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  exact ZMod.val_natCast_of_lt (show (16 : ℕ) < p by omega)

set_option maxHeartbeats 4000000 in
theorem storewordcols_constraints_faithful (cols : Extracted.StoreWordColumns (ZMod p))
    (h_real : cols.is_real = 1) :
    (List.Forall (· = 0) (Extracted.StoreWordColumns.asserts cols) ∧
      List.Forall Interaction.toProp (Extracted.StoreWordColumns.interactions cols)) ↔
      ((SP1Clean.AddressOperation.RawSpec
            #v[cols.adapter.op_b_memory.prev_value[0], cols.adapter.op_b_memory.prev_value[1],
              cols.adapter.op_b_memory.prev_value[2], cols.adapter.op_b_memory.prev_value[3]]
            #v[cols.adapter.op_c_imm[0], cols.adapter.op_c_imm[1], cols.adapter.op_c_imm[2],
              cols.adapter.op_c_imm[3]] 0 0 cols.offset_bit
            { addr_operation :=
                { value := #v[cols.address_operation.addr_operation.value[0],
                    cols.address_operation.addr_operation.value[1],
                    cols.address_operation.addr_operation.value[2]] },
              top_two_limb_inv := cols.address_operation.top_two_limb_inv }
          ∧ (((cols.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13
              ∧ cols.state.clk_16_24.val < 2 ^ 8))
        ∧ ((cols.adapter.op_a_0 * cols.adapter.op_a_memory.prev_value[0] = 0 ∧
              cols.adapter.op_a_0 * cols.adapter.op_a_memory.prev_value[1] = 0 ∧
              cols.adapter.op_a_0 * cols.adapter.op_a_memory.prev_value[2] = 0 ∧
              cols.adapter.op_a_0 * cols.adapter.op_a_memory.prev_value[3] = 0) ∧
            (cols.adapter.op_a_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 4
                  - cols.adapter.op_a_memory.access_timestamp.prev_low - 1
                  - cols.adapter.op_a_memory.access_timestamp.diff_low_limb)
                    * (65536 : ZMod p)⁻¹).val < 2 ^ 8) ∧
            cols.adapter.op_b_memory.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
              ((cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 3
                  - cols.adapter.op_b_memory.access_timestamp.prev_low - 1
                  - cols.adapter.op_b_memory.access_timestamp.diff_low_limb)
                    * (65536 : ZMod p)⁻¹).val < 2 ^ 8)
        ∧ ((cols.memory_access.access_timestamp.compare_low
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
              cols.store_value[0] - (cols.memory_access.prev_value[0]
                + (cols.adapter.op_a_memory.prev_value[0] - cols.memory_access.prev_value[0])
                  * (1 - cols.offset_bit)) = 0 ∧
              cols.store_value[1] - (cols.memory_access.prev_value[1]
                + (cols.adapter.op_a_memory.prev_value[1] - cols.memory_access.prev_value[1])
                  * (1 - cols.offset_bit)) = 0 ∧
              cols.store_value[2] - (cols.memory_access.prev_value[2]
                + (cols.adapter.op_a_memory.prev_value[0] - cols.memory_access.prev_value[2])
                  * cols.offset_bit) = 0 ∧
              cols.store_value[3] - (cols.memory_access.prev_value[3]
                + (cols.adapter.op_a_memory.prev_value[1] - cols.memory_access.prev_value[3])
                  * cols.offset_bit) = 0) ∧
            cols.memory_access.access_timestamp.diff_low_limb.val < 2 ^ 16 ∧
              cols.memory_access.access_timestamp.diff_high_limb.val < 2 ^ 8)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [Extracted.StoreWordColumns.asserts, Extracted.StoreWordColumns.interactions]
  rw [forall_append_pair, forall_append_pair, forall_append_pair]
  simp only [h_real]
  rw [address_constraints_faithful, cpustate_constraints_faithful,
    itypereaderimmutable_constraints_faithful]
  simp only [List.Forall, Interaction.toProp_send_byte, Interaction.toProp_receive,
    Interaction.toProp_send_memory, ByteOpcode.ofNat_six, ByteOpcode.ofNat_three,
    ByteOpcode.constrain_Range, ByteOpcode.constrain_U8Range, val_16, ZMod.val_zero,
    one_ne_zero, ne_eq, not_false_eq_true, true_implies, one_mul, sub_self, mul_zero,
    Nat.ofNat_pos, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, true_and, and_true,
    show (2 : ℕ) ^ 8 = 256 from by norm_num, show (2 : ℕ) ^ 16 = 65536 from by norm_num]
  tauto

end SP1Clean.Faithful
