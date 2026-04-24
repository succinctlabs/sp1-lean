import SP1Operations.Reader.ITypeReader.Operation
import SP1Operations.Reader.ITypeReader.Constraints

namespace ITypeReader

attribute [-simp] Opcode.trusted_instr

set_option maxHeartbeats 1000000 in

-- iff-characterization of ITypeReader constraints
lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints clk_high clk_low pc opcode instr_field_consts op_a_write_value cols is_real) ↔
    (is_real = 0 ∨ is_real = 1) ∧
    (¬is_real = 0 →
      Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0 cols.op_c_imm[0] cols.op_c_imm[1] cols.op_c_imm[2] cols.op_c_imm[3] 0 1 ∧
      cols.op_a < 32 ∧
      cols.op_b < 65536 ∧
      cols.op_c_imm[0] < 65536 ∧ cols.op_c_imm[1] < 65536 ∧ cols.op_c_imm[2] < 65536 ∧ cols.op_c_imm[3] < 65536 ∧
      (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
      (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
      pc[0] % 4 = 0 ∧
      pc[0] < 65536 ∧ pc[1] < 65536 ∧ pc[2] < 65536 ∧
      cols.op_a_memory.access_timestamp.diff_low_limb < 65536 ∧
      cols.op_b_memory.access_timestamp.diff_low_limb < 65536 ∧
      (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 - cols.op_b_memory.access_timestamp.diff_low_limb) * 2130673921 < 256 ∧
      (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 - cols.op_a_memory.access_timestamp.diff_low_limb) * 2130673921 < 256 ∧
      Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1], cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
      Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1], cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]]) ∧
    (cols.op_a_0 ≠ 0 →
      op_a_write_value[0] = 0 ∧
      op_a_write_value[1] = 0 ∧
      op_a_write_value[2] = 0 ∧
      op_a_write_value[3] = 0)
   := by
    simp [constraints, sub_eq_zero, SP1Constraint.toProp, Fin.lt_def]
    intros h_is_real
    rcases h_is_real with h | h
    · simp [h]
      by_cases ha0 : cols.op_a_0 = 0
      · simp [ha0]
      · tauto
    · simp [h]
      by_cases hop_a_0 : cols.op_a_0 = 0
      · simp [hop_a_0]
        aesop
      · simp [hop_a_0]
        aesop

lemma allHold_constraints_iff_is_real (h : is_real = 1) :
  List.Forall SP1Constraint.toProp (constraints clk_high clk_low pc opcode instr_field_consts op_a_write_value cols is_real) ↔
    Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0 cols.op_c_imm[0] cols.op_c_imm[1] cols.op_c_imm[2] cols.op_c_imm[3] 0 1 ∧
    cols.op_a < 32 ∧
    cols.op_b < 65536 ∧
    cols.op_c_imm[0] < 65536 ∧ cols.op_c_imm[1] < 65536 ∧ cols.op_c_imm[2] < 65536 ∧ cols.op_c_imm[3] < 65536 ∧
    (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
    (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
    pc[0] % 4 = 0 ∧
    pc[0] < 65536 ∧ pc[1] < 65536 ∧ pc[2] < 65536 ∧
    cols.op_a_memory.access_timestamp.diff_low_limb < 65536 ∧
    cols.op_b_memory.access_timestamp.diff_low_limb < 65536 ∧
    (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 - cols.op_b_memory.access_timestamp.diff_low_limb) * 2130673921 < 256 ∧
    (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 - cols.op_a_memory.access_timestamp.diff_low_limb) * 2130673921 < 256 ∧
    Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1], cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
    Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1], cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
    (cols.op_a_0 ≠ 0 →
      op_a_write_value[0] = 0 ∧
      op_a_write_value[1] = 0 ∧
      op_a_write_value[2] = 0 ∧
      op_a_write_value[3] = 0)
   := by aesop (add safe (by simp [allHold_constraints_iff]))

end ITypeReader
