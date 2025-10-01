import SP1Foundations
import SP1Operations.Reader.ALUTypeReader.Operation
import SP1Operations.Reader.ALUTypeReader.Constraints

namespace ALUTypeReader

attribute [-simp] Opcode.trusted_instr

set_option maxHeartbeats 2000000 in
lemma allHold_constraints_iff :
  List.Forall SP1Constraint.toProp (constraints clk_high clk_low pc opcode instr_field_consts op_a_write_value cols is_real) ↔
    (is_real = 0 ∨ is_real = 1) ∧
    (cols.is_trusted = is_real) ∧
    (is_real = 0 → cols.imm_c = 0) ∧
    (¬is_real = 0 →
      Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0 cols.op_c[0] cols.op_c[1] cols.op_c[2] cols.op_c[3] 0 cols.imm_c ∧
      cols.op_a < 32 ∧
      cols.op_b < 65536 ∧
      (cols.op_c[0] < 65536 ∧ cols.op_c[1] < 65536 ∧ cols.op_c[2] < 65536 ∧ cols.op_c[3] < 65536) ∧
      (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
      (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
      (cols.imm_c = 0 ∨ cols.imm_c = 1) ∧
      pc[0] % 4 = 0 ∧
      pc[0] < 65536 ∧ pc[1] < 65536 ∧ pc[2] < 65536 ∧
      cols.op_a_memory.access_timestamp.diff_low_limb < 65536 ∧
      cols.op_b_memory.access_timestamp.diff_low_limb < 65536 ∧
      (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 - cols.op_b_memory.access_timestamp.diff_low_limb) * 2130673921 < 256 ∧
      (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 - cols.op_a_memory.access_timestamp.diff_low_limb) * 2130673921 < 256 ∧
      Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1], cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
      Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1], cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]]) ∧
    (is_real - cols.imm_c = 0 ∨ is_real - cols.imm_c - 1 = 0) ∧
    (¬is_real - cols.imm_c = 0 →
      (clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1 - cols.op_c_memory.access_timestamp.diff_low_limb) * 2130673921 < 256 ∧
      cols.op_c_memory.access_timestamp.diff_low_limb < 65536 ∧
      Word.isU64 #v[cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1], cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]]) ∧
    (cols.op_a_0 ≠ 0 →
      op_a_write_value[0] = 0 ∧
      op_a_write_value[1] = 0 ∧
      op_a_write_value[2] = 0 ∧
      op_a_write_value[3] = 0) ∧
    (¬cols.imm_c = 0 →
      cols.op_c_memory.prev_value[0] = cols.op_c[0] ∧
      cols.op_c_memory.prev_value[1] = cols.op_c[1] ∧
      cols.op_c_memory.prev_value[2] = cols.op_c[2] ∧
      cols.op_c_memory.prev_value[3] = cols.op_c[3])
   := by
  simp [constraints, sub_eq_zero, SP1Constraint.toProp, Fin.lt_iff_val_lt_val]
  intros h_is_real
  rcases h_is_real with h | h
  · simp [h]
    by_cases htrust : cols.is_trusted = 0
    · simp [htrust]
      by_cases ha0 : cols.op_a_0 = 0 <;> simp [ha0]
      · intro himm_c
        simp [himm_c]
      · intro himm_c
        simp [himm_c]
    · simp [htrust]
  · simp [h]
    by_cases htrust : cols.is_trusted = 0
    · simp [htrust]
    · simp [htrust, ← @eq_comm _ cols.is_trusted, and_assoc]
      intros
      by_cases hop_a_0 : cols.op_a_0 = 0
      · simp [hop_a_0]
        aesop
      · simp [hop_a_0]
        aesop

set_option maxHeartbeats 1000000 in
lemma allHold_constraints_iff_is_real (h : is_real = 1) :
  List.Forall SP1Constraint.toProp (constraints clk_high clk_low pc opcode instr_field_consts op_a_write_value cols is_real) ↔
    (cols.is_trusted = is_real) ∧
    Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0 cols.op_c[0] cols.op_c[1] cols.op_c[2] cols.op_c[3] 0 cols.imm_c ∧
    cols.op_a < 32 ∧
    cols.op_b < 65536 ∧
    (cols.op_c[0] < 65536 ∧ cols.op_c[1] < 65536 ∧ cols.op_c[2] < 65536 ∧ cols.op_c[3] < 65536) ∧
    (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
    (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
    (cols.imm_c = 0 ∨ cols.imm_c = 1) ∧
    pc[0] % 4 = 0 ∧
    pc[0] < 65536 ∧ pc[1] < 65536 ∧ pc[2] < 65536 ∧
    cols.op_a_memory.access_timestamp.diff_low_limb < 65536 ∧
    cols.op_b_memory.access_timestamp.diff_low_limb < 65536 ∧
    (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 - cols.op_b_memory.access_timestamp.diff_low_limb) * 2130673921 < 256 ∧
    (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 - cols.op_a_memory.access_timestamp.diff_low_limb) * 2130673921 < 256 ∧
    Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1], cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
    Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1], cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
    (cols.imm_c = 0 →
      (clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1 - cols.op_c_memory.access_timestamp.diff_low_limb) * 2130673921 < 256 ∧
      cols.op_c_memory.access_timestamp.diff_low_limb < 65536 ∧
      Word.isU64 #v[cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1], cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]]) ∧
    (¬cols.op_a_0 = 0 →
      op_a_write_value[0] = 0 ∧
      op_a_write_value[1] = 0 ∧
      op_a_write_value[2] = 0 ∧
      op_a_write_value[3] = 0) ∧
    (¬cols.imm_c = 0 →
      cols.op_c_memory.prev_value[0] = cols.op_c[0] ∧
      cols.op_c_memory.prev_value[1] = cols.op_c[1] ∧
      cols.op_c_memory.prev_value[2] = cols.op_c[2] ∧
      cols.op_c_memory.prev_value[3] = cols.op_c[3])
   := by aesop (add safe (by simp [allHold_constraints_iff]))

end ALUTypeReader
