import SP1Foundations
import SP1Operations.MemoryConsistency
import LeanRV32D.RiscvRegs

open LeanRV32D.Functions

--- A Reader that only accesses values of type `T`.
structure RTypeReader where
  op_a : BabyBear
  op_a_memory : MemoryAccessInSharedCols
  op_a_0 : BabyBear
  op_b : BabyBear
  op_b_memory : MemoryAccessInSharedCols
  op_c : BabyBear
  op_c_memory : MemoryAccessInSharedCols

namespace RTypeReader

set_option linter.unusedVariables false in
def constraints
  (clk_high : BabyBear)
  (clk_low : BabyBear)
  (pc : BabyBear)
  (opcode : BabyBear)
  (op_a_write_value : Word BabyBear)
  (cols : RTypeReader)
  (is_real : BabyBear)
  : SP1ConstraintList :=
  let E0 : BabyBear := is_real - 1
  let E1 : BabyBear := is_real * E0
  let E2 : BabyBear := 0 + cols.op_b
  let E3 : BabyBear := 0 + cols.op_c
  let E4 : BabyBear := op_a_write_value[0] - 0
  let E5 : BabyBear := cols.op_a_0 * E4
  let E6 : BabyBear := op_a_write_value[1] - 0
  let E7 : BabyBear := cols.op_a_0 * E6
  let E8 : BabyBear := clk_low + 3
  let E9 : BabyBear := is_real - 1
  let E10 : BabyBear := is_real * E9
  let E11 : BabyBear := E8 - cols.op_a_memory.access_timestamp.prev_low
  let E12 : BabyBear := E11 - 1
  let E13 : BabyBear := E12 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E14 : BabyBear := E13 * 2013235201
  let E15 : BabyBear := clk_low + 2
  let E16 : BabyBear := is_real - 1
  let E17 : BabyBear := is_real * E16
  let E18 : BabyBear := E15 - cols.op_b_memory.access_timestamp.prev_low
  let E19 : BabyBear := E18 - 1
  let E20 : BabyBear := E19 - cols.op_b_memory.access_timestamp.diff_low_limb
  let E21 : BabyBear := E20 * 2013235201
  let E22 : BabyBear := clk_low + 1
  let E23 : BabyBear := is_real - 1
  let E24 : BabyBear := is_real * E23
  let E25 : BabyBear := E22 - cols.op_c_memory.access_timestamp.prev_low
  let E26 : BabyBear := E25 - 1
  let E27 : BabyBear := E26 - cols.op_c_memory.access_timestamp.diff_low_limb
  let E28 : BabyBear := E27 * 2013235201
  [
    .assertZero E1,
    .assertZero E5,
    .assertZero E7,
    .assertZero E10,
    .send (.byte (ByteOpcode.ofNat 6) cols.op_a_memory.access_timestamp.diff_low_limb 16 0) is_real,
    .send (.byte (ByteOpcode.ofNat 3) 0 E14 0) is_real,
    .send (.memory clk_high cols.op_a_memory.access_timestamp.prev_low cols.op_a cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1]) is_real,
    .receive (.memory clk_high E8 cols.op_a op_a_write_value[0] op_a_write_value[1]) is_real,
    .assertZero E17,
    .send (.byte (ByteOpcode.ofNat 6) cols.op_b_memory.access_timestamp.diff_low_limb 16 0) is_real,
    .send (.byte (ByteOpcode.ofNat 3) 0 E21 0) is_real,
    .send (.memory clk_high cols.op_b_memory.access_timestamp.prev_low cols.op_b cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1]) is_real,
    .receive (.memory clk_high E15 cols.op_b cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1]) is_real,
    .assertZero E24,
    .send (.byte (ByteOpcode.ofNat 6) cols.op_c_memory.access_timestamp.diff_low_limb 16 0) is_real,
    .send (.byte (ByteOpcode.ofNat 3) 0 E28 0) is_real,
    .send (.memory clk_high cols.op_c_memory.access_timestamp.prev_low cols.op_c cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1]) is_real,
    .receive (.memory clk_high E22 cols.op_c cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1]) is_real
  ]

lemma op_b_memory_lt_of_constraints {clk_high clk_low pc opcode : BabyBear}
    {op_a_write_value : Word BabyBear} {cols : RTypeReader}
    (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
    cols.op_b_memory.prev_value[0] < 65536 ∧ cols.op_b_memory.prev_value[1] < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

lemma op_c_memory_lt_of_constraints {clk_high clk_low pc opcode : BabyBear}
    {op_a_write_value : Word BabyBear} {cols : RTypeReader}
    (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
    cols.op_c_memory.prev_value[0] < 65536 ∧ cols.op_c_memory.prev_value[1] < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

lemma op_a_write_lt_of_constraints {clk_high clk_low pc opcode : BabyBear}
    {op_a_write_value : Word BabyBear} {cols : RTypeReader}
    (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
    op_a_write_value[0] < 65536 ∧ op_a_write_value[1] < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

lemma val_op_b_memory_lt_of_constraints {clk_high clk_low pc opcode : BabyBear}
    {op_a_write_value : Word BabyBear} {cols : RTypeReader}
    (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
    cols.op_b_memory.prev_value[0].val < 65536 ∧ cols.op_b_memory.prev_value[1].val < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

lemma val_op_c_memory_lt_of_constraints {clk_high clk_low pc opcode : BabyBear}
    {op_a_write_value : Word BabyBear} {cols : RTypeReader}
    (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
    cols.op_c_memory.prev_value[0].val < 65536 ∧ cols.op_c_memory.prev_value[1].val < 65536 := by
  have := op_c_memory_lt_of_constraints h
  aesop

lemma val_op_a_write_lt_of_constraints {clk_high clk_low pc opcode : BabyBear}
    {op_a_write_value : Word BabyBear} {cols : RTypeReader}
    (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
    op_a_write_value[0].val < 65536 ∧ op_a_write_value[1].val < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

end RTypeReader
