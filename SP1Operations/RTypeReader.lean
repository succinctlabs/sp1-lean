import SP1Foundations
import SP1Operations.MemoryConsistency
import LeanRV32IM.RiscvRegs

open LeanRV32IM.Functions

--- A Reader that only accesses values of type `T`.
structure RTypeReader where
  op_a : Fin BB
  op_a_memory : MemoryAccessInSharedCols
  op_a_0 : Fin BB
  op_b : Fin BB
  op_b_memory : MemoryAccessInSharedCols
  op_c : Fin BB
  op_c_memory : MemoryAccessInSharedCols

namespace RTypeReader

set_option linter.unusedVariables false in
def constraints
  (clk_high : Fin BB)
  (clk_low : Fin BB)
  (pc : Fin BB)
  (opcode : Fin BB)
  (op_a_write_value : Word (Fin BB))
  (cols : RTypeReader)
  (is_real : Fin BB)
  : SP1ConstraintList :=
  let E0 : Fin BB := is_real - 1
  let E1 : Fin BB := is_real * E0
  let E2 : Fin BB := 0 + cols.op_b
  let E3 : Fin BB := 0 + cols.op_c
  let E4 : Fin BB := op_a_write_value[0] - 0
  let E5 : Fin BB := cols.op_a_0 * E4
  let E6 : Fin BB := op_a_write_value[1] - 0
  let E7 : Fin BB := cols.op_a_0 * E6
  let E8 : Fin BB := clk_low + 3
  let E9 : Fin BB := is_real - 1
  let E10 : Fin BB := is_real * E9
  let E11 : Fin BB := E8 - cols.op_a_memory.access_timestamp.prev_low
  let E12 : Fin BB := E11 - 1
  let E13 : Fin BB := E12 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E14 : Fin BB := E13 * 2013235201
  let E15 : Fin BB := clk_low + 2
  let E16 : Fin BB := is_real - 1
  let E17 : Fin BB := is_real * E16
  let E18 : Fin BB := E15 - cols.op_b_memory.access_timestamp.prev_low
  let E19 : Fin BB := E18 - 1
  let E20 : Fin BB := E19 - cols.op_b_memory.access_timestamp.diff_low_limb
  let E21 : Fin BB := E20 * 2013235201
  let E22 : Fin BB := clk_low + 1
  let E23 : Fin BB := is_real - 1
  let E24 : Fin BB := is_real * E23
  let E25 : Fin BB := E22 - cols.op_c_memory.access_timestamp.prev_low
  let E26 : Fin BB := E25 - 1
  let E27 : Fin BB := E26 - cols.op_c_memory.access_timestamp.diff_low_limb
  let E28 : Fin BB := E27 * 2013235201
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

lemma op_b_memory_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
    {op_a_write_value : Word (Fin BB)} {cols : RTypeReader}
    (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
    cols.op_b_memory.prev_value[0] < 65536 ∧ cols.op_b_memory.prev_value[1] < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

lemma op_c_memory_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
    {op_a_write_value : Word (Fin BB)} {cols : RTypeReader}
    (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
    cols.op_c_memory.prev_value[0] < 65536 ∧ cols.op_c_memory.prev_value[1] < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

lemma op_a_write_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
    {op_a_write_value : Word (Fin BB)} {cols : RTypeReader}
    (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
    op_a_write_value[0] < 65536 ∧ op_a_write_value[1] < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

lemma val_op_b_memory_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
    {op_a_write_value : Word (Fin BB)} {cols : RTypeReader}
    (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
    cols.op_b_memory.prev_value[0].val < 65536 ∧ cols.op_b_memory.prev_value[1].val < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

lemma val_op_c_memory_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
    {op_a_write_value : Word (Fin BB)} {cols : RTypeReader}
    (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
    cols.op_c_memory.prev_value[0].val < 65536 ∧ cols.op_c_memory.prev_value[1].val < 65536 := by
  have := op_c_memory_lt_of_constraints h
  aesop

lemma val_op_a_write_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
    {op_a_write_value : Word (Fin BB)} {cols : RTypeReader}
    (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
    op_a_write_value[0].val < 65536 ∧ op_a_write_value[1].val < 65536 := by
  simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
  tauto

end RTypeReader
