import SP1Foundations

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

def constraints
  (clk_high : (Fin BB))
  (clk_low : (Fin BB))
  (_pc : (Vector (Fin BB) 3))
  (_opcode : (Fin BB))
  (op_a_write_value : (Word (Fin BB)))
  (cols : RTypeReader)
  (is_real : (Fin BB))
  : SP1ConstraintList :=
  let E0 : Fin BB := is_real - 1
  let E1 : Fin BB := is_real * E0
  let E2 : Fin BB := 0 + cols.op_b
  let E3 : Fin BB := 0 + cols.op_c
  let E4 : Fin BB := op_a_write_value[0] - 0
  let E5 : Fin BB := cols.op_a_0 * E4
  let E6 : Fin BB := op_a_write_value[1] - 0
  let E7 : Fin BB := cols.op_a_0 * E6
  let E8 : Fin BB := op_a_write_value[2] - 0
  let E9 : Fin BB := cols.op_a_0 * E8
  let E10 : Fin BB := op_a_write_value[3] - 0
  let E11 : Fin BB := cols.op_a_0 * E10
  let E12 : Fin BB := clk_low + 3
  let E13 : Fin BB := is_real - 1
  let E14 : Fin BB := is_real * E13
  let E15 : Fin BB := E12 - cols.op_a_memory.access_timestamp.prev_low
  let E16 : Fin BB := E15 - 1
  let E17 : Fin BB := E16 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E18 : Fin BB := E17 * 2013235201
  let E19 : Fin BB := clk_low + 2
  let E20 : Fin BB := is_real - 1
  let E21 : Fin BB := is_real * E20
  let E22 : Fin BB := E19 - cols.op_b_memory.access_timestamp.prev_low
  let E23 : Fin BB := E22 - 1
  let E24 : Fin BB := E23 - cols.op_b_memory.access_timestamp.diff_low_limb
  let E25 : Fin BB := E24 * 2013235201
  let E26 : Fin BB := clk_low + 1
  let E27 : Fin BB := is_real - 1
  let E28 : Fin BB := is_real * E27
  let E29 : Fin BB := E26 - cols.op_c_memory.access_timestamp.prev_low
  let E30 : Fin BB := E29 - 1
  let E31 : Fin BB := E30 - cols.op_c_memory.access_timestamp.diff_low_limb
  let E32 : Fin BB := E31 * 2013235201
  [
    (.assertZero E1),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero E11),
    (.assertZero E14),
    (.send (.byte (ByteOpcode.ofNat 7) cols.op_a_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E18 0) is_real),
    (.send (.memory clk_high cols.op_a_memory.access_timestamp.prev_low cols.op_a 0 0 cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1] cols.op_a_memory.prev_value[2] cols.op_a_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E12 cols.op_a 0 0 op_a_write_value[0] op_a_write_value[1] op_a_write_value[2] op_a_write_value[3]) is_real),
    (.assertZero E21),
    (.send (.byte (ByteOpcode.ofNat 7) cols.op_b_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E25 0) is_real),
    (.send (.memory clk_high cols.op_b_memory.access_timestamp.prev_low cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E19 cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
    (.assertZero E28),
    (.send (.byte (ByteOpcode.ofNat 7) cols.op_c_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E32 0) is_real),
    (.send (.memory clk_high cols.op_c_memory.access_timestamp.prev_low cols.op_c 0 0 cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1] cols.op_c_memory.prev_value[2] cols.op_c_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E26 cols.op_c 0 0 cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1] cols.op_c_memory.prev_value[2] cols.op_c_memory.prev_value[3]) is_real),
  ]

-- lemma op_b_memory_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
--     {op_a_write_value : Word (Fin BB)} {cols : RTypeReader}
--     (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
--     cols.op_b_memory.prev_value[0] < 65536 ∧ cols.op_b_memory.prev_value[1] < 65536 := by
--   simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
--   tauto

-- lemma op_c_memory_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
--     {op_a_write_value : Word (Fin BB)} {cols : RTypeReader}
--     (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
--     cols.op_c_memory.prev_value[0] < 65536 ∧ cols.op_c_memory.prev_value[1] < 65536 := by
--   simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
--   tauto

-- lemma op_a_write_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
--     {op_a_write_value : Word (Fin BB)} {cols : RTypeReader}
--     (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
--     op_a_write_value[0] < 65536 ∧ op_a_write_value[1] < 65536 := by
--   simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
--   tauto

-- lemma val_op_b_memory_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
--     {op_a_write_value : Word (Fin BB)} {cols : RTypeReader}
--     (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
--     cols.op_b_memory.prev_value[0].val < 65536 ∧ cols.op_b_memory.prev_value[1].val < 65536 := by
--   simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
--   tauto

-- lemma val_op_c_memory_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
--     {op_a_write_value : Word (Fin BB)} {cols : RTypeReader}
--     (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
--     cols.op_c_memory.prev_value[0].val < 65536 ∧ cols.op_c_memory.prev_value[1].val < 65536 := by
--   have := op_c_memory_lt_of_constraints h
--   aesop

-- lemma val_op_a_write_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
--     {op_a_write_value : Word (Fin BB)} {cols : RTypeReader}
--     (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
--     op_a_write_value[0].val < 65536 ∧ op_a_write_value[1].val < 65536 := by
--   simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
--   tauto

end RTypeReader
