import SP1Foundations


--- A Reader that only accesses values of type `T`.
structure ALUTypeReader where
  op_a : Fin BB
  op_a_memory : MemoryAccessInSharedCols
  op_a_0 : Fin BB
  op_b : Fin BB
  op_b_memory : MemoryAccessInSharedCols
  op_c : Word (Fin BB)
  op_c_memory : MemoryAccessInSharedCols
  imm_c : Fin BB

namespace ALUTypeReader

def constraints
  (clk_high : (Fin BB))
  (clk_low : (Fin BB))
  (_pc : (Vector (Fin BB) 3))
  (_opcode : (Fin BB))
  (op_a_write_value : (Word (Fin BB)))
  (cols : ALUTypeReader)
  (is_real : (Fin BB))
  : SP1ConstraintList :=
  let E0 : Fin BB := is_real - 1
  let E1 : Fin BB := is_real * E0
  let E2 : Fin BB := is_real - 1
  let E3 : Fin BB := cols.imm_c - 0
  let E4 : Fin BB := E2 * E3
  let E5 : Fin BB := 0 + cols.op_b
  let E6 : Fin BB := op_a_write_value[0] - 0
  let E7 : Fin BB := cols.op_a_0 * E6
  let E8 : Fin BB := op_a_write_value[1] - 0
  let E9 : Fin BB := cols.op_a_0 * E8
  let E10 : Fin BB := op_a_write_value[2] - 0
  let E11 : Fin BB := cols.op_a_0 * E10
  let E12 : Fin BB := op_a_write_value[3] - 0
  let E13 : Fin BB := cols.op_a_0 * E12
  let E14 : Fin BB := clk_low + 3
  let E15 : Fin BB := is_real - 1
  let E16 : Fin BB := is_real * E15
  let E17 : Fin BB := E14 - cols.op_a_memory.access_timestamp.prev_low
  let E18 : Fin BB := E17 - 1
  let E19 : Fin BB := E18 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E20 : Fin BB := E19 * 2013235201
  let E21 : Fin BB := clk_low + 2
  let E22 : Fin BB := is_real - 1
  let E23 : Fin BB := is_real * E22
  let E24 : Fin BB := E21 - cols.op_b_memory.access_timestamp.prev_low
  let E25 : Fin BB := E24 - 1
  let E26 : Fin BB := E25 - cols.op_b_memory.access_timestamp.diff_low_limb
  let E27 : Fin BB := E26 * 2013235201
  let E28 : Fin BB := clk_low + 1
  let E29 : Fin BB := is_real - cols.imm_c
  let E30 : Fin BB := E29 - 1
  let E31 : Fin BB := E29 * E30
  let E32 : Fin BB := E28 - cols.op_c_memory.access_timestamp.prev_low
  let E33 : Fin BB := E32 - 1
  let E34 : Fin BB := E33 - cols.op_c_memory.access_timestamp.diff_low_limb
  let E35 : Fin BB := E34 * 2013235201
  let E36 : Fin BB := cols.op_c_memory.prev_value[0] - cols.op_c[0]
  let E37 : Fin BB := cols.imm_c * E36
  let E38 : Fin BB := cols.op_c_memory.prev_value[1] - cols.op_c[1]
  let E39 : Fin BB := cols.imm_c * E38
  let E40 : Fin BB := cols.op_c_memory.prev_value[2] - cols.op_c[2]
  let E41 : Fin BB := cols.imm_c * E40
  let E42 : Fin BB := cols.op_c_memory.prev_value[3] - cols.op_c[3]
  let E43 : Fin BB := cols.imm_c * E42
  [
    (.assertZero E1),
    (.assertZero E4),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero E11),
    (.assertZero E13),
    (.assertZero E16),
    (.send (.byte (ByteOpcode.ofNat 7) cols.op_a_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E20 0) is_real),
    (.send (.memory clk_high cols.op_a_memory.access_timestamp.prev_low cols.op_a 0 0 cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1] cols.op_a_memory.prev_value[2] cols.op_a_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E14 cols.op_a 0 0 op_a_write_value[0] op_a_write_value[1] op_a_write_value[2] op_a_write_value[3]) is_real),
    (.assertZero E23),
    (.send (.byte (ByteOpcode.ofNat 7) cols.op_b_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E27 0) is_real),
    (.send (.memory clk_high cols.op_b_memory.access_timestamp.prev_low cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E21 cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
    (.assertZero E31),
    (.send (.byte (ByteOpcode.ofNat 7) cols.op_c_memory.access_timestamp.diff_low_limb 16 0) E29),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E35 0) E29),
    (.send (.memory clk_high cols.op_c_memory.access_timestamp.prev_low cols.op_c[0] 0 0 cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1] cols.op_c_memory.prev_value[2] cols.op_c_memory.prev_value[3]) E29),
    (.receive (.memory clk_high E28 cols.op_c[0] 0 0 cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1] cols.op_c_memory.prev_value[2] cols.op_c_memory.prev_value[3]) E29),
    (.assertZero E37),
    (.assertZero E39),
    (.assertZero E41),
    (.assertZero E43),
  ]

end ALUTypeReader

-- import SP1Foundations
-- import SP1Operations.MemoryConsistency
-- import LeanRV32IM.RiscvRegs

-- open LeanRV32IM.Functions


-- namespace ALUTypeReader

-- def constraints
--   (shard clk _pc _opcode: Fin BB)
--   (op_a_write_value : Word (Fin BB))
--   (cols : ALUTypeReader)
--   (is_real : Fin BB)
--   : SP1ConstraintList :=
--     let E0 : Fin BB := is_real - 1
--     let E2 : Fin BB := is_real * E0
--     let E4 : Fin BB := is_real - 1
--     let E6 : Fin BB := cols.imm_c - 0
--     let E8 : Fin BB := E4 * E6
--     let E10 : Fin BB := 0 + cols.op_b
--     let E12 : Fin BB := op_a_write_value[0] - 0
--     let E14 : Fin BB := cols.op_a_0 * E12
--     let E16 : Fin BB := op_a_write_value[1] - 0
--     let E18 : Fin BB := cols.op_a_0 * E16
--     let E20 : Fin BB := clk + 3
--     let E22 : Fin BB := is_real - 1
--     let E24 : Fin BB := is_real * E22
--     let E26 : Fin BB := E20 - cols.op_a_memory.access_timestamp.prev_low
--     let E28 : Fin BB := E26 - 1
--     let E30 : Fin BB := E28 - cols.op_a_memory.access_timestamp.diff_low_limb
--     let E32 : Fin BB := E30 * 2013143041
--     let E34 : Fin BB := clk + 2
--     let E36 : Fin BB := is_real - 1
--     let E38 : Fin BB := is_real * E36
--     let E40 : Fin BB := E34 - cols.op_b_memory.access_timestamp.prev_low
--     let E42 : Fin BB := E40 - 1
--     let E44 : Fin BB := E42 - cols.op_b_memory.access_timestamp.diff_low_limb
--     let E46 : Fin BB := E44 * 2013143041
--     let E48 : Fin BB := clk + 1
--     let E50 : Fin BB := is_real - cols.imm_c
--     let E52 : Fin BB := E50 - 1
--     let E54 : Fin BB := E50 * E52
--     let E56 : Fin BB := E48 - cols.op_c_memory.access_timestamp.prev_low
--     let E58 : Fin BB := E56 - 1
--     let E60 : Fin BB := E58 - cols.op_c_memory.access_timestamp.diff_low_limb
--     let E62 : Fin BB := E60 * 2013143041
--     let E64 : Fin BB := cols.op_c_memory.prev_value[0] - cols.op_c[0]
--     let E66 : Fin BB := cols.imm_c * E64
--     let E68 : Fin BB := cols.op_c_memory.prev_value[1] - cols.op_c[1]
--     let E70 : Fin BB := cols.imm_c * E68

--     [
--       .assertZero E2,
--       .assertZero E8,
--       .assertZero E14,
--       .assertZero E18,
--       .assertZero E24,
--       .send (.byte (ByteOpcode.ofNat 6) cols.op_a_memory.access_timestamp.diff_low_limb 14 0) is_real,
--       .send (.byte (ByteOpcode.ofNat 6) E32 14 0) is_real,
--       .send (.memory shard cols.op_a_memory.access_timestamp.prev_low cols.op_a cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1]) is_real,
--       .receive (.memory shard E20 cols.op_a op_a_write_value[0] op_a_write_value[1]) is_real,
--       .assertZero E38,
--       .send (.byte (ByteOpcode.ofNat 6) cols.op_b_memory.access_timestamp.diff_low_limb 14 0) is_real,
--       .send (.byte (ByteOpcode.ofNat 6) E46 14 0) is_real,
--       .send (.memory shard cols.op_b_memory.access_timestamp.prev_low cols.op_b cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1]) is_real,
--       .receive (.memory shard E34 cols.op_b cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1]) is_real,
--       .assertZero E54,
--       .send (.byte (ByteOpcode.ofNat 6) cols.op_c_memory.access_timestamp.diff_low_limb 14 0) E50,
--       .send (.byte (ByteOpcode.ofNat 6) E62 14 0) E50,
--       .send (.memory shard cols.op_c_memory.access_timestamp.prev_low cols.op_c[0] cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1]) E50,
--       .receive (.memory shard E48 cols.op_c[0] cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1]) E50,
--       .assertZero E66,
--       .assertZero E70
--     ]

-- /-- `.assertZero E2` (also `E22`) -/
-- lemma is_real_eq_of_constraints
--     (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
--     is_real = 0 ∨ is_real = 1 := by
--   simp_all [constraints, sub_eq_zero]

-- /-- `.assertZero E8` -/
-- lemma is_real_eq_one_or_imm_c_eq_zero_of_constraints
--     (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
--     is_real = 1 ∨ cols.imm_c = 0 := by
--   simp_all [constraints, sub_eq_zero]

-- /-- `.assertZero E14` -/
-- lemma op_a_zero_or_op_a_write_values_eq_zero_of_constraints₀
--     (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
--     cols.op_a_0 = 0 ∨ op_a_write_value[0] = 0 := by
--   simp_all [constraints, sub_eq_zero]

-- /-- `.assertZero E18` -/
-- lemma op_a_zero_or_op_a_write_values_eq_zero_of_constraints₁
--     (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
--     cols.op_a_0 = 0 ∨ op_a_write_value[1] = 0 := by
--   simp_all [constraints, sub_eq_zero]

-- lemma op_a_zero_or_op_a_write_values_word_eq_zero_of_constraints
--     (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
--     cols.op_a_0 = 0 ∨ Word.toFin32_BB op_a_write_value = 0 := by
--   rw [Word.toFin32_BB]
--   have h0 := op_a_zero_or_op_a_write_values_eq_zero_of_constraints₀ h
--   have h1 := op_a_zero_or_op_a_write_values_eq_zero_of_constraints₁ h
--   rw [or_iff_not_imp_left]
--   intro h
--   simp_all

-- /-- `.assertZero E54` NOTE: this one seems strange, should rephrase probably -/
-- lemma is_real_sub_imm_c
--     (h : (constraints shard clk pc opcode ap_a_write_value cols is_real).allHold) :
--     is_real - cols.imm_c = 0 ∨ is_real - cols.imm_c = 1 := by
--   simp_all [constraints, sub_eq_zero]

-- /-- `.assertZero E66` -/
-- lemma imm_c_eq_zero_or_prev_value_eq_op_c_of_constraints₀
--     (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
--     cols.imm_c = 0 ∨ cols.op_c_memory.prev_value[0] = cols.op_c[0] := by
--   simp_all [constraints, sub_eq_zero]

-- /-- `.assertZero 70` -/
-- lemma imm_c_eq_zero_or_prev_value_eq_op_c_of_constraints₁
--     (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
--     cols.imm_c = 0 ∨ cols.op_c_memory.prev_value[1] = cols.op_c[1] := by
--   simp_all [constraints, sub_eq_zero]

-- lemma imm_c_eq_zero_or_prev_value_eq_op_c
--     (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
--     cols.imm_c = 0 ∨ cols.op_c_memory.prev_value = cols.op_c := by
--   have h0 := imm_c_eq_zero_or_prev_value_eq_op_c_of_constraints₀ h
--   have h1 := imm_c_eq_zero_or_prev_value_eq_op_c_of_constraints₁ h
--   rw [Word.ext_cases_iff]
--   aesop


-- lemma op_b_memory_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
--     {op_a_write_value : Word (Fin BB)} {cols : ALUTypeReader}
--     (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
--     cols.op_b_memory.prev_value[0] < 65536 ∧ cols.op_b_memory.prev_value[1] < 65536 := by
--   simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
--   tauto

-- lemma op_c_memory_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
--     {op_a_write_value : Word (Fin BB)} {cols : ALUTypeReader}
--     (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold)
--     (himm : cols.imm_c = 0) :
--     cols.op_c_memory.prev_value[0] < 65536 ∧ cols.op_c_memory.prev_value[1] < 65536 := by
--   simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp,
--     sub_eq_zero] at h
--   simp [himm] at h
--   tauto

-- lemma val_op_b_memory_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
--     {op_a_write_value : Word (Fin BB)} {cols : ALUTypeReader}
--     (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold) :
--     cols.op_b_memory.prev_value[0].val < 65536 ∧ cols.op_b_memory.prev_value[1].val < 65536 := by
--   simp [constraints, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain, SP1Constraint.toProp] at h
--   tauto

-- lemma val_op_c_memory_lt_of_constraints {clk_high clk_low pc opcode : Fin BB}
--     {op_a_write_value : Word (Fin BB)} {cols : ALUTypeReader}
--     (h : (cols.constraints clk_high clk_low pc opcode op_a_write_value 1).allHold)
--     (himm : cols.imm_c = 0) :
--     cols.op_c_memory.prev_value[0].val < 65536 ∧ cols.op_c_memory.prev_value[1].val < 65536 := by
--   have := op_c_memory_lt_of_constraints h himm
--   aesop

-- end ALUTypeReader
