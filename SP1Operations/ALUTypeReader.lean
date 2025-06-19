import SP1Foundations
import SP1Operations.MemoryConsistency
import LeanRV32D.RiscvRegs

open LeanRV32D.Functions

--- A Reader that only accesses values of type `T`.
structure ALUTypeReader where
  op_a : BabyBear
  op_a_memory : MemoryAccessInSharedCols
  op_a_0 : BabyBear
  op_b : BabyBear
  op_b_memory : MemoryAccessInSharedCols
  op_c : Word BabyBear
  op_c_memory : MemoryAccessInSharedCols
  imm_c : BabyBear

namespace ALUTypeReader

def constraints
  (shard clk _pc _opcode: BabyBear)
  (op_a_write_value : Word BabyBear)
  (cols : ALUTypeReader)
  (is_real : BabyBear)
  : SP1ConstraintList :=
    let E0 : BabyBear := is_real - 1
    let E2 : BabyBear := is_real * E0
    let E4 : BabyBear := is_real - 1
    let E6 : BabyBear := cols.imm_c - 0
    let E8 : BabyBear := E4 * E6
    let E10 : BabyBear := 0 + cols.op_b
    let E12 : BabyBear := op_a_write_value[0] - 0
    let E14 : BabyBear := cols.op_a_0 * E12
    let E16 : BabyBear := op_a_write_value[1] - 0
    let E18 : BabyBear := cols.op_a_0 * E16
    let E20 : BabyBear := clk + 3
    let E22 : BabyBear := is_real - 1
    let E24 : BabyBear := is_real * E22
    let E26 : BabyBear := E20 - cols.op_a_memory.access_timestamp.prev_clk
    let E28 : BabyBear := E26 - 1
    let E30 : BabyBear := E28 - cols.op_a_memory.access_timestamp.diff_low_limb
    let E32 : BabyBear := E30 * 2013143041
    let E34 : BabyBear := clk + 2
    let E36 : BabyBear := is_real - 1
    let E38 : BabyBear := is_real * E36
    let E40 : BabyBear := E34 - cols.op_b_memory.access_timestamp.prev_clk
    let E42 : BabyBear := E40 - 1
    let E44 : BabyBear := E42 - cols.op_b_memory.access_timestamp.diff_low_limb
    let E46 : BabyBear := E44 * 2013143041
    let E48 : BabyBear := clk + 1
    let E50 : BabyBear := is_real - cols.imm_c
    let E52 : BabyBear := E50 - 1
    let E54 : BabyBear := E50 * E52
    let E56 : BabyBear := E48 - cols.op_c_memory.access_timestamp.prev_clk
    let E58 : BabyBear := E56 - 1
    let E60 : BabyBear := E58 - cols.op_c_memory.access_timestamp.diff_low_limb
    let E62 : BabyBear := E60 * 2013143041
    let E64 : BabyBear := cols.op_c_memory.prev_value[0] - cols.op_c[0]
    let E66 : BabyBear := cols.imm_c * E64
    let E68 : BabyBear := cols.op_c_memory.prev_value[1] - cols.op_c[1]
    let E70 : BabyBear := cols.imm_c * E68

    [
      .assertZero E2,
      .assertZero E8,
      .assertZero E14,
      .assertZero E18,
      .assertZero E24,
      .send (.byte (ByteOpcode.ofNat 6) cols.op_a_memory.access_timestamp.diff_low_limb 14 0) is_real,
      .send (.byte (ByteOpcode.ofNat 6) E32 14 0) is_real,
      .send (.memory shard cols.op_a_memory.access_timestamp.prev_clk cols.op_a cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1]) is_real,
      .receive (.memory shard E20 cols.op_a op_a_write_value[0] op_a_write_value[1]) is_real,
      .assertZero E38,
      .send (.byte (ByteOpcode.ofNat 6) cols.op_b_memory.access_timestamp.diff_low_limb 14 0) is_real,
      .send (.byte (ByteOpcode.ofNat 6) E46 14 0) is_real,
      .send (.memory shard cols.op_b_memory.access_timestamp.prev_clk cols.op_b cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1]) is_real,
      .receive (.memory shard E34 cols.op_b cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1]) is_real,
      .assertZero E54,
      .send (.byte (ByteOpcode.ofNat 6) cols.op_c_memory.access_timestamp.diff_low_limb 14 0) E50,
      .send (.byte (ByteOpcode.ofNat 6) E62 14 0) E50,
      .send (.memory shard cols.op_c_memory.access_timestamp.prev_clk cols.op_c[0] cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1]) E50,
      .receive (.memory shard E48 cols.op_c[0] cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1]) E50,
      .assertZero E66,
      .assertZero E70
    ]

/-- `.assertZero E2` (also `E22`) -/
lemma is_real_eq_of_constraints
    (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
    is_real = 0 ∨ is_real = 1 := by
  simp_all [constraints, sub_eq_zero]

/-- `.assertZero E8` -/
lemma is_real_eq_one_or_imm_c_eq_zero_of_constraints
    (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
    is_real = 1 ∨ cols.imm_c = 0 := by
  simp_all [constraints, sub_eq_zero]

/-- `.assertZero E14` -/
lemma op_a_zero_or_op_a_write_values_eq_zero_of_constraints₀
    (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
    cols.op_a_0 = 0 ∨ op_a_write_value[0] = 0 := by
  simp_all [constraints, sub_eq_zero]

/-- `.assertZero E18` -/
lemma op_a_zero_or_op_a_write_values_eq_zero_of_constraints₁
    (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
    cols.op_a_0 = 0 ∨ op_a_write_value[1] = 0 := by
  simp_all [constraints, sub_eq_zero]

lemma op_a_zero_or_op_a_write_values_word_eq_zero_of_constraints
    (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
    cols.op_a_0 = 0 ∨ Word.toFin32_BB op_a_write_value = 0 := by
  rw [Word.toFin32_BB]
  have h0 := op_a_zero_or_op_a_write_values_eq_zero_of_constraints₀ h
  have h1 := op_a_zero_or_op_a_write_values_eq_zero_of_constraints₁ h
  rw [or_iff_not_imp_left]
  intro h
  simp_all [h]

/-- `.assertZero E54` NOTE: this one seems strange, should rephrase probably -/
lemma is_real_sub_imm_c
    (h : (constraints shard clk pc opcode ap_a_write_value cols is_real).allHold) :
    is_real - cols.imm_c = 0 ∨ is_real - cols.imm_c = 1 := by
  simp_all [constraints, sub_eq_zero]

/-- `.assertZero E66` -/
lemma imm_c_eq_zero_or_prev_value_eq_op_c_of_constraints₀
    (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
    cols.imm_c = 0 ∨ cols.op_c_memory.prev_value[0] = cols.op_c[0] := by
  simp_all [constraints, sub_eq_zero]

/-- `.assertZero 70` -/
lemma imm_c_eq_zero_or_prev_value_eq_op_c_of_constraints₁
    (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
    cols.imm_c = 0 ∨ cols.op_c_memory.prev_value[1] = cols.op_c[1] := by
  simp_all [constraints, sub_eq_zero]

lemma imm_c_eq_zero_or_prev_value_eq_op_c
    (h : (constraints shard clk pc opcode op_a_write_value cols is_real).allHold) :
    cols.imm_c = 0 ∨ cols.op_c_memory.prev_value = cols.op_c := by
  have h0 := imm_c_eq_zero_or_prev_value_eq_op_c_of_constraints₀ h
  have h1 := imm_c_eq_zero_or_prev_value_eq_op_c_of_constraints₁ h
  rw [Word.ext_cases_iff]
  aesop

end ALUTypeReader
