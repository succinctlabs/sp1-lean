import SP1Operations.Reader.JTypeReader.Operation

namespace JTypeReader

set_option linter.unusedVariables false
-- Generated Lean code for operation JTypeReader (from chip Add)
section constraints

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (clk_high : F)
  (clk_low : F)
  (pc : (Vector F 3))
  (opcode : F)
  (instr_field_consts : (Vector F 4))
  (op_a_write_value : (Word F))
  (cols : JTypeReader F)
  (is_real : F)
  : SP1ConstraintList F :=
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let E2 : F := op_a_write_value[0] - 0
  let E3 : F := cols.op_a_0 * E2
  let E4 : F := op_a_write_value[1] - 0
  let E5 : F := cols.op_a_0 * E4
  let E6 : F := op_a_write_value[2] - 0
  let E7 : F := cols.op_a_0 * E6
  let E8 : F := op_a_write_value[3] - 0
  let E9 : F := cols.op_a_0 * E8
  let E10 : F := clk_low + 4
  let E11 : F := is_real - 1
  let E12 : F := is_real * E11
  let E13 : F := E10 - cols.op_a_memory.access_timestamp.prev_low
  let E14 : F := E13 - 1
  let E15 : F := E14 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E16 : F := E15 * ((65536 : F)⁻¹)
  [
    (.assertZero E1),
    (.send (.program pc[0] pc[1] pc[2] (Opcode.ofNat opcode) cols.op_a cols.op_b_imm[0] cols.op_b_imm[1] cols.op_b_imm[2] cols.op_b_imm[3] cols.op_c_imm[0] cols.op_c_imm[1] cols.op_c_imm[2] cols.op_c_imm[3] cols.op_a_0 1 1) is_real),
    (.assertZero E3),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero E12),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_a_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E16 0) is_real),
    (.send (.memory clk_high cols.op_a_memory.access_timestamp.prev_low cols.op_a 0 0 cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1] cols.op_a_memory.prev_value[2] cols.op_a_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E10 cols.op_a 0 0 op_a_write_value[0] op_a_write_value[1] op_a_write_value[2] op_a_write_value[3]) is_real),
  ]

end constraints

end JTypeReader
