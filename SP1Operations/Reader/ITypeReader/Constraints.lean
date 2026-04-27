import SP1Operations.Reader.ITypeReader.Operation

namespace ITypeReader

set_option linter.unusedVariables false
-- Generated Lean code for operation ITypeReader (from chip Addi)
section constraints

@[irreducible] def constraints
  (clk_high : (Fin KB))
  (clk_low : (Fin KB))
  (pc : (Vector (Fin KB) 3))
  (opcode : (Fin KB))
  (instr_field_consts : (Vector (Fin KB) 4))
  (op_a_write_value : (Word (Fin KB)))
  (cols : ITypeReader)
  (is_real : (Fin KB))
  : SP1ConstraintList (Fin KB) :=
  let E0 : Fin KB := is_real - 1
  let E1 : Fin KB := is_real * E0
  let E2 : Fin KB := 0 + cols.op_b
  let E3 : Fin KB := op_a_write_value[0] - 0
  let E4 : Fin KB := cols.op_a_0 * E3
  let E5 : Fin KB := op_a_write_value[1] - 0
  let E6 : Fin KB := cols.op_a_0 * E5
  let E7 : Fin KB := op_a_write_value[2] - 0
  let E8 : Fin KB := cols.op_a_0 * E7
  let E9 : Fin KB := op_a_write_value[3] - 0
  let E10 : Fin KB := cols.op_a_0 * E9
  let E11 : Fin KB := clk_low + 4
  let E12 : Fin KB := is_real - 1
  let E13 : Fin KB := is_real * E12
  let E14 : Fin KB := E11 - cols.op_a_memory.access_timestamp.prev_low
  let E15 : Fin KB := E14 - 1
  let E16 : Fin KB := E15 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E17 : Fin KB := E16 * ((65536 : Fin KB)⁻¹)
  let E18 : Fin KB := clk_low + 3
  let E19 : Fin KB := is_real - 1
  let E20 : Fin KB := is_real * E19
  let E21 : Fin KB := E18 - cols.op_b_memory.access_timestamp.prev_low
  let E22 : Fin KB := E21 - 1
  let E23 : Fin KB := E22 - cols.op_b_memory.access_timestamp.diff_low_limb
  let E24 : Fin KB := E23 * ((65536 : Fin KB)⁻¹)
  [
    (.assertZero E1),
    (.send (.program pc[0] pc[1] pc[2] (Opcode.ofNat opcode) cols.op_a E2 0 0 0 cols.op_c_imm[0] cols.op_c_imm[1] cols.op_c_imm[2] cols.op_c_imm[3] cols.op_a_0 0 1) is_real),
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero E8),
    (.assertZero E10),
    (.assertZero E13),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_a_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E17 0) is_real),
    (.send (.memory clk_high cols.op_a_memory.access_timestamp.prev_low cols.op_a 0 0 cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1] cols.op_a_memory.prev_value[2] cols.op_a_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E11 cols.op_a 0 0 op_a_write_value[0] op_a_write_value[1] op_a_write_value[2] op_a_write_value[3]) is_real),
    (.assertZero E20),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_b_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E24 0) is_real),
    (.send (.memory clk_high cols.op_b_memory.access_timestamp.prev_low cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E18 cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
  ]

end constraints

end ITypeReader
