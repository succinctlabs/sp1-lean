import SP1Operations.Reader.ITypeReader.Operation

namespace ITypeReader

set_option linter.unusedVariables false
-- Generated Lean code for operation ITypeReader (from chip Addi)
section constraints

def constraints
  (clk_high : (Fin BB))
  (clk_low : (Fin BB))
  (pc : (Vector (Fin BB) 3))
  (opcode : (Fin BB))
  (instr_field_consts : (Vector (Fin BB) 3))
  (op_a_write_value : (Word (Fin BB)))
  (cols : ITypeReader)
  (is_real : (Fin BB))
  : SP1ConstraintList :=
  let E0 : Fin BB := is_real - 1
  let E1 : Fin BB := is_real * E0
  let E2 : Fin BB := 0 + cols.op_b
  let E3 : Fin BB := op_a_write_value[0] - 0
  let E4 : Fin BB := cols.op_a_0 * E3
  let E5 : Fin BB := op_a_write_value[1] - 0
  let E6 : Fin BB := cols.op_a_0 * E5
  let E7 : Fin BB := op_a_write_value[2] - 0
  let E8 : Fin BB := cols.op_a_0 * E7
  let E9 : Fin BB := op_a_write_value[3] - 0
  let E10 : Fin BB := cols.op_a_0 * E9
  let E11 : Fin BB := clk_low + 3
  let E12 : Fin BB := is_real - 1
  let E13 : Fin BB := is_real * E12
  let E14 : Fin BB := E11 - cols.op_a_memory.access_timestamp.prev_low
  let E15 : Fin BB := E14 - 1
  let E16 : Fin BB := E15 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E17 : Fin BB := E16 * 2013235201
  let E18 : Fin BB := clk_low + 2
  let E19 : Fin BB := is_real - 1
  let E20 : Fin BB := is_real * E19
  let E21 : Fin BB := E18 - cols.op_b_memory.access_timestamp.prev_low
  let E22 : Fin BB := E21 - 1
  let E23 : Fin BB := E22 - cols.op_b_memory.access_timestamp.diff_low_limb
  let E24 : Fin BB := E23 * 2013235201
  [
    (.assertZero E1),
    (.send (.program pc[0] pc[1] pc[2] (Opcode.ofNat opcode) cols.op_a E2 0 0 0 cols.op_c_imm[0] cols.op_c_imm[1] cols.op_c_imm[2] cols.op_c_imm[3] cols.op_a_0 0 1 instr_field_consts[0] instr_field_consts[1] instr_field_consts[2]) is_real),
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
