import SP1Operations.Reader.JTypeReader.Operation

namespace JTypeReader

set_option linter.unusedVariables false
-- Generated Lean code for operation JTypeReader (from chip Add)
section constraints

def constraints
  (clk_high : (Fin BB))
  (clk_low : (Fin BB))
  (pc : (Vector (Fin BB) 3))
  (opcode : (Fin BB))
  (instr_field_consts : (Vector (Fin BB) 4))
  (op_a_write_value : (Word (Fin BB)))
  (cols : JTypeReader)
  (is_real : (Fin BB))
  : SP1ConstraintList :=
  let E0 : Fin BB := is_real - 1
  let E1 : Fin BB := is_real * E0
  let E2 : Fin BB := is_real - cols.is_trusted
  let E3 : Fin BB := E2 - 1
  let E4 : Fin BB := E2 * E3
  let E5 : Fin BB := cols.is_trusted - 1
  let E6 : Fin BB := cols.is_trusted * E5
  let E7 : Fin BB := E2 + cols.is_trusted
  let E8 : Fin BB := E7 - is_real
  let E9 : Fin BB := mprotect_enabled () - 1
  let E10 : Fin BB := E2 * E9
  let E11 : Fin BB := op_a_write_value[0] - 0
  let E12 : Fin BB := cols.op_a_0 * E11
  let E13 : Fin BB := op_a_write_value[1] - 0
  let E14 : Fin BB := cols.op_a_0 * E13
  let E15 : Fin BB := op_a_write_value[2] - 0
  let E16 : Fin BB := cols.op_a_0 * E15
  let E17 : Fin BB := op_a_write_value[3] - 0
  let E18 : Fin BB := cols.op_a_0 * E17
  let E19 : Fin BB := clk_low + 4
  let E20 : Fin BB := is_real - 1
  let E21 : Fin BB := is_real * E20
  let E22 : Fin BB := E19 - cols.op_a_memory.access_timestamp.prev_low
  let E23 : Fin BB := E22 - 1
  let E24 : Fin BB := E23 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E25 : Fin BB := E24 * 2130673921
  [
    (.assertZero E1),
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero E8),
    (.assertZero E10),
    (.send (.program pc[0] pc[1] pc[2] (Opcode.ofNat opcode) cols.op_a cols.op_b_imm[0] cols.op_b_imm[1] cols.op_b_imm[2] cols.op_b_imm[3] cols.op_c_imm[0] cols.op_c_imm[1] cols.op_c_imm[2] cols.op_c_imm[3] cols.op_a_0 1 1) cols.is_trusted),
    (.assertZero E12),
    (.assertZero E14),
    (.assertZero E16),
    (.assertZero E18),
    (.assertZero E21),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_a_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E25 0) is_real),
    (.send (.memory clk_high cols.op_a_memory.access_timestamp.prev_low cols.op_a 0 0 cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1] cols.op_a_memory.prev_value[2] cols.op_a_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E19 cols.op_a 0 0 op_a_write_value[0] op_a_write_value[1] op_a_write_value[2] op_a_write_value[3]) is_real),
  ]

end constraints

end JTypeReader
