import SP1Foundations
import SP1Operations.Reader.ALUTypeReader.Operation

namespace ALUTypeReader

set_option linter.unusedVariables false
-- Generated Lean code for operation ALUTypeReader (from chip Bitwise)
section constraints

def constraints
  (clk_high : (Fin BB))
  (clk_low : (Fin BB))
  (pc : (Vector (Fin BB) 3))
  (opcode : (Fin BB))
  (instr_field_consts : (Vector (Fin BB) 3))
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
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_a_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E20 0) is_real),
    (.send (.memory clk_high cols.op_a_memory.access_timestamp.prev_low cols.op_a 0 0 cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1] cols.op_a_memory.prev_value[2] cols.op_a_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E14 cols.op_a 0 0 op_a_write_value[0] op_a_write_value[1] op_a_write_value[2] op_a_write_value[3]) is_real),
    (.assertZero E23),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_b_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E27 0) is_real),
    (.send (.memory clk_high cols.op_b_memory.access_timestamp.prev_low cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E21 cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
    (.assertZero E31),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_c_memory.access_timestamp.diff_low_limb 16 0) E29),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E35 0) E29),
    (.send (.memory clk_high cols.op_c_memory.access_timestamp.prev_low cols.op_c[0] 0 0 cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1] cols.op_c_memory.prev_value[2] cols.op_c_memory.prev_value[3]) E29),
    (.receive (.memory clk_high E28 cols.op_c[0] 0 0 cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1] cols.op_c_memory.prev_value[2] cols.op_c_memory.prev_value[3]) E29),
    (.assertZero E37),
    (.assertZero E39),
    (.assertZero E41),
    (.assertZero E43),
  ]

end constraints
