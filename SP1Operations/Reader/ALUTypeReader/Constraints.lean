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
  (instr_field_consts : (Vector (Fin BB) 4))
  (op_a_write_value : (Word (Fin BB)))
  (cols : ALUTypeReader)
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
  let E11 : Fin BB := is_real - 1
  let E12 : Fin BB := cols.imm_c - 0
  let E13 : Fin BB := E11 * E12
  let E14 : Fin BB := 0 + cols.op_b
  let E15 : Fin BB := op_a_write_value[0] - 0
  let E16 : Fin BB := cols.op_a_0 * E15
  let E17 : Fin BB := op_a_write_value[1] - 0
  let E18 : Fin BB := cols.op_a_0 * E17
  let E19 : Fin BB := op_a_write_value[2] - 0
  let E20 : Fin BB := cols.op_a_0 * E19
  let E21 : Fin BB := op_a_write_value[3] - 0
  let E22 : Fin BB := cols.op_a_0 * E21
  let E23 : Fin BB := clk_low + 4
  let E24 : Fin BB := is_real - 1
  let E25 : Fin BB := is_real * E24
  let E26 : Fin BB := E23 - cols.op_a_memory.access_timestamp.prev_low
  let E27 : Fin BB := E26 - 1
  let E28 : Fin BB := E27 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E29 : Fin BB := E28 * 2130673921
  let E30 : Fin BB := clk_low + 3
  let E31 : Fin BB := is_real - 1
  let E32 : Fin BB := is_real * E31
  let E33 : Fin BB := E30 - cols.op_b_memory.access_timestamp.prev_low
  let E34 : Fin BB := E33 - 1
  let E35 : Fin BB := E34 - cols.op_b_memory.access_timestamp.diff_low_limb
  let E36 : Fin BB := E35 * 2130673921
  let E37 : Fin BB := clk_low + 2
  let E38 : Fin BB := is_real - cols.imm_c
  let E39 : Fin BB := E38 - 1
  let E40 : Fin BB := E38 * E39
  let E41 : Fin BB := E37 - cols.op_c_memory.access_timestamp.prev_low
  let E42 : Fin BB := E41 - 1
  let E43 : Fin BB := E42 - cols.op_c_memory.access_timestamp.diff_low_limb
  let E44 : Fin BB := E43 * 2130673921
  let E45 : Fin BB := cols.op_c_memory.prev_value[0] - cols.op_c[0]
  let E46 : Fin BB := cols.imm_c * E45
  let E47 : Fin BB := cols.op_c_memory.prev_value[1] - cols.op_c[1]
  let E48 : Fin BB := cols.imm_c * E47
  let E49 : Fin BB := cols.op_c_memory.prev_value[2] - cols.op_c[2]
  let E50 : Fin BB := cols.imm_c * E49
  let E51 : Fin BB := cols.op_c_memory.prev_value[3] - cols.op_c[3]
  let E52 : Fin BB := cols.imm_c * E51
  [
    (.assertZero E1),
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero E8),
    (.assertZero E10),
    (.assertZero E13),
    (.send (.program pc[0] pc[1] pc[2] (Opcode.ofNat opcode) cols.op_a E14 0 0 0 cols.op_c[0] cols.op_c[1] cols.op_c[2] cols.op_c[3] cols.op_a_0 0 cols.imm_c) cols.is_trusted),
    (.assertZero E16),
    (.assertZero E18),
    (.assertZero E20),
    (.assertZero E22),
    (.assertZero E25),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_a_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E29 0) is_real),
    (.send (.memory clk_high cols.op_a_memory.access_timestamp.prev_low cols.op_a 0 0 cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1] cols.op_a_memory.prev_value[2] cols.op_a_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E23 cols.op_a 0 0 op_a_write_value[0] op_a_write_value[1] op_a_write_value[2] op_a_write_value[3]) is_real),
    (.assertZero E32),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_b_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E36 0) is_real),
    (.send (.memory clk_high cols.op_b_memory.access_timestamp.prev_low cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E30 cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
    (.assertZero E40),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_c_memory.access_timestamp.diff_low_limb 16 0) E38),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E44 0) E38),
    (.send (.memory clk_high cols.op_c_memory.access_timestamp.prev_low cols.op_c[0] 0 0 cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1] cols.op_c_memory.prev_value[2] cols.op_c_memory.prev_value[3]) E38),
    (.receive (.memory clk_high E37 cols.op_c[0] 0 0 cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1] cols.op_c_memory.prev_value[2] cols.op_c_memory.prev_value[3]) E38),
    (.assertZero E46),
    (.assertZero E48),
    (.assertZero E50),
    (.assertZero E52),
  ]

end constraints
