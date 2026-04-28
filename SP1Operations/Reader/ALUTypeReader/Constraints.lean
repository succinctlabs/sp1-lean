import SP1Foundations
import SP1Operations.Reader.ALUTypeReader.Operation

namespace ALUTypeReader

set_option linter.unusedVariables false
-- Generated Lean code for operation ALUTypeReader (from chip Bitwise)
section constraints

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (clk_high : F)
  (clk_low : F)
  (pc : Vector F 3)
  (opcode : F)
  (instr_field_consts : Vector F 4)
  (op_a_write_value : Word F)
  (cols : ALUTypeReader F)
  (is_real : F)
  : SP1ConstraintList F :=
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let E2 : F := is_real - 1
  let E3 : F := cols.imm_c - 0
  let E4 : F := E2 * E3
  let E5 : F := 0 + cols.op_b
  let E6 : F := op_a_write_value[0] - 0
  let E7 : F := cols.op_a_0 * E6
  let E8 : F := op_a_write_value[1] - 0
  let E9 : F := cols.op_a_0 * E8
  let E10 : F := op_a_write_value[2] - 0
  let E11 : F := cols.op_a_0 * E10
  let E12 : F := op_a_write_value[3] - 0
  let E13 : F := cols.op_a_0 * E12
  let E14 : F := clk_low + 4
  let E15 : F := is_real - 1
  let E16 : F := is_real * E15
  let E17 : F := E14 - cols.op_a_memory.access_timestamp.prev_low
  let E18 : F := E17 - 1
  let E19 : F := E18 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E20 : F := E19 * ((65536 : F)⁻¹)
  let E21 : F := clk_low + 3
  let E22 : F := is_real - 1
  let E23 : F := is_real * E22
  let E24 : F := E21 - cols.op_b_memory.access_timestamp.prev_low
  let E25 : F := E24 - 1
  let E26 : F := E25 - cols.op_b_memory.access_timestamp.diff_low_limb
  let E27 : F := E26 * ((65536 : F)⁻¹)
  let E28 : F := clk_low + 2
  let E29 : F := is_real - cols.imm_c
  let E30 : F := E29 - 1
  let E31 : F := E29 * E30
  let E32 : F := E28 - cols.op_c_memory.access_timestamp.prev_low
  let E33 : F := E32 - 1
  let E34 : F := E33 - cols.op_c_memory.access_timestamp.diff_low_limb
  let E35 : F := E34 * ((65536 : F)⁻¹)
  let E36 : F := cols.op_c_memory.prev_value[0] - cols.op_c[0]
  let E37 : F := cols.imm_c * E36
  let E38 : F := cols.op_c_memory.prev_value[1] - cols.op_c[1]
  let E39 : F := cols.imm_c * E38
  let E40 : F := cols.op_c_memory.prev_value[2] - cols.op_c[2]
  let E41 : F := cols.imm_c * E40
  let E42 : F := cols.op_c_memory.prev_value[3] - cols.op_c[3]
  let E43 : F := cols.imm_c * E42
  [
    (.assertZero E1),
    (.assertZero E4),
    (.send (.program pc[0] pc[1] pc[2] (Opcode.ofNat opcode) cols.op_a E5 0 0 0 cols.op_c[0] cols.op_c[1] cols.op_c[2] cols.op_c[3] cols.op_a_0 0 cols.imm_c) is_real),
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

end ALUTypeReader
