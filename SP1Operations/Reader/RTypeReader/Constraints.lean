import SP1Operations.Reader.RTypeReader.Operation

namespace RTypeReader

set_option linter.style.setOption false
set_option linter.style.longLine false

set_option linter.unusedVariables false
-- Generated Lean code for operation RTypeReader (from chip Add)
section constraints

@[irreducible] def constraints {F : Type} [Field F] [CoeHead F ℕ]
  (clk_high : F)
  (clk_low : F)
  (pc : (Vector F 3))
  (opcode : F)
  (op_a_write_value : (Word F))
  (cols : RTypeReader F)
  (is_real : F)
  (is_trusted : F)
  : SP1ConstraintList F :=
  let E0 : F := is_real - 1
  let E1 : F := is_real * E0
  let E2 : F := 0 + cols.op_b
  let E3 : F := 0 + cols.op_c
  let E4 : F := op_a_write_value[0] - 0
  let E5 : F := cols.op_a_0 * E4
  let E6 : F := op_a_write_value[1] - 0
  let E7 : F := cols.op_a_0 * E6
  let E8 : F := op_a_write_value[2] - 0
  let E9 : F := cols.op_a_0 * E8
  let E10 : F := op_a_write_value[3] - 0
  let E11 : F := cols.op_a_0 * E10
  let E12 : F := clk_low + 4
  let E13 : F := is_real - 1
  let E14 : F := is_real * E13
  let E15 : F := E12 - cols.op_a_memory.access_timestamp.prev_low
  let E16 : F := E15 - 1
  let E17 : F := E16 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E18 : F := E17 * ((65536 : F)⁻¹)
  let E19 : F := clk_low + 3
  let E20 : F := is_real - 1
  let E21 : F := is_real * E20
  let E22 : F := E19 - cols.op_b_memory.access_timestamp.prev_low
  let E23 : F := E22 - 1
  let E24 : F := E23 - cols.op_b_memory.access_timestamp.diff_low_limb
  let E25 : F := E24 * ((65536 : F)⁻¹)
  let E26 : F := clk_low + 2
  let E27 : F := is_real - 1
  let E28 : F := is_real * E27
  let E29 : F := E26 - cols.op_c_memory.access_timestamp.prev_low
  let E30 : F := E29 - 1
  let E31 : F := E30 - cols.op_c_memory.access_timestamp.diff_low_limb
  let E32 : F := E31 * ((65536 : F)⁻¹)
  [
    (.assertZero E1),
    (.send (.program pc[0] pc[1] pc[2] (Opcode.ofNat opcode) cols.op_a E2 0 0 0 E3 0 0 0 cols.op_a_0 0 0) is_trusted),
    (.assertZero E5),
    (.assertZero E7),
    (.assertZero E9),
    (.assertZero E11),
    (.assertZero E14),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_a_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E18 0) is_real),
    (.send (.memory clk_high cols.op_a_memory.access_timestamp.prev_low cols.op_a 0 0 cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1] cols.op_a_memory.prev_value[2] cols.op_a_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E12 cols.op_a 0 0 op_a_write_value[0] op_a_write_value[1] op_a_write_value[2] op_a_write_value[3]) is_real),
    (.assertZero E21),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_b_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E25 0) is_real),
    (.send (.memory clk_high cols.op_b_memory.access_timestamp.prev_low cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E19 cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
    (.assertZero E28),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_c_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E32 0) is_real),
    (.send (.memory clk_high cols.op_c_memory.access_timestamp.prev_low cols.op_c 0 0 cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1] cols.op_c_memory.prev_value[2] cols.op_c_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E26 cols.op_c 0 0 cols.op_c_memory.prev_value[0] cols.op_c_memory.prev_value[1] cols.op_c_memory.prev_value[2] cols.op_c_memory.prev_value[3]) is_real),
  ]

end constraints

end RTypeReader
