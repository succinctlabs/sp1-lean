import SP1Foundations
import SP1Operations.Reader.ITypeReader.Operation

namespace ITypeReaderImmutable

-- dtumad: shouldn't need this really
set_option linter.unusedVariables false

section constraints

@[irreducible] def constraints
  (clk_high : (Fin KB))
  (clk_low : (Fin KB))
  (pc : (Vector (Fin KB) 3))
  (opcode : (Fin KB))
  (instr_field_consts : (Vector (Fin KB) 4))
  (cols : ITypeReader)
  (is_real : (Fin KB))
  : SP1ConstraintList :=
  let E0 : Fin KB := is_real - 1
  let E1 : Fin KB := is_real * E0
  let E2 : Fin KB := is_real - cols.is_trusted
  let E3 : Fin KB := E2 - 1
  let E4 : Fin KB := E2 * E3
  let E5 : Fin KB := cols.is_trusted - 1
  let E6 : Fin KB := cols.is_trusted * E5
  let E7 : Fin KB := E2 + cols.is_trusted
  let E8 : Fin KB := E7 - is_real
  let E9 : Fin KB := public_value () 151 - 1
  let E10 : Fin KB := E2 * E9
  let E11 : Fin KB := 0 + cols.op_b
  let E12 : Fin KB := cols.op_a_memory.prev_value[0] - 0
  let E13 : Fin KB := cols.op_a_0 * E12
  let E14 : Fin KB := cols.op_a_memory.prev_value[1] - 0
  let E15 : Fin KB := cols.op_a_0 * E14
  let E16 : Fin KB := cols.op_a_memory.prev_value[2] - 0
  let E17 : Fin KB := cols.op_a_0 * E16
  let E18 : Fin KB := cols.op_a_memory.prev_value[3] - 0
  let E19 : Fin KB := cols.op_a_0 * E18
  let E20 : Fin KB := clk_low + 4
  let E21 : Fin KB := is_real - 1
  let E22 : Fin KB := is_real * E21
  let E23 : Fin KB := E20 - cols.op_a_memory.access_timestamp.prev_low
  let E24 : Fin KB := E23 - 1
  let E25 : Fin KB := E24 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E26 : Fin KB := E25 * 2130673921
  let E27 : Fin KB := clk_low + 3
  let E28 : Fin KB := is_real - 1
  let E29 : Fin KB := is_real * E28
  let E30 : Fin KB := E27 - cols.op_b_memory.access_timestamp.prev_low
  let E31 : Fin KB := E30 - 1
  let E32 : Fin KB := E31 - cols.op_b_memory.access_timestamp.diff_low_limb
  let E33 : Fin KB := E32 * 2130673921
  [
    (.assertZero E1),
    (.assertZero E4),
    (.assertZero E6),
    (.assertZero E8),
    (.assertZero E10),
    (.send (.program pc[0] pc[1] pc[2] (Opcode.ofNat opcode) cols.op_a E11 0 0 0 cols.op_c_imm[0] cols.op_c_imm[1] cols.op_c_imm[2] cols.op_c_imm[3] cols.op_a_0 0 1) cols.is_trusted),
    (.assertZero E13),
    (.assertZero E15),
    (.assertZero E17),
    (.assertZero E19),
    (.assertZero E22),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_a_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E26 0) is_real),
    (.send (.memory clk_high cols.op_a_memory.access_timestamp.prev_low cols.op_a 0 0 cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1] cols.op_a_memory.prev_value[2] cols.op_a_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E20 cols.op_a 0 0 cols.op_a_memory.prev_value[0] cols.op_a_memory.prev_value[1] cols.op_a_memory.prev_value[2] cols.op_a_memory.prev_value[3]) is_real),
    (.assertZero E29),
    (.send (.byte (ByteOpcode.ofNat 6) cols.op_b_memory.access_timestamp.diff_low_limb 16 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E33 0) is_real),
    (.send (.memory clk_high cols.op_b_memory.access_timestamp.prev_low cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
    (.receive (.memory clk_high E27 cols.op_b 0 0 cols.op_b_memory.prev_value[0] cols.op_b_memory.prev_value[1] cols.op_b_memory.prev_value[2] cols.op_b_memory.prev_value[3]) is_real),
  ]

end constraints

end ITypeReaderImmutable
