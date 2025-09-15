import SP1Foundations
import SP1Operations.Reader.ITypeReader.Operation

namespace ITypeReaderImmutable

section constraints

def constraints
  (clk_high : (Fin BB))
  (clk_low : (Fin BB))
  (pc : (Vector (Fin BB) 3))
  (opcode : (Fin BB))
  (instr_field_consts : (Vector (Fin BB) 4))
  (cols : ITypeReader)
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
  let E11 : Fin BB := 0 + cols.op_b
  let E12 : Fin BB := cols.op_a_memory.prev_value[0] - 0
  let E13 : Fin BB := cols.op_a_0 * E12
  let E14 : Fin BB := cols.op_a_memory.prev_value[1] - 0
  let E15 : Fin BB := cols.op_a_0 * E14
  let E16 : Fin BB := cols.op_a_memory.prev_value[2] - 0
  let E17 : Fin BB := cols.op_a_0 * E16
  let E18 : Fin BB := cols.op_a_memory.prev_value[3] - 0
  let E19 : Fin BB := cols.op_a_0 * E18
  let E20 : Fin BB := clk_low + 4
  let E21 : Fin BB := is_real - 1
  let E22 : Fin BB := is_real * E21
  let E23 : Fin BB := E20 - cols.op_a_memory.access_timestamp.prev_low
  let E24 : Fin BB := E23 - 1
  let E25 : Fin BB := E24 - cols.op_a_memory.access_timestamp.diff_low_limb
  let E26 : Fin BB := E25 * 2130673921
  let E27 : Fin BB := clk_low + 3
  let E28 : Fin BB := is_real - 1
  let E29 : Fin BB := is_real * E28
  let E30 : Fin BB := E27 - cols.op_b_memory.access_timestamp.prev_low
  let E31 : Fin BB := E30 - 1
  let E32 : Fin BB := E31 - cols.op_b_memory.access_timestamp.diff_low_limb
  let E33 : Fin BB := E32 * 2130673921
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
