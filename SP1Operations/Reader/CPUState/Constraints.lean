import SP1Operations.Reader.CPUState.Operation

namespace CPUState

section constraints

@[irreducible] def constraints {F : Type*} [Field F]
  (cols : CPUState F)
  (next_pc : (Vector F 3))
  (clk_increment : F)
  (is_real : F)
  : SP1ConstraintList F :=
  let E0 : F := cols.clk_16_24 * 65536
  let E1 : F := cols.clk_0_16 + E0
  let E2 : F := is_real - 1
  let E3 : F := is_real * E2
  let E4 : F := E1 + clk_increment
  let E5 : F := cols.clk_0_16 - 1
  let E6 : F := E5 * ((8 : F)⁻¹)
  [
    (.assertZero E3),
    (.receive (.state cols.clk_high E1 cols.pc[0] cols.pc[1] cols.pc[2]) is_real),
    (.send (.state cols.clk_high E4 next_pc[0] next_pc[1] next_pc[2]) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) E6 13 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.clk_16_24 0) is_real),
  ]

end constraints

end CPUState
