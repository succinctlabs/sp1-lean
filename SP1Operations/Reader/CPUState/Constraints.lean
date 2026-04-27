import SP1Operations.Reader.CPUState.Operation

namespace CPUState

section constraints

@[irreducible] def constraints
  (cols : CPUState)
  (next_pc : (Vector (Fin KB) 3))
  (clk_increment : (Fin KB))
  (is_real : (Fin KB))
  : SP1ConstraintList (Fin KB) :=
  let E0 : Fin KB := cols.clk_16_24 * 65536
  let E1 : Fin KB := cols.clk_0_16 + E0
  let E2 : Fin KB := is_real - 1
  let E3 : Fin KB := is_real * E2
  let E4 : Fin KB := E1 + clk_increment
  let E5 : Fin KB := cols.clk_0_16 - 1
  let E6 : Fin KB := E5 * ((8 : Fin KB)⁻¹)
  [
    (.assertZero E3),
    (.receive (.state cols.clk_high E1 cols.pc[0] cols.pc[1] cols.pc[2]) is_real),
    (.send (.state cols.clk_high E4 next_pc[0] next_pc[1] next_pc[2]) is_real),
    (.send (.byte (ByteOpcode.ofNat 6) E6 13 0) is_real),
    (.send (.byte (ByteOpcode.ofNat 3) 0 cols.clk_16_24 0) is_real),
  ]

end constraints

end CPUState
