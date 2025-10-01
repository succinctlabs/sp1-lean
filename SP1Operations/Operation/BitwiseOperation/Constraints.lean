import SP1Foundations
import SP1Operations.Operation.BitwiseOperation.Operation

namespace BitwiseOperation

section constraints

@[irreducible] def constraints
  (a : (Vector (Fin KB) 8))
  (b : (Vector (Fin KB) 8))
  (cols : BitwiseOperation)
  (opcode : (Fin KB))
  (is_real : (Fin KB))
  : SP1ConstraintList :=
  [
    (.send (.byte (ByteOpcode.ofNat opcode) cols.result[0] a[0] b[0]) is_real),
    (.send (.byte (ByteOpcode.ofNat opcode) cols.result[1] a[1] b[1]) is_real),
    (.send (.byte (ByteOpcode.ofNat opcode) cols.result[2] a[2] b[2]) is_real),
    (.send (.byte (ByteOpcode.ofNat opcode) cols.result[3] a[3] b[3]) is_real),
    (.send (.byte (ByteOpcode.ofNat opcode) cols.result[4] a[4] b[4]) is_real),
    (.send (.byte (ByteOpcode.ofNat opcode) cols.result[5] a[5] b[5]) is_real),
    (.send (.byte (ByteOpcode.ofNat opcode) cols.result[6] a[6] b[6]) is_real),
    (.send (.byte (ByteOpcode.ofNat opcode) cols.result[7] a[7] b[7]) is_real),
  ]

end constraints
