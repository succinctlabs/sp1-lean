import SP1CleanTest.WitnessTests.Vectors.BitwiseOperation
import SP1Clean.Native.Operations.BitwiseOperation.Populate
import SP1CleanTest.WitnessTests.WitnessConformance

/-! # Witness-generation conformance anchor for `BitwiseOperation`.

Checks that `BitwiseOperation.populate` — the native witness generator the composing gadget uses to
assign the eight `result` bytes (the per-byte `byteOp opcode` of the operand bytes) — reproduces, at
SP1's concrete field, the bytes SP1's real `BitwiseOperation::populate_bitwise` wrote on every dumped
vector. Vectors span the operand battery × the three byte opcodes `{AND, OR, XOR}` (the dumper feeds
the precomputed result `a = b op c`; `byteOp` and SP1's `ByteOpcode` share the AND=0/OR=1/XOR=2
encoding). See `WitnessTests/WitnessConformance.lean` for the shared scaffolding and rationale. -/

namespace SP1Clean.WitnessTests

open SP1Clean

/-- One vector conforms iff the native `populate`, at SP1's concrete prime, reproduces the eight
`result` bytes SP1's real `populate_bitwise` wrote for the dumped operand bytes + opcode. The Lean
operand args `(a, b)` are SP1's `(b, c)` operands. Compared via `.toList` (structural `BEq`). -/
def bitwiseConforms (v : Vector ℕ 8 × Vector ℕ 8 × ℕ × Vector ℕ 8) : Bool :=
  (SP1Clean.BitwiseOperation.populate (toFieldVec v.1) (toFieldVec v.2.1)
      (toField v.2.2.1)).result.toList == (toFieldVec v.2.2.2).toList

/-- Build-checked: the native `populate` reproduces every dumped `BitwiseOperation::populate_bitwise`
vector at SP1's field. Corrupting any vector fails the build. -/
theorem bitwise_conforms :
    BitwiseOperationWitnessVectors.all bitwiseConforms = true := by native_decide

end SP1Clean.WitnessTests
