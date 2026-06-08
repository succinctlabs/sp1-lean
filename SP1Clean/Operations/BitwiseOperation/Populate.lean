import SP1Clean.Specs.Operation
import SP1Clean.Foundations.Bitwise
import SP1Clean.Operations.BitwiseOperation.Extracted

/-! # `BitwiseOperation` — `populate` (the witness generator)

The witness assignment `populate` (the eight result bytes — the per-byte `byteOp opcode` of the operand
bytes, threaded in by a composing operation) and `spec_populate` (the witnessed result satisfies the
gadget `Spec`). The elaborated `eval` circuit is the auto-generated sibling `Extracted` module; the
arithmetic core is in `RawSpec`; the `FormalAssertion` contract in `Formal`. -/

namespace SP1Clean.BitwiseOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native port of SP1's `BitwiseOperation` result column: each result byte is `byteOp opcode a b`. -/
def populate (a b : Vector (ZMod p) 8) (opcode : ZMod p) : Extracted.BitwiseOperation (ZMod p) :=
  ⟨#v[((byteOp opcode.val a[0].val b[0].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[1].val b[1].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[2].val b[2].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[3].val b[3].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[4].val b[4].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[5].val b[5].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[6].val b[6].val : ℕ) : ZMod p),
      ((byteOp opcode.val a[7].val b[7].val : ℕ) : ZMod p)]⟩

end SP1Clean.BitwiseOperation
