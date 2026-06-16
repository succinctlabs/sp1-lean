import SP1Clean.Math.Word
import SP1Clean.Math.Bitwise
import SP1Clean.Extracted.BitwiseOperation

/-! # `BitwiseOperation` — the arithmetic core (`AssertSpec` / `InteractSpec` + the byteOp lemma)

`AssertSpec` is trivially `True` (no algebraic asserts, all byte facts via the byte bus). `InteractSpec`
is the literal `interactions` list at `is_real = 1`; `bitwise_of_byteOp` derives the opcode-cased
semantic result. Faithful to `operations/bitwise.rs` (`send_byte(opcode, result, a, b, is_real)` per byte). -/

namespace SP1Clean.BitwiseOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **Assertion half** — trivial: `BitwiseOperation` emits no algebraic `asserts` (every byte fact
comes from the byte bus). -/
def AssertSpec (_a _b : Vector (ZMod p) 8) (_opcode : ZMod p)
    (_cols : Extracted.BitwiseOperation (ZMod p)) : Prop := True

/-- **Interaction half** — the literal meaning of SP1's `BitwiseOperation` `interactions` list at
`is_real = 1`: each result byte is the per-byte `byteOp opcode` of the operand bytes. -/
def InteractSpec (a b : Vector (ZMod p) 8) (opcode : ZMod p)
    (cols : Extracted.BitwiseOperation (ZMod p)) : Prop :=
  ((cols.result[0].val < 256 ∧ a[0].val < 256 ∧ b[0].val < 256) ∧ cols.result[0].val = byteOp opcode.val a[0].val b[0].val) ∧
  ((cols.result[1].val < 256 ∧ a[1].val < 256 ∧ b[1].val < 256) ∧ cols.result[1].val = byteOp opcode.val a[1].val b[1].val) ∧
  ((cols.result[2].val < 256 ∧ a[2].val < 256 ∧ b[2].val < 256) ∧ cols.result[2].val = byteOp opcode.val a[2].val b[2].val) ∧
  ((cols.result[3].val < 256 ∧ a[3].val < 256 ∧ b[3].val < 256) ∧ cols.result[3].val = byteOp opcode.val a[3].val b[3].val) ∧
  ((cols.result[4].val < 256 ∧ a[4].val < 256 ∧ b[4].val < 256) ∧ cols.result[4].val = byteOp opcode.val a[4].val b[4].val) ∧
  ((cols.result[5].val < 256 ∧ a[5].val < 256 ∧ b[5].val < 256) ∧ cols.result[5].val = byteOp opcode.val a[5].val b[5].val) ∧
  ((cols.result[6].val < 256 ∧ a[6].val < 256 ∧ b[6].val < 256) ∧ cols.result[6].val = byteOp opcode.val a[6].val b[6].val) ∧
  ((cols.result[7].val < 256 ∧ a[7].val < 256 ∧ b[7].val < 256) ∧ cols.result[7].val = byteOp opcode.val a[7].val b[7].val)

/-- Soundness core: from the per-byte `byteOp` relation (each byte pull's `ByteRowSpec` guarantee),
derive the opcode-cased semantic result (AND/OR/XOR). -/
theorem bitwise_of_byteOp {a b : Vector (ZMod p) 8} {opcode : ZMod p} {result : Fin 8 → ZMod p}
    (h_byteOp : ∀ i : Fin 8, (result i).val = byteOp opcode.val a[↑i].val b[↑i].val) :
    (opcode = 0 → ∀ i : Fin 8, (result i).val = a[↑i].val &&& b[↑i].val) ∧
    (opcode = 1 → ∀ i : Fin 8, (result i).val = a[↑i].val ||| b[↑i].val) ∧
    (opcode = 2 → ∀ i : Fin 8, (result i).val = a[↑i].val ^^^ b[↑i].val) := by
  have hp : 2 ^ 17 < p := Fact.out
  refine ⟨fun hop i => ?_, fun hop i => ?_, fun hop i => ?_⟩
  · have hov : opcode.val = 0 := by
      rw [hop, show ((0 : ZMod p)) = ((0 : ℕ) : ZMod p) from by norm_cast]
      exact ZMod.val_natCast_of_lt (by omega)
    rw [h_byteOp i, hov, byteOp_zero]
  · have hov : opcode.val = 1 := by
      rw [hop, show ((1 : ZMod p)) = ((1 : ℕ) : ZMod p) from by norm_cast]
      exact ZMod.val_natCast_of_lt (by omega)
    rw [h_byteOp i, hov, byteOp_one]
  · have hov : opcode.val = 2 := by
      rw [hop, show ((2 : ZMod p)) = ((2 : ℕ) : ZMod p) from by norm_cast]
      exact ZMod.val_natCast_of_lt (by omega)
    rw [h_byteOp i, hov, byteOp_two]

end SP1Clean.BitwiseOperation
