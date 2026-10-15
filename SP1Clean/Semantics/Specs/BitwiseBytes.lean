module

public import SP1Clean.Circuits.Types.Bitwise
public import SP1Clean.Math.Bitwise

/-! # Bytewise bitwise contract

Active rows have bounded operands and bytewise AND/OR/XOR results. Padding leaves all byte
columns free. The contract has no circuit, channel or witness-generation dependency.
-/

@[expose] public section

namespace SP1Clean.BitwiseOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Inputs for the native bytewise bitwise gadget. -/
structure Inputs (F : Type) where
  /-- First eight operand bytes. -/
  a : Vector F 8
  /-- Second eight operand bytes. -/
  b : Vector F 8
  /-- Committed result-byte columns. -/
  cols : Columns F
  /-- AND = 0, OR = 1, XOR = 2. -/
  opcode : F
  /-- One for an active row, zero for padding. -/
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Semantic, `is_real`- and opcode-gated contract: on a real row each result byte is the bitwise
AND/OR/XOR of the operand bytes (as 8-bit values), **and the operand bytes are genuine bytes** — the
byte table guarantees `a[i], b[i] < 256` for every fired send, so soundness exports those bounds and a
composing operation (e.g. `BitwiseU16Operation`) can consume them without having to range-check the
free byte columns itself. On padding (`is_real = 0`) it is vacuous — the gadget's gated byte-bus pulls
impose nothing there. The native input contains the result bytes as `input.cols.result`,
threaded in by the composing operation. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    (∀ i : Fin 8, input.a[i].val < 256 ∧ input.b[i].val < 256) ∧
    (input.opcode = 0 → ∀ i : Fin 8, input.cols.result[i].val = input.a[i].val &&& input.b[i].val) ∧
    (input.opcode = 1 → ∀ i : Fin 8, input.cols.result[i].val = input.a[i].val ||| input.b[i].val) ∧
    (input.opcode = 2 → ∀ i : Fin 8, input.cols.result[i].val = input.a[i].val ^^^ input.b[i].val)

/-- Opcode is one of AND/OR/XOR; `is_real` is binary (the latter discharged by the composing
operation's gate).
The operand byte bounds are **not** preconditions: the byte table guarantees them on every fired send,
so soundness exports them through `Spec` (and completeness reads them back from `Spec`), letting a
composing operation feed free byte columns without range-checking them itself. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  input.opcode.val < 3 ∧ (input.is_real = 0 ∨ input.is_real = 1)

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
      rw [hop, show ((0 : ZMod p)) = ((0 : ℕ) : ZMod p) by norm_cast]
      exact ZMod.val_natCast_of_lt (by omega)
    rw [h_byteOp i, hov, byteOp_zero]
  · have hov : opcode.val = 1 := by
      rw [hop, show ((1 : ZMod p)) = ((1 : ℕ) : ZMod p) by norm_cast]
      exact ZMod.val_natCast_of_lt (by omega)
    rw [h_byteOp i, hov, byteOp_one]
  · have hov : opcode.val = 2 := by
      rw [hop, show ((2 : ZMod p)) = ((2 : ℕ) : ZMod p) by norm_cast]
      exact ZMod.val_natCast_of_lt (by omega)
    rw [h_byteOp i, hov, byteOp_two]

end SP1Clean.BitwiseOperation
