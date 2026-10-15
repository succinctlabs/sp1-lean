module

public import SP1Clean.Circuits.Types.BitwiseChip
public import SP1Clean.Semantics.Specs.Bitwise
public import SP1Clean.Semantics.ISA.RV64

/-! # Bitwise instruction semantics

The contract states the selected RV64 AND, OR or XOR result and the selector obligations.
Byte witnesses and circuit implementation proofs remain outside this semantic boundary.
-/

@[expose] public section

namespace SP1Clean.BitwiseChip

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The reassembled bitwise result word the reader writes for `rd`: the eight result bytes packed into
four 16-bit limbs (`BitwiseU16Operation.resultWord`). -/
def resultWord (cols : Columns (ZMod p)) : Word (ZMod p) :=
  BitwiseU16Operation.resultWord cols.bitwise_operation.bitwise_operation.result

/-- Binary activity, the selected RV64 result and mutually exclusive boolean selectors.
Activity is the selector sum. Arithmetic is gated on active rows; the selector obligations
remain explicit on padding. Cross-row channel guarantees belong to the assembled trace. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    (cols.is_and = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.and (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_or = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.or (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_xor = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.xor (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))) ∧
  ((cols.is_and = 0 ∨ cols.is_and = 1) ∧ (cols.is_or = 0 ∨ cols.is_or = 1) ∧
    (cols.is_xor = 0 ∨ cols.is_xor = 1) ∧
    (cols.is_and = 1 → cols.is_xor = 0 ∧ cols.is_or = 0) ∧
    (cols.is_or = 1 → cols.is_xor = 0 ∧ cols.is_and = 0) ∧
    (cols.is_xor = 1 → cols.is_or = 0 ∧ cols.is_and = 0))

end SP1Clean.BitwiseChip
