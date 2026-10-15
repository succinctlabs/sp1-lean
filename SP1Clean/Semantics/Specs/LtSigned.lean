module

public import SP1Clean.Semantics.Specs.LtUnsigned
public import SP1Clean.Circuits.Types.LtOperationSigned

/-! # Signed and unsigned word comparison contract

Unsigned mode compares the original words and leaves both sign columns zero. Signed mode
is active, records the operands' high bits, and compares words whose sign bits are flipped.
The result states the selected whole-word ordering directly. The unsigned certificate also
describes every accepted padding row; it is not restricted to the canonical zero witness.
-/

@[expose] public section

namespace SP1Clean.LtOperationSigned

/-- Inputs for signed or unsigned comparison of two 64-bit words. -/
structure Inputs (F : Type) where
  /-- Left operand, in little-endian 16-bit limbs. -/
  b : Word F
  /-- Right operand. -/
  cc : Word F
  /-- Sign bits and the comparison certificate. -/
  cols : Circuits.Types.LtOperationSigned F
  /-- One selects signed order; zero selects unsigned order. -/
  is_signed : F
  /-- One for an active row, zero for padding. -/
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

variable {p : ℕ} [Fact p.Prime]

/-- Both operands are 64-bit words, and the activity and mode selectors are binary. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.b ∧ Word.isU64 input.cc ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_signed = 0 ∨ input.is_signed = 1)

/-- Unsigned mode has no sign bits. Signed mode is active and records each operand's high bit. -/
def Mode (input : Inputs (ZMod p)) : Prop :=
  (input.is_signed = 0 ∧ input.cols.b_msb.msb = 0 ∧ input.cols.c_msb.msb = 0) ∨
  (input.is_signed = 1 ∧ input.is_real = 1 ∧
    input.cols.b_msb.msb = (if input.b[3].val ≥ 32768 then 1 else 0) ∧
    input.cols.c_msb.msb = (if input.cc[3].val ≥ 32768 then 1 else 0))

/-- Unsigned comparison of the sign-biased words. In unsigned mode the bias is zero. -/
def unsignedInput (input : Inputs (ZMod p)) : LtOperationUnsigned.Inputs (ZMod p) :=
  ⟨#v[input.b[0], input.b[1], input.b[2],
      input.b[3] + input.is_signed * 32768 - 65536 * input.cols.b_msb.msb],
   #v[input.cc[0], input.cc[1], input.cc[2],
      input.cc[3] + input.is_signed * 32768 - 65536 * input.cols.c_msb.msb],
   input.cols.result, input.is_real⟩

/-- Whole-word ordering and equality, detected by a zero selector sum in either mode. -/
def Result (input : Inputs (ZMod p)) : Prop :=
  (input.cols.result.u16_compare_operation.bit =
    if (if input.is_signed = 1
        then (Word.toBitVec64 input.b).toInt < (Word.toBitVec64 input.cc).toInt
        else Word.toNat input.b < Word.toNat input.cc)
      then 1 else 0) ∧
  ((input.cols.result.u16_flags[0] + input.cols.result.u16_flags[1]
      + input.cols.result.u16_flags[2] + input.cols.result.u16_flags[3] = 0)
    ↔ Word.toBitVec64 input.b = Word.toBitVec64 input.cc)

/-- A comparison certificate for the chosen mode, agreeing with whole-word order on active rows.
Padding uses unsigned mode but retains every certificate accepted by the unsigned assertion. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧ Mode input ∧
  LtOperationUnsigned.Spec (unsignedInput input) ∧ (input.is_real = 1 → Result input)

/-- The comparison result is available directly from the semantic contract. -/
theorem result_semantic {input : Inputs (ZMod p)} (hs : Spec input)
    (hir : input.is_real = 1) : Result input := hs.2.2.2 hir

/-- A valid certificate selects zero or one limb, in either mode and on padding. -/
theorem flags_sum_binary {input : Inputs (ZMod p)} (hs : Spec input) :
    input.cols.result.u16_flags[0] + input.cols.result.u16_flags[1]
      + input.cols.result.u16_flags[2] + input.cols.result.u16_flags[3] = 0 ∨
    input.cols.result.u16_flags[0] + input.cols.result.u16_flags[1]
      + input.cols.result.u16_flags[2] + input.cols.result.u16_flags[3] = 1 :=
  LtOperationUnsigned.flags_sum_binary hs.2.2.1

end SP1Clean.LtOperationSigned
