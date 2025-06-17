import SP1Foundations
import LeanRV32D.RiscvRegs

open LeanRV32D.Functions

structure BitwiseOperation where
  result : Vector BabyBear WORD_BYTE_SIZE

namespace BitwiseOperation

def constraints
  (a : Vector BabyBear WORD_BYTE_SIZE)
  (b : Vector BabyBear WORD_BYTE_SIZE)
  (cols : BitwiseOperation)
  (opcode : BabyBear)
  (is_real : BabyBear)
  : List SP1Constraint :=
  [
    .send (.byte (ByteOpcode.ofNat opcode) cols.result[0] a[0] b[0]) is_real,
    .send (.byte (ByteOpcode.ofNat opcode) cols.result[1] a[1] b[1]) is_real,
    .send (.byte (ByteOpcode.ofNat opcode) cols.result[2] a[2] b[2]) is_real,
    .send (.byte (ByteOpcode.ofNat opcode) cols.result[3] a[3] b[3]) is_real
  ]

def spec (a b : Vector BabyBear WORD_BYTE_SIZE)
    (cols : BitwiseOperation) (opcode : BabyBear) : Prop :=
  if ByteOpcode.ofNat opcode = .AND then (
    ((cols.result[0] < 256 ∧ a[0] < 256 ∧ b[0] < 256) → cols.result[0] = a[0] &&& b[0]) ∧
    ((cols.result[1] < 256 ∧ a[1] < 256 ∧ b[1] < 256) → cols.result[1] = a[1] &&& b[1]) ∧
    ((cols.result[2] < 256 ∧ a[2] < 256 ∧ b[2] < 256) → cols.result[2] = a[2] &&& b[2]) ∧
    ((cols.result[3] < 256 ∧ a[3] < 256 ∧ b[3] < 256) → cols.result[3] = a[3] &&& b[3])
  ) else if ByteOpcode.ofNat opcode = .OR then (
    ((cols.result[0] < 256 ∧ a[0] < 256 ∧ b[0] < 256) → cols.result[0] = a[0] ||| b[0]) ∧
    ((cols.result[1] < 256 ∧ a[1] < 256 ∧ b[1] < 256) → cols.result[1] = a[1] ||| b[1]) ∧
    ((cols.result[2] < 256 ∧ a[2] < 256 ∧ b[2] < 256) → cols.result[2] = a[2] ||| b[2]) ∧
    ((cols.result[3] < 256 ∧ a[3] < 256 ∧ b[3] < 256) → cols.result[3] = a[3] ||| b[3])
  ) else if ByteOpcode.ofNat opcode = .XOR then (
    ((cols.result[0] < 256 ∧ a[0] < 256 ∧ b[0] < 256) → cols.result[0] = a[0] ^^^ b[0]) ∧
    ((cols.result[1] < 256 ∧ a[1] < 256 ∧ b[1] < 256) → cols.result[1] = a[1] ^^^ b[1]) ∧
    ((cols.result[2] < 256 ∧ a[2] < 256 ∧ b[2] < 256) → cols.result[2] = a[2] ^^^ b[2]) ∧
    ((cols.result[3] < 256 ∧ a[3] < 256 ∧ b[3] < 256) → cols.result[3] = a[3] ^^^ b[3])
  ) else True

lemma constraints_imp_spec (a b : Vector BabyBear WORD_BYTE_SIZE)
    (cols : BitwiseOperation) (opcode is_real : BabyBear)
    (h0 : is_real ≠ 0)
    (h : List.Forall SP1Constraint.toProp (cols.constraints a b opcode is_real)) :
    cols.spec a b opcode := by
  simp only [spec, constraints] at ⊢ h
  by_cases h1 : ByteOpcode.ofNat opcode = .AND
  · simpa [h0, h1] using h
  by_cases h2 : ByteOpcode.ofNat opcode = .OR
  · simpa [h0, h2] using h
  by_cases h3 : ByteOpcode.ofNat opcode = .XOR
  · simpa [h0, h3] using h
  simp [h1, h2, h3]

lemma eq_and_of_constraints (a b : Vector BabyBear WORD_BYTE_SIZE) (cols : BitwiseOperation)
    (i : Fin WORD_BYTE_SIZE) (ha : a[i] < 256) (hb : b[i] < 256) (hc : cols.result[i] < 256)
    (h : List.Forall SP1Constraint.toProp (cols.constraints a b 0 1)) :
    cols.result[i] = a[i] &&& b[i] := by
  have := constraints_imp_spec a b cols _ _ one_ne_zero h
  simp [spec] at this
  match i with
  | 0 => exact this.1 hc ha hb
  | 1 => exact this.2.1 hc ha hb
  | 2 => exact this.2.2.1 hc ha hb
  | 3 => exact this.2.2.2 hc ha hb

lemma eq_or_of_constraints (a b : Vector BabyBear WORD_BYTE_SIZE) (cols : BitwiseOperation)
    (i : Fin WORD_BYTE_SIZE) (ha : a[i] < 256) (hb : b[i] < 256) (hc : cols.result[i] < 256)
    (h : List.Forall SP1Constraint.toProp (cols.constraints a b 1 1)) :
    cols.result[i] = a[i] ||| b[i] := by
  have := constraints_imp_spec a b cols _ _ one_ne_zero h
  simp [spec] at this
  match i with
  | 0 => exact this.1 hc ha hb
  | 1 => exact this.2.1 hc ha hb
  | 2 => exact this.2.2.1 hc ha hb
  | 3 => exact this.2.2.2 hc ha hb

lemma eq_xor_of_constraints (a b : Vector BabyBear WORD_BYTE_SIZE) (cols : BitwiseOperation)
    (i : Fin WORD_BYTE_SIZE) (ha : a[i] < 256) (hb : b[i] < 256) (hc : cols.result[i] < 256)
    (h : List.Forall SP1Constraint.toProp (cols.constraints a b 2 1)) :
    cols.result[i] = a[i] ^^^ b[i] := by
  have := constraints_imp_spec a b cols _ _ one_ne_zero h
  simp [spec] at this
  match i with
  | 0 => exact this.1 hc ha hb
  | 1 => exact this.2.1 hc ha hb
  | 2 => exact this.2.2.1 hc ha hb
  | 3 => exact this.2.2.2 hc ha hb

end BitwiseOperation
