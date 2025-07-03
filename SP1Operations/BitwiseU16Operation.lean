import SP1Foundations
import SP1Operations.MemoryConsistency
import SP1Operations.U16toU8OperationUnsafe
import SP1Operations.BitwiseOperation
import LeanRV32D.RiscvRegs

open LeanRV32D.Functions

@[ext] structure BitwiseU16Operation where
  b_low_bytes : U16toU8Operation
  c_low_bytes : U16toU8Operation
  bitwise_operation : BitwiseOperation

namespace BitwiseU16Operation

def constraints
  (a : Word (Fin BB))
  (b : Word (Fin BB))
  (cols : BitwiseU16Operation)
  (opcode : Fin BB)
  (is_real : Fin BB)
  : Word (Fin BB) × SP1ConstraintList :=
  let E0 : Fin BB := is_real - 1
  let E2 : Fin BB := is_real * E0

  let ⟨V0, CS0⟩ := U16ToU8OperationUnsafe.constraints
    #v[a[0], a[1]]
    { low_bytes :=
        #v[cols.b_low_bytes.low_bytes[0]
        , cols.b_low_bytes.low_bytes[1]
        ]
    }
  let E4 : Fin BB := V0[0]
  let E5 : Fin BB := V0[1]
  let E6 : Fin BB := V0[2]
  let E7 : Fin BB := V0[3]

  let ⟨V1, CS1⟩ := U16ToU8OperationUnsafe.constraints
    #v[b[0], b[1]]
    { low_bytes :=
        #v[cols.c_low_bytes.low_bytes[0]
        , cols.c_low_bytes.low_bytes[1]
        ]
    }
  let E8 : Fin BB := V1[0]
  let E9 : Fin BB := V1[1]
  let E10 : Fin BB := V1[2]
  let E11 : Fin BB := V1[3]

  let E12 : Fin BB := cols.bitwise_operation.result[1] * 256
  let E14 : Fin BB := cols.bitwise_operation.result[0] + E12
  let E16 : Fin BB := cols.bitwise_operation.result[3] * 256
  let E18 : Fin BB := cols.bitwise_operation.result[2] + E16

  ⟨#v[E14, E18],
  [ .assertZero E2
  ] ++ CS0 ++ CS1 ++ (BitwiseOperation.constraints
      #v[E4, E5, E6, E7]
      #v[E8, E9, E10, E11]
      { result :=
          #v[cols.bitwise_operation.result[0]
          ,  cols.bitwise_operation.result[1]
          ,  cols.bitwise_operation.result[2]
          ,  cols.bitwise_operation.result[3]
          ] }
      opcode
      is_real)⟩

def main_output (a : Word (Fin BB))
  (b : Word (Fin BB))
  (cols : BitwiseU16Operation)
  (opcode : Fin BB)
  (is_real : Fin BB) : Word (Fin BB) := (constraints a b cols opcode is_real).1

def spec
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (opcode : Fin BB)
    (is_real : Fin BB) : Prop :=
  -- let cr := cols.bitwise_operation.result
  is_real ≠ 0 →
    BitwiseOperation.spec
      (#v[cols.b_low_bytes.low_bytes[0], (a[0] - cols.b_low_bytes.low_bytes[0]) * 2005401601,
          cols.b_low_bytes.low_bytes[1], (a[1] - cols.b_low_bytes.low_bytes[1]) * 2005401601])
      (#v[cols.c_low_bytes.low_bytes[0], (b[0] - cols.c_low_bytes.low_bytes[0]) * 2005401601,
          cols.c_low_bytes.low_bytes[1], (b[1] - cols.c_low_bytes.low_bytes[1]) * 2005401601])
      cols.bitwise_operation
      opcode

lemma bitwiseOperation_constraints_of_constraints
    {a b : Word (Fin BB)}
    {cols : BitwiseU16Operation}
    {opcode is_real : Fin BB}
    (h : (constraints a b cols opcode is_real).2.allHold) :
    (BitwiseOperation.constraints
      (#v[cols.b_low_bytes.low_bytes[0], (a[0] - cols.b_low_bytes.low_bytes[0]) * 2005401601,
        cols.b_low_bytes.low_bytes[1], (a[1] - cols.b_low_bytes.low_bytes[1]) * 2005401601])
      (#v[cols.c_low_bytes.low_bytes[0], (b[0] - cols.c_low_bytes.low_bytes[0]) * 2005401601,
        cols.c_low_bytes.low_bytes[1], (b[1] - cols.c_low_bytes.low_bytes[1]) * 2005401601])
      cols.bitwise_operation
      opcode
      is_real).allHold := by
  rw [constraints] at h
  simp at h
  convert h.2
  rw [BitwiseOperation.ext_cases_iff]
  simp

lemma bitwiseOperation_spec_of_allHold_constraints
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (opcode : Fin BB)
    -- (is_real : Fin BB)
    (h : (constraints a b cols opcode 1).2.allHold) :
    BitwiseOperation.spec
      (#v[cols.b_low_bytes.low_bytes[0], (a[0] - cols.b_low_bytes.low_bytes[0]) * 2005401601,
        cols.b_low_bytes.low_bytes[1], (a[1] - cols.b_low_bytes.low_bytes[1]) * 2005401601])
      (#v[cols.c_low_bytes.low_bytes[0], (b[0] - cols.c_low_bytes.low_bytes[0]) * 2005401601,
        cols.c_low_bytes.low_bytes[1], (b[1] - cols.c_low_bytes.low_bytes[1]) * 2005401601])
      cols.bitwise_operation
      opcode := by
  apply BitwiseOperation.constraints_imp_spec _ _ _ _ 1 one_ne_zero
  apply bitwiseOperation_constraints_of_constraints
  assumption

lemma constraintList_imp_spec
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (opcode : Fin BB)
    (is_real : Fin BB) :
    (constraints a b cols opcode is_real).2.allHold → (spec a b cols opcode is_real) := by
  rw [constraints, spec]
  intro h h_is_real
  simp only [WORD_SIZE, BabyBearPrime, Fin.isValue]
  refine BitwiseOperation.constraints_imp_spec
    (#v[cols.b_low_bytes.low_bytes[0], (a[0] - cols.b_low_bytes.low_bytes[0]) * 2005401601,
        cols.b_low_bytes.low_bytes[1], (a[1] - cols.b_low_bytes.low_bytes[1]) * 2005401601])
    (#v[cols.c_low_bytes.low_bytes[0], (b[0] - cols.c_low_bytes.low_bytes[0]) * 2005401601,
        cols.c_low_bytes.low_bytes[1], (b[1] - cols.c_low_bytes.low_bytes[1]) * 2005401601])
    cols.bitwise_operation
    opcode is_real h_is_real ?_
  apply bitwiseOperation_constraints_of_constraints
  exact h

-- TODO: pull forward lemmas about `BitWiseOperation.spec` to this `spec`
lemma eq_and_of_constraints
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (h : (constraints a b cols 0 1).2.allHold) :
    cols.bitwise_operation.result[0] =
      cols.b_low_bytes.low_bytes[0] &&& cols.c_low_bytes.low_bytes[0] := by
  have := constraintList_imp_spec _ _ _ _ _ h one_ne_zero
  simp [BitwiseOperation.spec] at this
  aesop

lemma eq_toBitwise_of_constraints₀
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (opcode : ByteOpcode)
    (hop : opcode = .AND ∨ opcode = .OR ∨ opcode = .XOR)
    (h : (constraints a b cols opcode.toBB 1).2.allHold) :
    cols.bitwise_operation.result[0] =
      ByteOpcode.toBitwise opcode cols.b_low_bytes.low_bytes[0] cols.c_low_bytes.low_bytes[0] := by
  have := bitwiseOperation_constraints_of_constraints h
  exact BitwiseOperation.eq_toBitwise_of_constraints _ _ _ 0 _ hop this

-- NOTE: `ha` and `hb` would probably be better to move the inverse over, bit tedious to write the `Fin BB` proofs though
lemma eq_toBitwise_of_constraints₁
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (opcode : ByteOpcode)
    (hop : opcode = .AND ∨ opcode = .OR ∨ opcode = .XOR)
    (h : (constraints a b cols opcode.toBB 1).2.allHold) :
    cols.bitwise_operation.result[1] =
      ByteOpcode.toBitwise opcode
        ((a[0] - cols.b_low_bytes.low_bytes[0]) * 2005401601)
        ((b[0] - cols.c_low_bytes.low_bytes[0]) * 2005401601) := by
  have := bitwiseOperation_constraints_of_constraints h
  have := BitwiseOperation.eq_toBitwise_of_constraints _ _ _ 1 _ hop this
  exact this

lemma eq_toBitwise_of_constraints₂
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (opcode : ByteOpcode)
    (hop : opcode = .AND ∨ opcode = .OR ∨ opcode = .XOR)
    (h : (constraints a b cols opcode.toBB 1).2.allHold) :
    cols.bitwise_operation.result[2] =
      ByteOpcode.toBitwise opcode cols.b_low_bytes.low_bytes[1] cols.c_low_bytes.low_bytes[1] := by
  have := bitwiseOperation_constraints_of_constraints h
  have := BitwiseOperation.eq_toBitwise_of_constraints _ _ _ 2 _ hop this
  exact this

-- NOTE: `ha` and `hb` would probably be better to move the inverse over, bit tedious to write the `Fin BB` proofs though
lemma eq_toBitwise_of_constraints₃
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (opcode : ByteOpcode)
    (hop : opcode = .AND ∨ opcode = .OR ∨ opcode = .XOR)
    (h : (constraints a b cols opcode.toBB 1).2.allHold) :
    cols.bitwise_operation.result[3] =
      ByteOpcode.toBitwise opcode
        ((a[1] - cols.b_low_bytes.low_bytes[1]) * 2005401601)
        ((b[1] - cols.c_low_bytes.low_bytes[1]) * 2005401601) := by
  have := bitwiseOperation_constraints_of_constraints h
  have := BitwiseOperation.eq_toBitwise_of_constraints _ _ _ 3 _ hop this
  exact this

-- -- version for (almost) actual bitvecs to use w/ sail stuff
-- -- Not clear yet how bounds should work here, come back after chip
-- lemma eq_toBitwise_word_of_constraints
--     (a : Word (Fin BB))
--     (b : Word (Fin BB))
--     (cols : BitwiseU16Operation)
--     (opcode : ByteOpcode)
--     (hop : opcode = .AND ∨ opcode = .OR ∨ opcode = .XOR)
--     (ha : cols.b_low_bytes.low_bytes[0] < 256)
--     (hb : cols.c_low_bytes.low_bytes[0] < 256)
--     (h : (constraints a b cols opcode.toBB 1).2.allHold) :
--     (cols.bitwise_operation.result[0] + cols.bitwise_operation.result[1] * (256 : Fin BB)) =
--       (ByteOpcode.toBitwise opcode a[0] b[0]) := by
--   rw [eq_toBitwise_of_constraints₀ a b cols opcode hop h,
--     eq_toBitwise_of_constraints₁ a b cols opcode hop h]
--   rw [ByteOpcode.toBitwise_add_toBitwise_mul_u8 _ _ _ _ _ ha hb]
--   simp [mul_assoc]

-- lemma eq_toBitwise_word_of_constraints'
--     (a : Word (Fin BB))
--     (b : Word (Fin BB))
--     (cols : BitwiseU16Operation)
--     (opcode : ByteOpcode)
--     (hop : opcode = .AND ∨ opcode = .OR ∨ opcode = .XOR)
--     (ha : cols.b_low_bytes.low_bytes[1] < 256)
--     (hb : cols.c_low_bytes.low_bytes[1] < 256)
--     (h : (constraints a b cols opcode.toBB 1).2.allHold) :
--     (cols.bitwise_operation.result[2] + cols.bitwise_operation.result[3] * (256 : Fin BB)) =
--       (ByteOpcode.toBitwise opcode a[1] b[1]) := by
--   rw [eq_toBitwise_of_constraints₂ a b cols opcode hop h,
--     eq_toBitwise_of_constraints₃ a b cols opcode hop h]
--   rw [ByteOpcode.toBitwise_add_toBitwise_mul_u8 _ _ _ _ _ ha hb]
--   simp [mul_assoc]

section xor

lemma eq_xor_word_of_constraints
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (ha : cols.b_low_bytes.low_bytes[0] < 256)
    (hb : cols.c_low_bytes.low_bytes[0] < 256)
    (h : (constraints a b cols 2 1).2.allHold) :
    (cols.bitwise_operation.result[0] + cols.bitwise_operation.result[1] * (256 : Fin BB)) =
      (a[0] ^^^ b[0]) := by
  rw [eq_toBitwise_of_constraints₀ a b cols .XOR (Or.inr (Or.inr rfl)) h,
    eq_toBitwise_of_constraints₁ a b cols .XOR (Or.inr (Or.inr rfl)) h]
  rw [ByteOpcode.toBitwise_add_toBitwise_mul_u8 _ _ _ _ _ ha hb]
  simp [mul_assoc]
  · simp [constraints, BitwiseOperation.constraints] at h
    aesop
  · simp [constraints, BitwiseOperation.constraints] at h
    aesop


lemma eq_xor_word_of_constraints'
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (ha : cols.b_low_bytes.low_bytes[1] < 256)
    (hb : cols.c_low_bytes.low_bytes[1] < 256)
    (h : (constraints a b cols 2 1).2.allHold) :
    (cols.bitwise_operation.result[2] + cols.bitwise_operation.result[3] * (256 : Fin BB)) =
      (a[1] ^^^ b[1]) := by
  rw [eq_toBitwise_of_constraints₂ a b cols .XOR (Or.inr (Or.inr rfl)) h,
    eq_toBitwise_of_constraints₃ a b cols .XOR (Or.inr (Or.inr rfl)) h]
  rw [ByteOpcode.toBitwise_add_toBitwise_mul_u8 _ _ _ _ _ ha hb]
  simp [mul_assoc]
  · simp [constraints, BitwiseOperation.constraints] at h
    aesop
  · simp [constraints, BitwiseOperation.constraints] at h
    aesop

lemma eq_xor_word_sub_of_constraints
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (ha : cols.b_low_bytes.low_bytes[0] < 256)
    (hb : cols.c_low_bytes.low_bytes[0] < 256)
    (h : (constraints a b cols 2 1).2.allHold) :
    cols.bitwise_operation.result[1] * (256 : Fin BB) =
      (a[0] ^^^ b[0]) - cols.bitwise_operation.result[0] := by
  rw [← eq_xor_word_of_constraints a b cols ha hb h]
  rw [add_sub_cancel_left]

lemma eq_xor_word_sub_of_constraints'
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (ha : cols.b_low_bytes.low_bytes[1] < 256)
    (hb : cols.c_low_bytes.low_bytes[1] < 256)
    (h : (constraints a b cols 2 1).2.allHold) :
    cols.bitwise_operation.result[3] * (256 : Fin BB) =
      (a[1] ^^^ b[1]) - cols.bitwise_operation.result[2] := by
  rw [← eq_xor_word_of_constraints' a b cols ha hb h]
  rw [add_sub_cancel_left]

end xor

section or

lemma eq_or_word_of_constraints
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (ha : cols.b_low_bytes.low_bytes[0] < 256)
    (hb : cols.c_low_bytes.low_bytes[0] < 256)
    (h : (constraints a b cols 1 1).2.allHold) :
    (cols.bitwise_operation.result[0] + cols.bitwise_operation.result[1] * (256 : Fin BB)) =
      (a[0] ||| b[0]) := by
  rw [eq_toBitwise_of_constraints₀ a b cols .OR (Or.inr (Or.inl rfl)) h,
    eq_toBitwise_of_constraints₁ a b cols .OR (Or.inr (Or.inl rfl)) h]
  rw [ByteOpcode.toBitwise_add_toBitwise_mul_u8 _ _ _ _ _ ha hb]
  simp [mul_assoc]
  · simp [constraints, BitwiseOperation.constraints] at h
    aesop
  · simp [constraints, BitwiseOperation.constraints] at h
    aesop

lemma eq_or_word_of_constraints'
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (ha : cols.b_low_bytes.low_bytes[1] < 256)
    (hb : cols.c_low_bytes.low_bytes[1] < 256)
    (h : (constraints a b cols 1 1).2.allHold) :
    (cols.bitwise_operation.result[2] + cols.bitwise_operation.result[3] * (256 : Fin BB)) =
      (a[1] ||| b[1]) := by
  rw [eq_toBitwise_of_constraints₂ a b cols .OR (Or.inr (Or.inl rfl)) h,
    eq_toBitwise_of_constraints₃ a b cols .OR (Or.inr (Or.inl rfl)) h]
  rw [ByteOpcode.toBitwise_add_toBitwise_mul_u8 _ _ _ _ _ ha hb]
  simp [mul_assoc]
  · simp [constraints, BitwiseOperation.constraints] at h
    aesop
  · simp [constraints, BitwiseOperation.constraints] at h
    aesop

lemma eq_or_word_sub_of_constraints
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (ha : cols.b_low_bytes.low_bytes[0] < 256)
    (hb : cols.c_low_bytes.low_bytes[0] < 256)
    (h : (constraints a b cols 1 1).2.allHold) :
    cols.bitwise_operation.result[1] * (256 : Fin BB) =
      (a[0] ||| b[0]) - cols.bitwise_operation.result[0] := by
  rw [← eq_or_word_of_constraints a b cols ha hb h]
  rw [add_sub_cancel_left]

lemma eq_or_word_sub_of_constraints'
    (a : Word (Fin BB))
    (b : Word (Fin BB))
    (cols : BitwiseU16Operation)
    (ha : cols.b_low_bytes.low_bytes[1] < 256)
    (hb : cols.c_low_bytes.low_bytes[1] < 256)
    (h : (constraints a b cols 1 1).2.allHold) :
    cols.bitwise_operation.result[3] * (256 : Fin BB) =
      (a[1] ||| b[1]) - cols.bitwise_operation.result[2] := by
  rw [← eq_or_word_of_constraints' a b cols ha hb h]
  rw [add_sub_cancel_left]

end or

end BitwiseU16Operation
