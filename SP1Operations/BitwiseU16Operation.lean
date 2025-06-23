import SP1Foundations
import SP1Operations.MemoryConsistency
import SP1Operations.U16toU8OperationUnsafe
import SP1Operations.BitwiseOperation
import LeanRV32D.RiscvRegs

open LeanRV32D.Functions

@[ext] structure BitwiseU16Operation where
  a_low_bytes : U16toU8Operation
  b_low_bytes : U16toU8Operation
  bitwise_operation : BitwiseOperation

namespace BitwiseU16Operation

def constraints
  (a : Word BabyBear)
  (b : Word BabyBear)
  (cols : BitwiseU16Operation)
  (opcode : BabyBear)
  (is_real : BabyBear)
  : Word BabyBear × SP1ConstraintList :=
  let E0 : BabyBear := is_real - 1
  let E2 : BabyBear := is_real * E0

  let ⟨V0, CS0⟩ := U16ToU8OperationUnsafe.constraints
    #v[a[0], a[1]]
    { low_bytes :=
        #v[cols.a_low_bytes.low_bytes[0]
        , cols.a_low_bytes.low_bytes[1]
        ]
    }
  let E4 : BabyBear := V0[0]
  let E5 : BabyBear := V0[1]
  let E6 : BabyBear := V0[2]
  let E7 : BabyBear := V0[3]

  let ⟨V1, CS1⟩ := U16ToU8OperationUnsafe.constraints
    #v[b[0], b[1]]
    { low_bytes :=
        #v[cols.b_low_bytes.low_bytes[0]
        , cols.b_low_bytes.low_bytes[1]
        ]
    }
  let E8 : BabyBear := V1[0]
  let E9 : BabyBear := V1[1]
  let E10 : BabyBear := V1[2]
  let E11 : BabyBear := V1[3]

  let E12 : BabyBear := cols.bitwise_operation.result[1] * 256
  let E14 : BabyBear := E8 + E12
  let E16 : BabyBear := cols.bitwise_operation.result[3] * 256
  let E18 : BabyBear := E10 + E16

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

def spec
    (a : Word BabyBear)
    (b : Word BabyBear)
    (cols : BitwiseU16Operation)
    (opcode : BabyBear)
    (is_real : BabyBear) : Prop :=
  -- let cr := cols.bitwise_operation.result
  is_real ≠ 0 →
    BitwiseOperation.spec
      (#v[cols.a_low_bytes.low_bytes[0], (a[0] - cols.a_low_bytes.low_bytes[0]) * 2005401601,
          cols.a_low_bytes.low_bytes[1], (a[1] - cols.a_low_bytes.low_bytes[1]) * 2005401601])
      (#v[cols.b_low_bytes.low_bytes[0], (b[0] - cols.b_low_bytes.low_bytes[0]) * 2005401601,
          cols.b_low_bytes.low_bytes[1], (b[1] - cols.b_low_bytes.low_bytes[1]) * 2005401601])
      cols.bitwise_operation
      opcode

lemma bitwiseOperation_constraints_of_constraints
    {a b : Word BabyBear}
    {cols : BitwiseU16Operation}
    {opcode is_real : BabyBear}
    (h : (constraints a b cols opcode is_real).2.allHold) :
    (BitwiseOperation.constraints
      (#v[cols.a_low_bytes.low_bytes[0], (a[0] - cols.a_low_bytes.low_bytes[0]) * 2005401601,
        cols.a_low_bytes.low_bytes[1], (a[1] - cols.a_low_bytes.low_bytes[1]) * 2005401601])
      (#v[cols.b_low_bytes.low_bytes[0], (b[0] - cols.b_low_bytes.low_bytes[0]) * 2005401601,
        cols.b_low_bytes.low_bytes[1], (b[1] - cols.b_low_bytes.low_bytes[1]) * 2005401601])
      cols.bitwise_operation
      opcode
      is_real).allHold := by
  rw [constraints] at h
  simp at h
  convert h.2
  rw [BitwiseOperation.ext_cases_iff]
  simp

lemma bitwiseOperation_spec_of_allHold_constraints
    (a : Word BabyBear)
    (b : Word BabyBear)
    (cols : BitwiseU16Operation)
    (opcode : BabyBear)
    -- (is_real : BabyBear)
    (h : (constraints a b cols opcode 1).2.allHold) :
    BitwiseOperation.spec
      (#v[cols.a_low_bytes.low_bytes[0], (a[0] - cols.a_low_bytes.low_bytes[0]) * 2005401601,
        cols.a_low_bytes.low_bytes[1], (a[1] - cols.a_low_bytes.low_bytes[1]) * 2005401601])
      (#v[cols.b_low_bytes.low_bytes[0], (b[0] - cols.b_low_bytes.low_bytes[0]) * 2005401601,
        cols.b_low_bytes.low_bytes[1], (b[1] - cols.b_low_bytes.low_bytes[1]) * 2005401601])
      cols.bitwise_operation
      opcode := by
  apply BitwiseOperation.constraints_imp_spec _ _ _ _ 1 one_ne_zero
  apply bitwiseOperation_constraints_of_constraints
  assumption

lemma constraintList_imp_spec
    (a : Word BabyBear)
    (b : Word BabyBear)
    (cols : BitwiseU16Operation)
    (opcode : BabyBear)
    (is_real : BabyBear) :
    (constraints a b cols opcode is_real).2.allHold → (spec a b cols opcode is_real) := by
  rw [constraints, spec]
  intro h h_is_real
  simp only [WORD_SIZE, BabyBearPrime, Fin.isValue]
  refine BitwiseOperation.constraints_imp_spec
    (#v[cols.a_low_bytes.low_bytes[0], (a[0] - cols.a_low_bytes.low_bytes[0]) * 2005401601,
        cols.a_low_bytes.low_bytes[1], (a[1] - cols.a_low_bytes.low_bytes[1]) * 2005401601])
    (#v[cols.b_low_bytes.low_bytes[0], (b[0] - cols.b_low_bytes.low_bytes[0]) * 2005401601,
        cols.b_low_bytes.low_bytes[1], (b[1] - cols.b_low_bytes.low_bytes[1]) * 2005401601])
    cols.bitwise_operation
    opcode is_real h_is_real ?_
  apply bitwiseOperation_constraints_of_constraints
  exact h

-- TODO: pull forward lemmas about `BitWiseOperation.spec` to this `spec`
lemma eq_and_of_constraints
    (a : Word BabyBear)
    (b : Word BabyBear)
    (cols : BitwiseU16Operation)
    (h : (constraints a b cols 0 1).2.allHold) :
    cols.bitwise_operation.result[0] =
      cols.a_low_bytes.low_bytes[0] &&& cols.b_low_bytes.low_bytes[0] := by
  have := constraintList_imp_spec _ _ _ _ _ h one_ne_zero
  simp [BitwiseOperation.spec] at this
  aesop

lemma eq_toBitwise_of_constraints₀
    (a : Word BabyBear)
    (b : Word BabyBear)
    (cols : BitwiseU16Operation)
    (opcode : ByteOpcode)
    (hop : opcode = .AND ∨ opcode = .OR ∨ opcode = .XOR)
    (h : (constraints a b cols opcode.toBB 1).2.allHold) :
    cols.bitwise_operation.result[0] =
      ByteOpcode.toBitwise opcode cols.a_low_bytes.low_bytes[0] cols.b_low_bytes.low_bytes[0] := by
  have := bitwiseOperation_constraints_of_constraints h
  exact BitwiseOperation.eq_toBitwise_of_constraints _ _ _ 0 _ hop this

-- NOTE: `ha` and `hb` would probably be better to move the inverse over, bit tedious to write the `BabyBear` proofs though
lemma eq_toBitwise_of_constraints₁
    (a : Word BabyBear)
    (b : Word BabyBear)
    (cols : BitwiseU16Operation)
    (opcode : ByteOpcode)
    (hop : opcode = .AND ∨ opcode = .OR ∨ opcode = .XOR)
    (h : (constraints a b cols opcode.toBB 1).2.allHold) :
    cols.bitwise_operation.result[1] =
      ByteOpcode.toBitwise opcode
        ((a[0] - cols.a_low_bytes.low_bytes[0]) * 2005401601)
        ((b[0] - cols.b_low_bytes.low_bytes[0]) * 2005401601) := by
  have := bitwiseOperation_constraints_of_constraints h
  have := BitwiseOperation.eq_toBitwise_of_constraints _ _ _ 1 _ hop this
  exact this

lemma eq_toBitwise_of_constraints₂
    (a : Word BabyBear)
    (b : Word BabyBear)
    (cols : BitwiseU16Operation)
    (opcode : ByteOpcode)
    (hop : opcode = .AND ∨ opcode = .OR ∨ opcode = .XOR)
    (h : (constraints a b cols opcode.toBB 1).2.allHold) :
    cols.bitwise_operation.result[2] =
      ByteOpcode.toBitwise opcode cols.a_low_bytes.low_bytes[1] cols.b_low_bytes.low_bytes[1] := by
  have := bitwiseOperation_constraints_of_constraints h
  have := BitwiseOperation.eq_toBitwise_of_constraints _ _ _ 2 _ hop this
  exact this

-- NOTE: `ha` and `hb` would probably be better to move the inverse over, bit tedious to write the `BabyBear` proofs though
lemma eq_toBitwise_of_constraints₃
    (a : Word BabyBear)
    (b : Word BabyBear)
    (cols : BitwiseU16Operation)
    (opcode : ByteOpcode)
    (hop : opcode = .AND ∨ opcode = .OR ∨ opcode = .XOR)
    (h : (constraints a b cols opcode.toBB 1).2.allHold) :
    cols.bitwise_operation.result[3] =
      ByteOpcode.toBitwise opcode
        ((a[1] - cols.a_low_bytes.low_bytes[1]) * 2005401601)
        ((b[1] - cols.b_low_bytes.low_bytes[1]) * 2005401601) := by
  have := bitwiseOperation_constraints_of_constraints h
  have := BitwiseOperation.eq_toBitwise_of_constraints _ _ _ 3 _ hop this
  exact this

-- version for (almost) actual bitvecs to use w/ sail stuff
-- Not clear yet how bounds should work here, come back after chip
lemma eq_toBitwise_word_of_constraints
    (a : Word BabyBear)
    (b : Word BabyBear)
    (cols : BitwiseU16Operation)
    (opcode : ByteOpcode)
    (hop : opcode = .AND ∨ opcode = .OR ∨ opcode = .XOR)
    (ha : cols.a_low_bytes.low_bytes[0] < 256)
    (hb : cols.b_low_bytes.low_bytes[0] < 256)
    (h : (constraints a b cols opcode.toBB 1).2.allHold) :
    (cols.bitwise_operation.result[0] + cols.bitwise_operation.result[1] * (256 : BabyBear)) =
      (ByteOpcode.toBitwise opcode a[0] b[0]) := by
  rw [eq_toBitwise_of_constraints₀ a b cols opcode hop h,
    eq_toBitwise_of_constraints₁ a b cols opcode hop h]
  rw [ByteOpcode.toBitwise_add_toBitwise_mul_u8 _ _ _ _ _ ha hb]
  simp [mul_assoc]


end BitwiseU16Operation
