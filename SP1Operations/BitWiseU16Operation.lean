import SP1Foundations
import SP1Operations.MemoryConsistency
import SP1Operations.U16toU8OperationUnsafe
import SP1Operations.BitwiseOperation
import LeanRV32D.RiscvRegs

open LeanRV32D.Functions

structure BitwiseU16Operation where
  a_low_bytes : U16toU8Operation
  b_low_bytes : U16toU8Operation
  bitwise_operation : BitwiseOperation

namespace BitwiseU16Operation

def constraintList
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

lemma constraintList_imp_spec
    (a : Word BabyBear)
    (b : Word BabyBear)
    (cols : BitwiseU16Operation)
    (opcode : BabyBear)
    (is_real : BabyBear) :
    (constraintList a b cols opcode is_real).2.allHold → (spec a b cols opcode is_real) := by
  rw [constraintList, spec]
  intro h h_is_real
  simp only [WORD_SIZE, BabyBearPrime, Fin.isValue]
  refine BitwiseOperation.constraints_imp_spec
    (#v[cols.a_low_bytes.low_bytes[0], (a[0] - cols.a_low_bytes.low_bytes[0]) * 2005401601,
        cols.a_low_bytes.low_bytes[1], (a[1] - cols.a_low_bytes.low_bytes[1]) * 2005401601])
    (#v[cols.b_low_bytes.low_bytes[0], (b[0] - cols.b_low_bytes.low_bytes[0]) * 2005401601,
        cols.b_low_bytes.low_bytes[1], (b[1] - cols.b_low_bytes.low_bytes[1]) * 2005401601])
    cols.bitwise_operation
    opcode is_real h_is_real ?_
  simp [] at h

  -- This is hacky, need some extensionality thing instead
  convert h.2 using 1

-- TODO: pull forward lemmas about `BitWiseOperation.spec` to this `spec`


end BitwiseU16Operation
