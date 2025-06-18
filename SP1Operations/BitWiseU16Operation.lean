import SP1Foundations
import SP1Operations.MemoryConsistency
import SP1Operations.U16toU8OperationUnsafe
import SP1Operations.BitwiseOperation
import LeanRV32D.RiscvRegs

open LeanRV32D.Functions

structure BitwiseU16Operation where
  b_low_bytes : U16toU8Operation
  c_low_bytes : U16toU8Operation
  bitwise_operation : BitwiseOperation

namespace BitwiseU16Operation

def constraint
  (b : Word BabyBear)
  (cc : Word BabyBear)
  (cols : BitwiseU16Operation)
  (opcode : BabyBear)
  (is_real : BabyBear)
  : Word BabyBear × List SP1Constraint :=
  let E0 : BabyBear := is_real - 1
  let E2 : BabyBear := is_real * E0

  let ⟨V0, CS0⟩ := U16ToU8OperationUnsafe.constraints
    #v[b[0], b[1]]
    { low_bytes :=
        #v[cols.b_low_bytes.low_bytes[0]
        , cols.b_low_bytes.low_bytes[1]
        ]
    }
  -- We will have our own syntax to pattern match
  -- Vector BabyBear WORD_BYTE_SIZE
  let E4 : BabyBear := V0[0]
  let E5 : BabyBear := V0[1]
  let E6 : BabyBear := V0[1]
  let E7 : BabyBear := V0[1]

  let ⟨V1, CS1⟩ := U16ToU8OperationUnsafe.constraints
    #v[cc[0], cc[1]]
    { low_bytes :=
        #v[cols.c_low_bytes.low_bytes[0]
        , cols.c_low_bytes.low_bytes[1]
        ]
    }
  -- We will have our own syntax to pattern match
  -- Vector BabyBear WORD_BYTE_SIZE
  let E8 : BabyBear := V0[0]
  let E9 : BabyBear := V0[1]
  let E10 : BabyBear := V0[1]
  let E11 : BabyBear := V0[1]

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

end BitwiseU16Operation
