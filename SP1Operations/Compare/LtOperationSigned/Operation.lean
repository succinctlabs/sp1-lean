import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Operations.Compare.LtOperationUnsigned.LtOperationUnsigned

structure LtOperationSigned (F : Type) where
  result : LtOperationUnsigned F
  b_msb : U16MSBOperation F
  c_msb : U16MSBOperation F
