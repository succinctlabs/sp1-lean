import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Compare.LtOperationUnsigned

structure LtOperationSigned (F : Type) where
  result : LtOperationUnsigned F
  b_msb : U16MSBOperation F
  c_msb : U16MSBOperation F
