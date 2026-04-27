import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Compare.LtOperationUnsigned

structure LtOperationSigned where
  result : LtOperationUnsigned
  b_msb : U16MSBOperation (Fin KB)
  c_msb : U16MSBOperation (Fin KB)
