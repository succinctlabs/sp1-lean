import SP1Operations.Operation.U16toU8OperationUnsafe
import SP1Operations.Operation.BitwiseOperation

@[ext] structure BitwiseU16Operation (F : Type) where
  b_low_bytes : U16toU8Operation F
  c_low_bytes : U16toU8Operation F
  bitwise_operation : BitwiseOperation F
