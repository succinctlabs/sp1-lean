import SP1Operations.Operation.U16toU8OperationUnsafe
import SP1Operations.Operation.BitwiseOperation

@[ext] structure BitwiseU16Operation where
  b_low_bytes : U16toU8Operation
  c_low_bytes : U16toU8Operation
  bitwise_operation : BitwiseOperation
