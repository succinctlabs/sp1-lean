import SP1Operations.Operation.U16toU8OperationSafe
import SP1Operations.Operation.U16MSBOperation

@[ext] structure MulOperation where
    carry : Vector (Fin KB) 16
    product : Vector (Fin KB) 16
    b_lower_byte: U16toU8Operation
    c_lower_byte: U16toU8Operation
    b_msb : Fin KB
    c_msb : Fin KB
    product_msb : U16MSBOperation
    b_sign_extend : Fin KB
    c_sign_extend : Fin KB
