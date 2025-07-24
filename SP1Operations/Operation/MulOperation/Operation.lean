import SP1Operations.Operation.U16toU8OperationSafe
import SP1Operations.Operation.U16MSBOperation

@[ext] structure MulOperation where
    carry : Vector (Fin BB) 16
    product : Vector (Fin BB) 16
    b_lower_byte: U16toU8Operation
    c_lower_byte: U16toU8Operation
    b_msb : Fin BB
    c_msb : Fin BB
    product_msb : U16MSBOperation
    b_sign_extend : Fin BB
    c_sign_extend : Fin BB
