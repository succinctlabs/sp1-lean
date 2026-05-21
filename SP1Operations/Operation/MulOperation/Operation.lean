import SP1Operations.Operation.U16toU8OperationSafe.U16toU8OperationSafe
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation

@[ext] structure MulOperation (F : Type) where
    carry : Vector F 16
    product : Vector F 16
    b_lower_byte: U16toU8Operation F
    c_lower_byte: U16toU8Operation F
    b_msb : F
    c_msb : F
    product_msb : U16MSBOperation F
    b_sign_extend : F
    c_sign_extend : F
