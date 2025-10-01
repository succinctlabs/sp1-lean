import SP1Operations.Compare.U16CompareOperation

structure LtOperationUnsigned where
  u16_compare_operation : U16CompareOperation
  u16_flags : Word (Fin KB)
  not_eq_inv : Fin KB
  comparison_limbs : Vector (Fin KB) 2
