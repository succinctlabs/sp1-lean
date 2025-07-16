import SP1Operations.Compare.U16CompareOperation

structure LtOperationUnsigned where
  u16_compare_operation : U16CompareOperation
  u16_flags : Word (Fin BB)
  not_eq_inv : Fin BB
  comparison_limbs : Vector (Fin BB) 2