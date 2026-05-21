import SP1Operations.Compare.U16CompareOperation.U16CompareOperation

structure LtOperationUnsigned (F : Type) where
  u16_compare_operation : U16CompareOperation F
  u16_flags : Word F
  not_eq_inv : F
  comparison_limbs : Vector F 2
