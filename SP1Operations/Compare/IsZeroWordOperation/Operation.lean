import SP1Operations.Compare.IsZeroOperation

structure IsZeroWordOperation where
  is_zero_limb : Vector IsZeroOperation 4
  is_zero_first_half : Fin KB
  is_zero_second_half : Fin KB
  result : Fin KB
