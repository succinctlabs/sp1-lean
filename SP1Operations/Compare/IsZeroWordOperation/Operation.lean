import SP1Operations.Compare.IsZeroOperation

structure IsZeroWordOperation where
  is_zero_limb : Vector IsZeroOperation 4
  is_zero_first_half : Fin BB
  is_zero_second_half : Fin BB
  result : Fin BB