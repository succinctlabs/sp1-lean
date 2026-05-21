import SP1Operations.Compare.IsZeroOperation.IsZeroOperation

structure IsZeroWordOperation (F : Type) where
  is_zero_limb : Vector (IsZeroOperation F) 4
  is_zero_first_half : F
  is_zero_second_half : F
  result : F
