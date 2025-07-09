-- import SP1Foundations

-- @[ext] structure U16toU8Operation where
--   low_bytes : Word (Fin BB)

-- namespace U16ToU8OperationUnsafe

-- def constraints
--     (u16_values : Word (Fin BB))
--     (cols : U16toU8Operation) :
--     ByteWord (Fin BB) × SP1ConstraintList :=
--   let E0 : Fin BB := u16_values[0] - cols.low_bytes[0]
--   let E2 : Fin BB := E0 * 2005401601
--   let E4 : Fin BB := u16_values[1] - cols.low_bytes[1]
--   let E6 : Fin BB := E4 * 2005401601
--   ⟨#v[cols.low_bytes[0], E2, cols.low_bytes[1], E6], []⟩

-- @[simp] lemma outputVector_eq
--     (u16_values : Word (Fin BB))
--     (cols : U16toU8Operation) :
--     (constraints u16_values cols).1 =
--       #v[cols.low_bytes[0], (u16_values[0] - cols.low_bytes[0]) * 2005401601,
--         cols.low_bytes[1], (u16_values[1] - cols.low_bytes[1]) * 2005401601] := rfl

-- @[simp] lemma low_bytes_add_high_bytes_eq_values₀
--     (u16_values : Word (Fin BB))
--     (cols : U16toU8Operation) :
--     (constraints u16_values cols).1[0] + (constraints u16_values cols).1[1] * 256 = u16_values[0] := by
--   simp [mul_assoc]

-- @[simp] lemma low_bytes_add_high_bytes_eq_values₁
--     (u16_values : Word (Fin BB))
--     (cols : U16toU8Operation) :
--     (constraints u16_values cols).1[2] + (constraints u16_values cols).1[3] * 256 = u16_values[1] := by
--   simp [mul_assoc]

-- @[simp] lemma constraintList_eq
--     (u16_values : Word (Fin BB))
--     (cols : U16toU8Operation) :
--     (constraints u16_values cols).2 = [] := rfl

-- @[simp] lemma allHold_constraintList
--     (u16_values : Word (Fin BB))
--     (cols : U16toU8Operation) :
--     (constraints u16_values cols).2.allHold := True.intro

-- end U16ToU8OperationUnsafe
