import SP1Foundations

structure U16toU8Operation where
  low_bytes : Vector BabyBear WORD_SIZE

-- Probably good to still namespace things
namespace U16ToU8OperationUnsafe

def constraints
    (u16_values : Vector BabyBear WORD_SIZE)
    (cols : U16toU8Operation) :
    Vector BabyBear WORD_BYTE_SIZE × SP1ConstraintList :=
  let E0 : BabyBear := u16_values[0] - cols.low_bytes[0]
  let E2 : BabyBear := E0 * 2005401601
  let E4 : BabyBear := u16_values[1] - cols.low_bytes[1]
  let E6 : BabyBear := E4 * 2005401601
  ⟨#v[cols.low_bytes[0], E2, cols.low_bytes[1], E6], []⟩

@[simp] lemma outputVector_eq
    (u16_values : Vector BabyBear WORD_SIZE)
    (cols : U16toU8Operation) :
    (constraints u16_values cols).1 =
      #v[cols.low_bytes[0], (u16_values[0] - cols.low_bytes[0]) * 2005401601,
        cols.low_bytes[1], (u16_values[1] - cols.low_bytes[1]) * 2005401601] := rfl

@[simp] lemma constraintList_eq
    (u16_values : Vector BabyBear WORD_SIZE)
    (cols : U16toU8Operation) :
    (constraints u16_values cols).2 = [] := rfl

@[simp] lemma allHold_constraintList
    (u16_values : Vector BabyBear WORD_SIZE)
    (cols : U16toU8Operation) :
    (constraints u16_values cols).2.allHold := True.intro

end U16ToU8OperationUnsafe
