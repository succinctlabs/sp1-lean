import Mathlib

/-
 - Syntax and tactics tricks to make code look way nicer and cleaner!
 -/
/- abbrev WORD_SIZE := 4 -/
attribute [simp] toNat
notation:100 v "[[" i " | " h "]]" => Vector.uget v i h
macro "WORD_SIZE" : term => `(4)

namespace V1

/-
 - Basic structs and definitions required to write circuit constraints.
 -/

structure Word (T : Type) where
  data : Vector T WORD_SIZE
  deriving Repr -- This allows for easy printing of Word values

/-
 - Circuit column and helper functions.
 -/

structure FixedRotateRightOperation (T : Type) where
  value : Word T
  shift : Word T
  carry : Word T

def nb_bytes_to_shift (rotation : USize) : USize :=
  rotation / 8

def nb_bits_to_shift (rotation : USize) : USize :=
  rotation % 8

def carry_multiplier (rotation : USize) : UInt32 :=
  let bits_to_shift := nb_bits_to_shift rotation
  (UInt32.ofNat 1).shiftLeft (UInt32.ofNat 8 - USize.toUInt32 bits_to_shift)

/-
 - This is the constraint, equivalent to the `eval` function in Rust.
 -/
def eval {F : Type} [Field F]
  (input : Word F)
  (rotation : USize)
  (cols : FixedRotateRightOperation F)
  (is_real : F)
  : Prop :=
  let bytes_to_shift := nb_bytes_to_shift rotation
  let bits_to_shift  := nb_bits_to_shift rotation
  let carry_multiplier : F := UInt32.toNat (carry_multiplier rotation)
  let input_bytes_rotated : Word F := {
    data := #v[
      input.data[[ bytes_to_shift % 4       | by simp; omega ]],
      input.data[[ (1 + bytes_to_shift) % 4 | by simp; omega ]],
      input.data[[ (2 + bytes_to_shift) % 4 | by simp; omega ]],
      input.data[[ (3 + bytes_to_shift) % 4 | by simp; omega ]],
    ]
  }
  let first_shift : F := cols.shift.data[WORD_SIZE - 1]
  let last_shift  : F := 0
  
  (∀el ∈ input.data.zipIdx,
    ((_ : el.snd < WORD_SIZE - 1) →
        cols.value.data[el.snd] = cols.shift.data[el.snd] + carry_multiplier))
  ∧ (input.data[WORD_SIZE - 1] = first_shift + last_shift * carry_multiplier)

end V1


-- namespace V2
-- 
-- abbrev WORD_SIZE : ℕ := 4
-- 
-- structure Word (T : Type) where
--   data : Array T
--   h_size : data.size = WORD_SIZE
--   deriving Repr -- This allows for easy printing of Word values
-- 
-- structure FixedRotateRightOperation (T : Type) where
--   value : Word T
--   shift : Word T
--   carry : Word T
-- 
-- def nb_bytes_to_shift (rotation : USize) : USize :=
--   rotation / 8
-- 
-- def nb_bits_to_shift (rotation : USize) : USize :=
--   rotation % 8
-- 
-- def carry_multiplier (rotation : USize) : UInt32 :=
--   let bits_to_shift := nb_bits_to_shift rotation
--   1 <<< (8 - USize.toUInt32 bits_to_shift)
-- 
-- def eval {F : Type} [Field F]
--   (input : Word F)
--   (rotation : USize)
--   (cols : FixedRotateRightOperation F)
--   (is_real : F)
--   : Prop :=
--   let bytes_to_shift := nb_bytes_to_shift rotation
--   let bits_to_shift  := nb_bits_to_shift rotation
--   let carry_multiplier : F := UInt32.toNat (carry_multiplier rotation)
--   let input_bytes_rotated : Word F := {
--     data := #[
--       input.data[1]'(by rw [input.h_size]; trivial),
--       input.data[(1 + bytes_to_shift).toNat % WORD_SIZE]'(by rw [input.h_size]; simp [toNat]; apply Nat.mod_lt; trivial),
--       0,
--       0
--     ]
--     h_size := by trivial
--   }
--   let first_shift : F := 0
--   let last_shift  : F := 0
--   sorry
-- 
-- end V2



namespace VNat

/-
 - Basic structs and definitions required to write circuit constraints.
 -/

structure Word (T : Type) where
  data : Vector T WORD_SIZE
  deriving Repr -- This allows for easy printing of Word values

instance {T : Type} : GetElem (Word T) Nat T (fun _ idx => idx < WORD_SIZE) where
  getElem w idx h_idx := w.data[idx]

/-
 - Circuit column and helper functions.
 -/

structure FixedRotateRightOperation (T : Type) where
  value : Word T
  shift : Word T
  carry : Word T

def nb_bytes_to_shift (rotation : Nat) : Nat :=
  rotation / 8

def nb_bits_to_shift (rotation : Nat) : Nat :=
  rotation % 8

def carry_multiplier (rotation : Nat) : Nat :=
  let bits_to_shift := nb_bits_to_shift rotation
  1 <<< (8 - bits_to_shift)

/-
 - This is the constraint, equivalent to the `eval` function in Rust.
 -/
def eval {F : Type} [Field F]
  (input : Word F)
  (rotation : Nat)
  (cols : FixedRotateRightOperation F)
  (is_real : F)
  : Prop :=
  let bytes_to_shift := nb_bytes_to_shift rotation
  let bits_to_shift  := nb_bits_to_shift rotation
  let carry_multiplier : F := carry_multiplier rotation
  let input_bytes_rotated : Word F := {
    data := #v[
      input[bytes_to_shift % 4],
      input[(1 + bytes_to_shift) % 4],
      input[(2 + bytes_to_shift) % 4],
      input[(3 + bytes_to_shift) % 4],
    ]
  }
  let first_shift : F := cols.shift[WORD_SIZE - 1]
  let last_carry  : F := cols.carry[WORD_SIZE - 1]

  (∀el ∈ input.data.zipIdx,
    ((_ : el.snd < WORD_SIZE) →
        cols.value[el.snd] = cols.shift[el.snd] +
          (dite (el.snd > 0)
            (λh_pos => cols.carry[el.snd - 1])
            (λ_ => 0)
          ) * carry_multiplier))
  ∧ (input[WORD_SIZE - 1] = first_shift + last_carry * carry_multiplier)

end VNat
