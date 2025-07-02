import SP1Foundations.Field

/-- Operations that are handled axiomatically by byte tables. -/
inductive ByteOpcode
  | AND
  | OR
  | XOR
  | U8Range
  | LTU
  | MSB
  | Range
  deriving DecidableEq

namespace ByteOpcode

section ofNat

-- Deriving decidable equality also derives an `OfNat` instance
@[simp] lemma ofNat_zero : ByteOpcode.ofNat 0 = .AND := rfl
@[simp] lemma ofNat_one : ByteOpcode.ofNat 1 = .OR := rfl
@[simp] lemma ofNat_two : ByteOpcode.ofNat 2 = .XOR := rfl
@[simp] lemma ofNat_three : ByteOpcode.ofNat 3 = .U8Range := rfl
@[simp] lemma ofNat_four : ByteOpcode.ofNat 4 = .LTU := rfl
@[simp] lemma ofNat_five : ByteOpcode.ofNat 5 = .MSB := rfl
@[simp] lemma ofNat_six : ByteOpcode.ofNat 6 = .Range := rfl

def toBB : ByteOpcode → BabyBear
  | AND => 0
  | OR => 1
  | XOR => 2
  | U8Range => 3
  | LTU => 4
  | MSB => 5
  | Range => 6

@[simp] lemma ofNat_toBB (op : ByteOpcode) : ByteOpcode.ofNat (op.toBB) = op := by
  induction op <;> rfl

end ofNat

section constrain

def constrain (op : ByteOpcode) (a b c : BabyBear) : Prop :=
  match op with
  | AND => (a < 256 ∧ b < 256 ∧ c < 256) ∧ a = b &&& c
  | OR  => (a < 256 ∧ b < 256 ∧ c < 256) ∧ a = b ||| c
  | XOR => (a < 256 ∧ b < 256 ∧ c < 256) ∧ a = b ^^^ c
  | U8Range => a < 256 ∧ b < 256 ∧ c < 256
  | LTU => (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b < c)
  | Range => a < 2 ^ b.val -- Is this right?
  | MSB => (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b >= 64)

@[simp] lemma constrain_AND (a b c : BabyBear) :
    ByteOpcode.AND.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ a = b &&& c := Iff.rfl

@[simp] lemma constrain_OR (a b c : BabyBear) :
    ByteOpcode.OR.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ a = b ||| c := Iff.rfl

@[simp] lemma constrain_XOR (a b c : BabyBear) :
    ByteOpcode.XOR.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ a = b ^^^ c := Iff.rfl

@[simp] lemma constrain_U8Range (a b c : BabyBear) :
    ByteOpcode.U8Range.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) := Iff.rfl

@[simp] lemma constrain_LTU (a b c : BabyBear) :
    ByteOpcode.LTU.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b < c) := Iff.rfl

@[simp] lemma constrain_MSB (a b c : BabyBear) :
    ByteOpcode.MSB.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b >= 64) := Iff.rfl

@[simp] lemma constrain_Range (a b c : BabyBear) :
    ByteOpcode.Range.constrain a b c ↔ (a < 2 ^ b.val) := Iff.rfl

end constrain

/-- Perform induction on `ByteOpcode` with all the non-bitwise operations consolidated.
Useful when you want to ignore non-bitwise operations (or treat them as some defualt). -/
@[elab_as_elim]
protected def bitwise_induction (C : ByteOpcode → Sort*)
    (and : C .AND) (or : C .OR) (xor : C .XOR)
    (other : (op : ByteOpcode) →
      (op ≠ .AND ∧ op ≠ .OR ∧ op ≠ .XOR) → C op)
    (op : ByteOpcode) : C op := by
  refine match op with
  | .AND => and
  | .OR => or
  | .XOR => xor
  | .U8Range | .LTU | .MSB | .Range => other _ (by simp)

section toBitwise

def toBitwise' (op : ByteOpcode) : BitVec n → BitVec n → BitVec n :=
  by induction op using ByteOpcode.bitwise_induction with
  | and => exact (· &&& ·)
  | or => exact (· ||| ·)
  | xor => exact (· ^^^ ·)
  | other _ _ => exact 0

/-- Convert a `ByteOpcode` to a bitwise operation.
Gives dummy outputs outside `AND`, `OR`, and `XOR` operations. -/
def toBitwise (op : ByteOpcode) : BabyBear → BabyBear → BabyBear :=
  by induction op using ByteOpcode.bitwise_induction with
  | and => exact (· &&& ·)
  | or => exact (· ||| ·)
  | xor => exact (· ^^^ ·)
  | other _ _ => exact 0

@[simp] lemma toBitwise_and (x y : BabyBear) :
    toBitwise AND x y = x &&& y := rfl

@[simp] lemma toBitwise_or (x y : BabyBear) :
    toBitwise OR x y = x ||| y := rfl

@[simp] lemma toBitwise_xor (x y : BabyBear) :
    toBitwise XOR x y = x ^^^ y := rfl

lemma and_add_and_mul (x_low x_high y_low y_high : BabyBear)
    (hx : x_low < 256) (hy : y_low < 256) :
    (x_low &&& y_low) + (x_high &&& y_high) * 256 =
      (x_low + x_high * 256) &&& (y_low + y_high * 256) := by
  sorry
  -- simp

lemma toBitwise_add_toBitwise_mul_u8 (op : ByteOpcode) (x_low x_high y_low y_high : BabyBear)
    (hx : x_low < 256) (hy : y_low < 256) :
    (op.toBitwise x_low y_low) + (op.toBitwise x_high y_high) * 256 =
      op.toBitwise (x_low + x_high * 256) (y_low + y_high * 256) := by

  sorry

end toBitwise

end ByteOpcode
