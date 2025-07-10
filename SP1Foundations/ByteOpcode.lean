import SP1Foundations.BitVec

/-- Operations that are handled axiomatically by byte tables.

dt: I think a lot would work better if and/or/xor had their own sub-inductive type -/
inductive ByteOpcode
  | AND
  | OR
  | XOR
  | U8Range
  | LTU
  | MSB
  | SR
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
@[simp] lemma ofNat_six : ByteOpcode.ofNat 6 = .SR := rfl
@[simp] lemma ofNat_seven : ByteOpcode.ofNat 7 = .Range := rfl

def toBB : ByteOpcode → Fin BB
  | AND => 0
  | OR => 1
  | XOR => 2
  | U8Range => 3
  | LTU => 4
  | MSB => 5
  | SR => 6
  | Range => 7

@[simp] lemma ofNat_toBB (op : ByteOpcode) : ByteOpcode.ofNat (op.toBB) = op := by
  induction op <;> rfl

end ofNat

section constrain

-- dt: it might make sense to add `Fin.val` calls in more places here.
def constrain (op : ByteOpcode) (a b c : Fin BB) : Prop :=
  match op with
  | AND => (a < 256 ∧ b < 256 ∧ c < 256) ∧ a = b &&& c
  | OR  => (a < 256 ∧ b < 256 ∧ c < 256) ∧ a = b ||| c
  | XOR => (a < 256 ∧ b < 256 ∧ c < 256) ∧ a = b ^^^ c
  | U8Range => a < 256 ∧ b < 256 ∧ c < 256
  | LTU => (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b < c)
  | SR => True
  | Range => a.val < 2 ^ b.val -- Is this right?
  | MSB => (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b >= 64)

@[simp] lemma constrain_AND (a b c : Fin BB) :
    ByteOpcode.AND.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ a = b &&& c := Iff.rfl

@[simp] lemma constrain_OR (a b c : Fin BB) :
    ByteOpcode.OR.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ a = b ||| c := Iff.rfl

@[simp] lemma constrain_XOR (a b c : Fin BB) :
    ByteOpcode.XOR.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ a = b ^^^ c := Iff.rfl

@[simp] lemma constrain_U8Range (a b c : Fin BB) :
    ByteOpcode.U8Range.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) := Iff.rfl

@[simp] lemma constrain_LTU (a b c : Fin BB) :
    ByteOpcode.LTU.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b < c) := Iff.rfl

@[simp] lemma constrain_MSB (a b c : Fin BB) :
    ByteOpcode.MSB.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b >= 64) := Iff.rfl

@[simp] lemma constrain_Range (a b c : Fin BB) :
    ByteOpcode.Range.constrain a b c ↔ (a.val < 2 ^ b.val) := Iff.rfl

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
  | .U8Range | .LTU | .MSB | .SR | .Range => other _ (by simp)

section toBitwise

def toBitwise' (op : ByteOpcode) : BitVec n → BitVec n → BitVec n :=
  by induction op using ByteOpcode.bitwise_induction with
  | and => exact (· &&& ·)
  | or => exact (· ||| ·)
  | xor => exact (· ^^^ ·)
  | other _ _ => exact 0

/-- Convert a `ByteOpcode` to a bitwise operation.
Gives dummy outputs outside `AND`, `OR`, and `XOR` operations. -/
def toBitwise (op : ByteOpcode) : Fin BB → Fin BB → Fin BB :=
  by induction op using ByteOpcode.bitwise_induction with
  | and => exact (· &&& ·)
  | or => exact (· ||| ·)
  | xor => exact (· ^^^ ·)
  | other _ _ => exact 0

@[simp] lemma toBitwise_and (x y : Fin BB) :
    toBitwise AND x y = x &&& y := rfl

@[simp] lemma toBitwise_or (x y : Fin BB) :
    toBitwise OR x y = x ||| y := rfl

@[simp] lemma toBitwise_xor (x y : Fin BB) :
    toBitwise XOR x y = x ^^^ y := rfl

lemma toBitwise_of_ne (x y : Fin BB) (op : ByteOpcode) (h : op ≠ AND ∧ op ≠ OR ∧ op ≠ XOR) :
    toBitwise op x y = 0 := by
  match op with
  | .AND | .OR | XOR => simp at h
  | U8Range | LTU | MSB | SR | Range => rfl

lemma toBitwise_add_toBitwise_mul_u8 (op : ByteOpcode) (x_low x_high y_low y_high : Fin BB)
    (hx : x_low < 256) (hy : y_low < 256)
    (hx' : x_high < 256) (hy' : y_high < 256) :
    (op.toBitwise x_low y_low) + (op.toBitwise x_high y_high) * 256 =
      op.toBitwise (x_low + x_high * 256) (y_low + y_high * 256) := by
  induction op using ByteOpcode.bitwise_induction with
  | and => exact BabyBear.and_add_and_mul256 hx hy hx' hy'
  | or => exact BabyBear.or_add_or_mul256 hx hy hx' hy'
  | xor => exact BabyBear.xor_add_xor_mul256 hx hy hx' hy'
  | other op hop => simp [toBitwise_of_ne _ _ op hop]

end toBitwise

end ByteOpcode
