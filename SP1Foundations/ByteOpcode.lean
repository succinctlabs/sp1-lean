import SP1Foundations.BitVec

/-- Operations that are handled manually by byte tables.

dt: I think a lot would work better if and/or/xor had their own sub-inductive type -/
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
@[simp] lemma ofNat_seven : ByteOpcode.ofNat 6 = .Range := rfl

/-- Inverse of `ofNat`: emit the natural-number tag the auto-generated
constraint compiler uses when it lowers `ByteOpcode` to a field literal. -/
def toNat : ByteOpcode → ℕ
  | AND => 0
  | OR => 1
  | XOR => 2
  | U8Range => 3
  | LTU => 4
  | MSB => 5
  | Range => 6

@[simp] lemma toNat_AND : ByteOpcode.AND.toNat = 0 := rfl
@[simp] lemma toNat_OR : ByteOpcode.OR.toNat = 1 := rfl
@[simp] lemma toNat_XOR : ByteOpcode.XOR.toNat = 2 := rfl
@[simp] lemma toNat_U8Range : ByteOpcode.U8Range.toNat = 3 := rfl
@[simp] lemma toNat_LTU : ByteOpcode.LTU.toNat = 4 := rfl
@[simp] lemma toNat_MSB : ByteOpcode.MSB.toNat = 5 := rfl
@[simp] lemma toNat_Range : ByteOpcode.Range.toNat = 6 := rfl

end ofNat

/-! ### Polymorphic `constrain_poly` over `ZMod p` -/
section constrain_poly

variable {p : ℕ} [NeZero p]

def constrain_poly (op : ByteOpcode) (a b c : ZMod p) : Prop :=
  match op with
  | AND => (a < 256 ∧ b < 256 ∧ c < 256) ∧ a.val = b.val &&& c.val
  | OR  => (a < 256 ∧ b < 256 ∧ c < 256) ∧ a.val = b.val ||| c.val
  | XOR => (a < 256 ∧ b < 256 ∧ c < 256) ∧ a.val = b.val ^^^ c.val
  | U8Range => a < 256 ∧ b < 256 ∧ c < 256
  | LTU => (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b < c)
  | Range => a.val < 2 ^ b.val
  | MSB => (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b >= 128)

@[simp] lemma constrain_poly_AND (a b c : ZMod p) :
    ByteOpcode.AND.constrain_poly a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ a.val = b.val &&& c.val := Iff.rfl

@[simp] lemma constrain_poly_OR (a b c : ZMod p) :
    ByteOpcode.OR.constrain_poly a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ a.val = b.val ||| c.val := Iff.rfl

@[simp] lemma constrain_poly_XOR (a b c : ZMod p) :
    ByteOpcode.XOR.constrain_poly a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ a.val = b.val ^^^ c.val := Iff.rfl

@[simp] lemma constrain_poly_U8Range (a b c : ZMod p) :
    ByteOpcode.U8Range.constrain_poly a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) := Iff.rfl

@[simp] lemma constrain_poly_LTU (a b c : ZMod p) :
    ByteOpcode.LTU.constrain_poly a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b < c) := Iff.rfl

@[simp] lemma constrain_poly_MSB (a b c : ZMod p) :
    ByteOpcode.MSB.constrain_poly a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b >= 128) := Iff.rfl

@[simp] lemma constrain_poly_Range (a b c : ZMod p) :
    ByteOpcode.Range.constrain_poly a b c ↔ (a.val < 2 ^ b.val) := Iff.rfl

end constrain_poly

end ByteOpcode
