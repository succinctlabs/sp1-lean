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

def toBB : ByteOpcode → Fin KB
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

def constrain (op : ByteOpcode) (a b c : Fin KB) : Prop :=
  match op with
  | AND => (a < 256 ∧ b < 256 ∧ c < 256) ∧ a.val = b.val &&& c.val
  | OR  => (a < 256 ∧ b < 256 ∧ c < 256) ∧ a.val = b.val ||| c.val
  | XOR => (a < 256 ∧ b < 256 ∧ c < 256) ∧ a.val = b.val ^^^ c.val
  | U8Range => a < 256 ∧ b < 256 ∧ c < 256
  | LTU => (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b < c)
  | Range => a.val < 2 ^ b.val
  | MSB => (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b >= 128)

@[simp] lemma constrain_AND (a b c : Fin KB) :
    ByteOpcode.AND.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ a.val = b.val &&& c.val := Iff.rfl

@[simp] lemma constrain_OR (a b c : Fin KB) :
    ByteOpcode.OR.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ a.val = b.val ||| c.val := Iff.rfl

@[simp] lemma constrain_XOR (a b c : Fin KB) :
    ByteOpcode.XOR.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ a.val = b.val ^^^ c.val := Iff.rfl

@[simp] lemma constrain_U8Range (a b c : Fin KB) :
    ByteOpcode.U8Range.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) := Iff.rfl

@[simp] lemma constrain_LTU (a b c : Fin KB) :
    ByteOpcode.LTU.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b < c) := Iff.rfl

@[simp] lemma constrain_MSB (a b c : Fin KB) :
    ByteOpcode.MSB.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) ∧ (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b >= 128) := Iff.rfl

@[simp] lemma constrain_Range (a b c : Fin KB) :
    ByteOpcode.Range.constrain a b c ↔ (a.val < 2 ^ b.val) := Iff.rfl

end constrain

/-! ### Polymorphic `constrain_poly` over `ZMod p`

Mirrors `constrain` (Fin KB) above but takes `ZMod p` parameters under
`[NeZero p]`. The two are propositionally equal at `p := KB` via
`ZMod KB = Fin KB` definitional equality. Used by `SP1Constraint.toProp_poly`
for sub-phase B.4 of the field-genericization effort
(`docs/FIELD_GENERIC.md`); the existing `Fin KB` version stays load-bearing
for chip code that calls `op.constrain` on `Fin KB`-typed terms. -/
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
def toBitwise (op : ByteOpcode) : Fin KB → Fin KB → Fin KB :=
  by induction op using ByteOpcode.bitwise_induction with
  | and => exact (· &&& ·)
  | or => exact (· ||| ·)
  | xor => exact (· ^^^ ·)
  | other _ _ => exact 0

@[simp] lemma toBitwise_and (x y : Fin KB) :
    toBitwise AND x y = x &&& y := rfl

@[simp] lemma toBitwise_or (x y : Fin KB) :
    toBitwise OR x y = x ||| y := rfl

@[simp] lemma toBitwise_xor (x y : Fin KB) :
    toBitwise XOR x y = x ^^^ y := rfl

lemma toBitwise_of_ne (x y : Fin KB) (op : ByteOpcode) (h : op ≠ AND ∧ op ≠ OR ∧ op ≠ XOR) :
    toBitwise op x y = 0 := by
  match op with
  | .AND | .OR | XOR => simp at h
  | U8Range | LTU | MSB | Range => rfl

end toBitwise

end ByteOpcode
