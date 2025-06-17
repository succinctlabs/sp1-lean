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

def ofBB : BabyBear → ByteOpcode
  | 0 => .AND
  | 1 => .OR
  | 2 => .XOR
  | _ => sorry

section ofNat

@[simp] lemma ofNat_zero : ByteOpcode.ofNat 0 = .AND := rfl
@[simp] lemma ofNat_one : ByteOpcode.ofNat 1 = .OR := rfl
@[simp] lemma ofNat_two : ByteOpcode.ofNat 2 = .XOR := rfl
@[simp] lemma ofNat_three : ByteOpcode.ofNat 3 = .U8Range := rfl
@[simp] lemma ofNat_four : ByteOpcode.ofNat 4 = .LTU := rfl
@[simp] lemma ofNat_five : ByteOpcode.ofNat 5 = .MSB := rfl
@[simp] lemma ofNat_six : ByteOpcode.ofNat 6 = .Range := rfl

end ofNat

def constrain (op : ByteOpcode) (a b c : BabyBear) : Prop :=
  match op with
  | AND => (a < 256 ∧ b < 256 ∧ c < 256) → a = b &&& c
  | OR  => (a < 256 ∧ b < 256 ∧ c < 256) → a = b ||| c
  | XOR => (a < 256 ∧ b < 256 ∧ c < 256) → a = b ^^^ c
  | U8Range => a < 256 ∧ b < 256 ∧ c < 256
  | LTU => (a < 256 ∧ b < 256 ∧ c < 256) → (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b < c)
  | Range => a < 2 ^ b.val -- Is this right?
  | MSB => (a < 256 ∧ b < 256 ∧ c < 256) → (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b >= 64)

@[simp] lemma constrain_AND (a b c : BabyBear) :
    ByteOpcode.AND.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256 → a = b &&& c) := Iff.rfl

@[simp] lemma constrain_OR (a b c : BabyBear) :
    ByteOpcode.OR.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256 → a = b ||| c) := Iff.rfl

@[simp] lemma constrain_XOR (a b c : BabyBear) :
    ByteOpcode.XOR.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256 → a = b ^^^ c) := Iff.rfl

@[simp] lemma constrain_U8Range (a b c : BabyBear) :
    ByteOpcode.U8Range.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256) := Iff.rfl

@[simp] lemma constrain_LTU (a b c : BabyBear) :
    ByteOpcode.LTU.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256 → (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b < c)) := Iff.rfl

@[simp] lemma constrain_MSB (a b c : BabyBear) :
    ByteOpcode.MSB.constrain a b c ↔ (a < 256 ∧ b < 256 ∧ c < 256 → (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b >= 64)) := Iff.rfl

@[simp] lemma constrain_Range (a b c : BabyBear) :
    ByteOpcode.Range.constrain a b c ↔ (a < 2 ^ b.val) := Iff.rfl

end ByteOpcode
