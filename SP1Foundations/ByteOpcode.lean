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

def constrain (op : ByteOpcode) (a b c : BabyBear) : Prop :=
  match op with
  | AND => (a < 256 ∧ b < 256 ∧ c < 256) → a = b &&& c
  | OR  => (a < 256 ∧ b < 256 ∧ c < 256) → a = b ||| c
  | XOR => (a < 256 ∧ b < 256 ∧ c < 256) → a = b ^^^ c
  | U8Range => a < 256 ∧ b < 256 ∧ c < 256
  | LTU => (a < 256 ∧ b < 256 ∧ c < 256) → (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b < c)
  | Range => a < 2 ^ b.val -- Is this right?
  | MSB => (a < 256 ∧ b < 256 ∧ c < 256) → (a = 0 ∨ a = 1) ∧ (a = 1 ↔ b >= 64)

-- @[reducible, simp] def ofNat : Fin 7 → ByteOpcode
--   | 0 => AND
--   | 1 => OR
--   | 2 => XOR
--   | 3 => U8Range
--   | 4 => LTU
--   | 5 => MSB
--   | 6 => Range

-- @[simp] lemma constrain_AND (a b c : BabyBear) :
--     AND.constrain a b c ↔ (a = b &&& c) := Iff.rfl
--
-- @[simp] lemma constrain_OR (a b c : BabyBear) :
--     OR.constrain a b c ↔ (a = b ||| c) := Iff.rfl
--
-- @[simp] lemma constrain_XOR (a b c : BabyBear) :
--     XOR.constrain a b c ↔ (a = b ^^^ c) := Iff.rfl
--
-- @[simp] lemma constrain_Range (a b c : BabyBear) :
--     Range.constrain a b c ↔ (a < 2 ^ b.val) := Iff.rfl

@[simp] lemma constrain_U8Range (c a b : BabyBear) :
    U8Range.constrain c a b ↔ c < 256 ∧ a < 256 := Iff.rfl

@[simp] lemma constrain_Range (c a b : BabyBear) :
    Range.constrain c a b ↔ (c < 2 ^ a.val) := Iff.rfl

end ByteOpcode
