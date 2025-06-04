import SP1Foundations.Field

inductive ByteOpcode
  | AND
  | OR
  | XOR
  | U8Range
  | LTU
  | MSB
  | Range

namespace ByteOpcode

@[reducible, simp] def ofNat : Fin 7 → ByteOpcode
  | 0 => AND
  | 1 => OR
  | 2 => XOR
  | 3 => U8Range
  | 4 => LTU
  | 5 => MSB
  | 6 => Range

def constrain (op : ByteOpcode) (c a b : BabyBear) : Prop :=
  match op with
  | AND => c = a &&& b
  | OR => c = a ||| b
  | XOR => c = a ^^^ b
  | _ => false -- TODO

@[simp] lemma constrain_AND (c a b : BabyBear) :
    AND.constrain c a b ↔ (c = a &&& b) := Iff.rfl

@[simp] lemma constrain_OR (c a b : BabyBear) :
    OR.constrain c a b ↔ (c = a ||| b) := Iff.rfl

@[simp] lemma constrain_XOR (c a b : BabyBear) :
    XOR.constrain c a b ↔ (c = a ^^^ b) := Iff.rfl

end ByteOpcode
