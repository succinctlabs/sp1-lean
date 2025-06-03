import Mathlib

inductive ByteOpcode
  | AND
  | OR
  | XOR
  | U8Range
  | LTU
  | MSB
  | Range

namespace ByteOpcode

def ofNat : Fin 7 → ByteOpcode
  | 0 => AND
  | 1 => OR
  | 2 => XOR
  | 3 => U8Range
  | 4 => LTU
  | 5 => MSB
  | 6 => Range

def constrain {p} (op : ByteOpcode) (c a b : Fin p) : Prop :=
  match op with
  | AND => c = a &&& b
  | OR => c = a ||| b
  | XOR => c = a ^^^ b
  | _ => false -- TODO

end ByteOpcode
