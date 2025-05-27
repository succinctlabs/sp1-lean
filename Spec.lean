import Mathlib

namespace Add 

/-
 - Annoyances:
 - 1. Nat should always be an acceptable paremeter for the number of bits to
 - shift in HShiftLeft and HShiftRight.
 -/

attribute [simp] toNat
notation:100 v "[[" i " | " h "]]" => Vector.uget v i h

macro "WORD_SIZE" : term => `(4)

structure Word (T : Type) where
  data : Vector T WORD_SIZE
  deriving Repr

instance {T : Type} : GetElem (Word T) Nat T (fun _ i => i < WORD_SIZE) where
  getElem w i h := w.data.get ⟨i, h⟩

variable {p : Nat}
variable [Fact (Nat.Prime p)]

-- TODO(gzgz): the implicit variable p cannot be automatically inferred.
-- abbrev P := ZMod p

@[simp]
def _root_.ZMod.toUInt8 (x : ZMod p) : UInt8 := x.val.toUInt8

@[simp]
def Word.is_u32 (w : Word (ZMod p)) : Prop :=
  w[0].val < 256
  ∧ w[1].val < 256
  ∧ w[2].val < 256
  ∧ w[3].val < 256

@[simp]
def Word.toUInt32 (self : Word (ZMod p)) : UInt32 :=
  let v0 : UInt8 := self[0].toUInt8
  let v1 : UInt8 := self[1].toUInt8
  let v2 : UInt8 := self[2].toUInt8
  let v3 : UInt8 := self[3].toUInt8
  -- TODO(gzgz): plus or bitwise-or here? which is more convenient to prove?
  (v3.toUInt32 <<< 24) + (v2.toUInt32 <<< 16) + (v1.toUInt32 <<< 8) +
  v0.toUInt32

-- TODO(gzgz): what's the most convenient format for us to prove properties on
-- it?
@[simp]
def UInt32.toWord (u : UInt32) : Word (ZMod p) :=
  /- { data := Vector.ofFn (fun (i : Fin WORD_SIZE) => -/
  /-     ((u >>> (i.val * 8).toUInt32) &&& (0xFF)).toNat -/
  /-   ) -/
  { data :=
    #v[ (u &&& 0xFF).toNat
    , ((u >>> 8) &&& 0xFF).toNat
    , ((u >>> 16) &&& 0xFF).toNat
    , ((u >>> 24) &&& 0xFF).toNat
    ]
  }

-- TODO(gzgz): maybe it's better to use `UInt32.toWord 0`? using this for now
-- because I think that may make proofs more complicated.
instance : Zero (Word (ZMod p)) where
  zero := { data := #v[0, 0, 0, 0] }

instance : One (Word (ZMod p)) where
  one := { data := #v[1, 0, 0, 0] }

instance : Add (Word (ZMod p)) where
  add w1 w2 := UInt32.toWord (w1.toUInt32 + w2.toUInt32)

instance : Sub (Word (ZMod p)) where
  sub w1 w2 := UInt32.toWord (w1.toUInt32 - w2.toUInt32)

instance : Mul (Word (ZMod p)) where
  mul w1 w2 := UInt32.toWord (w1.toUInt32 * w2.toUInt32)

structure AddOperation (T : Type) where
  value : Word T 
  carry : Vector T 3

/-
 - What we probably want:
 - is_real = 0 -> idc
 - is_real ≠ 0 -> a + b = c
 -/

def AddOpeartion.spec
  (cols : AddOperation (ZMod p))
  (a : Word (ZMod p))
  (b : Word (ZMod p))
  (is_real : ZMod p)
  : Prop :=
    is_real = 1
    ∧ a.is_u32
    ∧ b.is_u32
    ->
      cols.value.is_u32 -- c
      ∧ a + b = cols.value

def AddOperation.constraints
  (cols : AddOperation P)
  (a : Word (ZMod p))
  (b : Word (ZMod p))
  (is_real : ZMod p)
  : Prop :=
    _

-- The specification:
structure AddSubChip (T : Type) where
  pc : T 
  add_operation : AddOperation T 
  operand_1 : Word T
  operand_2 : Word T
  op_a_not_0 : T
  is_add : T
  is_sub : T


def AddSubChip.constraints
  (self : AddSubChip (ZMod p)) : Prop :=
    _

-- This should be a high-level description of what we expect the circuit to
-- perform.
def AddSubChip.spec
  (self : AddSubChip (ZMod p)) : Prop :=
    self.operand_1 + self.operand_2 = self.add_operation.value

def AddSubChip.safety
  (self : AddSubChip (ZMod p)) : self.constraints -> self.spec := by
    sorry



end Add
