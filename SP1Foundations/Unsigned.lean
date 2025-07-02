import SP1Foundations.Field

/-- General definition that can be used to define `U1`, `U8`, and `U16`.
Allows writing unified lemmas for all three definitions. -/
structure BoundedBabyBear (bound : ℕ) extends BabyBear where
  in_range : val < bound

namespace BoundedBabyBear

@[ext] lemma ext {bound : ℕ} {x y : BoundedBabyBear bound} (h : x.val = y.val) :
    x = y := match x, y with
  | ⟨⟨x, ?_⟩, ?_⟩, ⟨⟨y, ?_⟩, ?_⟩ => by simpa

def ofNat (bound_dec x : ℕ) : BoundedBabyBear bound_dec.succ where
  val := (x % bound_dec.succ) % BabyBearPrime
  isLt := Nat.mod_lt _ Nat.succ_pos'
  in_range := Nat.mod_lt_of_lt (Nat.mod_lt _ Nat.succ_pos')

/-- If the bound is at least `1` then `boundedBabyBear` has a natural `0`. -/
def boundedBabyBear.zero (bound_dec : ℕ) : BoundedBabyBear bound_dec.succ where
  in_range := by simp
  __ := (0 : BabyBear)

/-- If the bound is at least `2` then `boundedBabyBear` has a natural `1`. -/
def boundedBabyBear.one (bound_dec_dec : ℕ) : BoundedBabyBear (bound_dec_dec.succ.succ) where
  in_range := by simp
  __ := (1 : BabyBear)

instance (bound_dec : ℕ) : Zero (BoundedBabyBear bound_dec.succ) := ⟨boundedBabyBear.zero _⟩
instance (bound_dec_dec : ℕ) : One (BoundedBabyBear bound_dec_dec.succ.succ) := ⟨boundedBabyBear.one _⟩

/-- Should only make an actual instance for special cases. -/
def coe_of_le {bound bound' : ℕ} (h : bound ≤ bound') :
    Coe (BoundedBabyBear bound) (BoundedBabyBear bound') where
  coe x := { in_range := lt_of_lt_of_le x.in_range h, __ := x }

variable {bound : ℕ}

@[aesop 50% forward]
lemma lt_babyBearPrime (x : BoundedBabyBear bound) : x.val < BabyBearPrime := Fin.is_lt _

instance : Inhabited (BoundedBabyBear bound.succ) where default := 0
lemma default_eq_zero : (default : BoundedBabyBear bound.succ) = 0 := rfl

section toFin

-- /-- Convert a `BoundedBabyBear` to a `BabyBear` by forgetting the bound. -/
-- @[simp] alias toBabyBear := BoundedBabyBear.toFin

-- lemma toBabyBear_def (x : BoundedBabyBear bound) : x.toBabyBear = x.toFin := rfl

@[simp] lemma toFin_zero : (0 : BoundedBabyBear bound.succ).toFin = 0 := rfl
@[simp] lemma toFin_one : (1 : BoundedBabyBear bound.succ.succ).toFin = 1 := rfl

lemma toFin_inj (x y : BoundedBabyBear bound) : x.toFin = y.toFin ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rwa [BoundedBabyBear.ext_iff, ← Fin.ext_iff]

lemma injective_toFin : Function.Injective (BoundedBabyBear.toFin : BoundedBabyBear bound → BabyBear) :=
  fun x y h => (toFin_inj x y).1 h

lemma toFin_eq_iff (x : BoundedBabyBear bound) (y : Fin BabyBearPrime) : x.toFin = y ↔ x.val = y.val := by
  erw [Fin.ext_iff]

end toFin

-- section toBabyBear

-- lemma toBabyBear_zero : (0 : BoundedBabyBear bound.succ).toBabyBear = 0 := rfl
-- lemma toBabyBear_one : (1 : BoundedBabyBear bound.succ.succ).toBabyBear = 1 := rfl

-- lemma val_toBabyBear (x : BoundedBabyBear bound) : (x.toBabyBear : ℕ) = x.val := rfl

-- lemma toBabyBear_inj (x y : BoundedBabyBear bound) : toBabyBear x = toBabyBear y ↔ x = y := by
--   simp [toBabyBear, toFin_inj]

-- lemma injective_toBabyBear :
--     Function.Injective (toBabyBear : BoundedBabyBear bound → BabyBear) :=
--   fun x y h => (toBabyBear_inj x y).1 h

-- end toBabyBear

lemma eq_zero_iff (x : BoundedBabyBear bound.succ) : x = 0 ↔ x.val = 0 := by aesop

lemma eq_one_iff (x : BoundedBabyBear bound.succ.succ) : x = 1 ↔ x.val = 1 := by aesop

section LinearOrder

/-- Lift the linear order on the underlying field to `BoundedBabyBear`. -/
instance : LinearOrder (BoundedBabyBear bound) :=
  LinearOrder.lift' BoundedBabyBear.toFin injective_toFin

@[simp] lemma lt_iff_val_lt_val (x y : BoundedBabyBear bound) :
    x < y ↔ x.val < y.val := Iff.rfl

@[simp] lemma le_iff_val_le_val (x y : BoundedBabyBear bound) :
    x ≤ y ↔ x.val ≤ y.val := Iff.rfl

end LinearOrder

end BoundedBabyBear

abbrev U16 := BoundedBabyBear 65536
abbrev U8 := BoundedBabyBear 256
abbrev U1 := BoundedBabyBear 2

instance : Coe U16 BabyBear where coe := BoundedBabyBear.toFin
instance : Coe U8 BabyBear where coe := BoundedBabyBear.toFin
instance : Coe U1 BabyBear where coe := BoundedBabyBear.toFin

instance : Coe U1 U8 := BoundedBabyBear.coe_of_le <| by omega
instance : Coe U8 U16 := BoundedBabyBear.coe_of_le <| by omega

def U1.in_range' (x : U1) : x.val = 0 ∨ x.val = 1 := by
  have := x.in_range; omega

def U1.in_range'' (x : U1) : x = 0 ∨ x = 1 := by
  have := x.in_range'
  aesop

@[aesop 50% forward]
lemma U16.lt_bound (x : U16) : x.val < 65536 := x.in_range

@[aesop 50% forward]
lemma U8.lt_bound (x : U8) : x.val < 256 := x.in_range

namespace BitVec

def ofU16 (low_limb high_limb : U16) : BitVec 32 :=
  (low_limb.val + high_limb.val * 65536)#'(by aesop (add 50% tactic (by omega)))

def decompose (x : BitVec 32) : U16 × U16 :=
  let low_val := x.toNat % 65536
  let high_val := x.toNat / 65536
  let low_limb : U16 := {
    val := low_val
    isLt := by trans 65536 <;> [ omega; trivial ]
    in_range := by omega
  }
  let high_limb : U16 := {
    val := high_val
    isLt := by trans 65536 <;> [ omega; trivial ]
    in_range := by omega
  }
  (low_limb, high_limb)

theorem decompose_ofU16_inverse (bv : BitVec 32) :
    let (a, b) := decompose bv
    bv = BitVec.ofU16 a b := by
  unfold decompose BitVec.ofU16
  apply BitVec.eq_of_toNat_eq
  simp only [toNat_ofNatLT]
  omega

end BitVec
