import SP1Foundations.Field

/-- General definition that can be used to define `U1`, `U8`, and `U16`.
Allows writing unified lemmas for all three definitions. -/
structure BoundedBabyBear (bound : ℕ) extends BabyBear where
  in_range : val < bound

namespace BoundedBabyBear

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

@[ext] lemma ext {x y : BoundedBabyBear bound} (h : x.val = y.val) : x = y := by
  sorry

instance : Inhabited (BoundedBabyBear bound.succ) where default := 0

@[simp] lemma default_eq_zero : (default : BoundedBabyBear bound.succ) = 0 := rfl

section toFin

@[simp] lemma toFin_zero : (0 : BoundedBabyBear bound.succ).toFin = 0 := rfl
@[simp] lemma toFin_one : (1 : BoundedBabyBear bound.succ.succ).toFin = 1 := rfl

lemma toFin_inj (x y : BoundedBabyBear bound) : x.toFin = y.toFin ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rwa [BoundedBabyBear.ext_iff, ← Fin.ext_iff]

lemma toFin_eq_iff (x : BoundedBabyBear bound) (y : Fin BabyBearPrime) : x.toFin = y ↔ x.val = y.val := by
  erw [Fin.ext_iff]

end toFin

section toBabyBear

/-- Convert a `BoundedBabyBear` to a `BabyBear` by forgetting the bound. -/
def toBabyBear (x : BoundedBabyBear bound) : BabyBear where __ := x

@[simp] lemma toBabyBear_zero : (0 : BoundedBabyBear bound.succ).toBabyBear = 0 := rfl
@[simp] lemma toBabyBear_one : (1 : BoundedBabyBear bound.succ.succ).toBabyBear = 1 := rfl

@[simp] lemma val_toBabyBear (x : BoundedBabyBear bound) : (x.toBabyBear : ℕ) = x.val := rfl

lemma toBabyBear_inj (x y : BoundedBabyBear bound) : toBabyBear x = toBabyBear y ↔ x = y := by
  simp [toBabyBear, toFin_inj]

lemma injective_toBabyBear :
    Function.Injective (toBabyBear : BoundedBabyBear bound → BabyBear) :=
  fun x y h => (toBabyBear_inj x y).1 h

end toBabyBear

lemma eq_zero_iff (x : BoundedBabyBear bound.succ) : x = 0 ↔ x.val = 0 := by aesop

lemma eq_one_iff (x : BoundedBabyBear bound.succ.succ) : x = 1 ↔ x.val = 1 := by aesop

section LinearOrder

/-- Lift the linear order on the underlying field to `BoundedBabyBear`. -/
instance : LinearOrder (BoundedBabyBear bound) :=
  LinearOrder.lift' BoundedBabyBear.toBabyBear injective_toBabyBear

@[simp] lemma lt_iff_val_lt_val (x y : BoundedBabyBear bound) :
    x < y ↔ x.val < y.val := Iff.rfl

@[simp] lemma le_iff_val_le_val (x y : BoundedBabyBear bound) :
    x ≤ y ↔ x.val ≤ y.val := Iff.rfl

end LinearOrder

end BoundedBabyBear

abbrev U32 := BoundedBabyBear 4294967296
abbrev U16 := BoundedBabyBear 65536
abbrev U8 := BoundedBabyBear 256
abbrev U1 := BoundedBabyBear 2

instance : Coe U16 BabyBear where coe := BoundedBabyBear.toBabyBear
instance : Coe U8 BabyBear where coe := BoundedBabyBear.toBabyBear
instance : Coe U1 BabyBear where coe := BoundedBabyBear.toBabyBear

instance : Coe U1 U8 := BoundedBabyBear.coe_of_le <| by omega
instance : Coe U8 U16 := BoundedBabyBear.coe_of_le <| by omega

def U1.in_range' (x : U1) : x.val = 0 ∨ x.val = 1 := by
  have := x.in_range; omega
