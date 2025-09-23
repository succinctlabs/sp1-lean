import SP1Foundations.Field

/-- General definition that can be used to define `U1`, `U8`, and `U16`.
Allows writing unified lemmas for all three definitions.

dt: it's not clear to me how useful this is in most cases.
Often you have to restructure the bounds yourselves anyways -/
structure BoundedKoalaBear (bound : ℕ) extends Fin KB where
  in_range : val < bound

namespace BoundedKoalaBear

@[ext] lemma ext {bound : ℕ} {x y : BoundedKoalaBear bound} (h : x.val = y.val) :
    x = y := match x, y with
  | ⟨⟨x, ?_⟩, ?_⟩, ⟨⟨y, ?_⟩, ?_⟩ => by simpa

def ofNat (bound_dec x : ℕ) : BoundedKoalaBear bound_dec.succ where
  val := (x % bound_dec.succ) % KB
  isLt := Nat.mod_lt _ Nat.succ_pos'
  in_range := Nat.mod_lt_of_lt (Nat.mod_lt _ Nat.succ_pos')

/-- If the bound is at least `1` then `boundedKoalaBear` has a natural `0`. -/
def boundedKoalaBear.zero (bound_dec : ℕ) : BoundedKoalaBear bound_dec.succ where
  in_range := by simp
  __ := (0 : Fin KB)

/-- If the bound is at least `2` then `boundedKoalaBear` has a natural `1`. -/
def boundedKoalaBear.one (bound_dec_dec : ℕ) : BoundedKoalaBear (bound_dec_dec.succ.succ) where
  in_range := by simp
  __ := (1 : Fin KB)

instance (bound_dec : ℕ) : Zero (BoundedKoalaBear bound_dec.succ) := ⟨boundedKoalaBear.zero _⟩
instance (bound_dec_dec : ℕ) : One (BoundedKoalaBear bound_dec_dec.succ.succ) := ⟨boundedKoalaBear.one _⟩

/-- Should only make an actual instance for special cases. -/
def coe_of_le {bound bound' : ℕ} (h : bound ≤ bound') :
    Coe (BoundedKoalaBear bound) (BoundedKoalaBear bound') where
  coe x := { in_range := lt_of_lt_of_le x.in_range h, __ := x }

variable {bound : ℕ}

@[aesop 50% forward]
lemma lt_KoalaBearPrime (x : BoundedKoalaBear bound) : x.val < KB := Fin.is_lt _

instance : Inhabited (BoundedKoalaBear bound.succ) where default := 0
lemma default_eq_zero : (default : BoundedKoalaBear bound.succ) = 0 := rfl

section toFin

-- /-- Convert a `BoundedKoalaBear` to a `Fin KB` by forgetting the bound. -/
-- @[simp] alias toKoalaBear := BoundedKoalaBear.toFin

-- lemma toKoalaBear_def (x : BoundedKoalaBear bound) : x.toKoalaBear = x.toFin := rfl

@[simp] lemma toFin_zero : (0 : BoundedKoalaBear bound.succ).toFin = 0 := rfl
@[simp] lemma toFin_one : (1 : BoundedKoalaBear bound.succ.succ).toFin = 1 := rfl

lemma toFin_inj (x y : BoundedKoalaBear bound) : x.toFin = y.toFin ↔ x = y := by
  refine ⟨fun h => ?_, fun h => h ▸ rfl⟩
  rwa [BoundedKoalaBear.ext_iff, ← Fin.ext_iff]

lemma injective_toFin : Function.Injective (BoundedKoalaBear.toFin : BoundedKoalaBear bound → Fin KB) :=
  fun x y h => (toFin_inj x y).1 h

lemma toFin_eq_iff (x : BoundedKoalaBear bound) (y : Fin KB) : x.toFin = y ↔ x.val = y.val := by
  erw [Fin.ext_iff]

end toFin

-- section toKoalaBear

-- lemma toKoalaBear_zero : (0 : BoundedKoalaBear bound.succ).toKoalaBear = 0 := rfl
-- lemma toKoalaBear_one : (1 : BoundedKoalaBear bound.succ.succ).toKoalaBear = 1 := rfl

-- lemma val_toKoalaBear (x : BoundedKoalaBear bound) : (x.toKoalaBear : ℕ) = x.val := rfl

-- lemma toKoalaBear_inj (x y : BoundedKoalaBear bound) : toKoalaBear x = toKoalaBear y ↔ x = y := by
--   simp [toKoalaBear, toFin_inj]

-- lemma injective_toKoalaBear :
--     Function.Injective (toKoalaBear : BoundedKoalaBear bound → Fin KB) :=
--   fun x y h => (toKoalaBear_inj x y).1 h

-- end toKoalaBear

lemma eq_zero_iff (x : BoundedKoalaBear bound.succ) : x = 0 ↔ x.val = 0 := by aesop

lemma eq_one_iff (x : BoundedKoalaBear bound.succ.succ) : x = 1 ↔ x.val = 1 := by aesop

section LinearOrder

/-- Lift the linear order on the underlying field to `BoundedKoalaBear`. -/
instance : LinearOrder (BoundedKoalaBear bound) :=
  LinearOrder.lift' BoundedKoalaBear.toFin injective_toFin

@[simp] lemma lt_iff_val_lt_val (x y : BoundedKoalaBear bound) :
    x < y ↔ x.val < y.val := Iff.rfl

@[simp] lemma le_iff_val_le_val (x y : BoundedKoalaBear bound) :
    x ≤ y ↔ x.val ≤ y.val := Iff.rfl

end LinearOrder

end BoundedKoalaBear

abbrev U16 := BoundedKoalaBear 65536
abbrev U8 := BoundedKoalaBear 256
abbrev U1 := BoundedKoalaBear 2

instance : Coe U16 (Fin KB) where coe := BoundedKoalaBear.toFin
instance : Coe U8 (Fin KB) where coe := BoundedKoalaBear.toFin
instance : Coe U1 (Fin KB) where coe := BoundedKoalaBear.toFin

instance : Coe U1 U8 := BoundedKoalaBear.coe_of_le <| by omega
instance : Coe U8 U16 := BoundedKoalaBear.coe_of_le <| by omega

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
