import SP1Foundations.Field
-- import SP1Foundations.Tactics

@[simp] notation "BYTE_DWORD_SIZE" => 16
@[simp] notation "BYTE_WORD_SIZE" => 8
@[simp] notation "BYTE_HWORD_SIZE" => 4
@[simp] notation "DWORD_SIZE" => 8
@[simp] notation "WORD_SIZE" => 4
@[simp] notation "HWORD_SIZE" => 2

@[reducible] def HWord (T : Type) := Vector T HWORD_SIZE
@[reducible] def Word (T : Type) := Vector T WORD_SIZE
@[reducible] def DWord (T : Type) := Vector T DWORD_SIZE
@[reducible] def BHWord (T : Type) := Vector T BYTE_HWORD_SIZE
@[reducible] def BWord (T : Type) := Vector T BYTE_WORD_SIZE
@[reducible] def BDWord (T : Type) := Vector T BYTE_DWORD_SIZE

namespace BitVec

lemma setWidth_idem {m n : ℕ} {bv : BitVec m} :
  (m ≤ n) → (BitVec.setWidth n bv).toNat = bv.toNat
    := by
  intro hle; simp
  rw [Nat.mod_eq_of_lt]
  apply lt_of_lt_of_le (b := 2 ^ m)
  · unfold BitVec.toNat; apply bv.toFin.isLt
  · apply Nat.pow_le_pow_right (by simp) (by assumption)

end BitVec

open BitVec

namespace HWord

/-- Prove two `HWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : HWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1
  | n + 2, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `HWord`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : HWord T}
    (h : ∀ i : Fin HWORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : HWord T) : w = #v[w[0], w[1]] := ext_cases rfl rfl

lemma eq_pointwise (w w' : HWord T) : (w[0] = w'[0]) ∧ (w[1] = w'[1]) ↔ w = w' := by
   constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `HWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : HWord T → Prop}
    (mk : ∀ x1 x2 : T, C #v[x1, x2]) (w : HWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U32

/-- `isU32 w` means that each limb of the `HWord` is properly bounded. -/
def isU32 (w : HWord (Fin KB)) : Prop := ∀ i : Fin HWORD_SIZE, w[i].val < 2 ^ 16

/-- Polymorphic counterpart of `isU32`. -/
def isU32_poly {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : Prop :=
  ∀ i : Fin HWORD_SIZE, w[i].val < 2 ^ 16

@[aesop unsafe apply]
lemma isU32_of_cases {w : HWord (Fin KB)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16) : w.isU32
  := by intro i; fin_cases i <;> simpa

/-- Polymorphic counterpart of `isU32_of_cases`. -/
@[aesop unsafe apply]
lemma isU32_of_cases_poly {p : ℕ} [NeZero p] {w : HWord (ZMod p)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16) : w.isU32_poly
  := by intro i; fin_cases i <;> simpa [isU32_poly]

/-- Pull in bounds on a `HWord`s limbs given a `isU32` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU32 {w : HWord (Fin KB)} (hw : w.isU32) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 :=
  ⟨hw 0, hw 1⟩

/-- Polymorphic counterpart of `lt_cases_of_isU32`. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU32_poly {p : ℕ} [NeZero p] {w : HWord (ZMod p)} (hw : w.isU32_poly) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 :=
  ⟨hw 0, hw 1⟩

end U32

section conversions

/-- Convert a `HWord` to a `Nat` by shifting and adding the limbs. -/
def toNat (w : HWord (Fin KB)) : ℕ := w[0] + w[1] * 2 ^ 16

/-- Polymorphic counterpart of `HWord.toNat`. -/
def toNat_poly {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 16

lemma toNat_lt_of_isU32 {w : HWord (Fin KB)} (hw : w.isU32) : w.toNat < 2 ^ 32 := by
  unfold toNat
  aesop (add 50% tactic (by omega))

/-- Polymorphic counterpart of `toNat_lt_of_isU32`. -/
lemma toNat_poly_lt_of_isU32_poly {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (hw : w.isU32_poly) : w.toNat_poly < 2 ^ 32 := by
  have := lt_cases_of_isU32_poly hw
  unfold toNat_poly
  omega

/-- Convert a `HWord` to a `BitVec 32` by shifting and adding the limbs. -/
def toBitVec32 (w : HWord (Fin KB)) : BitVec 32 := BitVec.ofNat 32 w.toNat

/-- Polymorphic counterpart of `HWord.toBitVec32`. -/
def toBitVec32_poly {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : BitVec 32 :=
  BitVec.ofNat 32 (toNat_poly w)

lemma toBitVec32_toNat {w : HWord (Fin KB)} (hw : w.isU32) :
    w.toBitVec32.toNat = w.toNat := by
  simp only [toBitVec32, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU32 hw
  omega

/-- Polymorphic counterpart of `toBitVec32_toNat`. -/
lemma toBitVec32_poly_toNat_poly {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (hw : w.isU32_poly) :
    w.toBitVec32_poly.toNat = w.toNat_poly := by
  simp only [toBitVec32_poly, BitVec.toNat_ofNat, toNat_poly]
  have := lt_cases_of_isU32_poly hw
  omega

/-- Convert a `HWord` to a `BitVec 64` by shifting and adding the limbs, with sign extension. -/
def toBitVec64 (w : HWord (Fin KB)) : BitVec 64 := BitVec.signExtend 64 w.toBitVec32

/-- Polymorphic counterpart of `HWord.toBitVec64`. -/
def toBitVec64_poly {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : BitVec 64 :=
  BitVec.signExtend 64 (toBitVec32_poly w)

/-- A 32-bit integer is negative if its msb equals one -/
@[grind] def isNegative (w : HWord (Fin KB)) : Prop := w[1] ≥ 32768
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

/-- Polymorphic counterpart of `HWord.isNegative`. -/
@[grind] def isNegative_poly {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : Prop := w[1].val ≥ 32768

instance {p : ℕ} [NeZero p] {w : HWord (ZMod p)} : Decidable (isNegative_poly w) := by
  unfold isNegative_poly; infer_instance

lemma isNegative_msb
  {w : HWord (Fin KB)}
  (h_w_isU32 : w.isU32) :
    w.isNegative ↔ (w.toBitVec32.msb = true) := by
  have := lt_cases_of_isU32 h_w_isU32
  simp [isNegative, toBitVec32, toNat, BitVec.msb_eq_decide]
  omega

/-- Polymorphic counterpart of `HWord.isNegative_msb`. -/
lemma isNegative_poly_msb {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (h_w_isU32 : w.isU32_poly) :
    w.isNegative_poly ↔ (w.toBitVec32_poly.msb = true) := by
  have := lt_cases_of_isU32_poly h_w_isU32
  simp [isNegative_poly, toBitVec32_poly, toNat_poly, BitVec.msb_eq_decide]
  omega

/-- Convert a `HWord` to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : HWord (Fin KB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 32 else w.toNat

/-- Polymorphic counterpart of `HWord.toInt`. -/
def toInt_poly {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : ℤ :=
  if (isNegative_poly w) then w.toNat_poly - 2 ^ 32 else w.toNat_poly

lemma toInt_lb {w : HWord (Fin KB)} (is_U32_w : w.isU32) :
  -2147483648 ≤ w.toInt := by
  apply HWord.lt_cases_of_isU32 at is_U32_w
  simp [HWord.toInt, HWord.isNegative, HWord.toNat] at *
  omega

/-- Polymorphic counterpart of `HWord.toInt_lb`. -/
lemma toInt_poly_lb {p : ℕ} [NeZero p] {w : HWord (ZMod p)} (is_U32_w : w.isU32_poly) :
  -2147483648 ≤ w.toInt_poly := by
  have ⟨h0, h1⟩ := lt_cases_of_isU32_poly is_U32_w
  unfold HWord.toInt_poly HWord.isNegative_poly HWord.toNat_poly
  split_ifs <;> push_cast <;> omega

lemma toInt_ub {w : HWord (Fin KB)} (is_U32_w : w.isU32) :
  w.toInt < 2147483648 := by
  apply HWord.lt_cases_of_isU32 at is_U32_w
  simp [HWord.toInt, HWord.isNegative, HWord.toNat] at *
  omega

/-- Polymorphic counterpart of `HWord.toInt_ub`. -/
lemma toInt_poly_ub {p : ℕ} [NeZero p] {w : HWord (ZMod p)} (is_U32_w : w.isU32_poly) :
  w.toInt_poly < 2147483648 := by
  have ⟨h0, h1⟩ := lt_cases_of_isU32_poly is_U32_w
  unfold HWord.toInt_poly HWord.isNegative_poly HWord.toNat_poly
  split_ifs <;> push_cast <;> omega

lemma eq_toInt_eq {wx wy : HWord (Fin KB)} (is32_wx : HWord.isU32 wx) (is32_wy : HWord.isU32 wy) :
  wx = wy ↔ wx.toInt = wy.toInt := by
  constructor
  · simp_all
  · apply HWord.lt_cases_of_isU32 at is32_wx
    apply HWord.lt_cases_of_isU32 at is32_wy
    unfold HWord.toInt HWord.isNegative HWord.toNat; intro heq
    rw [← HWord.eq_pointwise]
    omega

/-- Polymorphic counterpart of `HWord.eq_toInt_eq`. The reverse direction
is structured similarly to the `Fin KB` version but uses
`ZMod.val_injective` per limb to recover pointwise equality from the
`.val`-bound facts. -/
lemma eq_toInt_poly_eq {p : ℕ} [NeZero p] {wx wy : HWord (ZMod p)}
    (is32_wx : wx.isU32_poly) (is32_wy : wy.isU32_poly) :
  wx = wy ↔ wx.toInt_poly = wy.toInt_poly := by
  constructor
  · simp_all
  · apply HWord.lt_cases_of_isU32_poly at is32_wx
    apply HWord.lt_cases_of_isU32_poly at is32_wy
    unfold HWord.toInt_poly HWord.isNegative_poly HWord.toNat_poly; intro heq
    rw [← HWord.eq_pointwise]
    refine ⟨?_, ?_⟩ <;> apply ZMod.val_injective <;> omega

lemma toBitVec32_toInt {w : HWord (Fin KB)} (h_w_isU64 : w.isU32) :
    w.toBitVec32.toInt = w.toInt
  := by
    have := lt_cases_of_isU32 h_w_isU64
    have := toNat_lt_of_isU32 h_w_isU64
    unfold toBitVec32 toInt BitVec.toInt
    simp_all only [Nat.reducePow, Int.reducePow, toNat_ofNat, Nat.cast_ofNat]
    rw [Nat.mod_eq_of_lt this]
    by_cases h_neg : w.isNegative <;> unfold isNegative at * <;>
    unfold toNat at * <;> simp_all <;> omega

/-- Polymorphic counterpart of `HWord.toBitVec32_toInt`. -/
lemma toBitVec32_poly_toInt_poly {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (h_w_isU32 : w.isU32_poly) :
    w.toBitVec32_poly.toInt = w.toInt_poly
  := by
    have := lt_cases_of_isU32_poly h_w_isU32
    have := toNat_poly_lt_of_isU32_poly h_w_isU32
    unfold toBitVec32_poly toInt_poly BitVec.toInt
    simp_all only [Nat.reducePow, Int.reducePow, toNat_ofNat, Nat.cast_ofNat]
    rw [Nat.mod_eq_of_lt this]
    by_cases h_neg : w.isNegative_poly <;> unfold isNegative_poly at * <;>
    unfold toNat_poly at * <;> push_cast <;> simp_all <;> omega

lemma toBitVec64_toInt {w : HWord (Fin KB)} (h_w_isU32 : w.isU32) :
    w.toBitVec64.toInt = w.toInt
  := by
    have := lt_cases_of_isU32 h_w_isU32
    simp [toBitVec64, BitVec.toInt_signExtend]
    rw [toBitVec32_toInt h_w_isU32]
    unfold toInt isNegative toNat
    refine Int.bmod_eq_of_le ?_ ?_ <;> omega

/-- Polymorphic counterpart of `HWord.toBitVec64_toInt`. -/
lemma toBitVec64_poly_toInt_poly {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (h_w_isU32 : w.isU32_poly) :
    w.toBitVec64_poly.toInt = w.toInt_poly
  := by
    have := lt_cases_of_isU32_poly h_w_isU32
    simp [toBitVec64_poly, BitVec.toInt_signExtend]
    rw [toBitVec32_poly_toInt_poly h_w_isU32]
    unfold toInt_poly isNegative_poly toNat_poly
    refine Int.bmod_eq_of_le ?_ ?_ <;> push_cast <;> omega

lemma isNegative_toInt {w : HWord (Fin KB)} (is32_w : HWord.isU32 w) :
  w.isNegative ↔ w.toInt < 0
    := by
  unfold HWord.toInt HWord.isNegative HWord.toNat
  apply HWord.lt_cases_of_isU32 at is32_w
  omega

/-- Polymorphic counterpart of `HWord.isNegative_toInt`. -/
lemma isNegative_poly_toInt_poly {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (is32_w : HWord.isU32_poly w) :
    w.isNegative_poly ↔ w.toInt_poly < 0 := by
  have := lt_cases_of_isU32_poly is32_w
  unfold HWord.toInt_poly HWord.isNegative_poly HWord.toNat_poly
  split_ifs <;> push_cast <;> omega

lemma sign_cases {w : HWord (Fin KB)} (is32_w : HWord.isU32 w) : w.toInt.sign = if w.isNegative then -1 else if w.toInt = 0 then 0 else 1 := by
  simp [HWord.isNegative_toInt is32_w]
  exact Int.sign_cases w.toInt

/-- Polymorphic counterpart of `HWord.sign_cases`. -/
lemma sign_cases_poly {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (is32_w : HWord.isU32_poly w) :
    w.toInt_poly.sign = if w.isNegative_poly then -1 else if w.toInt_poly = 0 then 0 else 1 := by
  simp [HWord.isNegative_poly_toInt_poly is32_w]
  exact Int.sign_cases w.toInt_poly

end conversions

end HWord

namespace Word

/-- Prove two `Word`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : Word T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1])
    (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3
  | n + 4, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `Word`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : Word T}
    (h : ∀ i : Fin WORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : Word T) : w = #v[w[0], w[1], w[2], w[3]] := ext_cases rfl rfl rfl rfl

lemma eq_pointwise {w w' : Word T} : (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ↔ w = w' := by
   constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `Word`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : Word T → Prop}
    (mk : ∀ x1 x2 x3 x4 : T, C #v[x1, x2, x3, x4]) (w : Word T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U64

/-- `isU64 w` means that each limb of the `Word` is properly bounded. -/
def isU64 (w : Word (Fin KB)) : Prop := ∀ i : Fin WORD_SIZE, w[i].val < 2 ^ 16

/-- Polymorphic counterpart of `Word.isU64` over `Word (ZMod p)`. Used by
`SP1Constraint.toProp_poly` (sub-phase B.4 of the field-genericization
effort, `docs/FIELD_GENERIC.md`). The Fin-KB-typed `isU64` above is kept
load-bearing for the ~50 internal Word.lean lemmas that the 2026-04-26
parametric lift attempt revealed. At `p := KB`, `ZMod KB = Fin KB`
definitionally, so `isU64_poly` and `isU64` agree on the same value. -/
def isU64_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : Prop :=
  ∀ i : Fin WORD_SIZE, w[i].val < 2 ^ 16

@[aesop unsafe apply]
lemma isU64_of_cases {w : Word (Fin KB)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16)
    (h2 : w[2].val < 2 ^ 16) (h3 : w[3].val < 2 ^ 16) : w.isU64
  := by intro i; fin_cases i <;> simpa

/-- Polymorphic counterpart of `isU64_of_cases`. -/
@[aesop unsafe apply]
lemma isU64_of_cases_poly {p : ℕ} [NeZero p] {w : Word (ZMod p)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16)
    (h2 : w[2].val < 2 ^ 16) (h3 : w[3].val < 2 ^ 16) : w.isU64_poly
  := by intro i; fin_cases i <;> simpa [isU64_poly]

/-- Pull in bounds on a word's limbs given a `isU64` proof. -/
@[aesop unsafe forward, grind →]
lemma lt_cases_of_isU64 {w : Word (Fin KB)} (hw : w.isU64) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 ∧ w[2].val < 2 ^ 16 ∧ w[3].val < 2 ^ 16 :=
  ⟨hw 0, hw 1, hw 2, hw 3⟩

/-- Polymorphic counterpart of `lt_cases_of_isU64`. -/
@[aesop unsafe forward, grind →]
lemma lt_cases_of_isU64_poly {p : ℕ} [NeZero p] {w : Word (ZMod p)} (hw : w.isU64_poly) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 ∧ w[2].val < 2 ^ 16 ∧ w[3].val < 2 ^ 16 :=
  ⟨hw 0, hw 1, hw 2, hw 3⟩

@[simp] -- common enough to want a lemma
lemma four_isU64 : Word.isU64 #v[4, 0, 0, 0] := by aesop

end U64

section conversions

opaque toNat_aux : { f : Word (Fin KB) → ℕ //
    ∀ w, f w = w[0] + w[1] * 2 ^ 16 + w[2] * 2 ^ 32 + w[3] * 2 ^ 48 } :=
  ⟨fun w => w[0] + w[1] * 2 ^ 16 + w[2] * 2 ^ 32 + w[3] * 2 ^ 48, fun _ => rfl⟩

@[simp] lemma toNat_aux_def (w : Word (Fin KB)) : toNat_aux.1 w =
    w[0] + w[1] * 2 ^ 16 + w[2] * 2 ^ 32 + w[3] * 2 ^ 48 := toNat_aux.2 w

/-- Convert a `Word` to a `Nat` by shifting and adding the limbs. -/
def toNat (w : Word (Fin KB)) : ℕ := toNat_aux.1 w --w[0] + w[1] * 2 ^ 16 + w[2] * 2 ^ 32 + w[3] * 2 ^ 48

-- /-- Convert a `Word` to a `Nat` by shifting and adding the limbs. -/
-- def toNat (w : Word (Fin KB)) : ℕ := w[0] + w[1] * 2 ^ 16 + w[2] * 2 ^ 32 + w[3] * 2 ^ 48

/-- Polymorphic counterpart of `Word.toNat` over `Word (ZMod p)`. Companion
to `isU64_poly`; used by `SP1Constraint.toStateProp_poly`. Defined
directly (without the `toNat_aux` opaque wrapper) since the polymorphic
proof obligations live at the operation iff layer, where the unfolded
form is preferred. -/
def toNat_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 16 + w[2].val * 2 ^ 32 + w[3].val * 2 ^ 48

@[aesop unsafe forward]
lemma toNat_def (w : Word (Fin KB)) : w.toNat = w[0] + w[1] * 2 ^ 16 + w[2] * 2 ^ 32 + w[3] * 2 ^ 48 :=
  toNat_aux.2 w

/-- Polymorphic counterpart of `toNat_def`. The polymorphic `toNat_poly` is
defined directly (no opaque wrapper), so this is `rfl`. -/
lemma toNat_poly_def {p : ℕ} [NeZero p] (w : Word (ZMod p)) :
    w.toNat_poly = w[0].val + w[1].val * 2 ^ 16 + w[2].val * 2 ^ 32 + w[3].val * 2 ^ 48 := rfl

lemma toNat_lt_of_isU64 {w : Word (Fin KB)} (hw : w.isU64) : w.toNat < 2 ^ 64 := by
  unfold Word.toNat
  aesop (add 50% tactic (by omega))

/-- Polymorphic counterpart of `toNat_lt_of_isU64`. -/
lemma toNat_poly_lt_of_isU64_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (hw : w.isU64_poly) : w.toNat_poly < 2 ^ 64 := by
  have := lt_cases_of_isU64_poly hw
  unfold toNat_poly
  omega

lemma eq_toNat_eq {wx wy : Word (Fin KB)} (is64_wx : Word.isU64 wx) (is64_wy : Word.isU64 wy) :
  wx = wy ↔ wx.toNat = wy.toNat := by
  constructor
  · simp_all
  · apply Word.lt_cases_of_isU64 at is64_wx
    apply Word.lt_cases_of_isU64 at is64_wy
    simp [Word.toNat]; intro heq
    rw [← Word.eq_pointwise]
    omega

/-- Polymorphic counterpart of `eq_toNat_eq`. -/
lemma eq_toNat_poly_eq {p : ℕ} [NeZero p] {wx wy : Word (ZMod p)}
    (is64_wx : wx.isU64_poly) (is64_wy : wy.isU64_poly) :
    wx = wy ↔ wx.toNat_poly = wy.toNat_poly := by
  constructor
  · simp_all
  · have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly is64_wx
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly is64_wy
    unfold toNat_poly; intro heq
    rw [← Word.eq_pointwise]
    refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ZMod.val_injective <;> omega

lemma toNat_reconstruct {w : Word (Fin KB)} {x : ℕ} (is64_w : Word.isU64 w) :
  w.toNat = x →
    w = #v[⟨x % 65536, by omega⟩, ⟨x / 65536 % 65536, by omega⟩, ⟨x / 4294967296 % 65536, by omega⟩, ⟨x / 281474976710656 % 65536, by omega⟩ ] := by
  intro toNat; rw [← toNat]; clear toNat
  apply Word.lt_cases_of_isU64 at is64_w
  rw [← Word.eq_pointwise]
  simp_all [Word.toNat, Fin.ext_iff]
  split_ands <;> omega

/-- Polymorphic counterpart of `Word.toNat_reconstruct`. The reconstructed
vector uses `((N : ℕ) : ZMod p)` natural-cast literals instead of the
`Fin KB` `⟨N, _⟩` triples. -/
lemma toNat_reconstruct_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} {x : ℕ} (is64_w : Word.isU64_poly w) :
  w.toNat_poly = x →
    w = #v[((x % 65536 : ℕ) : ZMod p), ((x / 65536 % 65536 : ℕ) : ZMod p),
           ((x / 4294967296 % 65536 : ℕ) : ZMod p),
           ((x / 281474976710656 % 65536 : ℕ) : ZMod p)] := by
  intro toNat; rw [← toNat]; clear toNat
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly is64_w
  have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
  rw [← Word.eq_pointwise]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
               List.getElem_cons_succ] <;>
    apply ZMod.val_injective
  all_goals
    rw [ZMod.val_natCast_of_lt (by omega)]
    unfold toNat_poly
    omega

/-- Convert a `Word` to a `BitVec 64` by shifting and adding the limbs. -/
def toBitVec64 (w : Word (Fin KB)) : BitVec 64 := BitVec.ofNat 64 w.toNat

/-- Polymorphic counterpart of `Word.toBitVec64` over `Word (ZMod p)`.
Companion to `toNat_poly`; used by `SP1Constraint.toStateProp_poly`. -/
def toBitVec64_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 (toNat_poly w)

lemma toBitVec64_toNat {w : Word (Fin KB)} (hw : w.isU64) :
    w.toBitVec64.toNat = w.toNat := by
  simp only [toBitVec64, toNat_def, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU64 hw
  omega

/-- Polymorphic counterpart of `toBitVec64_toNat`. -/
lemma toBitVec64_poly_toNat_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (hw : w.isU64_poly) :
    w.toBitVec64_poly.toNat = w.toNat_poly := by
  simp only [toBitVec64_poly, BitVec.toNat_ofNat, toNat_poly]
  have := lt_cases_of_isU64_poly hw
  omega

/-- A 64-bit integer is negative if its msb equals one -/
@[grind] def isNegative (w : Word (Fin KB)) : Prop := w[3] ≥ 32768
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

/-- Polymorphic counterpart of `isNegative`. -/
@[grind] def isNegative_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : Prop := w[3].val ≥ 32768

instance {p : ℕ} [NeZero p] {w : Word (ZMod p)} : Decidable (isNegative_poly w) := by
  unfold isNegative_poly; infer_instance

lemma isNegative_msb
  {w : Word (Fin KB)}
  (h_w_isU64 : w.isU64) :
    w.isNegative ↔ (w.toBitVec64.msb = true) := by
  have := lt_cases_of_isU64 h_w_isU64
  simp [isNegative, toBitVec64, toNat, BitVec.msb_eq_decide]
  omega

/-- Polymorphic counterpart of `isNegative_msb`. -/
lemma isNegative_poly_msb {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.isNegative_poly ↔ (w.toBitVec64_poly.msb = true) := by
  have := lt_cases_of_isU64_poly h_w_isU64
  simp [isNegative_poly, toBitVec64_poly, toNat_poly, BitVec.msb_eq_decide]
  omega

/-- Obtain the low 32 bits of a `Word` -/
def low (w : Word (Fin KB)) : HWord (Fin KB) := #v[w[0], w[1]]

/-- Polymorphic counterpart of `low`. -/
def low_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : HWord (ZMod p) := #v[w[0], w[1]]

lemma isU64_low_isU32 {w : Word (Fin KB)} (hw : w.isU64) : w.low.isU32 := by aesop

/-- Polymorphic counterpart of `Word.isU64_low_isU32`. -/
lemma isU64_poly_low_poly_isU32_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (hw : w.isU64_poly) : w.low_poly.isU32_poly := by
  have ⟨h0, h1, _, _⟩ := lt_cases_of_isU64_poly hw
  intro i; fin_cases i <;> simp [low_poly, HWord.isU32_poly] <;> assumption

lemma low_toNat (hw : HWord.isU32 #v[b0, b1]) : (Word.toBitVec64 #v[b0, b1, 0, 0]).toNat = HWord.toNat #v[b0, b1] := by
  rw [Word.toBitVec64_toNat]
  · simp [Word.toNat, HWord.toNat]
  · apply HWord.lt_cases_of_isU32 at hw; apply Word.isU64_of_cases <;> simp_all

lemma setWidth_eq_low {w : Word (Fin KB)} (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 w.toBitVec64 = w.low.toBitVec32
  := by
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
    simp [toBitVec64, ← BitVec.toNat_inj, low, Word.toNat, HWord.toBitVec32, HWord.toNat]
    omega

/-- Polymorphic counterpart of `Word.setWidth_eq_low`. -/
lemma setWidth_eq_low_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    BitVec.setWidth 32 w.toBitVec64_poly = w.low_poly.toBitVec32_poly
  := by
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
    simp [toBitVec64_poly, ← BitVec.toNat_inj, low_poly, Word.toNat_poly,
          HWord.toBitVec32_poly, HWord.toNat_poly]
    omega

/-- Obtain the high 32 bits of a `Word` -/
def high (w : Word (Fin KB)) : HWord (Fin KB) := #v[w[2], w[3]]

/-- Polymorphic counterpart of `high`. -/
def high_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : HWord (ZMod p) := #v[w[2], w[3]]

lemma isU64_high_isU32 {w : Word (Fin KB)} (hw : w.isU64) : w.high.isU32 := by aesop

/-- Polymorphic counterpart of `Word.isU64_high_isU32`. -/
lemma isU64_poly_high_poly_isU32_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (hw : w.isU64_poly) : w.high_poly.isU32_poly := by
  have ⟨_, _, h2, h3⟩ := lt_cases_of_isU64_poly hw
  intro i; fin_cases i <;> simp [high_poly, HWord.isU32_poly] <;> assumption

lemma setWidth_rshift_eq_high {w : Word (Fin KB)} (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 (w.toBitVec64 >>> 32) = w.high.toBitVec32
  := by
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
    simp_all [toBitVec64, ← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow, high, Word.toNat, HWord.toBitVec32, HWord.toNat]
    omega

/-- Polymorphic counterpart of `Word.setWidth_rshift_eq_high`. -/
lemma setWidth_rshift_eq_high_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    BitVec.setWidth 32 (w.toBitVec64_poly >>> 32) = w.high_poly.toBitVec32_poly
  := by
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
    simp_all [toBitVec64_poly, ← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow,
              high_poly, Word.toNat_poly, HWord.toBitVec32_poly, HWord.toNat_poly]
    omega

/-- Convert a `Word` to a `BitVec 64` by shifting and adding the limbs, supplying a proof . -/
def toBitVec64LT {w : Word (Fin KB)} (h_w : w.isU64) : BitVec 64 :=
  BitVec.ofNatLT w.toNat (by
    simp [Word.toNat]
    have := h_w 0
    have := h_w 1
    have := h_w 2
    have := h_w 3
    simp at *
    linarith)

/-- Convert a `Word` to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : Word (Fin KB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 64 else w.toNat

/-- Polymorphic counterpart of `Word.toInt`. -/
def toInt_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : ℤ :=
  if (isNegative_poly w) then w.toNat_poly - 2 ^ 64 else w.toNat_poly

lemma eq_toInt_eq {wx wy : Word (Fin KB)} (is64_wx : Word.isU64 wx) (is64_wy : Word.isU64 wy) :
  wx = wy ↔ wx.toInt = wy.toInt := by
  constructor
  · simp_all
  · apply Word.lt_cases_of_isU64 at is64_wx
    apply Word.lt_cases_of_isU64 at is64_wy
    simp only [Word.toInt, Word.isNegative, Word.toNat_def]; intro heq
    rw [← Word.eq_pointwise]
    omega

/-- Polymorphic counterpart of `Word.eq_toInt_eq`. -/
lemma eq_toInt_poly_eq {p : ℕ} [NeZero p] {wx wy : Word (ZMod p)}
    (is64_wx : Word.isU64_poly wx) (is64_wy : Word.isU64_poly wy) :
    wx = wy ↔ wx.toInt_poly = wy.toInt_poly := by
  constructor
  · simp_all
  · have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly is64_wx
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly is64_wy
    unfold Word.toInt_poly Word.isNegative_poly Word.toNat_poly; intro heq
    rw [← Word.eq_pointwise]
    refine ⟨?_, ?_, ?_, ?_⟩ <;>
      apply ZMod.val_injective <;>
      (push_cast at heq; split_ifs at heq <;> omega)

lemma toInt_lb {w : Word (Fin KB)} (is_U64_w : w.isU64) :
  -9223372036854775808 ≤ w.toInt := by
  apply Word.lt_cases_of_isU64 at is_U64_w
  simp [Word.toInt, Word.isNegative, Word.toNat] at *
  omega

/-- Polymorphic counterpart of `Word.toInt_lb`. -/
lemma toInt_poly_lb {p : ℕ} [NeZero p] {w : Word (ZMod p)} (is_U64_w : w.isU64_poly) :
  -9223372036854775808 ≤ w.toInt_poly := by
  have ⟨h0, h1, h2, h3⟩ := lt_cases_of_isU64_poly is_U64_w
  unfold Word.toInt_poly Word.isNegative_poly Word.toNat_poly
  split_ifs <;> push_cast <;> omega

lemma toInt_ub {w : Word (Fin KB)} (is_U64_w : w.isU64) :
  w.toInt < 9223372036854775808 := by
  apply Word.lt_cases_of_isU64 at is_U64_w
  simp [Word.toInt, Word.isNegative, Word.toNat] at *
  omega

/-- Polymorphic counterpart of `Word.toInt_ub`. -/
lemma toInt_poly_ub {p : ℕ} [NeZero p] {w : Word (ZMod p)} (is_U64_w : w.isU64_poly) :
  w.toInt_poly < 9223372036854775808 := by
  have ⟨h0, h1, h2, h3⟩ := lt_cases_of_isU64_poly is_U64_w
  unfold Word.toInt_poly Word.isNegative_poly Word.toNat_poly
  split_ifs <;> push_cast <;> omega

lemma isU64_toInt {w : Word (Fin KB)} (is64_w : Word.isU64 w) : - 2 ^ 63 ≤ w.toInt ∧ w.toInt < 2 ^ 63 := by
  unfold Word.toInt Word.isNegative Word.toNat
  grind

/-- Polymorphic counterpart of `Word.isU64_toInt`. -/
lemma isU64_poly_toInt_poly {p : ℕ} [NeZero p] {w : Word (ZMod p)}
    (is64_w : Word.isU64_poly w) :
    - 2 ^ 63 ≤ w.toInt_poly ∧ w.toInt_poly < 2 ^ 63 := by
  have ⟨h0, h1, h2, h3⟩ := lt_cases_of_isU64_poly is64_w
  unfold Word.toInt_poly Word.isNegative_poly Word.toNat_poly
  split_ifs <;> push_cast <;> omega

lemma toBitVec64_toInt {w : Word (Fin KB)} (h_w_isU64 : w.isU64) :
    w.toBitVec64.toInt = w.toInt
  := by
    rw [BitVec.toInt, Word.toInt]
    split_ifs <;>
    rw [isNegative_msb h_w_isU64] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec64_toNat h_w_isU64] at * <;>
    omega

/-- Polymorphic counterpart of `toBitVec64_toInt`. -/
lemma toBitVec64_poly_toInt_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.toBitVec64_poly.toInt = w.toInt_poly
  := by
    rw [BitVec.toInt, Word.toInt_poly]
    split_ifs <;>
    rw [isNegative_poly_msb h_w_isU64] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec64_poly_toNat_poly h_w_isU64] at * <;>
    omega

lemma isNegative_toInt {w : Word (Fin KB)} (is64_w : Word.isU64 w) :
  w.isNegative ↔ w.toInt < 0
    := by
  unfold Word.toInt Word.isNegative Word.toNat
  grind

/-- Polymorphic counterpart of `Word.isNegative_toInt`. -/
lemma isNegative_poly_toInt_poly {p : ℕ} [NeZero p] {w : Word (ZMod p)}
    (is64_w : Word.isU64_poly w) :
    w.isNegative_poly ↔ w.toInt_poly < 0 := by
  have ⟨h0, h1, h2, h3⟩ := lt_cases_of_isU64_poly is64_w
  unfold Word.toInt_poly Word.isNegative_poly Word.toNat_poly
  split_ifs <;> push_cast <;> omega

lemma toInt_nneg_reconstruct {w : Word (Fin KB)} {x : ℤ} (is64_w : Word.isU64 w) (nneg : 0 ≤ x) :
  w.toInt = x →
    w = #v[⟨x.toNat % 65536, by omega⟩, ⟨x.toNat / 65536 % 65536, by omega⟩, ⟨x.toNat / 4294967296 % 65536, by omega⟩, ⟨x.toNat / 281474976710656 % 65536, by omega⟩ ] := by
  intro toInt; rw [← toInt]
  have nneg : ¬ w.isNegative := by rw [isNegative_toInt is64_w]; omega
  apply Word.lt_cases_of_isU64 at is64_w
  rw [← Word.eq_pointwise]
  simp_all [Word.toInt, Word.toNat, Fin.ext_iff]
  split_ands <;> omega

lemma sign_cases {w : Word (Fin KB)} (is64_w : Word.isU64 w) : w.toInt.sign = if w.isNegative then -1 else if w.toInt = 0 then 0 else 1 := by
  simp [Word.isNegative_toInt is64_w]
  exact Int.sign_cases w.toInt

/-- Polymorphic counterpart of `Word.sign_cases`. -/
lemma sign_cases_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (is64_w : Word.isU64_poly w) :
    w.toInt_poly.sign = if w.isNegative_poly then -1 else if w.toInt_poly = 0 then 0 else 1 := by
  simp [Word.isNegative_poly_toInt_poly is64_w]
  exact Int.sign_cases w.toInt_poly

end conversions

end Word

namespace DWord

/-- Prove two `DWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : DWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1])
    (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3])
    (h4 : w[4] = w'[4]) (h5 : w[5] = w'[5])
    (h6 : w[6] = w'[6]) (h7 : w[7] = w'[7]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3
  | 4, _ => h4 | 5, _ => h5 | 6, _ => h6 | 7, _ => h7
  | n + 8, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `DWord`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : DWord T}
    (h : ∀ i : Fin DWORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : DWord T) : w = #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]] := ext_cases rfl rfl rfl rfl rfl rfl rfl rfl

lemma eq_pointwise {w w' : DWord T} : (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ∧ (w[4] = w'[4]) ∧ (w[5] = w'[5]) ∧ (w[6] = w'[6]) ∧ (w[7] = w'[7]) ↔ w = w' := by
   constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `DWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : DWord T → Prop}
    (mk : ∀ x1 x2 x3 x4 x5 x6 x7 x8 : T, C #v[x1, x2, x3, x4, x5, x6, x7, x8]) (w : DWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U128

/-- `is128 w` means that each limb of the `DWord` is properly bounded. -/
def isU128 (w : DWord (Fin KB)) : Prop := ∀ i : Fin DWORD_SIZE, w[i].val < 2 ^ 16

/-- Polymorphic counterpart of `DWord.isU128`. -/
def isU128_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : Prop :=
  ∀ i : Fin DWORD_SIZE, w[i].val < 2 ^ 16

@[aesop unsafe apply]
lemma isU128_of_cases {w : DWord (Fin KB)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16)
    (h2 : w[2].val < 2 ^ 16) (h3 : w[3].val < 2 ^ 16)
    (h4 : w[4].val < 2 ^ 16) (h5 : w[5].val < 2 ^ 16)
    (h6 : w[6].val < 2 ^ 16) (h7 : w[7].val < 2 ^ 16) : w.isU128
  := by intro i; fin_cases i <;> simpa

/-- Polymorphic counterpart of `DWord.isU128_of_cases`. -/
@[aesop unsafe apply]
lemma isU128_of_cases_poly {p : ℕ} [NeZero p] {w : DWord (ZMod p)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16)
    (h2 : w[2].val < 2 ^ 16) (h3 : w[3].val < 2 ^ 16)
    (h4 : w[4].val < 2 ^ 16) (h5 : w[5].val < 2 ^ 16)
    (h6 : w[6].val < 2 ^ 16) (h7 : w[7].val < 2 ^ 16) : w.isU128_poly
  := by intro i; fin_cases i <;> simpa [isU128_poly]

/-- Pull in bounds on a word's limbs given a `isU128` proof. -/
@[aesop unsafe forward, grind →]
lemma lt_cases_of_isU128 {w : DWord (Fin KB)} (hw : w.isU128) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 ∧ w[2].val < 2 ^ 16 ∧ w[3].val < 2 ^ 16 ∧
    w[4].val < 2 ^ 16 ∧ w[5].val < 2 ^ 16 ∧ w[6].val < 2 ^ 16 ∧ w[7].val < 2 ^ 16 :=
  ⟨hw 0, hw 1, hw 2, hw 3, hw 4, hw 5, hw 6, hw 7⟩

/-- Polymorphic counterpart of `lt_cases_of_isU128`. -/
@[aesop unsafe forward, grind →]
lemma lt_cases_of_isU128_poly {p : ℕ} [NeZero p] {w : DWord (ZMod p)} (hw : w.isU128_poly) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 ∧ w[2].val < 2 ^ 16 ∧ w[3].val < 2 ^ 16 ∧
    w[4].val < 2 ^ 16 ∧ w[5].val < 2 ^ 16 ∧ w[6].val < 2 ^ 16 ∧ w[7].val < 2 ^ 16 :=
  ⟨hw 0, hw 1, hw 2, hw 3, hw 4, hw 5, hw 6, hw 7⟩

end U128

section conversions

/-- Convert a `DWord` to a `Nat` by shifting and adding the limbs. -/
@[aesop unsafe forward]
def toNat (w : DWord (Fin KB)) : ℕ := w[0] + w[1] * 2 ^ 16 + w[2] * 2 ^ 32 + w[3] * 2 ^ 48 + w[4] * 2 ^ 64 + w[5] * 2 ^ 80 + w[6] * 2 ^ 96 + w[7] * 2 ^ 112

/-- Polymorphic counterpart of `DWord.toNat`. -/
@[aesop unsafe forward]
def toNat_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 16 + w[2].val * 2 ^ 32 + w[3].val * 2 ^ 48 +
  w[4].val * 2 ^ 64 + w[5].val * 2 ^ 80 + w[6].val * 2 ^ 96 + w[7].val * 2 ^ 112

lemma eq_toNat_eq {wx wy : DWord (Fin KB)} (is128_wx : DWord.isU128 wx) (is128_wy : DWord.isU128 wy) :
  wx = wy ↔ wx.toNat = wy.toNat := by
  constructor
  · simp_all
  · apply DWord.lt_cases_of_isU128 at is128_wx
    apply DWord.lt_cases_of_isU128 at is128_wy
    unfold DWord.toNat; intro heq
    rw [← DWord.eq_pointwise]
    omega

/-- Convert a `DWord` to a `BitVec 128` by shifting and adding the limbs. -/
def toBitVec128 (w : DWord (Fin KB)) : BitVec 128 := BitVec.ofNat 128 w.toNat

/-- Polymorphic counterpart of `DWord.toBitVec128`. -/
def toBitVec128_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : BitVec 128 :=
  BitVec.ofNat 128 (toNat_poly w)

lemma toBitVec128_toNat {w : DWord (Fin KB)} (hw : w.isU128) :
    w.toBitVec128.toNat = w.toNat := by
  simp only [toBitVec128, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU128 hw
  omega

/-- Polymorphic counterpart of `DWord.toBitVec128_toNat`. -/
lemma toBitVec128_poly_toNat_poly {p : ℕ} [NeZero p]
    {w : DWord (ZMod p)} (hw : w.isU128_poly) :
    w.toBitVec128_poly.toNat = w.toNat_poly := by
  simp only [DWord.toBitVec128_poly, BitVec.toNat_ofNat, toNat_poly]
  have := lt_cases_of_isU128_poly hw
  omega

/-- A 128-bit integer is negative if its msb equals one -/
@[grind] def isNegative (w : DWord (Fin KB)) : Prop := w[7] ≥ 32768
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

/-- Polymorphic counterpart of `DWord.isNegative`. -/
@[grind] def isNegative_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : Prop := w[7].val ≥ 32768

instance {p : ℕ} [NeZero p] {w : DWord (ZMod p)} : Decidable (isNegative_poly w) := by
  unfold isNegative_poly; infer_instance

lemma isNegative_msb
  {w : DWord (Fin KB)}
  (h_w_isU128 : w.isU128) :
    w.isNegative ↔ (w.toBitVec128.msb = true) := by
  have := lt_cases_of_isU128 h_w_isU128
  simp [isNegative, toBitVec128, toNat, BitVec.msb_eq_decide]
  omega

/-- Polymorphic counterpart of `DWord.isNegative_msb`. -/
lemma isNegative_poly_msb {p : ℕ} [NeZero p]
    {w : DWord (ZMod p)} (h_w_isU128 : w.isU128_poly) :
    w.isNegative_poly ↔ (w.toBitVec128_poly.msb = true) := by
  have := lt_cases_of_isU128_poly h_w_isU128
  simp [isNegative_poly, toBitVec128_poly, toNat_poly, BitVec.msb_eq_decide]
  omega

/-- Obtain the low 64 bits of a `DWord` -/
def low (w : DWord (Fin KB)) : Word (Fin KB) := #v[w[0], w[1], w[2], w[3]]

/-- Polymorphic counterpart of `DWord.low`. -/
def low_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : Word (ZMod p) :=
  #v[w[0], w[1], w[2], w[3]]

lemma isU128_low_isU64 {w : DWord (Fin KB)} (hw : w.isU128) : w.low.isU64 := by aesop

lemma setWidth_eq_low {w : DWord (Fin KB)} (h_w_isU64 : w.isU128) :
    BitVec.setWidth 64 w.toBitVec128 = w.low.toBitVec64
  := by
    have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU128 h_w_isU64
    simp [toBitVec128, ← BitVec.toNat_inj, low, DWord.toNat, Word.toBitVec64, Word.toNat]
    omega

/-- Obtain the high 64 bits of a `DWord` -/
def high (w : DWord (Fin KB)) : Word (Fin KB) := #v[w[4], w[5], w[6], w[7]]

/-- Polymorphic counterpart of `DWord.high`. -/
def high_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : Word (ZMod p) :=
  #v[w[4], w[5], w[6], w[7]]

lemma isU128_high_isU32 {w : DWord (Fin KB)} (hw : w.isU128) : w.high.isU64 := by aesop

lemma setWidth_rshift_eq_high {w : DWord (Fin KB)} (h_w_isU128 : w.isU128) :
    BitVec.setWidth 64 (w.toBitVec128 >>> 64) = w.high.toBitVec64
  := by
    have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU128 h_w_isU128
    simp_all [toBitVec128, ← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow, high, DWord.toNat, Word.toBitVec64, Word.toNat]
    omega

/-- Convert a `DWord` to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : DWord (Fin KB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 128 else w.toNat

/-- Polymorphic counterpart of `DWord.toInt`. -/
def toInt_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : ℤ :=
  if (isNegative_poly w) then w.toNat_poly - 2 ^ 128 else w.toNat_poly

lemma eq_toInt_eq {wx wy : DWord (Fin KB)} (is128_wx : DWord.isU128 wx) (is128_wy : DWord.isU128 wy) :
  wx = wy ↔ wx.toInt = wy.toInt := by
  constructor
  · simp_all
  · apply DWord.lt_cases_of_isU128 at is128_wx
    apply DWord.lt_cases_of_isU128 at is128_wy
    unfold DWord.toInt DWord.isNegative DWord.toNat; intro heq
    rw [← DWord.eq_pointwise]
    omega

/-- Polymorphic counterpart of `DWord.eq_toInt_eq`. -/
lemma eq_toInt_poly_eq {p : ℕ} [NeZero p] {wx wy : DWord (ZMod p)}
    (is128_wx : DWord.isU128_poly wx) (is128_wy : DWord.isU128_poly wy) :
    wx = wy ↔ wx.toInt_poly = wy.toInt_poly := by
  constructor
  · simp_all
  · have ⟨_, _, _, _, _, _, _, _⟩ := DWord.lt_cases_of_isU128_poly is128_wx
    have ⟨_, _, _, _, _, _, _, _⟩ := DWord.lt_cases_of_isU128_poly is128_wy
    unfold DWord.toInt_poly DWord.isNegative_poly DWord.toNat_poly; intro heq
    rw [← DWord.eq_pointwise]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      apply ZMod.val_injective <;>
      (push_cast at heq; split_ifs at heq <;> omega)

lemma isU128_toInt {w : DWord (Fin KB)} (is128_w : DWord.isU128 w) : - 2 ^ 127 ≤ w.toInt ∧ w.toInt < 2 ^ 127 := by
  unfold DWord.toInt DWord.isNegative DWord.toNat
  apply DWord.lt_cases_of_isU128 at is128_w
  omega

/-- Polymorphic counterpart of `DWord.isU128_toInt`. -/
lemma isU128_poly_toInt_poly {p : ℕ} [NeZero p] {w : DWord (ZMod p)}
    (is128_w : DWord.isU128_poly w) :
    - 2 ^ 127 ≤ w.toInt_poly ∧ w.toInt_poly < 2 ^ 127 := by
  have := DWord.lt_cases_of_isU128_poly is128_w
  unfold DWord.toInt_poly DWord.isNegative_poly DWord.toNat_poly
  split_ifs <;> push_cast <;> omega

lemma toBitVec128_toInt {w : DWord (Fin KB)} (h_w_isU128 : w.isU128) :
    w.toBitVec128.toInt = w.toInt
  := by
    rw [BitVec.toInt, DWord.toInt]
    split_ifs <;>
    rw [isNegative_msb h_w_isU128] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec128_toNat h_w_isU128] at * <;>
    omega

/-- Polymorphic counterpart of `DWord.toBitVec128_toInt`. -/
lemma toBitVec128_poly_toInt_poly {p : ℕ} [NeZero p]
    {w : DWord (ZMod p)} (h_w_isU128 : w.isU128_poly) :
    w.toBitVec128_poly.toInt = w.toInt_poly
  := by
    rw [BitVec.toInt, DWord.toInt_poly]
    split_ifs <;>
    rw [isNegative_poly_msb h_w_isU128] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec128_poly_toNat_poly h_w_isU128] at * <;>
    omega

lemma isNegative_toInt {w : DWord (Fin KB)} (is128_w : DWord.isU128 w) :
  w.isNegative ↔ w.toInt < 0
    := by
  unfold DWord.toInt DWord.isNegative DWord.toNat
  apply DWord.lt_cases_of_isU128 at is128_w
  omega

/-- Polymorphic counterpart of `DWord.isNegative_toInt`. -/
lemma isNegative_poly_toInt_poly {p : ℕ} [NeZero p] {w : DWord (ZMod p)}
    (is128_w : DWord.isU128_poly w) :
    w.isNegative_poly ↔ w.toInt_poly < 0 := by
  have := DWord.lt_cases_of_isU128_poly is128_w
  unfold DWord.toInt_poly DWord.isNegative_poly DWord.toNat_poly
  split_ifs <;> push_cast <;> omega

lemma sign_cases {w : DWord (Fin KB)} (is128_w : DWord.isU128 w) : w.toInt.sign = if w.isNegative then -1 else if w.toInt = 0 then 0 else 1 := by
  simp [DWord.isNegative_toInt is128_w]
  exact Int.sign_cases w.toInt

/-- Polymorphic counterpart of `DWord.sign_cases`. -/
lemma sign_cases_poly {p : ℕ} [NeZero p]
    {w : DWord (ZMod p)} (is128_w : DWord.isU128_poly w) :
    w.toInt_poly.sign = if w.isNegative_poly then -1 else if w.toInt_poly = 0 then 0 else 1 := by
  simp [DWord.isNegative_poly_toInt_poly is128_w]
  exact Int.sign_cases w.toInt_poly

end conversions

end DWord

namespace BHWord

/-- Prove two `BHWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : BHWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3
  | n + 4, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `BHWord`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : BHWord T}
    (h : ∀ i : Fin BYTE_HWORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : BHWord T) : w = #v[w[0], w[1], w[2], w[3]]
  := ext_cases rfl rfl rfl rfl

lemma eq_pointwise {w w' : BHWord T} :
    (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ↔ w = w' := by
  constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `BHWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : BHWord T → Prop}
    (mk : ∀ x0 x1 x2 x3 : T, C #v[x0, x1, x2, x3]) (w : BHWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U32

/-- `isU32 w` means that each limb of the word is properly bounded. -/
def isU32 (w : BHWord (Fin KB)) : Prop := ∀ i : Fin BYTE_HWORD_SIZE, w[i].val < 256

/-- Polymorphic counterpart of `BHWord.isU32`. -/
def isU32_poly {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : Prop :=
  ∀ i : Fin BYTE_HWORD_SIZE, w[i].val < 256

@[aesop unsafe apply]
lemma isU32_of_cases {w : BHWord (Fin KB)}
    (h0 : w[0].val < 256) (h1 : w[1].val < 256)
    (h2 : w[2].val < 256) (h3 : w[3].val < 256) : w.isU32
  := by intro i; fin_cases i <;> simpa

/-- Polymorphic counterpart of `BHWord.isU32_of_cases`. -/
@[aesop unsafe apply]
lemma isU32_of_cases_poly {p : ℕ} [NeZero p] {w : BHWord (ZMod p)}
    (h0 : w[0].val < 256) (h1 : w[1].val < 256)
    (h2 : w[2].val < 256) (h3 : w[3].val < 256) : w.isU32_poly
  := by intro i; fin_cases i <;> simpa [isU32_poly]

/-- Pull in bounds on a `BHWord`s limbs given a `isU32` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU32 {w : BHWord (Fin KB)} (hbhw : w.isU32) :
    w[0].val < 256 ∧ w[1].val < 256 ∧ w[2].val < 256 ∧ w[3].val < 256
    :=
  ⟨hbhw 0, hbhw 1, hbhw 2, hbhw 3⟩

/-- Polymorphic counterpart of `BHWord.lt_cases_of_isU32`. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU32_poly {p : ℕ} [NeZero p] {w : BHWord (ZMod p)} (hbhw : w.isU32_poly) :
    w[0].val < 256 ∧ w[1].val < 256 ∧ w[2].val < 256 ∧ w[3].val < 256
    :=
  ⟨hbhw 0, hbhw 1, hbhw 2, hbhw 3⟩

end U32

section conversions

/-- Convert a `BHWord` to a `Nat` by shifting and adding the limbs. -/
def toNat (w : BHWord (Fin KB)) : ℕ :=
  w[0] + w[1] * 2 ^ 8 + w[2] * 2 ^ 16 + w[3] * 2 ^ 24

/-- Polymorphic counterpart of `BHWord.toNat`. -/
def toNat_poly {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 8 + w[2].val * 2 ^ 16 + w[3].val * 2 ^ 24

lemma toNat_lt_of_isU32 {w : BHWord (Fin KB)} (hw : w.isU32) : w.toNat < 2 ^ 32 := by
  unfold toNat
  aesop (add 50% tactic (by omega))

/-- Polymorphic counterpart of `BHWord.toNat_lt_of_isU32`. -/
lemma toNat_poly_lt_of_isU32_poly {p : ℕ} [NeZero p]
    {w : BHWord (ZMod p)} (hw : w.isU32_poly) : w.toNat_poly < 2 ^ 32 := by
  have := lt_cases_of_isU32_poly hw
  unfold toNat_poly
  omega

/-- Convert a `BHWord` to a `BitVec 32` by shifting and adding the limbs. -/
def toBitVec32 (w : BHWord (Fin KB)) : BitVec 32 := BitVec.ofNat 32 w.toNat

/-- Polymorphic counterpart of `BHWord.toBitVec32`. -/
def toBitVec32_poly {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : BitVec 32 :=
  BitVec.ofNat 32 (toNat_poly w)

lemma toBitVec32_toNat {w : BHWord (Fin KB)} (hw : w.isU32) :
    w.toBitVec32.toNat = w.toNat := by
  simp only [toBitVec32, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU32 hw
  omega

/-- Polymorphic counterpart of `BHWord.toBitVec32_toNat`. -/
lemma toBitVec32_poly_toNat_poly {p : ℕ} [NeZero p]
    {w : BHWord (ZMod p)} (hw : w.isU32_poly) :
    w.toBitVec32_poly.toNat = w.toNat_poly := by
  simp only [toBitVec32_poly, BitVec.toNat_ofNat, toNat_poly]
  have := lt_cases_of_isU32_poly hw
  omega

/-- A 32-bit integer is negative if its msb equals one -/
@[grind] def isNegative (w : BHWord (Fin KB)) : Prop := w[3] ≥ 128
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

/-- Polymorphic counterpart of `BHWord.isNegative`. -/
@[grind] def isNegative_poly {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : Prop := w[3].val ≥ 128

instance {p : ℕ} [NeZero p] {w : BHWord (ZMod p)} : Decidable (isNegative_poly w) := by
  unfold isNegative_poly; infer_instance

lemma isNegative_msb
  {w : BHWord (Fin KB)}
  (h_w_isU32 : w.isU32) :
    w.isNegative ↔ (w.toBitVec32.msb = true) := by
  have := lt_cases_of_isU32 h_w_isU32
  simp [isNegative, BHWord.toBitVec32, BHWord.toNat, BitVec.msb_eq_decide]
  omega

/-- Polymorphic counterpart of `BHWord.isNegative_msb`. -/
lemma isNegative_poly_msb {p : ℕ} [NeZero p]
    {w : BHWord (ZMod p)} (h_w_isU32 : w.isU32_poly) :
    w.isNegative_poly ↔ (w.toBitVec32_poly.msb = true) := by
  have := lt_cases_of_isU32_poly h_w_isU32
  simp [isNegative_poly, BHWord.toBitVec32_poly, BHWord.toNat_poly, BitVec.msb_eq_decide]
  omega

lemma isNegative_BitVec.toInt
  {w : BHWord (Fin KB)}
  (h_w_isU32 : w.isU32) :
    w.isNegative ↔ ¬ 2 * w.toNat < 2 ^ 32 := by
  rw [isNegative_msb h_w_isU32]
  simp [BitVec.msb_eq_decide]
  rw [toBitVec32_toNat h_w_isU32]
  omega

/-- Polymorphic counterpart of `BHWord.isNegative_BitVec.toInt`. -/
lemma isNegative_poly_BitVec.toInt
  {p : ℕ} [NeZero p]
  {w : BHWord (ZMod p)}
  (h_w_isU32 : w.isU32_poly) :
    w.isNegative_poly ↔ ¬ 2 * w.toNat_poly < 2 ^ 32 := by
  rw [isNegative_poly_msb h_w_isU32]
  simp [BitVec.msb_eq_decide]
  rw [toBitVec32_poly_toNat_poly h_w_isU32]
  omega

/-- Convert a `BHWord` to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : BHWord (Fin KB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 32 else w.toNat

/-- Polymorphic counterpart of `BHWord.toInt`. -/
def toInt_poly {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : ℤ :=
  if (isNegative_poly w) then w.toNat_poly - 2 ^ 32 else w.toNat_poly

lemma toBitVec32_toInt {w : BHWord (Fin KB)} (h_w_isU32 : w.isU32) :
    w.toBitVec32.toInt = w.toInt
  := by
    have := lt_cases_of_isU32 h_w_isU32
    have : w.toNat < 2 ^ 32 := by unfold BHWord.toNat; omega
    simp_all [toBitVec32, toInt, BitVec.toInt]
    split_ifs <;> rw [isNegative_BitVec.toInt h_w_isU32] at * <;> omega

/-- Polymorphic counterpart of `BHWord.toBitVec32_toInt`. -/
lemma toBitVec32_poly_toInt_poly {p : ℕ} [NeZero p]
    {w : BHWord (ZMod p)} (h_w_isU32 : w.isU32_poly) :
    w.toBitVec32_poly.toInt = w.toInt_poly
  := by
    have := lt_cases_of_isU32_poly h_w_isU32
    have : w.toNat_poly < 2 ^ 32 := toNat_poly_lt_of_isU32_poly h_w_isU32
    simp_all [toBitVec32_poly, toInt_poly, BitVec.toInt]
    split_ifs <;> rw [isNegative_poly_BitVec.toInt h_w_isU32] at * <;> omega

end conversions

end BHWord

namespace BWord

/-- Prove two `BWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : BWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3])
    (h4 : w[4] = w'[4]) (h5 : w[5] = w'[5]) (h6 : w[6] = w'[6]) (h7 : w[7] = w'[7]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3 | 4, _ => h4 | 5, _ => h5 | 6, _ => h6 | 7, _ => h7
  | n + 8, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `BWord`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : BWord T}
    (h : ∀ i : Fin BYTE_WORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : BWord T) : w = #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]] := ext_cases rfl rfl rfl rfl rfl rfl rfl rfl

lemma eq_pointwise {w w' : BWord T} :
    (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ∧
    (w[4] = w'[4]) ∧ (w[5] = w'[5]) ∧ (w[6] = w'[6]) ∧ (w[7] = w'[7]) ↔ w = w' := by
  constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `BWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : BWord T → Prop}
    (mk : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : T, C #v[x0, x1, x2, x3, x4, x5, x6, x7]) (w : BWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U64

/-- `isU64 w` means that each limb of the `BWord` is properly bounded. -/
def isU64 (w : BWord (Fin KB)) : Prop := ∀ i : Fin BYTE_WORD_SIZE, w[i].val < 2 ^ 8

/-- Polymorphic counterpart of `BWord.isU64`. -/
def isU64_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : Prop :=
  ∀ i : Fin BYTE_WORD_SIZE, w[i].val < 2 ^ 8

@[aesop unsafe apply]
lemma isU64_of_cases {w : BWord (Fin KB)}
    (h0 : w[0].val < 2 ^ 8) (h1 : w[1].val < 2 ^ 8)
    (h2 : w[2].val < 2 ^ 8) (h3 : w[3].val < 2 ^ 8)
    (h4 : w[4].val < 2 ^ 8) (h5 : w[5].val < 2 ^ 8)
    (h6 : w[6].val < 2 ^ 8) (h7 : w[7].val < 2 ^ 8) : w.isU64
  := by intro i; fin_cases i <;> simpa

/-- Polymorphic counterpart of `BWord.isU64_of_cases`. -/
@[aesop unsafe apply]
lemma isU64_of_cases_poly {p : ℕ} [NeZero p] {w : BWord (ZMod p)}
    (h0 : w[0].val < 2 ^ 8) (h1 : w[1].val < 2 ^ 8)
    (h2 : w[2].val < 2 ^ 8) (h3 : w[3].val < 2 ^ 8)
    (h4 : w[4].val < 2 ^ 8) (h5 : w[5].val < 2 ^ 8)
    (h6 : w[6].val < 2 ^ 8) (h7 : w[7].val < 2 ^ 8) : w.isU64_poly
  := by intro i; fin_cases i <;> simpa [isU64_poly]

/-- Pull in bounds on a `BWord`'s limbs given a `isU64` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU64 {w : BWord (Fin KB)} (hbw : w.isU64) :
    w[0].val < 2 ^ 8 ∧ w[1].val < 2 ^ 8 ∧ w[2].val < 2 ^ 8 ∧ w[3].val < 2 ^ 8 ∧
    w[4].val < 2 ^ 8 ∧ w[5].val < 2 ^ 8 ∧ w[6].val < 2 ^ 8 ∧ w[7].val < 2 ^ 8 :=
  ⟨hbw 0, hbw 1, hbw 2, hbw 3, hbw 4, hbw 5, hbw 6, hbw 7⟩

/-- Polymorphic counterpart of `BWord.lt_cases_of_isU64`. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU64_poly {p : ℕ} [NeZero p] {w : BWord (ZMod p)} (hbw : w.isU64_poly) :
    w[0].val < 2 ^ 8 ∧ w[1].val < 2 ^ 8 ∧ w[2].val < 2 ^ 8 ∧ w[3].val < 2 ^ 8 ∧
    w[4].val < 2 ^ 8 ∧ w[5].val < 2 ^ 8 ∧ w[6].val < 2 ^ 8 ∧ w[7].val < 2 ^ 8 :=
  ⟨hbw 0, hbw 1, hbw 2, hbw 3, hbw 4, hbw 5, hbw 6, hbw 7⟩

end U64

section conversions

/-- Convert a `BWord` to a `Word` by combining the limbs. -/
def toWord (w : BWord (Fin KB)) : Word (Fin KB) :=
  #v[w[0] + w[1] * 256, w[2] + w[3] * 256, w[4] + w[5] * 256, w[6] + w[7] * 256]

/-- Polymorphic counterpart of `BWord.toWord`. The body only uses ring
operations and `OfNat`, so `[CommRing F]` is sufficient — no `Field`
hypothesis needed. -/
def toWord_poly {F : Type} [CommRing F] (w : BWord F) : Word F :=
  #v[w[0] + w[1] * 256, w[2] + w[3] * 256, w[4] + w[5] * 256, w[6] + w[7] * 256]

/-- Convert a `BWord` to a `Nat` by shifting and adding the limbs. -/
def toNat (w : BWord (Fin KB)) : ℕ := w[0] + w[1] * 2 ^ 8 + w[2] * 2 ^ 16 + w[3] * 2 ^ 24 + w[4] * 2 ^ 32 + w[5] * 2 ^ 40 + w[6] * 2 ^ 48 + w[7] * 2 ^ 56

/-- Polymorphic counterpart of `BWord.toNat`. -/
def toNat_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 8 + w[2].val * 2 ^ 16 + w[3].val * 2 ^ 24 +
  w[4].val * 2 ^ 32 + w[5].val * 2 ^ 40 + w[6].val * 2 ^ 48 + w[7].val * 2 ^ 56

lemma toNat_toWord
  {w : BWord (Fin KB)}
  (h_w_isU64 : w.isU64) :
    w.toNat = Word.toNat (w.toWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [toNat, toWord, Word.toNat]
  simp [Fin.add_def, Fin.mul_def]
  omega

/-- Helper: `(a + b * 256).val = a.val + b.val * 256` when `a.val, b.val < 2^8`,
under `[Fact (2^17 < p)]`. The byte-pair packing primitive used by
`toNat_poly_toWord_poly`, `toWord_poly_U64_poly`, and downstream lemmas. -/
private lemma val_byte_combine {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (a b : ZMod p) (ha : a.val < 2 ^ 8) (hb : b.val < 2 ^ 8) :
    (a + b * 256).val = a.val + b.val * 256 := by
  have h256 : (256 : ZMod p).val = 256 := val_256_zmod_p
  have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
  have hbm : (b * 256).val = b.val * 256 := by
    rw [ZMod.val_mul_of_lt]
    · rw [h256]
    · rw [h256]; omega
  rw [ZMod.val_add_of_lt, hbm]
  · rw [hbm]; omega

/-- Polymorphic counterpart of `BWord.toNat_toWord`. -/
lemma toNat_poly_toWord_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.toNat_poly = Word.toNat_poly (w.toWord_poly) := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
  simp only [BWord.toNat_poly, BWord.toWord_poly, Word.toNat_poly_def,
             Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ]
  rw [val_byte_combine, val_byte_combine, val_byte_combine, val_byte_combine] <;> omega

lemma toWord_U64 {w : BWord (Fin KB)} (h_w_isU64 : w.isU64) : w.toWord.isU64
  := by
    have := lt_cases_of_isU64 h_w_isU64
    simp [toWord]
    apply Word.isU64_of_cases <;> simp <;> grind

/-- Polymorphic counterpart of `BWord.toWord_U64`. -/
lemma toWord_poly_U64_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.toWord_poly.isU64_poly := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
  simp only [toWord_poly]
  apply Word.isU64_of_cases_poly
  all_goals
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
               List.getElem_cons_succ]
    rw [val_byte_combine] <;> omega

/-- Convert a `BWord` to a `BitVec 64` by shifting and adding the limbs. -/
def toBitVec64 (w : BWord (Fin KB)) : BitVec 64 := BitVec.ofNat 64 w.toNat

/-- Polymorphic counterpart of `BWord.toBitVec64`. -/
def toBitVec64_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 (toNat_poly w)

lemma toBitVec64_toNat {w : BWord (Fin KB)} (hw : w.isU64) :
    w.toBitVec64.toNat = w.toNat := by
  simp only [toBitVec64, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU64 hw
  omega

/-- Polymorphic counterpart of `BWord.toBitVec64_toNat`. -/
lemma toBitVec64_poly_toNat_poly {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (hw : w.isU64_poly) :
    w.toBitVec64_poly.toNat = w.toNat_poly := by
  simp only [BWord.toBitVec64_poly, BitVec.toNat_ofNat, toNat_poly]
  have := lt_cases_of_isU64_poly hw
  omega

lemma toWord_toBitVec64 {w : BWord (Fin KB)} (h_w_isU64 : w.isU64) :
    w.toWord.toBitVec64 = w.toBitVec64
  := by
    have := lt_cases_of_isU64 h_w_isU64
    rw [← BitVec.toNat_inj]
    simp [BWord.toBitVec64, Word.toBitVec64]; congr
    simp [BWord.toWord, Word.toNat, BWord.toNat]
    grind

/-- Polymorphic counterpart of `BWord.toWord_toBitVec64`. -/
lemma toWord_poly_toBitVec64_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.toWord_poly.toBitVec64_poly = w.toBitVec64_poly := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
  rw [← BitVec.toNat_inj]
  rw [Word.toBitVec64_poly_toNat_poly (toWord_poly_U64_poly h_w_isU64)]
  rw [BWord.toBitVec64_poly_toNat_poly h_w_isU64]
  rw [toNat_poly_toWord_poly h_w_isU64]

/-- A 64-bit integer is negative if its msb equals one -/
@[grind] def isNegative (w : BWord (Fin KB)) : Prop := w[7] ≥ 128
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

/-- Polymorphic counterpart of `BWord.isNegative`. -/
@[grind] def isNegative_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : Prop := w[7].val ≥ 128

instance {p : ℕ} [NeZero p] {w : BWord (ZMod p)} : Decidable (isNegative_poly w) := by
  unfold isNegative_poly; infer_instance

lemma isNegative_toWord
  {w : BWord (Fin KB)}
  (h_w_isU64 : w.isU64) :
    w.isNegative ↔ Word.isNegative (w.toWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [isNegative, Word.isNegative, toWord]
  grind

lemma isNegative_msb
  {w : BWord (Fin KB)}
  (h_w_isU64 : w.isU64) :
    w.isNegative ↔ (w.toBitVec64.msb = true) := by
  have := lt_cases_of_isU64 h_w_isU64
  simp [isNegative, BWord.toBitVec64, BWord.toNat, BitVec.msb_eq_decide]
  omega

/-- Polymorphic counterpart of `BWord.isNegative_msb`. -/
lemma isNegative_poly_msb {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.isNegative_poly ↔ (w.toBitVec64_poly.msb = true) := by
  have := lt_cases_of_isU64_poly h_w_isU64
  simp [isNegative_poly, BWord.toBitVec64_poly, BWord.toNat_poly, BitVec.msb_eq_decide]
  omega

/-- Convert a `BWord` to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : BWord (Fin KB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 64 else w.toNat

/-- Polymorphic counterpart of `BWord.toInt`. -/
def toInt_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : ℤ :=
  if (isNegative_poly w) then w.toNat_poly - 2 ^ 64 else w.toNat_poly

lemma toInt_toWord
  {w : BWord (Fin KB)}
  (h_w_isU64 : w.isU64) :
    w.toInt = Word.toInt (w.toWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [toWord, toInt, toNat, Word.toInt, Word.toNat, isNegative, Word.isNegative]
  simp [Fin.le_def, Fin.add_def, Fin.mul_def]
  omega

lemma toBitVec64_toInt {w : BWord (Fin KB)} (h_w_isU64 : w.isU64) :
    w.toBitVec64.toInt = w.toInt
  := by
    rw [BitVec.toInt, BWord.toInt]
    split_ifs <;>
    rw [isNegative_msb h_w_isU64] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec64_toNat h_w_isU64] at * <;>
    omega

/-- Polymorphic counterpart of `BWord.toBitVec64_toInt`. -/
lemma toBitVec64_poly_toInt_poly {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.toBitVec64_poly.toInt = w.toInt_poly
  := by
    rw [BitVec.toInt, BWord.toInt_poly]
    split_ifs <;>
    rw [isNegative_poly_msb h_w_isU64] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec64_poly_toNat_poly h_w_isU64] at * <;>
    omega

/-- Obtain the low 32 bits of a `BWord` -/
def low (w : BWord (Fin KB)) : BHWord (Fin KB) := #v[w[0], w[1], w[2], w[3]]

/-- Polymorphic counterpart of `BWord.low`. -/
def low_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : BHWord (ZMod p) :=
  #v[w[0], w[1], w[2], w[3]]

lemma isU64_low_isU32 {w : BWord (Fin KB)} (hw : w.isU64) : w.low.isU32 := by aesop

/-- Polymorphic counterpart of `BWord.isU64_low_isU32`. -/
lemma isU64_low_isU32_poly {p : ℕ} [NeZero p] {w : BWord (ZMod p)}
    (hw : w.isU64_poly) : w.low_poly.isU32_poly := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly hw
  apply BHWord.isU32_of_cases_poly <;> simp [low_poly] <;> omega

lemma setWidth_eq_low {w : BWord (Fin KB)} (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 w.toBitVec64 = w.low.toBitVec32
  := by
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
    simp [toBitVec64, ← BitVec.toNat_inj, low, BWord.toNat, BHWord.toBitVec32, BHWord.toNat]
    omega

/-- Polymorphic counterpart of `BWord.setWidth_eq_low`. -/
lemma setWidth_eq_low_poly {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    BitVec.setWidth 32 w.toBitVec64_poly = w.low_poly.toBitVec32_poly := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
  simp [toBitVec64_poly, ← BitVec.toNat_inj, low_poly,
        BWord.toNat_poly, BHWord.toBitVec32_poly, BHWord.toNat_poly]
  omega

/-- Obtain the high 32 bits of a `BWord` -/
def high (w : BWord (Fin KB)) : BHWord (Fin KB) := #v[w[4], w[5], w[6], w[7]]

/-- Polymorphic counterpart of `BWord.high`. -/
def high_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : BHWord (ZMod p) :=
  #v[w[4], w[5], w[6], w[7]]

lemma isU64_high_isU32 {w : BWord (Fin KB)} (hw : w.isU64) : w.high.isU32 := by aesop

/-- Polymorphic counterpart of `BWord.isU64_high_isU32`. -/
lemma isU64_high_isU32_poly {p : ℕ} [NeZero p] {w : BWord (ZMod p)}
    (hw : w.isU64_poly) : w.high_poly.isU32_poly := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly hw
  apply BHWord.isU32_of_cases_poly <;> simp [high_poly] <;> omega

lemma setWidth_rshift_eq_high {w : BWord (Fin KB)} (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 (w.toBitVec64 >>> 32) = w.high.toBitVec32
  := by
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64 h_w_isU64
    simp_all [toBitVec64, ← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow, high, BWord.toNat, BHWord.toBitVec32, BHWord.toNat]
    omega

/-- Polymorphic counterpart of `BWord.setWidth_rshift_eq_high`. -/
lemma setWidth_rshift_eq_high_poly {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    BitVec.setWidth 32 (w.toBitVec64_poly >>> 32) = w.high_poly.toBitVec32_poly := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
  simp_all [toBitVec64_poly, ← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow,
            high_poly, BWord.toNat_poly, BHWord.toBitVec32_poly, BHWord.toNat_poly]
  omega

end conversions

end BWord

namespace BDWord

/-- Prove two `BDWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : BDWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3])
    (h4 : w[4] = w'[4]) (h5 : w[5] = w'[5]) (h6 : w[6] = w'[6]) (h7 : w[7] = w'[7])
    (h8 : w[8] = w'[8]) (h9 : w[9] = w'[9]) (h10 : w[10] = w'[10]) (h11 : w[11] = w'[11])
    (h12 : w[12] = w'[12]) (h13 : w[13] = w'[13]) (h14 : w[14] = w'[14]) (h15 : w[15] = w'[15]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3 | 4, _ => h4 | 5, _ => h5 | 6, _ => h6 | 7, _ => h7
  | 8, _ => h8 | 9, _ => h9 | 10, _ => h10 | 11, _ => h11 | 12, _ => h12 | 13, _ => h13 | 14, _ => h14 | 15, _ => h15
  | n + 16, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `BDWord`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : BDWord T}
    (h : ∀ i : Fin BYTE_DWORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : BDWord T) : w = #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]]
  := ext_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

lemma eq_pointwise {w w' : BDWord T} :
    (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ∧
    (w[4] = w'[4]) ∧ (w[5] = w'[5]) ∧ (w[6] = w'[6]) ∧ (w[7] = w'[7]) ∧
    (w[8] = w'[8]) ∧ (w[9] = w'[9]) ∧ (w[10] = w'[10]) ∧ (w[11] = w'[11]) ∧
    (w[12] = w'[12]) ∧ (w[13] = w'[13]) ∧ (w[14] = w'[14]) ∧ (w[15] = w'[15])
    ↔ w = w' := by
  constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `BDWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : BDWord T → Prop}
    (mk : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : T, C #v[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15]) (w : BDWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U128

/-- `isU128 w` means that each limb of the word is properly bounded. -/
def isU128 (w : BDWord (Fin KB)) : Prop := ∀ i : Fin BYTE_DWORD_SIZE, w[i].val < 256

/-- Polymorphic counterpart of `BDWord.isU128`. -/
def isU128_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : Prop :=
  ∀ i : Fin BYTE_DWORD_SIZE, w[i].val < 256

@[aesop unsafe apply]
lemma isU128_of_cases {w : BDWord (Fin KB)}
    (h0 : w[0].val < 256) (h1 : w[1].val < 256)
    (h2 : w[2].val < 256) (h3 : w[3].val < 256)
    (h4 : w[4].val < 256) (h5 : w[5].val < 256)
    (h6 : w[6].val < 256) (h7 : w[7].val < 256)
    (h8 : w[8].val < 256) (h9 : w[9].val < 256)
    (h10 : w[10].val < 256) (h11 : w[11].val < 256)
    (h12 : w[12].val < 256) (h13 : w[13].val < 256)
    (h14 : w[14].val < 256) (h15 : w[15].val < 256) : w.isU128
  := by intro i; fin_cases i <;> simpa

/-- Polymorphic counterpart of `BDWord.isU128_of_cases`. -/
@[aesop unsafe apply]
lemma isU128_of_cases_poly {p : ℕ} [NeZero p] {w : BDWord (ZMod p)}
    (h0 : w[0].val < 256) (h1 : w[1].val < 256)
    (h2 : w[2].val < 256) (h3 : w[3].val < 256)
    (h4 : w[4].val < 256) (h5 : w[5].val < 256)
    (h6 : w[6].val < 256) (h7 : w[7].val < 256)
    (h8 : w[8].val < 256) (h9 : w[9].val < 256)
    (h10 : w[10].val < 256) (h11 : w[11].val < 256)
    (h12 : w[12].val < 256) (h13 : w[13].val < 256)
    (h14 : w[14].val < 256) (h15 : w[15].val < 256) : w.isU128_poly
  := by intro i; fin_cases i <;> simpa [isU128_poly]

/-- Pull in bounds on a bytedword's limbs given a `isU128` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU128 {w : BDWord (Fin KB)} (hbdw : w.isU128) :
    w[0].val < 256 ∧ w[1].val < 256 ∧ w[2].val < 256 ∧ w[3].val < 256 ∧
    w[4].val < 256 ∧ w[5].val < 256 ∧ w[6].val < 256 ∧ w[7].val < 256 ∧
    w[8].val < 256 ∧ w[9].val < 256 ∧ w[10].val < 256 ∧ w[11].val < 256 ∧
    w[12].val < 256 ∧ w[13].val < 256 ∧ w[14].val < 256 ∧ w[15].val < 256
    :=
  ⟨hbdw 0, hbdw 1, hbdw 2, hbdw 3, hbdw 4, hbdw 5, hbdw 6, hbdw 7, hbdw 8, hbdw 9, hbdw 10, hbdw 11, hbdw 12, hbdw 13, hbdw 14, hbdw 15⟩

/-- Polymorphic counterpart of `BDWord.lt_cases_of_isU128`. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU128_poly {p : ℕ} [NeZero p] {w : BDWord (ZMod p)} (hbdw : w.isU128_poly) :
    w[0].val < 256 ∧ w[1].val < 256 ∧ w[2].val < 256 ∧ w[3].val < 256 ∧
    w[4].val < 256 ∧ w[5].val < 256 ∧ w[6].val < 256 ∧ w[7].val < 256 ∧
    w[8].val < 256 ∧ w[9].val < 256 ∧ w[10].val < 256 ∧ w[11].val < 256 ∧
    w[12].val < 256 ∧ w[13].val < 256 ∧ w[14].val < 256 ∧ w[15].val < 256
    :=
  ⟨hbdw 0, hbdw 1, hbdw 2, hbdw 3, hbdw 4, hbdw 5, hbdw 6, hbdw 7, hbdw 8, hbdw 9, hbdw 10, hbdw 11, hbdw 12, hbdw 13, hbdw 14, hbdw 15⟩

end U128

section conversions

/-- Obtain the low 64 bits of a `BDWord` -/
def low (w : BDWord (Fin KB)) : BWord (Fin KB) := #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]]

/-- Polymorphic counterpart of `BDWord.low`. -/
def low_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : BWord (ZMod p) :=
  #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]]

lemma isU128_low_isU64 {w : BDWord (Fin KB)} (hw : w.isU128) : w.low.isU64 := by aesop

/-- Polymorphic counterpart of `BDWord.isU128_low_isU64`. -/
lemma isU128_poly_low_poly_isU64_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (hw : w.isU128_poly) : w.low_poly.isU64_poly := by
  have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := lt_cases_of_isU128_poly hw
  intro i; fin_cases i <;> simp [low_poly, BWord.isU64_poly] <;> omega

/-- Obtain the high 64 bits of a `BDWord` -/
def high (w : BDWord (Fin KB)) : BWord (Fin KB) := #v[w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]]

/-- Polymorphic counterpart of `BDWord.high`. -/
def high_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : BWord (ZMod p) :=
  #v[w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]]

lemma isU128_high_isU64 {w : BDWord (Fin KB)} (hw : w.isU128) : w.high.isU64 := by aesop

/-- Polymorphic counterpart of `BDWord.isU128_high_isU64`. -/
lemma isU128_poly_high_poly_isU64_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (hw : w.isU128_poly) : w.high_poly.isU64_poly := by
  have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := lt_cases_of_isU128_poly hw
  intro i; fin_cases i <;> simp [high_poly, BWord.isU64_poly] <;> omega

/-- Convert a bytedword to a `Nat` by shifting and adding the limbs. -/
def toNat (w : BDWord (Fin KB)) : ℕ :=
  w[0] + w[1] * 2 ^ 8 + w[2] * 2 ^ 16 + w[3] * 2 ^ 24 + w[4] * 2 ^ 32 + w[5] * 2 ^ 40 + w[6] * 2 ^ 48 + w[7] * 2 ^ 56 +
  w[8] * 2 ^ 64 + w[9] * 2 ^ 72 + w[10] * 2 ^ 80 + w[11] * 2 ^ 88 + w[12] * 2 ^ 96 + w[13] * 2 ^ 104 + w[14] * 2 ^ 112 + w[15] * 2 ^ 120

/-- Polymorphic counterpart of `BDWord.toNat`. -/
def toNat_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 8 + w[2].val * 2 ^ 16 + w[3].val * 2 ^ 24 +
  w[4].val * 2 ^ 32 + w[5].val * 2 ^ 40 + w[6].val * 2 ^ 48 + w[7].val * 2 ^ 56 +
  w[8].val * 2 ^ 64 + w[9].val * 2 ^ 72 + w[10].val * 2 ^ 80 + w[11].val * 2 ^ 88 +
  w[12].val * 2 ^ 96 + w[13].val * 2 ^ 104 + w[14].val * 2 ^ 112 + w[15].val * 2 ^ 120

lemma toNat_lt_of_isU128 {w : BDWord (Fin KB)} (hw : w.isU128) : w.toNat < 2 ^ 128 := by
  unfold toNat
  aesop (add 50% tactic (by omega))

/-- Polymorphic counterpart of `BDWord.toNat_lt_of_isU128`. -/
lemma toNat_poly_lt_of_isU128_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (hw : w.isU128_poly) : w.toNat_poly < 2 ^ 128 := by
  have := lt_cases_of_isU128_poly hw
  unfold toNat_poly
  omega

/-- Convert a bytedword to a `BitVec 128` by shifting and adding the limbs. -/
def toBitVec128 (w : BDWord (Fin KB)) : BitVec 128 := BitVec.ofNat 128 w.toNat

/-- Polymorphic counterpart of `BDWord.toBitVec128`. -/
def toBitVec128_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : BitVec 128 :=
  BitVec.ofNat 128 (toNat_poly w)

lemma toBitVec128_toNat {w : BDWord (Fin KB)} (hw : w.isU128) :
    w.toBitVec128.toNat = w.toNat := by
  simp only [toBitVec128, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU128 hw
  omega

/-- Polymorphic counterpart of `BDWord.toBitVec128_toNat`. -/
lemma toBitVec128_poly_toNat_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (hw : w.isU128_poly) :
    w.toBitVec128_poly.toNat = w.toNat_poly := by
  simp only [BDWord.toBitVec128_poly, BitVec.toNat_ofNat, toNat_poly]
  have := lt_cases_of_isU128_poly hw
  omega

/-- A 128-bit integer is negative if its msb equals one -/
@[grind] def isNegative (w : BDWord (Fin KB)) : Prop := w[15] ≥ 128
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

/-- Polymorphic counterpart of `BDWord.isNegative`. -/
@[grind] def isNegative_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : Prop := w[15].val ≥ 128

instance {p : ℕ} [NeZero p] {w : BDWord (ZMod p)} : Decidable (isNegative_poly w) := by
  unfold isNegative_poly; infer_instance

lemma isNegative_msb
  {w : BDWord (Fin KB)}
  (h_w_isU128 : w.isU128) :
    w.isNegative ↔ (w.toBitVec128.msb = true) := by
  have := lt_cases_of_isU128 h_w_isU128
  simp [isNegative, BDWord.toBitVec128, BDWord.toNat, BitVec.msb_eq_decide]
  omega

/-- Polymorphic counterpart of `BDWord.isNegative_msb`. -/
lemma isNegative_poly_msb {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (h_w_isU128 : w.isU128_poly) :
    w.isNegative_poly ↔ (w.toBitVec128_poly.msb = true) := by
  have := lt_cases_of_isU128_poly h_w_isU128
  simp [isNegative_poly, BDWord.toBitVec128_poly, BDWord.toNat_poly, BitVec.msb_eq_decide]
  omega

lemma isNegative_BitVec.toInt
  {w : BDWord (Fin KB)}
  (h_w_isU128 : w.isU128) :
    w.isNegative ↔ ¬ 2 * w.toNat < 2 ^ 128 := by
  rw [isNegative_msb h_w_isU128]
  simp [BitVec.msb_eq_decide]
  rw [toBitVec128_toNat h_w_isU128]
  omega

/-- Polymorphic counterpart of `BDWord.isNegative_BitVec.toInt`. -/
lemma isNegative_poly_BitVec.toInt
  {p : ℕ} [NeZero p]
  {w : BDWord (ZMod p)}
  (h_w_isU128 : w.isU128_poly) :
    w.isNegative_poly ↔ ¬ 2 * w.toNat_poly < 2 ^ 128 := by
  rw [isNegative_poly_msb h_w_isU128]
  simp [BitVec.msb_eq_decide]
  rw [toBitVec128_poly_toNat_poly h_w_isU128]
  omega

/-- Convert a bytedword to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : BDWord (Fin KB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 128 else w.toNat

/-- Polymorphic counterpart of `BDWord.toInt`. -/
def toInt_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : ℤ :=
  if (isNegative_poly w) then w.toNat_poly - 2 ^ 128 else w.toNat_poly

set_option maxRecDepth 200000
lemma toBitVec128_toInt {w : BDWord (Fin KB)} (h_w_isU128 : w.isU128) :
    w.toBitVec128.toInt = w.toInt
  := by
    have := lt_cases_of_isU128 h_w_isU128
    have : w.toNat < 2 ^ 128 := by unfold BDWord.toNat; omega
    simp_all [toBitVec128, toInt, BitVec.toInt]
    split_ifs <;> rw [isNegative_BitVec.toInt h_w_isU128] at * <;> omega

set_option maxRecDepth 200000 in
-- Polymorphic counterpart of `BDWord.toBitVec128_toInt`.
lemma toBitVec128_poly_toInt_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (h_w_isU128 : w.isU128_poly) :
    w.toBitVec128_poly.toInt = w.toInt_poly
  := by
    have := lt_cases_of_isU128_poly h_w_isU128
    have : w.toNat_poly < 2 ^ 128 := toNat_poly_lt_of_isU128_poly h_w_isU128
    simp_all [toBitVec128_poly, toInt_poly, BitVec.toInt]
    split_ifs <;> rw [isNegative_poly_BitVec.toInt h_w_isU128] at * <;> omega

lemma low_as_extract {w : BDWord (Fin KB)} (h_w_isU128 : w.isU128) :
  (w.low).toBitVec64 = BitVec.extractLsb 63 0 (w.toBitVec128) := by
  have ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ := lt_cases_of_isU128 h_w_isU128
  simp [BDWord.low, BWord.toBitVec64, BDWord.toBitVec128]
  simp [← BitVec.toNat_inj, BWord.toNat, BDWord.toNat]
  omega

/-- Polymorphic counterpart of `BDWord.low_as_extract`. -/
lemma low_as_extract_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (h_w_isU128 : w.isU128_poly) :
    (w.low_poly).toBitVec64_poly = BitVec.extractLsb 63 0 (w.toBitVec128_poly) := by
  have ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ :=
    lt_cases_of_isU128_poly h_w_isU128
  simp [BDWord.low_poly, BWord.toBitVec64_poly, BDWord.toBitVec128_poly]
  simp [← BitVec.toNat_inj, BWord.toNat_poly, BDWord.toNat_poly]
  omega

lemma high_as_extract {w : BDWord (Fin KB)} (h_w_isU128 : w.isU128) :
  (w.high).toBitVec64 = BitVec.extractLsb 127 64 (w.toBitVec128) := by
  have ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ := lt_cases_of_isU128 h_w_isU128
  simp [BDWord.high, BWord.toBitVec64, BDWord.toBitVec128]
  simp [← BitVec.toNat_inj, BWord.toNat, BDWord.toNat]
  omega

/-- Polymorphic counterpart of `BDWord.high_as_extract`. -/
lemma high_as_extract_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (h_w_isU128 : w.isU128_poly) :
    (w.high_poly).toBitVec64_poly = BitVec.extractLsb 127 64 (w.toBitVec128_poly) := by
  have ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ :=
    lt_cases_of_isU128_poly h_w_isU128
  simp [BDWord.high_poly, BWord.toBitVec64_poly, BDWord.toBitVec128_poly]
  simp [← BitVec.toNat_inj, BWord.toNat_poly, BDWord.toNat_poly]
  omega

end conversions

end BDWord

namespace HWord

lemma sign_extend_32_to_64_msb {w : HWord (Fin KB)} :
  w.isU32 →
  BitVec.signExtend 64 w.toBitVec32 = Word.toBitVec64 #v[w[0], w[1], if w.toBitVec32.msb = true then 65535 else 0, if w.toBitVec32.msb = true then 65535 else 0]
    := by
  let sw : Word (Fin KB) := #v[w[0], w[1], if w.toBitVec32.msb = true then 65535 else 0, if w.toBitVec32.msb = true then 65535 else 0]
  intro is_U32_w
  have is_U64_sw : Word.isU64 sw := by
    have := w.lt_cases_of_isU32 is_U32_w
    subst sw; apply Word.isU64_of_cases <;> split_ifs <;> simp_all
  have is_neg : w.isNegative ↔ sw.isNegative := by
    subst sw
    simp [isNegative, Word.isNegative]
    split_ifs with h_neg <;>
    rw [← isNegative_msb] at h_neg <;>
    simp [isNegative] at h_neg <;>
    omega
  rw [← BitVec.toInt_inj]
  simp [BitVec.toInt_signExtend_of_le]
  rw [toBitVec32_toInt is_U32_w, Word.toBitVec64_toInt is_U64_sw]
  simp [toInt, Word.toInt]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, HWord.toNat, Word.toNat] <;>
  rw [isNegative_msb] at * <;>
  simp_all; omega

/-- Sign-extension to 64 bits -/
def extend (w : HWord (Fin KB)) (sgn : Bool) : Word (Fin KB) :=
  let ext := (if sgn then (if w.isNegative then (1 : Fin KB) else 0) else 0) * 65535
  #v[w[0], w[1], ext, ext]

lemma extend_U32_U64 {w : HWord (Fin KB)} (is_U32_w : w.isU32) (sgn : Bool) : (w.extend sgn).isU64 := by
  have := lt_cases_of_isU32 is_U32_w
  apply Word.isU64_of_cases <;>
  simp [extend] <;> (try split_ifs) <;> omega

lemma extend_true_is_signExtend {w : HWord (Fin KB)} :
  w.isU32 →
  (w.extend true).toBitVec64 = BitVec.signExtend 64 w.toBitVec32
    := by
  set sw := extend w true
  intro is_U32_w
  have is_U64_hw : sw.isU64 := by
    have := lt_cases_of_isU32 is_U32_w
    subst sw; simp [extend]
    apply Word.isU64_of_cases <;> split_ifs <;> simp_all
  have is_neg : w.isNegative ↔ sw.isNegative := by
    subst sw
    simp [extend, isNegative, Word.isNegative]
    aesop
  rw [← BitVec.toInt_inj]
  simp [BitVec.toInt_signExtend_of_le]
  rw [toBitVec32_toInt is_U32_w, Word.toBitVec64_toInt is_U64_hw]
  rw [toInt, Word.toInt]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, extend, Word.toNat, HWord.toNat] <;>
  simp_all; omega

lemma extend_false_is_setWidth {w : HWord (Fin KB)} :
  w.isU32 →
  (w.extend false).toBitVec64 = BitVec.setWidth 64 w.toBitVec32
    := by
  set sw := extend w false
  intro is_U32_w
  have is_U64_hw : sw.isU64 := by
    have := lt_cases_of_isU32 is_U32_w
    subst sw; simp [extend]
    apply Word.isU64_of_cases <;> split_ifs <;> simp_all
  rw [← BitVec.toNat_inj]
  rw [Word.toBitVec64_toNat is_U64_hw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [HWord.toBitVec32_toNat is_U32_w]
  simp [sw, Word.toNat, extend, HWord.toNat]

end HWord

namespace Word

/-- Convert a word to a `BWord` by separating the limbs. -/
def toBWord (w : Word (Fin KB)) : BWord (Fin KB) :=
  #v[w[0] % 256, w[0] / 256, w[1] % 256, w[1] / 256, w[2] % 256, w[2] / 256, w[3] % 256, w[3] / 256 ]

lemma toBWord_toU64
  {w : Word (Fin KB)}
  (h_w_isU64 : w.isU64) :
    w.toBWord.isU64 := by
  simp [Word.toBWord]
  apply Word.lt_cases_of_isU64 at h_w_isU64
  apply BWord.isU64_of_cases <;> simp <;> omega

lemma toNat_toBWord
  {w : Word (Fin KB)}
  (h_w_isU64 : w.isU64) :
    w.toNat = BWord.toNat (w.toBWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [toNat, toBWord, BWord.toNat]
  omega

lemma isNegative_toBWord
  {w : Word (Fin KB)}
  (h_w_isU64 : w.isU64) :
    w.isNegative ↔ BWord.isNegative (w.toBWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [isNegative, BWord.isNegative, toBWord, Fin.le_def]
  omega

lemma toInt_toBWord
  {w : Word (Fin KB)}
  (h_w_isU64 : w.isU64) :
    w.toInt = BWord.toInt (w.toBWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [toBWord, toInt, toNat, BWord.toInt, BWord.toNat, isNegative, BWord.isNegative, Fin.le_def]
  omega

lemma toBitVec64_toBWord
  {w : Word (Fin KB)}
  (h_w_isU64 : w.isU64) :
    w.toBWord.toBitVec64 = w.toBitVec64 := by
  rw [← BitVec.toNat_inj, BWord.toBitVec64_toNat (by apply toBWord_toU64 h_w_isU64), Word.toBitVec64_toNat h_w_isU64, Word.toNat_toBWord h_w_isU64]

/-- Polymorphic counterpart of `Word.toBWord`. Decomposes each 16-bit limb
into low/high bytes via `.val`-level arithmetic (since `/` on `ZMod p` is
field-division, not byte-extraction). -/
def toBWord_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : BWord (ZMod p) :=
  #v[((w[0].val % 256 : ℕ) : ZMod p), ((w[0].val / 256 : ℕ) : ZMod p),
     ((w[1].val % 256 : ℕ) : ZMod p), ((w[1].val / 256 : ℕ) : ZMod p),
     ((w[2].val % 256 : ℕ) : ZMod p), ((w[2].val / 256 : ℕ) : ZMod p),
     ((w[3].val % 256 : ℕ) : ZMod p), ((w[3].val / 256 : ℕ) : ZMod p)]

/-- Polymorphic counterpart of `Word.toBWord_toU64`. -/
lemma toBWord_poly_toU64 {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.toBWord_poly.isU64_poly := by
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
  have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
  apply BWord.isU64_of_cases_poly <;> simp [toBWord_poly] <;>
    (rw [Nat.mod_eq_of_lt (show _ < p by omega)]; omega)

/-- Polymorphic counterpart of `Word.toNat_toBWord`. -/
lemma toNat_poly_toBWord_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.toNat_poly = BWord.toNat_poly (w.toBWord_poly) := by
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
  have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
  simp only [toNat_poly_def, toBWord_poly, BWord.toNat_poly]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ]
  repeat rw [ZMod.val_natCast_of_lt (show _ < p by omega)]
  omega

/-- Polymorphic counterpart of `Word.isNegative_toBWord`. -/
lemma isNegative_poly_toBWord_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.isNegative_poly ↔ BWord.isNegative_poly (w.toBWord_poly) := by
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
  have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
  simp only [isNegative_poly, BWord.isNegative_poly, toBWord_poly]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
             List.getElem_cons_succ]
  rw [ZMod.val_natCast_of_lt (show w[3].val / 256 < p by omega)]
  omega

/-- Polymorphic counterpart of `Word.toBitVec64_toBWord`. -/
lemma toBitVec64_poly_toBWord_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.toBWord_poly.toBitVec64_poly = w.toBitVec64_poly := by
  rw [← BitVec.toNat_inj]
  rw [BWord.toBitVec64_poly_toNat_poly (toBWord_poly_toU64 h_w_isU64)]
  rw [Word.toBitVec64_poly_toNat_poly h_w_isU64]
  rw [toNat_poly_toBWord_poly h_w_isU64]

lemma sign_extend_imm_toBitVec64 {x₀ x₁ x₂ x₃ : Fin KB} {x : ℕ} :
  let imm_x := BitVec.ofNat 12 x
  x < 65536 → isU64 #v[ x₀, x₁, x₂, x₃ ] →
  Word.toBitVec64 #v[ x₀, x₁, x₂, x₃ ] = signExtend 64 imm_x →
    x₀.val = (signExtend 16 imm_x).toNat ∧
    x₁ = (if imm_x.msb = true then 65535 else 0) ∧
    x₂ = (if imm_x.msb = true then 65535 else 0) ∧
    x₃ = (if imm_x.msb = true then 65535 else 0)
  := by
    intro imm_x h_16 h_64 h_eq
    have := lt_cases_of_isU64 h_64
    rw [signExtend, BitVec.toInt] at *
    rw [BitVec.msb_eq_decide] at *
    split_ifs at * <;> simp_all <;> [ omega; skip; skip; omega ]
    · rw [← BitVec.toNat_inj, BitVec.toNat_setWidth, toBitVec64_toNat h_64 ] at h_eq
      simp_all [BitVec.toNat_ofNat, toNat]
      omega
    · rw [← BitVec.toInt_inj, toBitVec64_toInt h_64, toInt] at h_eq
      split_ifs at h_eq with h_neg <;>
      rw [isNegative_msb, BitVec.msb_eq_decide, toBitVec64_toNat h_64] at h_neg <;>
      subst imm_x <;>
      simp_all [BitVec.toNat_ofNat, toNat] <;>
      rw [Int.bmod_def] at h_eq <;>
      omega

/-- Sign-extension to 128 bits -/
def extend (w : Word (Fin KB)) (sgn : Bool) : DWord (Fin KB) :=
  let ext := (if sgn then (if w.isNegative then (1 : Fin KB) else 0) else 0) * 65535
  #v[w[0], w[1], w[2], w[3], ext, ext, ext, ext]

lemma extend_U64_U128 {w : Word (Fin KB)} (is_U64_w : w.isU64) (sgn : Bool) : (w.extend sgn).isU128 := by
  have := lt_cases_of_isU64 is_U64_w
  apply DWord.isU128_of_cases <;>
  simp [extend] <;> (try split_ifs) <;> omega

lemma extend_true_is_signExtend {w : Word (Fin KB)} :
  w.isU64 →
  (w.extend true).toBitVec128 = BitVec.signExtend 128 w.toBitVec64
    := by
  set sw := extend w true
  intro is_U64_w
  have is_U128_bdw : sw.isU128 := by
    have := lt_cases_of_isU64 is_U64_w
    subst sw; simp [extend]
    apply DWord.isU128_of_cases <;> split_ifs <;> simp_all
  have is_neg : w.isNegative ↔ sw.isNegative := by
    subst sw
    simp [extend, isNegative, DWord.isNegative]
    aesop
  rw [← BitVec.toInt_inj]
  simp [BitVec.toInt_signExtend_of_le]
  rw [toBitVec64_toInt is_U64_w, DWord.toBitVec128_toInt is_U128_bdw]
  rw [toInt, DWord.toInt]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, extend, DWord.toNat, Word.toNat] <;>
  simp_all; omega

lemma extend_false_is_setWidth {w : Word (Fin KB)} :
  w.isU64 →
  (w.extend false).toBitVec128 = BitVec.setWidth 128 w.toBitVec64
    := by
  set sw := extend w false
  intro is_U64_w
  have is_U128_bdw : sw.isU128 := by
    have := lt_cases_of_isU64 is_U64_w
    subst sw; simp [extend]
    apply DWord.isU128_of_cases <;> split_ifs <;> simp_all
  rw [← BitVec.toNat_inj]
  rw [DWord.toBitVec128_toNat is_U128_bdw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [Word.toBitVec64_toNat is_U64_w]
  simp [sw, DWord.toNat, extend, Word.toNat]

/-- Polymorphic counterpart of `Word.extend`. -/
def extend_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) (sgn : Bool) : DWord (ZMod p) :=
  let ext := (if sgn then (if w.isNegative_poly then (1 : ZMod p) else 0) else 0) * 65535
  #v[w[0], w[1], w[2], w[3], ext, ext, ext, ext]

/-- Polymorphic counterpart of `Word.extend_U64_U128`. -/
lemma extend_U64_U128_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} (is_U64_w : w.isU64_poly) (sgn : Bool) :
    (w.extend_poly sgn).isU128_poly := by
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly is_U64_w
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (65535 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  apply DWord.isU128_of_cases_poly <;>
    simp [extend_poly] <;> (try split_ifs) <;>
    (try simp [h65535, h0]) <;> omega

-- Polymorphic counterpart of `Word.extend_true_is_signExtend`. Routes through
-- `BitVec.toInt_signExtend_of_le` (the `Fin KB` siblings' approach) so the
-- proof term never exposes `(... % 2^128).toNat` to kernel re-check. Each ZMod
-- arithmetic step uses `h65535` / `h0` lemmas to keep `ZMod.val` evaluable.
lemma extend_true_is_signExtend_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} :
  w.isU64_poly →
  (w.extend_poly true).toBitVec128_poly = BitVec.signExtend 128 w.toBitVec64_poly
    := by
  set sw := extend_poly w true
  intro is_U64_w
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (65535 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly is_U64_w
  have is_U128_bdw : sw.isU128_poly := by
    subst sw; simp [extend_poly]
    apply DWord.isU128_of_cases_poly <;> split_ifs <;>
      simp [h65535, h0] <;> omega
  have is_neg : w.isNegative_poly ↔ sw.isNegative_poly := by
    subst sw
    simp [extend_poly, isNegative_poly, DWord.isNegative_poly]
    by_cases h : 32768 ≤ w[3].val <;> simp [h, h65535, h0]
  rw [← BitVec.toInt_inj]
  simp [BitVec.toInt_signExtend_of_le]
  rw [Word.toBitVec64_poly_toInt_poly is_U64_w,
      DWord.toBitVec128_poly_toInt_poly is_U128_bdw]
  rw [Word.toInt_poly, DWord.toInt_poly]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, extend_poly, DWord.toNat_poly, Word.toNat_poly] <;>
  (rename_i h1 h2;
   simp only [h2, ↓reduceIte, ZMod.cast_eq_val, h65535, h0]) <;>
  push_cast <;> omega

/-- Polymorphic counterpart of `Word.extend_false_is_setWidth`. -/
lemma extend_false_is_setWidth_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} :
  w.isU64_poly →
  (w.extend_poly false).toBitVec128_poly = BitVec.setWidth 128 w.toBitVec64_poly
    := by
  set sw := extend_poly w false
  intro is_U64_w
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly is_U64_w
  have is_U128_bdw : sw.isU128_poly := by
    subst sw; simp [extend_poly]
    apply DWord.isU128_of_cases_poly <;> simp <;> omega
  rw [← BitVec.toNat_inj]
  rw [DWord.toBitVec128_poly_toNat_poly is_U128_bdw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [Word.toBitVec64_poly_toNat_poly is_U64_w]
  simp [sw, DWord.toNat_poly, extend_poly, Word.toNat_poly]

end Word

namespace BWord

/-- Sign-extension to 128 bits -/
def extend (w : BWord (Fin KB)) (sgn : Bool) : BDWord (Fin KB) :=
  let ext := (if sgn then (if w.isNegative then (1 : Fin KB) else 0) else 0) * 255
  #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], ext, ext, ext, ext, ext, ext, ext, ext]

lemma extend_U64_U128 {w : BWord (Fin KB)} (is_U64_w : w.isU64) (sgn : Bool) : (w.extend sgn).isU128 := by
  have := lt_cases_of_isU64 is_U64_w
  apply BDWord.isU128_of_cases <;>
  simp [extend] <;> (try split_ifs) <;> omega

lemma extend_true_is_signExtend {w : BWord (Fin KB)} :
  w.isU64 →
  (w.extend true).toBitVec128 = BitVec.signExtend 128 w.toBitVec64
    := by
  set sw := extend w true
  intro is_U64_w
  have is_U128_bdw : sw.isU128 := by
    have := lt_cases_of_isU64 is_U64_w
    subst sw; simp [extend]
    apply BDWord.isU128_of_cases <;> split_ifs <;> simp_all
  have is_neg : w.isNegative ↔ sw.isNegative := by
    subst sw
    simp [extend, isNegative, BDWord.isNegative]
    aesop
  rw [← BitVec.toInt_inj]
  simp [BitVec.toInt_signExtend_of_le]
  rw [toBitVec64_toInt is_U64_w, BDWord.toBitVec128_toInt is_U128_bdw]
  rw [toInt, BDWord.toInt]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, extend, BDWord.toNat, BWord.toNat] <;>
  simp_all; omega

lemma extend_false_is_setWidth {w : BWord (Fin KB)} :
  w.isU64 →
  (w.extend false).toBitVec128 = BitVec.setWidth 128 w.toBitVec64
    := by
  set sw := extend w false
  intro is_U64_w
  have is_U128_bdw : sw.isU128 := by
    have := lt_cases_of_isU64 is_U64_w
    subst sw; simp [extend]
    apply BDWord.isU128_of_cases <;> split_ifs <;> simp_all
  rw [← BitVec.toNat_inj]
  rw [BDWord.toBitVec128_toNat is_U128_bdw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [BWord.toBitVec64_toNat is_U64_w]
  simp [sw, BDWord.toNat, extend, BWord.toNat]

/-- Polymorphic counterpart of `BWord.extend`. -/
def extend_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) (sgn : Bool) : BDWord (ZMod p) :=
  let ext := (if sgn then (if w.isNegative_poly then (1 : ZMod p) else 0) else 0) * 255
  #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], ext, ext, ext, ext, ext, ext, ext, ext]

/-- Polymorphic counterpart of `BWord.extend_U64_U128`. -/
lemma extend_U64_U128_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} (is_U64_w : w.isU64_poly) (sgn : Bool) :
    (w.extend_poly sgn).isU128_poly := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly is_U64_w
  have h255 : (255 : ZMod p).val = 255 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (255 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  apply BDWord.isU128_of_cases_poly <;>
    simp [extend_poly] <;> (try split_ifs) <;>
    (try simp [h255, h0]) <;> omega

-- Polymorphic counterpart of `BWord.extend_true_is_signExtend`. Routes through
-- `BitVec.toInt_signExtend_of_le` (mirroring the `Fin KB` siblings + the
-- `Word (ZMod p)` version above) so the proof term never exposes
-- `(... % 2^128).toNat` to kernel re-check.
lemma extend_true_is_signExtend_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} :
  w.isU64_poly →
  (w.extend_poly true).toBitVec128_poly = BitVec.signExtend 128 w.toBitVec64_poly
    := by
  set sw := extend_poly w true
  intro is_U64_w
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly is_U64_w
  have h255 : (255 : ZMod p).val = 255 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (255 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  have is_U128_bdw : sw.isU128_poly := by
    subst sw; simp [extend_poly]
    apply BDWord.isU128_of_cases_poly <;> split_ifs <;>
      simp [h255, h0] <;> omega
  have is_neg : w.isNegative_poly ↔ sw.isNegative_poly := by
    subst sw
    simp [extend_poly, isNegative_poly, BDWord.isNegative_poly]
    by_cases h : 128 ≤ w[7].val <;> simp [h, h255, h0]
  rw [← BitVec.toInt_inj]
  simp [BitVec.toInt_signExtend_of_le]
  rw [BWord.toBitVec64_poly_toInt_poly is_U64_w,
      BDWord.toBitVec128_poly_toInt_poly is_U128_bdw]
  rw [BWord.toInt_poly, BDWord.toInt_poly]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, extend_poly, BDWord.toNat_poly, BWord.toNat_poly] <;>
  (rename_i h1 h2;
   simp only [h2, ↓reduceIte, ZMod.cast_eq_val, h255, h0]) <;>
  push_cast <;> omega

/-- Polymorphic counterpart of `BWord.extend_false_is_setWidth`. -/
lemma extend_false_is_setWidth_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} :
  w.isU64_poly →
  (w.extend_poly false).toBitVec128_poly = BitVec.setWidth 128 w.toBitVec64_poly
    := by
  set sw := extend_poly w false
  intro is_U64_w
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly is_U64_w
  have is_U128_bdw : sw.isU128_poly := by
    subst sw; simp [extend_poly]
    apply BDWord.isU128_of_cases_poly <;> simp <;> omega
  rw [← BitVec.toNat_inj]
  rw [BDWord.toBitVec128_poly_toNat_poly is_U128_bdw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [BWord.toBitVec64_poly_toNat_poly is_U64_w]
  simp [sw, BDWord.toNat_poly, extend_poly, BWord.toNat_poly]

lemma low_as_setWidth {w : BWord (Fin KB)} :
  w.isU64 →
  w.low.toBitVec32 = BitVec.setWidth 32 w.toBitVec64
    := by
  intro is_U64_w
  simp [BWord.low, BHWord.toBitVec32, BHWord.toNat, BWord.toBitVec64, BWord.toNat]
  simp [← BitVec.toNat_inj]
  omega

/-- Polymorphic counterpart of `BWord.low_as_setWidth`. -/
lemma low_as_setWidth_poly {p : ℕ} [NeZero p] {w : BWord (ZMod p)} :
  w.isU64_poly →
  w.low_poly.toBitVec32_poly = BitVec.setWidth 32 w.toBitVec64_poly
    := by
  intro is_U64_w
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly is_U64_w
  simp [BWord.low_poly, BHWord.toBitVec32_poly, BHWord.toNat_poly,
        BWord.toBitVec64_poly, BWord.toNat_poly]
  simp [← BitVec.toNat_inj]
  omega

end BWord

namespace BHWord

/-- Sign-extension to 64 bits -/
def extend (w : BHWord (Fin KB)) (sgn : Bool) : BWord (Fin KB) :=
  let ext := (if sgn then (if w.isNegative then (1 : Fin KB) else 0) else 0) * 255
  #v[w[0], w[1], w[2], w[3], ext, ext, ext, ext]

lemma extend_U32_U64 {w : BHWord (Fin KB)} (is_U32_w : w.isU32) (sgn : Bool) : (w.extend sgn).isU64 := by
  have := lt_cases_of_isU32 is_U32_w
  apply BWord.isU64_of_cases <;>
  simp [extend] <;> (try split_ifs) <;> omega

lemma extend_true_is_signExtend {w : BHWord (Fin KB)} :
  w.isU32 →
  (w.extend true).toBitVec64 = BitVec.signExtend 64 w.toBitVec32
    := by
  set sw := extend w true
  intro is_U32_w
  have is_U64_bhw : sw.isU64 := by
    have := lt_cases_of_isU32 is_U32_w
    subst sw; simp [extend]
    apply BWord.isU64_of_cases <;> split_ifs <;> simp_all
  have is_neg : w.isNegative ↔ sw.isNegative := by
    subst sw
    simp [extend, isNegative, BWord.isNegative]
    aesop
  rw [← BitVec.toInt_inj]
  simp [BitVec.toInt_signExtend_of_le]
  rw [toBitVec32_toInt is_U32_w, BWord.toBitVec64_toInt is_U64_bhw]
  rw [toInt, BWord.toInt]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, extend, BWord.toNat, BHWord.toNat] <;>
  simp_all; omega

lemma extend_false_is_setWidth {w : BHWord (Fin KB)} :
  w.isU32 →
  (w.extend false).toBitVec64 = BitVec.setWidth 64 w.toBitVec32
    := by
  set sw := extend w false
  intro is_U32_w
  have is_U64_bhw : sw.isU64 := by
    have := lt_cases_of_isU32 is_U32_w
    subst sw; simp [extend]
    apply BWord.isU64_of_cases <;> split_ifs <;> simp_all
  rw [← BitVec.toNat_inj]
  rw [BWord.toBitVec64_toNat is_U64_bhw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [BHWord.toBitVec32_toNat is_U32_w]
  simp [sw, BWord.toNat, extend, BHWord.toNat]

end BHWord

section Bitwise

namespace Word

lemma and_toBWord {a b : Word (Fin KB)} : a.isU64 → b.isU64 →
  a.toBitVec64 &&& b.toBitVec64 = a.toBWord.toBitVec64 &&& b.toBWord.toBitVec64
    := by
  intro h_a_64 h_b_64
  simp [Word.toBitVec64, BWord.toBitVec64]
  rw [Word.toNat_toBWord h_a_64, Word.toNat_toBWord h_b_64]

lemma or_toBWord {a b : Word (Fin KB)} : a.isU64 → b.isU64 →
  a.toBitVec64 ||| b.toBitVec64 = a.toBWord.toBitVec64 ||| b.toBWord.toBitVec64
    := by
  intro h_a_64 h_b_64
  simp [Word.toBitVec64, BWord.toBitVec64]
  rw [Word.toNat_toBWord h_a_64, Word.toNat_toBWord h_b_64]

lemma xor_toBWord {a b : Word (Fin KB)} : a.isU64 → b.isU64 →
  a.toBitVec64 ^^^ b.toBitVec64 = a.toBWord.toBitVec64 ^^^ b.toBWord.toBitVec64
    := by
  intro h_a_64 h_b_64
  simp [Word.toBitVec64, BWord.toBitVec64]
  rw [Word.toNat_toBWord h_a_64, Word.toNat_toBWord h_b_64]

end Word

end Bitwise

lemma shiftRight_eq_sub_mod (x : ℕ) {n : ℕ} :
    x >>> n = (x - (x % 2 ^ n)) >>> n := by
  simp only [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_sub_mod_div

lemma lt_65536_of_mul_inv_lt' (x : Fin KB) (h : (x * (256 : Fin KB)⁻¹).val < 256) :
    x.val < 65536 := by
  have hne : (256 : Fin KB) ≠ 0 := by decide
  have hinv : x * (256 : Fin KB)⁻¹ * 256 = x := by field_simp
  rw [← hinv, Fin.val_mul]
  have h256 : ((256 : Fin KB).val = 256) := by decide
  rw [h256, Nat.mod_eq_of_lt (by omega)]
  omega

/-- If `x * 4⁻¹` is range-checked to `< 16384` in `Fin KB` (i.e. it fits in 14
bits as a quarter of a 16-bit limb), then `x.val < 65536`. Companion to
`lt_65536_of_mul_inv_lt'` for the `4⁻¹` / 14-bit case used by branch-target
limb checks. -/
lemma lt_65536_of_mul_inv_4_lt (x : Fin KB) (h : (x * (4 : Fin KB)⁻¹).val < 16384) :
    x.val < 65536 := by
  have hne : (4 : Fin KB) ≠ 0 := by decide
  have hinv : x * (4 : Fin KB)⁻¹ * 4 = x := by field_simp
  rw [← hinv, Fin.val_mul]
  have h4 : ((4 : Fin KB).val = 4) := by decide
  rw [h4, Nat.mod_eq_of_lt (by omega)]
  omega

/-- Sign-extend a byte whose MSB is 1: produces 0xFFFFFFFFFFFFFF00 | byte. -/
lemma signExtend64_ofNat8_of_ge_128 (x : Fin KB) (hlt : x.val < 256) (hge : 128 ≤ x.val) :
    BitVec.signExtend 64 (BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x + 65280, 65535, 65535, 65535] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb : BitVec.msb (BitVec.ofNat 8 x.val) = true := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp [hmsb, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat]
  rw [Word.toNat_def]
  simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  have hcast : ((x + 65280 : Fin KB).val : ℕ) = x.val + 65280 := by
    rw [Fin.val_add]; rw [show ((65280 : Fin KB).val = 65280) from rfl]
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hcast]
  rw [show ((65535 : Fin KB).val = 65535) from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- If `lo + hi * 256 = x` (in Fin KB) with `lo < 256` and `hi < 256`, then
    `x.val = lo.val + hi.val * 256` at the Nat level (no mod). -/
lemma nat_decomp_of_inv8_decomp (lo hi x : Fin KB)
    (h : lo + hi * (2 ^ 8 : Fin KB) = x)
    (hlo : lo.val < 256) (hhi : hi.val < 256) :
    x.val = lo.val + hi.val * 256 := by
  have hx := congr_arg Fin.val h
  have h256 : ((2 ^ 8 : Fin KB).val = 256) := by decide
  rw [Fin.val_add, Fin.val_mul, h256,
      Nat.mod_eq_of_lt (show hi.val * 256 < _ by omega),
      Nat.mod_eq_of_lt (show lo.val + hi.val * 256 < _ by omega)] at hx
  omega

/-- The byte-slice of an 8-bit `ofNat` equals itself modulo 256. -/
lemma bitVec_ofNat8_eq_of_mod (a b : ℕ) (h : a % 256 = b % 256) :
    BitVec.ofNat 8 a = BitVec.ofNat 8 b := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simpa using h

/-- Zero-extend a byte: always produces just the byte (upper zeros). -/
lemma setWidth64_ofNat8 (x : Fin KB) (hlt : x.val < 256) :
    BitVec.setWidth 64 (BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, 0, 0, 0] := by
  apply BitVec.toNat_inj.mp
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat]
  rw [Word.toNat_def]
  simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, show ((0 : Fin KB).val = 0) from rfl]
  rw [Nat.mod_eq_of_lt (by have := x.isLt; omega)]
  omega

/-- Sign-extend a byte whose MSB is 0: produces just the byte (upper zeros). -/
lemma signExtend64_ofNat8_of_lt_128 (x : Fin KB) (hlt : x.val < 256) (hge : x.val < 128) :
    BitVec.signExtend 64 (BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, 0, 0, 0] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb : BitVec.msb (BitVec.ofNat 8 x.val) = false := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp [hmsb, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat]
  rw [Word.toNat_def]
  simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, show ((0 : Fin KB).val = 0) from rfl]
  rw [Nat.mod_eq_of_lt (by have := x.isLt; omega)]
  omega

/-- toNat of `hi ++ lo` as bytes equals `(hi.toNat) * 256 + (lo.toNat)`. Specialized form. -/
private lemma toNat_append_bytes (hi lo : BitVec 8) :
    (hi ++ lo).toNat = hi.toNat * 256 + lo.toNat := by
  rw [BitVec.toNat_append]
  have hlo : lo.toNat < 2 ^ 8 := lo.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hlo, Nat.shiftLeft_eq]

/-- Concat of low and high bytes of a halfword `x` (value < 65536) equals `x.val` as Nat. -/
private lemma toNat_concat_halfword_bytes (x : Fin KB) (hlt : x.val < 65536) :
    (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val).toNat = x.val := by
  rw [toNat_append_bytes, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h256 : (2 ^ 8 : ℕ) = 256 := rfl
  rw [h256]
  omega

/-- Zero-extend a halfword (16-bit) split into two bytes: always produces just the halfword. -/
lemma setWidth64_ofNat16_concat (x : Fin KB) (hlt : x.val < 65536) :
    BitVec.setWidth 64 (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, 0, 0, 0] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_setWidth, toNat_concat_halfword_bytes x hlt]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, show ((0 : Fin KB).val = 0) from rfl]
  rw [Nat.mod_eq_of_lt (by have := x.isLt; omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

/-- Sign-extend a halfword whose MSB is 0 (value < 32768): zero-extend form. -/
lemma signExtend64_ofNat16_concat_of_lt_32768
    (x : Fin KB) (hlt : x.val < 65536) (hmsb : x.val < 32768) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, 0, 0, 0] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_false : BitVec.msb (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = false := by
    rw [BitVec.msb_eq_decide, toNat_concat_halfword_bytes x hlt]
    simp only [decide_eq_false_iff_not, not_le]
    change _ < 2 ^ 15
    omega
  rw [hmsb_false]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [BitVec.toNat_setWidth, toNat_concat_halfword_bytes x hlt]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, show ((0 : Fin KB).val = 0) from rfl]
  rw [Nat.mod_eq_of_lt (by have := x.isLt; omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

/-- Sign-extend a halfword whose MSB is 1 (value ≥ 32768): fills upper with 0xFFFF. -/
lemma signExtend64_ofNat16_concat_of_ge_32768
    (x : Fin KB) (hlt : x.val < 65536) (hmsb : 32768 ≤ x.val) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, 65535, 65535, 65535] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_true : BitVec.msb (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = true := by
    rw [BitVec.msb_eq_decide, toNat_concat_halfword_bytes x hlt]
    simp only [decide_eq_true_eq]
    change 2 ^ 15 ≤ _
    omega
  rw [hmsb_true]
  simp only [↓reduceIte]
  rw [BitVec.toNat_setWidth, toNat_concat_halfword_bytes x hlt]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, show ((65535 : Fin KB).val = 65535) from rfl]
  rw [Nat.mod_eq_of_lt (by have := x.isLt; omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  change x.val + (2 ^ 64 - 2^(8 + 8)) = x.val + 65535 * 2 ^ 16 + 65535 * 2 ^ 32 + 65535 * 2 ^ 48
  omega

/-- toNat of a 4-byte (32-bit word) concat equals `x.val + y.val * 65536` when each halfword
    fits in 16 bits. Left-associative concat matches `run_vmem_read_of_width_4'` output. -/
private lemma toNat_concat_word_bytes (x y : Fin KB)
    (hx : x.val < 65536) (hy : y.val < 65536) :
    (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val).toNat =
      x.val + y.val * 65536 := by
  have hx_hi : x.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hy_hi : y.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hx_decomp : x.val % 256 + (x.val >>> 8) * 256 = x.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hy_decomp : y.val % 256 + (y.val >>> 8) * 256 = y.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat, Nat.reducePow,
    show (2 ^ 8 : ℕ) = 256 from rfl]
  have hx_hi_mod : x.val >>> 8 % 256 = x.val >>> 8 := Nat.mod_eq_of_lt hx_hi
  have hy_hi_mod : y.val >>> 8 % 256 = y.val >>> 8 := Nat.mod_eq_of_lt hy_hi
  rw [hx_hi_mod, hy_hi_mod]
  -- innermost: (y >>> 8) <<< 8 ||| (y % 256) = y.val
  rw [show y.val >>> 8 <<< 8 ||| y.val % 256 = y.val by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]; omega]
  -- next: y <<< 8 ||| (x >>> 8) = y * 256 + x >>> 8
  rw [show y.val <<< 8 ||| x.val >>> 8 = y.val * 256 + x.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hx_hi, Nat.shiftLeft_eq]]
  -- outer: (y*256 + x>>>8) <<< 8 ||| (x % 256) = (y*256 + x>>>8) * 256 + x%256 = x + y*65536
  rw [show (y.val * 256 + x.val >>> 8) <<< 8 ||| x.val % 256 =
      (y.val * 256 + x.val >>> 8) * 256 + x.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  have := hx_decomp
  omega

/-- Zero-extend a word (32-bit) split into four bytes: always produces just the word. -/
lemma setWidth64_ofNat32_concat (x y : Fin KB) (hx : x.val < 65536) (hy : y.val < 65536) :
    BitVec.setWidth 64 (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, y, 0, 0] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_setWidth, toNat_concat_word_bytes x y hx hy]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, show ((0 : Fin KB).val = 0) from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

/-- Sign-extend a word whose MSB is 0 (high halfword `y` has `y.val < 32768`): zero-extend form. -/
lemma signExtend64_ofNat32_concat_of_lt_32768
    (x y : Fin KB) (hx : x.val < 65536) (hy : y.val < 65536) (hmsb : y.val < 32768) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, y, 0, 0] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_false : BitVec.msb
      (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
       BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = false := by
    rw [BitVec.msb_eq_decide, toNat_concat_word_bytes x y hx hy]
    simp only [decide_eq_false_iff_not, not_le]
    change _ < 2 ^ 31
    omega
  rw [hmsb_false]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [BitVec.toNat_setWidth, toNat_concat_word_bytes x y hx hy]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, show ((0 : Fin KB).val = 0) from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

/-- Sign-extend a word whose MSB is 1 (high halfword `y` has `32768 ≤ y.val`): upper fills 0xFFFF_FFFF. -/
lemma signExtend64_ofNat32_concat_of_ge_32768
    (x y : Fin KB) (hx : x.val < 65536) (hy : y.val < 65536) (hmsb : 32768 ≤ y.val) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, y, 65535, 65535] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_true : BitVec.msb
      (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
       BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = true := by
    rw [BitVec.msb_eq_decide, toNat_concat_word_bytes x y hx hy]
    simp only [decide_eq_true_eq]
    change 2 ^ 31 ≤ _
    omega
  rw [hmsb_true]
  simp only [↓reduceIte]
  rw [BitVec.toNat_setWidth, toNat_concat_word_bytes x y hx hy]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_def]
  simp only [Fin.isValue, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, show ((65535 : Fin KB).val = 65535) from rfl]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  change x.val + y.val * 2 ^ 16 + (2 ^ 64 - 2^(8 + 8 + 8 + 8)) =
       x.val + y.val * 2 ^ 16 + 65535 * 2 ^ 32 + 65535 * 2 ^ 48
  omega

section getByte

namespace BitVec

def getByte {n : ℕ} (bv : BitVec n) (i : ℕ) : ℕ := (bv.extractLsb (i * 8 + 7) (i * 8)).toNat

lemma getByte_is_byte : getByte bv i < 256 := by simp [getByte]; omega

lemma byte_decomp_128 (bv : BitVec 128) :
  bv = BDWord.toBitVec128
        #v[getByte bv 0, getByte bv 1, getByte bv 2, getByte bv 3,
           getByte bv 4, getByte bv 5, getByte bv 6, getByte bv 7,
           getByte bv 8, getByte bv 9, getByte bv 10, getByte bv 11,
           getByte bv 12, getByte bv 13, getByte bv 14, getByte bv 15]
    := by
  have : 256 = (256#128).toNat := by simp
  simp [getByte, BDWord.toBitVec128, BDWord.toNat]
  simp [ofNat_add, ofNat_mul]
  repeat rw [← BitVec.toNat_ushiftRight]
  repeat rw [this, ← BitVec.toNat_umod]; simp [-toNat_umod, -toNat_ushiftRight]
  have hcast : ∀ (x : BitVec 128),
      (((x % 256#128).toNat : Fin 2130706433) : ℕ) = (x % 256#128).toNat := by
    intro x
    apply Fin.val_cast_of_lt
    rw [BitVec.toNat_umod]; simp
    have := Nat.mod_lt x.toNat (show 0 < 256 by omega); omega
  simp_rw [hcast, BitVec.ofNat_toNat]
  bv_decide

end BitVec

end getByte

section cross_product

def cp {n : ℕ} (a b : Vector (Fin KB) n) (k : ℕ) (hk : k < n) : Fin KB :=
  let product := ((Vector.ofFn (fun i => a.get ⟨i.val, by omega⟩ * b.get ⟨k - i.val, by
                     have h : i.val < (k + 1) := i.isLt
                     omega⟩)) : Vector (Fin KB) (k + 1)).toList
  product.foldl (· + ·) 0

end cross_product
