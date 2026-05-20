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
set_option linter.style.setOption false
set_option linter.style.longLine false

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

/-- Polymorphic counterpart of `isU32`. -/
def isU32_poly {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : Prop :=
  ∀ i : Fin HWORD_SIZE, w[i].val < 2 ^ 16

/-- Polymorphic counterpart of `isU32_of_cases`. -/
@[aesop unsafe apply]
lemma isU32_of_cases_poly {p : ℕ} [NeZero p] {w : HWord (ZMod p)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16) : w.isU32_poly
  := by intro i; fin_cases i <;> simpa [isU32_poly]

/-- Polymorphic counterpart of `lt_cases_of_isU32`. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU32_poly {p : ℕ} [NeZero p] {w : HWord (ZMod p)} (hw : w.isU32_poly) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 :=
  ⟨hw 0, hw 1⟩

end U32

section conversions

/-- Polymorphic counterpart of `HWord.toNat`. -/
def toNat_poly {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 16

/-- Polymorphic counterpart of `toNat_lt_of_isU32`. -/
lemma toNat_poly_lt_of_isU32_poly {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (hw : w.isU32_poly) : w.toNat_poly < 2 ^ 32 := by
  have := lt_cases_of_isU32_poly hw
  unfold toNat_poly
  omega

/-- Polymorphic counterpart of `HWord.toBitVec32`. -/
def toBitVec32_poly {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : BitVec 32 :=
  BitVec.ofNat 32 (toNat_poly w)

/-- Polymorphic counterpart of `toBitVec32_toNat`. -/
lemma toBitVec32_poly_toNat_poly {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (hw : w.isU32_poly) :
    w.toBitVec32_poly.toNat = w.toNat_poly := by
  simp only [toBitVec32_poly, BitVec.toNat_ofNat, toNat_poly]
  have := lt_cases_of_isU32_poly hw
  omega

/-- Polymorphic counterpart of `HWord.toBitVec64`. -/
def toBitVec64 {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : BitVec 64 :=
  BitVec.signExtend 64 (toBitVec32_poly w)

/-- Polymorphic counterpart of `HWord.isNegative`. -/
@[grind] def isNegative_poly {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : Prop := w[1].val ≥ 32768

instance {p : ℕ} [NeZero p] {w : HWord (ZMod p)} : Decidable (isNegative_poly w) := by
  unfold isNegative_poly; infer_instance

/-- Polymorphic counterpart of `HWord.isNegative_msb`. -/
lemma isNegative_poly_msb {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (h_w_isU32 : w.isU32_poly) :
    w.isNegative_poly ↔ (w.toBitVec32_poly.msb = true) := by
  have := lt_cases_of_isU32_poly h_w_isU32
  simp [isNegative_poly, toBitVec32_poly, toNat_poly, BitVec.msb_eq_decide]
  omega

/-- Polymorphic counterpart of `HWord.toInt`. -/
def toInt_poly {p : ℕ} [NeZero p] (w : HWord (ZMod p)) : ℤ :=
  if (isNegative_poly w) then w.toNat_poly - 2 ^ 32 else w.toNat_poly

/-- Polymorphic counterpart of `HWord.toInt_lb`. -/
lemma toInt_poly_lb {p : ℕ} [NeZero p] {w : HWord (ZMod p)} (is_U32_w : w.isU32_poly) :
  -2147483648 ≤ w.toInt_poly := by
  have ⟨h0, h1⟩ := lt_cases_of_isU32_poly is_U32_w
  unfold HWord.toInt_poly HWord.isNegative_poly HWord.toNat_poly
  split_ifs <;> push_cast <;> omega

/-- Polymorphic counterpart of `HWord.toInt_ub`. -/
lemma toInt_poly_ub {p : ℕ} [NeZero p] {w : HWord (ZMod p)} (is_U32_w : w.isU32_poly) :
  w.toInt_poly < 2147483648 := by
  have ⟨h0, h1⟩ := lt_cases_of_isU32_poly is_U32_w
  unfold HWord.toInt_poly HWord.isNegative_poly HWord.toNat_poly
  split_ifs <;> push_cast <;> omega

/-- Uses `ZMod.val_injective` per limb to recover pointwise equality from
the `.val`-bound facts. -/
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

/-- Polymorphic counterpart of `HWord.toBitVec64_toInt`. -/
lemma toBitVec64_toInt_poly {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (h_w_isU32 : w.isU32_poly) :
    w.toBitVec64.toInt = w.toInt_poly
  := by
    have := lt_cases_of_isU32_poly h_w_isU32
    simp [toBitVec64, BitVec.toInt_signExtend]
    rw [toBitVec32_poly_toInt_poly h_w_isU32]
    unfold toInt_poly isNegative_poly toNat_poly
    refine Int.bmod_eq_of_le ?_ ?_ <;> push_cast <;> omega

/-- Polymorphic counterpart of `HWord.isNegative_toInt`. -/
lemma isNegative_poly_toInt_poly {p : ℕ} [NeZero p]
    {w : HWord (ZMod p)} (is32_w : HWord.isU32_poly w) :
    w.isNegative_poly ↔ w.toInt_poly < 0 := by
  have := lt_cases_of_isU32_poly is32_w
  unfold HWord.toInt_poly HWord.isNegative_poly HWord.toNat_poly
  split_ifs <;> push_cast <;> omega

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

/-- `isU64_poly w` means that each limb of the `Word` is properly bounded.
Used by `SP1Constraint.toProp`. -/
def isU64_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : Prop :=
  ∀ i : Fin WORD_SIZE, w[i].val < 2 ^ 16

/-- Polymorphic counterpart of `isU64_of_cases`. -/
@[aesop unsafe apply]
lemma isU64_of_cases_poly {p : ℕ} [NeZero p] {w : Word (ZMod p)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16)
    (h2 : w[2].val < 2 ^ 16) (h3 : w[3].val < 2 ^ 16) : w.isU64_poly
  := by intro i; fin_cases i <;> simpa [isU64_poly]

/-- Polymorphic counterpart of `lt_cases_of_isU64`. -/
@[aesop unsafe forward, grind →]
lemma lt_cases_of_isU64_poly {p : ℕ} [NeZero p] {w : Word (ZMod p)} (hw : w.isU64_poly) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 ∧ w[2].val < 2 ^ 16 ∧ w[3].val < 2 ^ 16 :=
  ⟨hw 0, hw 1, hw 2, hw 3⟩

/-- Common enough to want a lemma. -/
@[simp]
lemma four_isU64_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] :
    Word.isU64_poly (#v[4, 0, 0, 0] : Word (ZMod p)) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  apply Word.isU64_of_cases_poly <;>
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h4_val : ((4 : ℕ) : ZMod p).val = 4 := ZMod.val_natCast_of_lt (by omega)
    rw [show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by push_cast; rfl]
    rw [h4_val]; omega
  all_goals (rw [ZMod.val_zero]; omega)

end U64

section conversions

/-- Polymorphic counterpart of `Word.toNat` over `Word (ZMod p)`. Companion
to `isU64_poly`; used by `SP1Constraint.toStateProp`. Defined
directly since the polymorphic
proof obligations live at the operation iff layer, where the unfolded
form is preferred. -/
def toNat_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 16 + w[2].val * 2 ^ 32 + w[3].val * 2 ^ 48

/-- Polymorphic counterpart of `toNat_def`. The polymorphic `toNat_poly` is
defined directly (no opaque wrapper), so this is `rfl`. -/
lemma toNat_poly_def {p : ℕ} [NeZero p] (w : Word (ZMod p)) :
    w.toNat_poly = w[0].val + w[1].val * 2 ^ 16 + w[2].val * 2 ^ 32 + w[3].val * 2 ^ 48 := rfl

/-- Polymorphic counterpart of `toNat_lt_of_isU64`. -/
lemma toNat_poly_lt_of_isU64_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (hw : w.isU64_poly) : w.toNat_poly < 2 ^ 64 := by
  have := lt_cases_of_isU64_poly hw
  unfold toNat_poly
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

/-- The reconstructed vector uses `((N : ℕ) : ZMod p)` natural-cast
literals. -/
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

/-- Polymorphic counterpart of `Word.toBitVec64` over `Word (ZMod p)`.
Companion to `toNat_poly`; used by `SP1Constraint.toStateProp`. -/
def toBitVec64 {p : ℕ} [NeZero p] (w : Word (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 (toNat_poly w)

/-- Polymorphic counterpart of `toBitVec64_toNat`. -/
lemma toBitVec64_toNat_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (hw : w.isU64_poly) :
    w.toBitVec64.toNat = w.toNat_poly := by
  simp only [toBitVec64, BitVec.toNat_ofNat, toNat_poly]
  have := lt_cases_of_isU64_poly hw
  omega

/-- Adding a small Nat constant `k` to a Word's BitVec representation is the
same as adding `k` to the low limb, provided the low limb plus `k` fits in
17 bits (so the ZMod-level `(a + k).val = a.val + k` lift is clean). The
other limbs are unconstrained — BitVec arithmetic associativity handles the
mod 2^64 carries regardless. Used by chip-side `correct_*` proofs to bridge
`Word.toBitVec64 #v[..] + 4#64 = Word.toBitVec64 #v[low+4, ..]`
when normalizing `+ 4` between the BitVec and limb forms (e.g. PC update). -/
lemma toBitVec64_lowLimb_add_nat
    {p : ℕ} [Fact (Nat.Prime p)] [NeZero p]--[Fact (2 ^ 17 < p)]
    (a b c d : ZMod p) (k : ℕ) (hak : a.val + k < p) :
    Word.toBitVec64 #v[a, b, c, d] + BitVec.ofNat 64 k =
      Word.toBitVec64 #v[a + (k : ZMod p), b, c, d] := by
  have hk_val : (k : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
  have hak_val : (a + (k : ZMod p)).val = a.val + k := by
    rw [ZMod.val_add_of_lt (by rw [hk_val]; omega), hk_val]
  simp [Word.toBitVec64, Word.toNat_poly_def]
  rw [← BitVec.toNat_inj, BitVec.toNat_add,
      BitVec.toNat_ofNat, BitVec.toNat_ofNat, BitVec.toNat_ofNat,
      hak_val, ← Nat.add_mod]
  congr 1; ring

/-- Polymorphic counterpart of `isNegative`. -/
@[grind] def isNegative_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : Prop := w[3].val ≥ 32768

instance {p : ℕ} [NeZero p] {w : Word (ZMod p)} : Decidable (isNegative_poly w) := by
  unfold isNegative_poly; infer_instance

/-- Polymorphic counterpart of `isNegative_msb`. -/
lemma isNegative_poly_msb {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.isNegative_poly ↔ (w.toBitVec64.msb = true) := by
  have := lt_cases_of_isU64_poly h_w_isU64
  simp [isNegative_poly, toBitVec64, toNat_poly, BitVec.msb_eq_decide]
  omega

/-- Polymorphic counterpart of `low`. -/
def low_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : HWord (ZMod p) := #v[w[0], w[1]]

/-- Polymorphic counterpart of `Word.isU64_low_isU32`. -/
lemma isU64_poly_low_poly_isU32_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (hw : w.isU64_poly) : w.low_poly.isU32_poly := by
  have ⟨h0, h1, _, _⟩ := lt_cases_of_isU64_poly hw
  intro i; fin_cases i <;> simp [low_poly, HWord.isU32_poly] <;> assumption

lemma low_toNat_poly {p : ℕ} [NeZero p] {b0 b1 : ZMod p}
    (hw : HWord.isU32_poly #v[b0, b1]) :
    (Word.toBitVec64 #v[b0, b1, 0, 0]).toNat = HWord.toNat_poly #v[b0, b1] := by
  rw [Word.toBitVec64_toNat_poly]
  · simp [Word.toNat_poly, HWord.toNat_poly, ZMod.val_zero]
  · apply HWord.lt_cases_of_isU32_poly at hw
    apply Word.isU64_of_cases_poly <;> simp_all [ZMod.val_zero]

/-- Polymorphic counterpart of `Word.setWidth_eq_low`. -/
lemma setWidth_eq_low_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    BitVec.setWidth 32 w.toBitVec64 = w.low_poly.toBitVec32_poly
  := by
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
    simp [toBitVec64, ← BitVec.toNat_inj, low_poly, Word.toNat_poly,
          HWord.toBitVec32_poly, HWord.toNat_poly]
    omega

/-- Polymorphic counterpart of `high`. -/
def high_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : HWord (ZMod p) := #v[w[2], w[3]]

/-- Polymorphic counterpart of `Word.isU64_high_isU32`. -/
lemma isU64_poly_high_poly_isU32_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (hw : w.isU64_poly) : w.high_poly.isU32_poly := by
  have ⟨_, _, h2, h3⟩ := lt_cases_of_isU64_poly hw
  intro i; fin_cases i <;> simp [high_poly, HWord.isU32_poly] <;> assumption

/-- Polymorphic counterpart of `Word.setWidth_rshift_eq_high`. -/
lemma setWidth_rshift_eq_high_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    BitVec.setWidth 32 (w.toBitVec64 >>> 32) = w.high_poly.toBitVec32_poly
  := by
    have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
    simp_all [toBitVec64, ← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow,
              high_poly, Word.toNat_poly, HWord.toBitVec32_poly, HWord.toNat_poly]
    omega

/-- Polymorphic counterpart of `Word.toInt`. -/
def toInt_poly {p : ℕ} [NeZero p] (w : Word (ZMod p)) : ℤ :=
  if (isNegative_poly w) then w.toNat_poly - 2 ^ 64 else w.toNat_poly

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

/-- Polymorphic counterpart of `Word.toInt_lb`. -/
lemma toInt_poly_lb {p : ℕ} [NeZero p] {w : Word (ZMod p)} (is_U64_w : w.isU64_poly) :
  -9223372036854775808 ≤ w.toInt_poly := by
  have ⟨h0, h1, h2, h3⟩ := lt_cases_of_isU64_poly is_U64_w
  unfold Word.toInt_poly Word.isNegative_poly Word.toNat_poly
  split_ifs <;> push_cast <;> omega

/-- Polymorphic counterpart of `Word.toInt_ub`. -/
lemma toInt_poly_ub {p : ℕ} [NeZero p] {w : Word (ZMod p)} (is_U64_w : w.isU64_poly) :
  w.toInt_poly < 9223372036854775808 := by
  have ⟨h0, h1, h2, h3⟩ := lt_cases_of_isU64_poly is_U64_w
  unfold Word.toInt_poly Word.isNegative_poly Word.toNat_poly
  split_ifs <;> push_cast <;> omega

/-- Polymorphic counterpart of `Word.isU64_toInt`. -/
lemma isU64_poly_toInt_poly {p : ℕ} [NeZero p] {w : Word (ZMod p)}
    (is64_w : Word.isU64_poly w) :
    - 2 ^ 63 ≤ w.toInt_poly ∧ w.toInt_poly < 2 ^ 63 := by
  have ⟨h0, h1, h2, h3⟩ := lt_cases_of_isU64_poly is64_w
  unfold Word.toInt_poly Word.isNegative_poly Word.toNat_poly
  split_ifs <;> push_cast <;> omega

/-- Polymorphic counterpart of `toBitVec64_toInt`. -/
lemma toBitVec64_toInt_poly {p : ℕ} [NeZero p]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.toBitVec64.toInt = w.toInt_poly
  := by
    rw [BitVec.toInt, Word.toInt_poly]
    split_ifs <;>
    rw [isNegative_poly_msb h_w_isU64] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec64_toNat_poly h_w_isU64] at * <;>
    omega

/-- Polymorphic counterpart of `Word.isNegative_toInt`. -/
lemma isNegative_poly_toInt_poly {p : ℕ} [NeZero p] {w : Word (ZMod p)}
    (is64_w : Word.isU64_poly w) :
    w.isNegative_poly ↔ w.toInt_poly < 0 := by
  have ⟨h0, h1, h2, h3⟩ := lt_cases_of_isU64_poly is64_w
  unfold Word.toInt_poly Word.isNegative_poly Word.toNat_poly
  split_ifs <;> push_cast <;> omega

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

/-- Polymorphic counterpart of `DWord.isU128`. -/
def isU128_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : Prop :=
  ∀ i : Fin DWORD_SIZE, w[i].val < 2 ^ 16

/-- Polymorphic counterpart of `DWord.isU128_of_cases`. -/
@[aesop unsafe apply]
lemma isU128_of_cases_poly {p : ℕ} [NeZero p] {w : DWord (ZMod p)}
    (h0 : w[0].val < 2 ^ 16) (h1 : w[1].val < 2 ^ 16)
    (h2 : w[2].val < 2 ^ 16) (h3 : w[3].val < 2 ^ 16)
    (h4 : w[4].val < 2 ^ 16) (h5 : w[5].val < 2 ^ 16)
    (h6 : w[6].val < 2 ^ 16) (h7 : w[7].val < 2 ^ 16) : w.isU128_poly
  := by intro i; fin_cases i <;> simpa [isU128_poly]

/-- Polymorphic counterpart of `lt_cases_of_isU128`. -/
@[aesop unsafe forward, grind →]
lemma lt_cases_of_isU128_poly {p : ℕ} [NeZero p] {w : DWord (ZMod p)} (hw : w.isU128_poly) :
    w[0].val < 2 ^ 16 ∧ w[1].val < 2 ^ 16 ∧ w[2].val < 2 ^ 16 ∧ w[3].val < 2 ^ 16 ∧
    w[4].val < 2 ^ 16 ∧ w[5].val < 2 ^ 16 ∧ w[6].val < 2 ^ 16 ∧ w[7].val < 2 ^ 16 :=
  ⟨hw 0, hw 1, hw 2, hw 3, hw 4, hw 5, hw 6, hw 7⟩

end U128

section conversions

/-- Polymorphic counterpart of `DWord.toNat`. -/
@[aesop unsafe forward]
def toNat_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 16 + w[2].val * 2 ^ 32 + w[3].val * 2 ^ 48 +
  w[4].val * 2 ^ 64 + w[5].val * 2 ^ 80 + w[6].val * 2 ^ 96 + w[7].val * 2 ^ 112

/-- Polymorphic counterpart of `DWord.toBitVec128`. -/
def toBitVec128_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : BitVec 128 :=
  BitVec.ofNat 128 (toNat_poly w)

/-- Polymorphic counterpart of `DWord.toBitVec128_toNat`. -/
lemma toBitVec128_poly_toNat_poly {p : ℕ} [NeZero p]
    {w : DWord (ZMod p)} (hw : w.isU128_poly) :
    w.toBitVec128_poly.toNat = w.toNat_poly := by
  simp only [DWord.toBitVec128_poly, BitVec.toNat_ofNat, toNat_poly]
  have := lt_cases_of_isU128_poly hw
  omega

/-- Polymorphic counterpart of `DWord.isNegative`. -/
@[grind] def isNegative_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : Prop := w[7].val ≥ 32768

instance {p : ℕ} [NeZero p] {w : DWord (ZMod p)} : Decidable (isNegative_poly w) := by
  unfold isNegative_poly; infer_instance

/-- Polymorphic counterpart of `DWord.isNegative_msb`. -/
lemma isNegative_poly_msb {p : ℕ} [NeZero p]
    {w : DWord (ZMod p)} (h_w_isU128 : w.isU128_poly) :
    w.isNegative_poly ↔ (w.toBitVec128_poly.msb = true) := by
  have := lt_cases_of_isU128_poly h_w_isU128
  simp [isNegative_poly, toBitVec128_poly, toNat_poly, BitVec.msb_eq_decide]
  omega

/-- Polymorphic counterpart of `DWord.low`. -/
def low_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : Word (ZMod p) :=
  #v[w[0], w[1], w[2], w[3]]

/-- Polymorphic counterpart of `DWord.high`. -/
def high_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : Word (ZMod p) :=
  #v[w[4], w[5], w[6], w[7]]

/-- Polymorphic counterpart of `DWord.toInt`. -/
def toInt_poly {p : ℕ} [NeZero p] (w : DWord (ZMod p)) : ℤ :=
  if (isNegative_poly w) then w.toNat_poly - 2 ^ 128 else w.toNat_poly

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

/-- Polymorphic counterpart of `DWord.isU128_toInt`. -/
lemma isU128_poly_toInt_poly {p : ℕ} [NeZero p] {w : DWord (ZMod p)}
    (is128_w : DWord.isU128_poly w) :
    - 2 ^ 127 ≤ w.toInt_poly ∧ w.toInt_poly < 2 ^ 127 := by
  have := DWord.lt_cases_of_isU128_poly is128_w
  unfold DWord.toInt_poly DWord.isNegative_poly DWord.toNat_poly
  split_ifs <;> push_cast <;> omega

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

/-- Polymorphic counterpart of `DWord.isNegative_toInt`. -/
lemma isNegative_poly_toInt_poly {p : ℕ} [NeZero p] {w : DWord (ZMod p)}
    (is128_w : DWord.isU128_poly w) :
    w.isNegative_poly ↔ w.toInt_poly < 0 := by
  have := DWord.lt_cases_of_isU128_poly is128_w
  unfold DWord.toInt_poly DWord.isNegative_poly DWord.toNat_poly
  split_ifs <;> push_cast <;> omega

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

/-- Polymorphic counterpart of `BHWord.isU32`. -/
def isU32_poly {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : Prop :=
  ∀ i : Fin BYTE_HWORD_SIZE, w[i].val < 256

/-- Polymorphic counterpart of `BHWord.isU32_of_cases`. -/
@[aesop unsafe apply]
lemma isU32_of_cases_poly {p : ℕ} [NeZero p] {w : BHWord (ZMod p)}
    (h0 : w[0].val < 256) (h1 : w[1].val < 256)
    (h2 : w[2].val < 256) (h3 : w[3].val < 256) : w.isU32_poly
  := by intro i; fin_cases i <;> simpa [isU32_poly]

/-- Polymorphic counterpart of `BHWord.lt_cases_of_isU32`. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU32_poly {p : ℕ} [NeZero p] {w : BHWord (ZMod p)} (hbhw : w.isU32_poly) :
    w[0].val < 256 ∧ w[1].val < 256 ∧ w[2].val < 256 ∧ w[3].val < 256
    :=
  ⟨hbhw 0, hbhw 1, hbhw 2, hbhw 3⟩

end U32

section conversions

/-- Polymorphic counterpart of `BHWord.toNat`. -/
def toNat_poly {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 8 + w[2].val * 2 ^ 16 + w[3].val * 2 ^ 24

/-- Polymorphic counterpart of `BHWord.toNat_lt_of_isU32`. -/
lemma toNat_poly_lt_of_isU32_poly {p : ℕ} [NeZero p]
    {w : BHWord (ZMod p)} (hw : w.isU32_poly) : w.toNat_poly < 2 ^ 32 := by
  have := lt_cases_of_isU32_poly hw
  unfold toNat_poly
  omega

/-- Polymorphic counterpart of `BHWord.toBitVec32`. -/
def toBitVec32_poly {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : BitVec 32 :=
  BitVec.ofNat 32 (toNat_poly w)

/-- Polymorphic counterpart of `BHWord.toBitVec32_toNat`. -/
lemma toBitVec32_poly_toNat_poly {p : ℕ} [NeZero p]
    {w : BHWord (ZMod p)} (hw : w.isU32_poly) :
    w.toBitVec32_poly.toNat = w.toNat_poly := by
  simp only [toBitVec32_poly, BitVec.toNat_ofNat, toNat_poly]
  have := lt_cases_of_isU32_poly hw
  omega

/-- Polymorphic counterpart of `BHWord.isNegative`. -/
@[grind] def isNegative_poly {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : Prop := w[3].val ≥ 128

instance {p : ℕ} [NeZero p] {w : BHWord (ZMod p)} : Decidable (isNegative_poly w) := by
  unfold isNegative_poly; infer_instance

/-- Polymorphic counterpart of `BHWord.isNegative_msb`. -/
lemma isNegative_poly_msb {p : ℕ} [NeZero p]
    {w : BHWord (ZMod p)} (h_w_isU32 : w.isU32_poly) :
    w.isNegative_poly ↔ (w.toBitVec32_poly.msb = true) := by
  have := lt_cases_of_isU32_poly h_w_isU32
  simp [isNegative_poly, BHWord.toBitVec32_poly, BHWord.toNat_poly, BitVec.msb_eq_decide]
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

/-- Polymorphic counterpart of `BHWord.toInt`. -/
def toInt_poly {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) : ℤ :=
  if (isNegative_poly w) then w.toNat_poly - 2 ^ 32 else w.toNat_poly

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

/-- Polymorphic counterpart of `BWord.isU64`. -/
def isU64_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : Prop :=
  ∀ i : Fin BYTE_WORD_SIZE, w[i].val < 2 ^ 8

/-- Polymorphic counterpart of `BWord.isU64_of_cases`. -/
@[aesop unsafe apply]
lemma isU64_of_cases_poly {p : ℕ} [NeZero p] {w : BWord (ZMod p)}
    (h0 : w[0].val < 2 ^ 8) (h1 : w[1].val < 2 ^ 8)
    (h2 : w[2].val < 2 ^ 8) (h3 : w[3].val < 2 ^ 8)
    (h4 : w[4].val < 2 ^ 8) (h5 : w[5].val < 2 ^ 8)
    (h6 : w[6].val < 2 ^ 8) (h7 : w[7].val < 2 ^ 8) : w.isU64_poly
  := by intro i; fin_cases i <;> simpa [isU64_poly]

/-- Polymorphic counterpart of `BWord.lt_cases_of_isU64`. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU64_poly {p : ℕ} [NeZero p] {w : BWord (ZMod p)} (hbw : w.isU64_poly) :
    w[0].val < 2 ^ 8 ∧ w[1].val < 2 ^ 8 ∧ w[2].val < 2 ^ 8 ∧ w[3].val < 2 ^ 8 ∧
    w[4].val < 2 ^ 8 ∧ w[5].val < 2 ^ 8 ∧ w[6].val < 2 ^ 8 ∧ w[7].val < 2 ^ 8 :=
  ⟨hbw 0, hbw 1, hbw 2, hbw 3, hbw 4, hbw 5, hbw 6, hbw 7⟩

end U64

section conversions

/-- Polymorphic counterpart of `BWord.toWord`. The body only uses ring
operations and `OfNat`, so `[CommRing F]` is sufficient — no `Field`
hypothesis needed. -/
def toWord_poly {F : Type} [CommRing F] (w : BWord F) : Word F :=
  #v[w[0] + w[1] * 256, w[2] + w[3] * 256, w[4] + w[5] * 256, w[6] + w[7] * 256]

/-- Polymorphic counterpart of `BWord.toNat`. -/
def toNat_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 8 + w[2].val * 2 ^ 16 + w[3].val * 2 ^ 24 +
  w[4].val * 2 ^ 32 + w[5].val * 2 ^ 40 + w[6].val * 2 ^ 48 + w[7].val * 2 ^ 56

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

/-- Polymorphic counterpart of `BWord.toBitVec64`. -/
def toBitVec64 {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 (toNat_poly w)

/-- Polymorphic counterpart of `BWord.toBitVec64_toNat`. -/
lemma toBitVec64_toNat_poly {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (hw : w.isU64_poly) :
    w.toBitVec64.toNat = w.toNat_poly := by
  simp only [BWord.toBitVec64, BitVec.toNat_ofNat, toNat_poly]
  have := lt_cases_of_isU64_poly hw
  omega

/-- Polymorphic counterpart of `BWord.toWord_toBitVec64`. -/
lemma toWord_poly_toBitVec64 {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.toWord_poly.toBitVec64 = w.toBitVec64 := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
  rw [← BitVec.toNat_inj]
  rw [Word.toBitVec64_toNat_poly (toWord_poly_U64_poly h_w_isU64)]
  rw [BWord.toBitVec64_toNat_poly h_w_isU64]
  rw [toNat_poly_toWord_poly h_w_isU64]

/-- Polymorphic counterpart of `BWord.isNegative`. -/
@[grind] def isNegative_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : Prop := w[7].val ≥ 128

instance {p : ℕ} [NeZero p] {w : BWord (ZMod p)} : Decidable (isNegative_poly w) := by
  unfold isNegative_poly; infer_instance

/-- Polymorphic counterpart of `BWord.isNegative_msb`. -/
lemma isNegative_poly_msb {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.isNegative_poly ↔ (w.toBitVec64.msb = true) := by
  have := lt_cases_of_isU64_poly h_w_isU64
  simp [isNegative_poly, BWord.toBitVec64, BWord.toNat_poly, BitVec.msb_eq_decide]
  omega

/-- Polymorphic counterpart of `BWord.toInt`. -/
def toInt_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : ℤ :=
  if (isNegative_poly w) then w.toNat_poly - 2 ^ 64 else w.toNat_poly

/-- Polymorphic counterpart of `BWord.toBitVec64_toInt`. -/
lemma toBitVec64_toInt_poly {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.toBitVec64.toInt = w.toInt_poly
  := by
    rw [BitVec.toInt, BWord.toInt_poly]
    split_ifs <;>
    rw [isNegative_poly_msb h_w_isU64] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec64_toNat_poly h_w_isU64] at * <;>
    omega

/-- Polymorphic counterpart of `BWord.low`. -/
def low_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : BHWord (ZMod p) :=
  #v[w[0], w[1], w[2], w[3]]

/-- Polymorphic counterpart of `BWord.isU64_low_isU32`. -/
lemma isU64_low_isU32_poly {p : ℕ} [NeZero p] {w : BWord (ZMod p)}
    (hw : w.isU64_poly) : w.low_poly.isU32_poly := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly hw
  apply BHWord.isU32_of_cases_poly <;> simp [low_poly] <;> omega

/-- Polymorphic counterpart of `BWord.setWidth_eq_low`. -/
lemma setWidth_eq_low_poly {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    BitVec.setWidth 32 w.toBitVec64 = w.low_poly.toBitVec32_poly := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
  simp [toBitVec64, ← BitVec.toNat_inj, low_poly,
        BWord.toNat_poly, BHWord.toBitVec32_poly, BHWord.toNat_poly]
  omega

/-- Polymorphic counterpart of `BWord.high`. -/
def high_poly {p : ℕ} [NeZero p] (w : BWord (ZMod p)) : BHWord (ZMod p) :=
  #v[w[4], w[5], w[6], w[7]]

/-- Polymorphic counterpart of `BWord.isU64_high_isU32`. -/
lemma isU64_high_isU32_poly {p : ℕ} [NeZero p] {w : BWord (ZMod p)}
    (hw : w.isU64_poly) : w.high_poly.isU32_poly := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly hw
  apply BHWord.isU32_of_cases_poly <;> simp [high_poly] <;> omega

/-- Polymorphic counterpart of `BWord.setWidth_rshift_eq_high`. -/
lemma setWidth_rshift_eq_high_poly {p : ℕ} [NeZero p]
    {w : BWord (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    BitVec.setWidth 32 (w.toBitVec64 >>> 32) = w.high_poly.toBitVec32_poly := by
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly h_w_isU64
  simp_all [toBitVec64, ← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow,
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

/-- Polymorphic counterpart of `BDWord.isU128`. -/
def isU128_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : Prop :=
  ∀ i : Fin BYTE_DWORD_SIZE, w[i].val < 256

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

/-- Polymorphic counterpart of `BDWord.low`. -/
def low_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : BWord (ZMod p) :=
  #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]]

/-- Polymorphic counterpart of `BDWord.isU128_low_isU64`. -/
lemma isU128_poly_low_poly_isU64_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (hw : w.isU128_poly) : w.low_poly.isU64_poly := by
  have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := lt_cases_of_isU128_poly hw
  intro i; fin_cases i <;> simp [low_poly, BWord.isU64_poly] <;> omega

/-- Polymorphic counterpart of `BDWord.high`. -/
def high_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : BWord (ZMod p) :=
  #v[w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]]

/-- Polymorphic counterpart of `BDWord.isU128_high_isU64`. -/
lemma isU128_poly_high_poly_isU64_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (hw : w.isU128_poly) : w.high_poly.isU64_poly := by
  have ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ := lt_cases_of_isU128_poly hw
  intro i; fin_cases i <;> simp [high_poly, BWord.isU64_poly] <;> omega

/-- Polymorphic counterpart of `BDWord.toNat`. -/
def toNat_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : ℕ :=
  w[0].val + w[1].val * 2 ^ 8 + w[2].val * 2 ^ 16 + w[3].val * 2 ^ 24 +
  w[4].val * 2 ^ 32 + w[5].val * 2 ^ 40 + w[6].val * 2 ^ 48 + w[7].val * 2 ^ 56 +
  w[8].val * 2 ^ 64 + w[9].val * 2 ^ 72 + w[10].val * 2 ^ 80 + w[11].val * 2 ^ 88 +
  w[12].val * 2 ^ 96 + w[13].val * 2 ^ 104 + w[14].val * 2 ^ 112 + w[15].val * 2 ^ 120

/-- Polymorphic counterpart of `BDWord.toNat_lt_of_isU128`. -/
lemma toNat_poly_lt_of_isU128_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (hw : w.isU128_poly) : w.toNat_poly < 2 ^ 128 := by
  have := lt_cases_of_isU128_poly hw
  unfold toNat_poly
  omega

/-- Polymorphic counterpart of `BDWord.toBitVec128`. -/
def toBitVec128_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : BitVec 128 :=
  BitVec.ofNat 128 (toNat_poly w)

/-- Polymorphic counterpart of `BDWord.toBitVec128_toNat`. -/
lemma toBitVec128_poly_toNat_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (hw : w.isU128_poly) :
    w.toBitVec128_poly.toNat = w.toNat_poly := by
  simp only [BDWord.toBitVec128_poly, BitVec.toNat_ofNat, toNat_poly]
  have := lt_cases_of_isU128_poly hw
  omega

/-- Polymorphic counterpart of `BDWord.isNegative`. -/
@[grind] def isNegative_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : Prop := w[15].val ≥ 128

instance {p : ℕ} [NeZero p] {w : BDWord (ZMod p)} : Decidable (isNegative_poly w) := by
  unfold isNegative_poly; infer_instance

/-- Polymorphic counterpart of `BDWord.isNegative_msb`. -/
lemma isNegative_poly_msb {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (h_w_isU128 : w.isU128_poly) :
    w.isNegative_poly ↔ (w.toBitVec128_poly.msb = true) := by
  have := lt_cases_of_isU128_poly h_w_isU128
  simp [isNegative_poly, BDWord.toBitVec128_poly, BDWord.toNat_poly, BitVec.msb_eq_decide]
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

/-- Polymorphic counterpart of `BDWord.toInt`. -/
def toInt_poly {p : ℕ} [NeZero p] (w : BDWord (ZMod p)) : ℤ :=
  if (isNegative_poly w) then w.toNat_poly - 2 ^ 128 else w.toNat_poly

set_option maxRecDepth 200000

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

/-- Polymorphic counterpart of `BDWord.low_as_extract`. -/
lemma low_as_extract_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (h_w_isU128 : w.isU128_poly) :
    (w.low_poly).toBitVec64 = BitVec.extractLsb 63 0 (w.toBitVec128_poly) := by
  have ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ :=
    lt_cases_of_isU128_poly h_w_isU128
  simp [BDWord.low_poly, BWord.toBitVec64, BDWord.toBitVec128_poly]
  simp [← BitVec.toNat_inj, BWord.toNat_poly, BDWord.toNat_poly]
  omega

/-- Polymorphic counterpart of `BDWord.high_as_extract`. -/
lemma high_as_extract_poly {p : ℕ} [NeZero p]
    {w : BDWord (ZMod p)} (h_w_isU128 : w.isU128_poly) :
    (w.high_poly).toBitVec64 = BitVec.extractLsb 127 64 (w.toBitVec128_poly) := by
  have ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ :=
    lt_cases_of_isU128_poly h_w_isU128
  simp [BDWord.high_poly, BWord.toBitVec64, BDWord.toBitVec128_poly]
  simp [← BitVec.toNat_inj, BWord.toNat_poly, BDWord.toNat_poly]
  omega

end conversions

end BDWord

namespace HWord

/-- Polymorphic companion of `sign_extend_32_to_64_msb`. The 32-bit
sign extension of `HWord` `w` (viewed as `BitVec 64`) is the `Word`
whose two high limbs are `65535` if `w`'s top bit is set, else `0`. -/
lemma sign_extend_32_to_64_msb_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : HWord (ZMod p)} :
    w.isU32_poly →
    BitVec.signExtend 64 w.toBitVec32_poly = Word.toBitVec64
      #v[w[0], w[1],
         if w.toBitVec32_poly.msb = true then 65535 else 0,
         if w.toBitVec32_poly.msb = true then 65535 else 0] := by
  intro is_U32_w
  have ⟨hw0, hw1⟩ := lt_cases_of_isU32_poly is_U32_w
  have hp : 2 ^ 17 < p := Fact.out
  have h_w32 : w.toBitVec32_poly.toNat = w[0].val + w[1].val * 2 ^ 16 := by
    rw [HWord.toBitVec32_poly_toNat_poly is_U32_w]; simp [HWord.toNat_poly]
  have h_w32_lt : w.toBitVec32_poly.toNat < 2 ^ 32 := by rw [h_w32]; omega
  have h_msb_decide : w.toBitVec32_poly.msb = decide (2 ^ 31 ≤ w.toBitVec32_poly.toNat) := by
    simp [BitVec.msb_eq_decide]
  have h65535_val : (65535 : ZMod p).val = 65535 := by
    rw [show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) from by push_cast; rfl]
    rw [ZMod.val_natCast_of_lt (by omega)]
  have h0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  rw [← BitVec.toNat_inj, BitVec.toNat_signExtend, Word.toBitVec64]
  simp only [BitVec.toNat_ofNat, if_pos (show (32 : ℕ) ≤ 64 from by omega),
    BitVec.toNat_setWidth, Word.toNat_poly_def, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
  rw [Nat.mod_eq_of_lt (show w.toBitVec32_poly.toNat < 2 ^ 64 from by omega), h_w32]
  by_cases h_msb : w.toBitVec32_poly.msb = true
  · have h_msb_nat : (2 ^ 31 : ℕ) ≤ w[0].val + w[1].val * 2 ^ 16 := by
      rw [h_msb_decide] at h_msb; rw [h_w32] at h_msb; simpa using h_msb
    simp only [h_msb, if_true, h65535_val]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega
  · simp only [Bool.not_eq_true] at h_msb
    have h_msb_nat : w[0].val + w[1].val * 2 ^ 16 < 2 ^ 31 := by
      rw [h_msb_decide] at h_msb; rw [h_w32] at h_msb; simpa using h_msb
    simp only [h_msb, Bool.false_eq_true, if_false, h0_val]
    rw [Nat.mod_eq_of_lt (by omega)]
    omega

/-- Polymorphic counterpart of `HWord.extend`. Sign-extends a 32-bit `HWord`
to a 64-bit `Word` (when `sgn = true`); zero-extends otherwise. -/
def extend_poly {p : ℕ} [NeZero p] (w : HWord (ZMod p)) (sgn : Bool) : Word (ZMod p) :=
  let ext := (if sgn then (if w.isNegative_poly then (1 : ZMod p) else 0) else 0) * 65535
  #v[w[0], w[1], ext, ext]

/-- Polymorphic counterpart of `HWord.extend_U32_U64`. -/
lemma extend_U32_U64_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : HWord (ZMod p)} (is_U32_w : w.isU32_poly) (sgn : Bool) :
    (w.extend_poly sgn).isU64_poly := by
  have ⟨_, _⟩ := lt_cases_of_isU32_poly is_U32_w
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (65535 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  apply Word.isU64_of_cases_poly <;>
    simp [extend_poly] <;> (try split_ifs) <;>
    (try simp [h65535, h0]) <;> omega

/-- Polymorphic counterpart of `HWord.extend_true_is_signExtend`. Mirrors
`Word.extend_true_is_signExtend_poly` recipe at smaller dimension via
`BitVec.toInt_inj` + `HWord.toBitVec32_poly_toInt_poly` /
`Word.toBitVec64_toInt_poly`. -/
lemma extend_true_is_signExtend_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : HWord (ZMod p)} :
  w.isU32_poly →
  (w.extend_poly true).toBitVec64 = BitVec.signExtend 64 w.toBitVec32_poly
    := by
  set sw := extend_poly w true
  intro is_U32_w
  have ⟨_, _⟩ := lt_cases_of_isU32_poly is_U32_w
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (65535 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  have is_U64_hw : sw.isU64_poly := by
    subst sw; simp [extend_poly]
    apply Word.isU64_of_cases_poly <;> split_ifs <;>
      simp [h65535, h0] <;> omega
  have is_neg : w.isNegative_poly ↔ sw.isNegative_poly := by
    subst sw
    simp [extend_poly, isNegative_poly, Word.isNegative_poly]
    by_cases h : 32768 ≤ w[1].val <;> simp [h, h65535, h0]
  rw [← BitVec.toInt_inj]
  simp [BitVec.toInt_signExtend_of_le]
  rw [HWord.toBitVec32_poly_toInt_poly is_U32_w,
      Word.toBitVec64_toInt_poly is_U64_hw]
  rw [HWord.toInt_poly, Word.toInt_poly]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, extend_poly, Word.toNat_poly, HWord.toNat_poly] <;>
  (rename_i h1 h2;
   simp only [h2, ↓reduceIte, ZMod.cast_eq_val, h65535, h0]) <;>
  push_cast <;> omega

/-- Polymorphic counterpart of `HWord.extend_false_is_setWidth`. -/
lemma extend_false_is_setWidth_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : HWord (ZMod p)} :
  w.isU32_poly →
  (w.extend_poly false).toBitVec64 = BitVec.setWidth 64 w.toBitVec32_poly
    := by
  set sw := extend_poly w false
  intro is_U32_w
  have ⟨_, _⟩ := lt_cases_of_isU32_poly is_U32_w
  have is_U64_hw : sw.isU64_poly := by
    subst sw; simp [extend_poly]
    apply Word.isU64_of_cases_poly <;> simp <;> omega
  rw [← BitVec.toNat_inj]
  rw [Word.toBitVec64_toNat_poly is_U64_hw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [HWord.toBitVec32_poly_toNat_poly is_U32_w]
  simp [sw, Word.toNat_poly, extend_poly, HWord.toNat_poly]

end HWord

namespace Word

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
lemma toBitVec64_toBWord_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} (h_w_isU64 : w.isU64_poly) :
    w.toBWord_poly.toBitVec64 = w.toBitVec64 := by
  rw [← BitVec.toNat_inj]
  rw [BWord.toBitVec64_toNat_poly (toBWord_poly_toU64 h_w_isU64)]
  rw [Word.toBitVec64_toNat_poly h_w_isU64]
  rw [toNat_poly_toBWord_poly h_w_isU64]

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

/-- Polymorphic counterpart of `Word.extend_false_is_setWidth`. -/
lemma extend_false_is_setWidth_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} :
  w.isU64_poly →
  (w.extend_poly false).toBitVec128_poly = BitVec.setWidth 128 w.toBitVec64
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
  rw [Word.toBitVec64_toNat_poly is_U64_w]
  simp [sw, DWord.toNat_poly, extend_poly, Word.toNat_poly]

-- Polymorphic counterpart of `Word.extend_true_is_signExtend`.
-- Earlier proof routed everything through `BitVec.toNat_signExtend` and a
-- `simp only` chain over `BitVec.setWidth`, tripping the kernel's `whnf`
-- re-check (deep recursion); the refactor below splits on
-- `w.isNegative_poly` first and dispatches each case to one of the two
-- structural rewrites of `BitVec.signExtend` (`signExtend_eq_setWidth_of_msb_false`
-- / `signExtend_eq_not_setWidth_not_of_msb_true`), bringing the goal back
-- to a `setWidth`-shaped equality that `extend_false_is_setWidth_poly` (or
-- a parallel computation in the negative case) closes. This keeps the
-- elaborated proof term shallow enough that the kernel re-checks without
-- `set_option debug.skipKernelTC`. See `docs/SKIP_KERNEL_TC.md` for prior
-- history.
lemma extend_true_is_signExtend_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : Word (ZMod p)} :
  w.isU64_poly →
  (w.extend_poly true).toBitVec128_poly = BitVec.signExtend 128 w.toBitVec64
    := by
  intro is_U64_w
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (65535 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  have ⟨_, _, _, _⟩ := lt_cases_of_isU64_poly is_U64_w
  by_cases h : w.isNegative_poly
  · -- negative case: signExtend = ~~~ setWidth (~~~ x); compute both toNats
    rw [BitVec.signExtend_eq_not_setWidth_not_of_msb_true
        ((Word.isNegative_poly_msb is_U64_w).mp h)]
    have is_U128_sw : (w.extend_poly true).isU128_poly := by
      simp [extend_poly]
      apply DWord.isU128_of_cases_poly <;> split_ifs <;>
        simp [h65535, h0] <;> omega
    rw [← BitVec.toNat_inj, DWord.toBitVec128_poly_toNat_poly is_U128_sw]
    simp [extend_poly, DWord.toNat_poly, Word.toNat_poly, h, h65535, h0,
          BitVec.toNat_not, BitVec.toNat_setWidth,
          Word.toBitVec64_toNat_poly is_U64_w]
    omega
  · -- non-negative case: extend_poly w true = extend_poly w false in this
    -- branch, and signExtend = setWidth, so reduce to extend_false case.
    have hmsb : w.toBitVec64.msb = false :=
      Bool.not_eq_true _ |>.mp (fun hm => h ((Word.isNegative_poly_msb is_U64_w).mpr hm))
    rw [BitVec.signExtend_eq_setWidth_of_msb_false hmsb]
    have heq : w.extend_poly true = w.extend_poly false := by
      simp [extend_poly, h]
    rw [heq]
    exact extend_false_is_setWidth_poly is_U64_w

end Word

namespace BWord

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

/-- Polymorphic counterpart of `BWord.extend_false_is_setWidth`. -/
lemma extend_false_is_setWidth_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} :
  w.isU64_poly →
  (w.extend_poly false).toBitVec128_poly = BitVec.setWidth 128 w.toBitVec64
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
  rw [BWord.toBitVec64_toNat_poly is_U64_w]
  simp [sw, BDWord.toNat_poly, extend_poly, BWord.toNat_poly]

-- Polymorphic counterpart of `BWord.extend_true_is_signExtend`.
-- Mirrors the `Word.extend_true_is_signExtend_poly` refactor: case-split on
-- `w.isNegative_poly`, dispatch each case via `signExtend_eq_setWidth_of_msb_false`
-- / `signExtend_eq_not_setWidth_not_of_msb_true`, and reduce the
-- non-negative case to `extend_false_is_setWidth_poly`. Avoids the
-- `BitVec.toNat_signExtend` chain that previously tripped the kernel
-- "deep recursion" re-check on the 8-limb BWord structure.
lemma extend_true_is_signExtend_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BWord (ZMod p)} :
  w.isU64_poly →
  (w.extend_poly true).toBitVec128_poly = BitVec.signExtend 128 w.toBitVec64
    := by
  intro is_U64_w
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly is_U64_w
  have h255 : (255 : ZMod p).val = 255 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (255 : ℕ) < p by omega)
  have h0 : (0 : ZMod p).val = 0 := ZMod.val_zero
  by_cases h : w.isNegative_poly
  · rw [BitVec.signExtend_eq_not_setWidth_not_of_msb_true
        ((BWord.isNegative_poly_msb is_U64_w).mp h)]
    have is_U128_sw : (w.extend_poly true).isU128_poly := by
      simp [extend_poly]
      apply BDWord.isU128_of_cases_poly <;> split_ifs <;>
        simp [h255, h0] <;> omega
    rw [← BitVec.toNat_inj, BDWord.toBitVec128_poly_toNat_poly is_U128_sw]
    simp [extend_poly, BDWord.toNat_poly, BWord.toNat_poly, h, h255, h0,
          BitVec.toNat_not, BitVec.toNat_setWidth,
          BWord.toBitVec64_toNat_poly is_U64_w]
    omega
  · have hmsb : w.toBitVec64.msb = false :=
      Bool.not_eq_true _ |>.mp (fun hm => h ((BWord.isNegative_poly_msb is_U64_w).mpr hm))
    rw [BitVec.signExtend_eq_setWidth_of_msb_false hmsb]
    have heq : w.extend_poly true = w.extend_poly false := by
      simp [extend_poly, h]
    rw [heq]
    exact extend_false_is_setWidth_poly is_U64_w

/-- Polymorphic counterpart of `BWord.low_as_setWidth`. -/
lemma low_as_setWidth_poly {p : ℕ} [NeZero p] {w : BWord (ZMod p)} :
  w.isU64_poly →
  w.low_poly.toBitVec32_poly = BitVec.setWidth 32 w.toBitVec64
    := by
  intro is_U64_w
  have ⟨_, _, _, _, _, _, _, _⟩ := lt_cases_of_isU64_poly is_U64_w
  simp [BWord.low_poly, BHWord.toBitVec32_poly, BHWord.toNat_poly,
        BWord.toBitVec64, BWord.toNat_poly]
  simp [← BitVec.toNat_inj]
  omega

end BWord

namespace BHWord

/-- Polymorphic counterpart of `BHWord.extend`. -/
def extend_poly {p : ℕ} [NeZero p] (w : BHWord (ZMod p)) (sgn : Bool) : BWord (ZMod p) :=
  let ext := (if sgn then (if w.isNegative_poly then (1 : ZMod p) else 0) else 0) * 255
  #v[w[0], w[1], w[2], w[3], ext, ext, ext, ext]

/-- Polymorphic counterpart of `BHWord.extend_U32_U64`. Mirrors
`BWord.extend_U64_U128_poly` recipe at smaller dimension. -/
lemma extend_U32_U64_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BHWord (ZMod p)} (is_U32_w : w.isU32_poly) (sgn : Bool) :
    (w.extend_poly sgn).isU64_poly := by
  have ⟨_, _, _, _⟩ := lt_cases_of_isU32_poly is_U32_w
  have h255 : (255 : ZMod p).val = 255 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (255 : ℕ) < p by omega)
  have h0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  apply BWord.isU64_of_cases_poly <;>
    simp [extend_poly] <;> (try split_ifs) <;>
    (try simp [h255, h0_val]) <;> omega

/-- Polymorphic counterpart of `BHWord.extend_true_is_signExtend`. Mirrors
`BWord.extend_true_is_signExtend_poly` recipe at smaller dimension via
`BitVec.toInt_inj` + `BHWord.toBitVec32_poly_toInt_poly` /
`BWord.toBitVec64_toInt_poly`. -/
lemma extend_true_is_signExtend_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BHWord (ZMod p)} :
  w.isU32_poly →
  (w.extend_poly true).toBitVec64 = BitVec.signExtend 64 w.toBitVec32_poly
    := by
  set sw := extend_poly w true
  intro is_U32_w
  have ⟨_, _, _, _⟩ := lt_cases_of_isU32_poly is_U32_w
  have h255 : (255 : ZMod p).val = 255 := by
    have hp : 131072 < p := by have := (Fact.out : 2 ^ 17 < p); omega
    exact ZMod.val_natCast_of_lt (show (255 : ℕ) < p by omega)
  have h0_val : (0 : ZMod p).val = 0 := ZMod.val_zero
  have is_U64_bhw : sw.isU64_poly := by
    subst sw; simp [extend_poly]
    apply BWord.isU64_of_cases_poly <;> split_ifs <;>
      simp [h255, h0_val] <;> omega
  have is_neg : w.isNegative_poly ↔ sw.isNegative_poly := by
    subst sw
    simp [extend_poly, isNegative_poly, BWord.isNegative_poly]
    by_cases h : 128 ≤ w[3].val <;> simp [h, h255, h0_val]
  rw [← BitVec.toInt_inj]
  simp [BitVec.toInt_signExtend_of_le]
  rw [BHWord.toBitVec32_poly_toInt_poly is_U32_w,
      BWord.toBitVec64_toInt_poly is_U64_bhw]
  rw [BHWord.toInt_poly, BWord.toInt_poly]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, extend_poly, BWord.toNat_poly, BHWord.toNat_poly] <;>
  (rename_i h1 h2;
   simp only [h2, ↓reduceIte, ZMod.cast_eq_val, h255, h0_val]) <;>
  push_cast <;> omega

/-- Polymorphic counterpart of `BHWord.extend_false_is_setWidth`. -/
lemma extend_false_is_setWidth_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {w : BHWord (ZMod p)} :
  w.isU32_poly →
  (w.extend_poly false).toBitVec64 = BitVec.setWidth 64 w.toBitVec32_poly
    := by
  set sw := extend_poly w false
  intro is_U32_w
  have ⟨_, _, _, _⟩ := lt_cases_of_isU32_poly is_U32_w
  have is_U64_bhw : sw.isU64_poly := by
    subst sw; simp [extend_poly]
    apply BWord.isU64_of_cases_poly <;> simp <;> omega
  rw [← BitVec.toNat_inj]
  rw [BWord.toBitVec64_toNat_poly is_U64_bhw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [BHWord.toBitVec32_poly_toNat_poly is_U32_w]
  simp [sw, BWord.toNat_poly, extend_poly, BHWord.toNat_poly]

end BHWord

section Bitwise

namespace Word

/-- Polymorphic counterpart of `Word.and_toBWord`. -/
lemma and_toBWord_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {a b : Word (ZMod p)} : a.isU64_poly → b.isU64_poly →
    a.toBitVec64 &&& b.toBitVec64 =
      a.toBWord_poly.toBitVec64 &&& b.toBWord_poly.toBitVec64 := by
  intro h_a_64 h_b_64
  rw [Word.toBitVec64_toBWord_poly h_a_64, Word.toBitVec64_toBWord_poly h_b_64]

/-- Polymorphic counterpart of `Word.or_toBWord`. -/
lemma or_toBWord_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {a b : Word (ZMod p)} : a.isU64_poly → b.isU64_poly →
    a.toBitVec64 ||| b.toBitVec64 =
      a.toBWord_poly.toBitVec64 ||| b.toBWord_poly.toBitVec64 := by
  intro h_a_64 h_b_64
  rw [Word.toBitVec64_toBWord_poly h_a_64, Word.toBitVec64_toBWord_poly h_b_64]

/-- Polymorphic counterpart of `Word.xor_toBWord`. -/
lemma xor_toBWord_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    {a b : Word (ZMod p)} : a.isU64_poly → b.isU64_poly →
    a.toBitVec64 ^^^ b.toBitVec64 =
      a.toBWord_poly.toBitVec64 ^^^ b.toBWord_poly.toBitVec64 := by
  intro h_a_64 h_b_64
  rw [Word.toBitVec64_toBWord_poly h_a_64, Word.toBitVec64_toBWord_poly h_b_64]

end Word

end Bitwise

lemma shiftRight_eq_sub_mod (x : ℕ) {n : ℕ} :
    x >>> n = (x - (x % 2 ^ n)) >>> n := by
  simp only [Nat.shiftRight_eq_div_pow]; exact Nat.div_eq_sub_mod_div

/-- Polymorphic counterpart of `lt_65536_of_mul_inv_4_lt`: branch-target limb
range check `(x * 4⁻¹).val < 16384` in `ZMod p` lifts to `x.val < 65536`. -/
lemma lt_65536_of_mul_inv_4_lt_poly {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
    (x : ZMod p) (h : (x * (4 : ZMod p)⁻¹).val < 16384) :
    x.val < 65536 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h4ne : (4 : ZMod p) ≠ 0 := by
    have : (4 : ZMod p).val = 4 := val_4_zmod_p
    intro hz; rw [hz, ZMod.val_zero] at this; omega
  have hinv : x * (4 : ZMod p)⁻¹ * 4 = x := by field_simp
  have h4 : (4 : ZMod p).val = 4 := val_4_zmod_p
  apply_fun ZMod.val at hinv
  rw [ZMod.val_mul, h4] at hinv
  have hp : 2 ^ 17 < p := Fact.out
  have hbound : (x * (4 : ZMod p)⁻¹).val * 4 < 65536 := by omega
  have : (x * (4 : ZMod p)⁻¹).val * 4 % p = (x * (4 : ZMod p)⁻¹).val * 4 :=
    Nat.mod_eq_of_lt (by omega)
  rw [this] at hinv
  omega

/-- The byte-slice of an 8-bit `ofNat` equals itself modulo 256. -/
lemma bitVec_ofNat8_eq_of_mod (a b : ℕ) (h : a % 256 = b % 256) :
    BitVec.ofNat 8 a = BitVec.ofNat 8 b := by
  rw [← BitVec.toNat_inj, BitVec.toNat_ofNat, BitVec.toNat_ofNat]
  simpa using h

/-- Polymorphic counterpart of `signExtend64_ofNat8_of_ge_128`. -/
lemma signExtend64_ofNat8_of_ge_128_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (x : ZMod p) (hlt : x.val < 256) (hge : 128 ≤ x.val) :
    BitVec.signExtend 64 (BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x + 65280, (65535 : ZMod p), (65535 : ZMod p), (65535 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb : BitVec.msb (BitVec.ofNat 8 x.val) = true := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp [hmsb, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat]
  rw [Word.toNat_poly_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  have hp : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h65280 : (65280 : ZMod p).val = 65280 := by
    have : (65280 : ZMod p).val = 65280 % p := by
      rw [show (65280 : ZMod p) = ((65280 : ℕ) : ZMod p) from by norm_cast,
          ZMod.val_natCast]
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have : (65535 : ZMod p).val = 65535 % p := by
      rw [show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) from by norm_cast,
          ZMod.val_natCast]
    rw [this, Nat.mod_eq_of_lt (by omega)]
  have hxk_lt : x.val + (65280 : ZMod p).val < p := by rw [h65280]; omega
  have hxk_val : (x + 65280 : ZMod p).val = x.val + 65280 := by
    rw [ZMod.val_add_of_lt hxk_lt, h65280]
  rw [hxk_val, h65535]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Polymorphic counterpart of `nat_decomp_of_inv8_decomp`. -/
lemma nat_decomp_of_inv8_decomp_poly {p : ℕ} [NeZero p] [Fact (2 ^ 17 < p)]
    (lo hi x : ZMod p)
    (h : lo + hi * (2 ^ 8 : ZMod p) = x)
    (hlo : lo.val < 256) (hhi : hi.val < 256) :
    x.val = lo.val + hi.val * 256 := by
  have hp : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h256 : ((2 ^ 8 : ZMod p).val = 256) := by
    have h1 : (2 ^ 8 : ZMod p) = ((256 : ℕ) : ZMod p) := by norm_cast
    rw [h1, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  have hmul : (hi * (2 ^ 8 : ZMod p)).val = hi.val * 256 := by
    rw [ZMod.val_mul, h256, Nat.mod_eq_of_lt (by
      have : hi.val * 256 < 256 * 256 := by
        have : hi.val * 256 ≤ 255 * 256 := Nat.mul_le_mul_right _ (by omega); omega
      omega)]
  have hadd : (lo + hi * (2 ^ 8 : ZMod p)).val = lo.val + hi.val * 256 := by
    rw [ZMod.val_add_of_lt (by rw [hmul]; omega), hmul]
  rw [← h, hadd]

/-- Polymorphic counterpart of `setWidth64_ofNat8`. -/
lemma setWidth64_ofNat8_poly {p : ℕ} [NeZero p]
    (x : ZMod p) (hlt : x.val < 256) :
    BitVec.setWidth 64 (BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, (0 : ZMod p), (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  simp [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat]
  rw [Word.toNat_poly_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- Polymorphic counterpart of `signExtend64_ofNat8_of_lt_128`. -/
lemma signExtend64_ofNat8_of_lt_128_poly {p : ℕ} [NeZero p]
    (x : ZMod p) (hlt : x.val < 256) (hge : x.val < 128) :
    BitVec.signExtend 64 (BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, (0 : ZMod p), (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb : BitVec.msb (BitVec.ofNat 8 x.val) = false := by
    rw [BitVec.msb_eq_decide]; simp [BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt (by omega)]; omega
  simp [hmsb, BitVec.toNat_setWidth, BitVec.toNat_ofNat]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat]
  rw [Word.toNat_poly_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- toNat of `hi ++ lo` as bytes equals `(hi.toNat) * 256 + (lo.toNat)`. Specialized form. -/
private lemma toNat_append_bytes (hi lo : BitVec 8) :
    (hi ++ lo).toNat = hi.toNat * 256 + lo.toNat := by
  rw [BitVec.toNat_append]
  have hlo : lo.toNat < 2 ^ 8 := lo.isLt
  rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hlo, Nat.shiftLeft_eq]

private lemma toNat_concat_halfword_bytes_poly {p : ℕ} [NeZero p]
    (x : ZMod p) (hlt : x.val < 65536) :
    (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val).toNat = x.val := by
  rw [toNat_append_bytes, BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
  have h256 : (2 ^ 8 : ℕ) = 256 := rfl
  rw [h256]
  omega

/-- Polymorphic counterpart of `setWidth64_ofNat16_concat`. -/
lemma setWidth64_ofNat16_concat_poly {p : ℕ} [NeZero p]
    (x : ZMod p) (hlt : x.val < 65536) :
    BitVec.setWidth 64 (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, 0, 0, 0] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_setWidth, toNat_concat_halfword_bytes_poly x hlt]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_poly_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

/-- Polymorphic counterpart of `signExtend64_ofNat16_concat_of_lt_32768`. -/
lemma signExtend64_ofNat16_concat_of_lt_32768_poly {p : ℕ} [NeZero p]
    (x : ZMod p) (hlt : x.val < 65536) (hmsb : x.val < 32768) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, 0, 0, 0] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_false : BitVec.msb (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = false := by
    rw [BitVec.msb_eq_decide, toNat_concat_halfword_bytes_poly x hlt]
    simp only [decide_eq_false_iff_not, not_le]
    change _ < 2 ^ 15
    omega
  rw [hmsb_false]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [BitVec.toNat_setWidth, toNat_concat_halfword_bytes_poly x hlt]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_poly_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

/-- Polymorphic counterpart of `signExtend64_ofNat16_concat_of_ge_32768`. -/
lemma signExtend64_ofNat16_concat_of_ge_32768_poly {p : ℕ} [NeZero p]
    [Fact (2 ^ 17 < p)]
    (x : ZMod p) (hlt : x.val < 65536) (hmsb : 32768 ≤ x.val) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, (65535 : ZMod p), (65535 : ZMod p), (65535 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_true : BitVec.msb (BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = true := by
    rw [BitVec.msb_eq_decide, toNat_concat_halfword_bytes_poly x hlt]
    simp only [decide_eq_true_eq]
    change 2 ^ 15 ≤ _
    omega
  rw [hmsb_true]
  simp only [↓reduceIte]
  rw [BitVec.toNat_setWidth, toNat_concat_halfword_bytes_poly x hlt]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_poly_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have hp : 131072 < p := by
      have := Fact.out (p := 2 ^ 17 < p)
      have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
      omega
    have : (65535 : ZMod p).val = 65535 % p := by
      rw [show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) from by norm_cast,
          ZMod.val_natCast]
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [h65535]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  change x.val + (2 ^ 64 - 2^(8 + 8)) = x.val + 65535 * 2 ^ 16 + 65535 * 2 ^ 32 + 65535 * 2 ^ 48
  omega

private lemma toNat_concat_word_bytes_poly {p : ℕ} [NeZero p]
    (x y : ZMod p) (hx : x.val < 65536) (hy : y.val < 65536) :
    (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val).toNat =
      x.val + y.val * 65536 := by
  have hx_hi : x.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hy_hi : y.val >>> 8 < 256 := by rw [Nat.shiftRight_eq_div_pow]; omega
  have hx_decomp : x.val % 256 + (x.val >>> 8) * 256 = x.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  have hy_decomp : y.val % 256 + (y.val >>> 8) * 256 = y.val := by
    rw [Nat.shiftRight_eq_div_pow]; omega
  simp only [BitVec.toNat_append, BitVec.toNat_ofNat,
    show (2 ^ 8 : ℕ) = 256 from rfl]
  have hx_hi_mod : x.val >>> 8 % 256 = x.val >>> 8 := Nat.mod_eq_of_lt hx_hi
  have hy_hi_mod : y.val >>> 8 % 256 = y.val >>> 8 := Nat.mod_eq_of_lt hy_hi
  rw [hx_hi_mod, hy_hi_mod]
  rw [show y.val >>> 8 <<< 8 ||| y.val % 256 = y.val by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]; omega]
  rw [show y.val <<< 8 ||| x.val >>> 8 = y.val * 256 + x.val >>> 8 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) hx_hi, Nat.shiftLeft_eq]]
  rw [show (y.val * 256 + x.val >>> 8) <<< 8 ||| x.val % 256 =
      (y.val * 256 + x.val >>> 8) * 256 + x.val % 256 by
    rw [← Nat.shiftLeft_add_eq_or_of_lt (i := 8) (by omega), Nat.shiftLeft_eq]]
  have := hx_decomp
  omega

/-- Polymorphic counterpart of `setWidth64_ofNat32_concat`. -/
lemma setWidth64_ofNat32_concat_poly {p : ℕ} [NeZero p]
    (x y : ZMod p) (hx : x.val < 65536) (hy : y.val < 65536) :
    BitVec.setWidth 64 (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, y, (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_setWidth, toNat_concat_word_bytes_poly x y hx hy]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_poly_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

/-- Polymorphic counterpart of `signExtend64_ofNat32_concat_of_lt_32768`. -/
lemma signExtend64_ofNat32_concat_of_lt_32768_poly {p : ℕ} [NeZero p]
    (x y : ZMod p) (hx : x.val < 65536) (hy : y.val < 65536) (hmsb : y.val < 32768) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, y, (0 : ZMod p), (0 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_false : BitVec.msb
      (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
       BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = false := by
    rw [BitVec.msb_eq_decide, toNat_concat_word_bytes_poly x y hx hy]
    simp only [decide_eq_false_iff_not, not_le]
    change _ < 2 ^ 31
    omega
  rw [hmsb_false]
  simp only [Bool.false_eq_true, ↓reduceIte, add_zero]
  rw [BitVec.toNat_setWidth, toNat_concat_word_bytes_poly x y hx hy]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_poly_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, ZMod.val_zero]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  ring

/-- Polymorphic counterpart of `signExtend64_ofNat32_concat_of_ge_32768`. -/
lemma signExtend64_ofNat32_concat_of_ge_32768_poly {p : ℕ} [NeZero p]
    [Fact (2 ^ 17 < p)]
    (x y : ZMod p) (hx : x.val < 65536) (hy : y.val < 65536) (hmsb : 32768 ≤ y.val) :
    BitVec.signExtend 64 (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
      BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) =
      Word.toBitVec64 #v[x, y, (65535 : ZMod p), (65535 : ZMod p)] := by
  apply BitVec.toNat_inj.mp
  rw [BitVec.toNat_signExtend]
  have hmsb_true : BitVec.msb
      (BitVec.ofNat 8 (y.val >>> 8) ++ BitVec.ofNat 8 y.val ++
       BitVec.ofNat 8 (x.val >>> 8) ++ BitVec.ofNat 8 x.val) = true := by
    rw [BitVec.msb_eq_decide, toNat_concat_word_bytes_poly x y hx hy]
    simp only [decide_eq_true_eq]
    change 2 ^ 31 ≤ _
    omega
  rw [hmsb_true]
  simp only [↓reduceIte]
  rw [BitVec.toNat_setWidth, toNat_concat_word_bytes_poly x y hx hy]
  unfold Word.toBitVec64
  rw [BitVec.toNat_ofNat, Word.toNat_poly_def]
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  have hp : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h65535 : (65535 : ZMod p).val = 65535 := by
    have : (65535 : ZMod p).val = 65535 % p := by
      rw [show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) from by norm_cast,
          ZMod.val_natCast]
    rw [this, Nat.mod_eq_of_lt (by omega)]
  rw [h65535]
  rw [Nat.mod_eq_of_lt (by omega)]
  rw [Nat.mod_eq_of_lt (by omega)]
  change x.val + y.val * 2 ^ 16 + (2 ^ 64 - 2^(8 + 8 + 8 + 8)) =
       x.val + y.val * 2 ^ 16 + 65535 * 2 ^ 32 + 65535 * 2 ^ 48
  omega

section getByte

namespace BitVec

def getByte {n : ℕ} (bv : BitVec n) (i : ℕ) : ℕ := (bv.extractLsb (i * 8 + 7) (i * 8)).toNat

lemma getByte_is_byte : getByte bv i < 256 := by simp [getByte]; omega

end BitVec

end getByte

section cross_product

def cp_poly {p : ℕ} [NeZero p] {n : ℕ} (a b : Vector (ZMod p) n) (k : ℕ) (hk : k < n) : ZMod p :=
  let product := ((Vector.ofFn (fun i => a.get ⟨i.val, by omega⟩ * b.get ⟨k - i.val, by
                     have h : i.val < (k + 1) := i.isLt
                     omega⟩)) : Vector (ZMod p) (k + 1)).toList
  product.foldl (· + ·) 0

end cross_product
