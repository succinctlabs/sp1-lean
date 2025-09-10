import SP1Foundations.Unsigned
import SP1Foundations.Tactics

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
  . unfold BitVec.toNat; apply bv.toFin.isLt
  . apply Nat.pow_le_pow_right (by simp) (by assumption)

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

lemma eq_pointwise (w w': HWord T) : (w[0] = w'[0]) ∧ (w[1] = w'[1]) ↔ w = w' := by
   constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `HWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : HWord T → Prop}
    (mk : ∀ x1 x2 : T, C #v[x1, x2]) (w : HWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U32

/-- `isU32 w` means that each limb of the `HWord` is properly bounded. -/
def isU32 (w : HWord (Fin BB)) : Prop := ∀ i : Fin HWORD_SIZE, w[i].val < 2^16

@[aesop unsafe apply]
lemma isU32_of_cases {w : HWord (Fin BB)}
    (h0 : w[0].val < 2^16) (h1 : w[1].val < 2^16) : w.isU32
  := by intro i; fin_cases i <;> simpa

/-- Pull in bounds on a `HWord`s limbs given a `isU32` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU32 {w : HWord (Fin BB)} (hw : w.isU32) :
    w[0].val < 2^16 ∧ w[1].val < 2^16 :=
  ⟨hw 0, hw 1⟩

end U32

section conversions

/-- Convert a `HWord` to a `Nat` by shifting and adding the limbs. -/
def toNat (w : HWord (Fin BB)) : ℕ := w[0] + w[1] * 2^16

lemma toNat_lt_of_isU32 {w : HWord (Fin BB)} (hw : w.isU32) : w.toNat < 2^32 := by
  unfold toNat
  aesop (add 50% tactic (by omega))

/-- Convert a `HWord` to a `BitVec 32` by shifting and adding the limbs. -/
def toBitVec32 (w : HWord (Fin BB)) : BitVec 32 := BitVec.ofNat 32 w.toNat

lemma toBitVec32_toNat {w : HWord (Fin BB)} (hw : w.isU32) :
    w.toBitVec32.toNat = w.toNat := by
  simp only [toBitVec32, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU32 hw
  omega

/-- Convert a `HWord` to a `BitVec 64` by shifting and adding the limbs, with sign extension. -/
def toBitVec64 (w : HWord (Fin BB)) : BitVec 64 := BitVec.signExtend 64 w.toBitVec32

/-- A 32-bit integer is negative if its msb equals one -/
@[grind] def isNegative (w : HWord (Fin BB)) : Prop := w[1] ≥ 32768
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

lemma isNegative_msb
  {w : HWord (Fin BB)}
  (h_w_isU32 : w.isU32) :
    w.isNegative ↔ (w.toBitVec32.msb = true) := by
  have := lt_cases_of_isU32 h_w_isU32
  simp [isNegative, toBitVec32, toNat, BitVec.msb_eq_decide]
  omega

/-- Convert a `HWord` to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : HWord (Fin BB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 32 else w.toNat

lemma toInt_lb {w : HWord (Fin BB)} (is_U32_w : w.isU32) :
  -2147483648 ≤ w.toInt := by
  apply HWord.lt_cases_of_isU32 at is_U32_w
  simp [HWord.toInt, HWord.isNegative, HWord.toNat] at *
  omega

lemma toInt_ub {w : HWord (Fin BB)} (is_U32_w : w.isU32) :
  w.toInt < 2147483648 := by
  apply HWord.lt_cases_of_isU32 at is_U32_w
  simp [HWord.toInt, HWord.isNegative, HWord.toNat] at *
  omega

lemma eq_toInt_eq {wx wy : HWord (Fin BB)} (is32_wx : HWord.isU32 wx) (is32_wy : HWord.isU32 wy) :
  wx = wy ↔ wx.toInt = wy.toInt := by
  constructor
  . simp_all
  . apply HWord.lt_cases_of_isU32 at is32_wx
    apply HWord.lt_cases_of_isU32 at is32_wy
    unfold HWord.toInt HWord.isNegative HWord.toNat; intro heq
    rw [← HWord.eq_pointwise]
    omega

lemma toBitVec32_toInt {w : HWord (Fin BB)} (h_w_isU64 : w.isU32) :
    w.toBitVec32.toInt = w.toInt
  := by
    have := lt_cases_of_isU32 h_w_isU64
    have := toNat_lt_of_isU32 h_w_isU64
    unfold toBitVec32 toInt BitVec.toInt
    simp_all only [Nat.reducePow, Int.reducePow, toNat_ofNat, Nat.cast_ofNat]
    rw [Nat.mod_eq_of_lt this]
    by_cases h_neg : w.isNegative <;> unfold isNegative at * <;>
    unfold toNat at * <;> simp_all <;> omega

lemma toBitVec64_toInt {w : HWord (Fin BB)} (h_w_isU32 : w.isU32) :
    w.toBitVec64.toInt = w.toInt
  := by
    have := lt_cases_of_isU32 h_w_isU32
    simp [toBitVec64, BitVec.toInt_signExtend]
    rw [toBitVec32_toInt h_w_isU32]
    unfold toInt isNegative toNat
    refine Int.bmod_eq_of_le ?_ ?_ <;> omega

lemma isNegative_toInt {w : HWord (Fin BB)} (is32_w : HWord.isU32 w) :
  w.isNegative ↔ w.toInt < 0
    := by
  unfold HWord.toInt HWord.isNegative HWord.toNat
  apply HWord.lt_cases_of_isU32 at is32_w
  omega

lemma sign_cases {w : HWord (Fin BB)} (is32_w : HWord.isU32 w) : w.toInt.sign = if w.isNegative then -1 else if w.toInt = 0 then 0 else 1 := by
  simp [HWord.isNegative_toInt is32_w]
  exact Int.sign_cases w.toInt

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

lemma eq_pointwise {w w': Word T} : (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ↔ w = w' := by
   constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `Word`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : Word T → Prop}
    (mk : ∀ x1 x2 x3 x4 : T, C #v[x1, x2, x3, x4]) (w : Word T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U64

/-- `isU64 w` means that each limb of the `Word` is properly bounded. -/
def isU64 (w : Word (Fin BB)) : Prop := ∀ i : Fin WORD_SIZE, w[i].val < 2^16

@[aesop unsafe apply]
lemma isU64_of_cases {w : Word (Fin BB)}
    (h0 : w[0].val < 2^16) (h1 : w[1].val < 2^16)
    (h2 : w[2].val < 2^16) (h3 : w[3].val < 2^16) : w.isU64
  := by intro i; fin_cases i <;> simpa

/-- Pull in bounds on a word's limbs given a `isU64` proof. -/
@[aesop unsafe forward, grind →]
lemma lt_cases_of_isU64 {w : Word (Fin BB)} (hw : w.isU64) :
    w[0].val < 2^16 ∧ w[1].val < 2^16 ∧ w[2].val < 2^16 ∧ w[3].val < 2^16 :=
  ⟨hw 0, hw 1, hw 2, hw 3⟩

@[simp] -- common enough to want a lemma
lemma four_isU64 : Word.isU64 #v[4, 0, 0, 0] := by aesop

end U64

section conversions

/-- Convert a `Word` to a `Nat` by shifting and adding the limbs. -/
@[aesop unsafe forward]
def toNat (w : Word (Fin BB)) : ℕ := w[0] + w[1] * 2^16 + w[2] * 2^32 + w[3] * 2^48

lemma toNat_lt_of_isU64 {w : Word (Fin BB)} (hw : w.isU64) : w.toNat < 2^64 := by
  unfold Word.toNat
  aesop (add 50% tactic (by omega))

lemma eq_toNat_eq {wx wy : Word (Fin BB)} (is64_wx : Word.isU64 wx) (is64_wy : Word.isU64 wy) :
  wx = wy ↔ wx.toNat = wy.toNat := by
  constructor
  . simp_all
  . apply Word.lt_cases_of_isU64 at is64_wx
    apply Word.lt_cases_of_isU64 at is64_wy
    unfold Word.toNat; intro heq
    rw [← Word.eq_pointwise]
    omega

lemma toNat_reconstruct {w : Word (Fin BB)} {x : ℕ} (is64_w : Word.isU64 w) :
  w.toNat = x →
    w = #v[⟨x % 65536, by omega⟩, ⟨ x / 65536 % 65536, by omega ⟩, ⟨ x / 4294967296 % 65536, by omega ⟩, ⟨ x / 281474976710656 % 65536, by omega ⟩ ] := by
  intro toNat; rw [← toNat]; clear toNat
  apply Word.lt_cases_of_isU64 at is64_w
  rw [← Word.eq_pointwise]
  simp_all [Word.toNat, Fin.ext_iff]
  split_ands <;> omega

/-- Convert a `Word` to a `BitVec 64` by shifting and adding the limbs. -/
def toBitVec64 (w : Word (Fin BB)) : BitVec 64 := BitVec.ofNat 64 w.toNat

lemma toBitVec64_toNat {w : Word (Fin BB)} (hw : w.isU64) :
    w.toBitVec64.toNat = w.toNat := by
  simp only [toBitVec64, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU64 hw
  omega

/-- A 64-bit integer is negative if its msb equals one -/
@[grind] def isNegative (w : Word (Fin BB)) : Prop := w[3] ≥ 32768
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

lemma isNegative_msb
  {w : Word (Fin BB)}
  (h_w_isU64 : w.isU64) :
    w.isNegative ↔ (w.toBitVec64.msb = true) := by
  have := lt_cases_of_isU64 h_w_isU64
  simp [isNegative, toBitVec64, toNat, BitVec.msb_eq_decide]
  omega

/-- Obtain the low 32 bits of a `Word` -/
def low (w : Word (Fin BB)) : HWord (Fin BB) := #v[w[0], w[1]]

lemma isU64_low_isU32 {w : Word (Fin BB)} (hw : w.isU64) : w.low.isU32 := by aesop

lemma low_toNat (hw : HWord.isU32 #v[b0, b1]): (Word.toBitVec64 #v[b0, b1, 0, 0]).toNat = HWord.toNat #v[b0, b1] := by
  rw [Word.toBitVec64_toNat]
  . simp [Word.toNat, HWord.toNat]
  . apply HWord.lt_cases_of_isU32 at hw; apply Word.isU64_of_cases <;> simp_all

lemma setWidth_eq_low {w : Word (Fin BB)} (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 w.toBitVec64 = w.low.toBitVec32
  := by
    have ⟨ _, _, _, _ ⟩ := lt_cases_of_isU64 h_w_isU64
    simp [toBitVec64, ← BitVec.toNat_inj, low, Word.toNat, HWord.toBitVec32, HWord.toNat]
    omega

/-- Obtain the high 32 bits of a `Word` -/
def high (w : Word (Fin BB)) : HWord (Fin BB) := #v[w[2], w[3]]

lemma isU64_high_isU32 {w : Word (Fin BB)} (hw : w.isU64) : w.high.isU32 := by aesop

lemma setWidth_rshift_eq_high {w : Word (Fin BB)} (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 (w.toBitVec64 >>> 32) = w.high.toBitVec32
  := by
    have ⟨ _, _, _, _ ⟩ := lt_cases_of_isU64 h_w_isU64
    simp_all [toBitVec64, ← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow, high, Word.toNat, HWord.toBitVec32, HWord.toNat]
    omega

/-- Convert a `Word` to a `BitVec 64` by shifting and adding the limbs, supplying a proof . -/
def toBitVec64LT {w : Word (Fin BB)} (h_w : w.isU64) : BitVec 64 :=
  BitVec.ofNatLT w.toNat (by
    simp [Word.toNat]
    have := h_w 0
    have := h_w 1
    have := h_w 2
    have := h_w 3
    simp at *
    linarith)

/-- Convert a `Word` to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : Word (Fin BB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 64 else w.toNat

lemma eq_toInt_eq {wx wy : Word (Fin BB)} (is64_wx : Word.isU64 wx) (is64_wy : Word.isU64 wy) :
  wx = wy ↔ wx.toInt = wy.toInt := by
  constructor
  . simp_all
  . apply Word.lt_cases_of_isU64 at is64_wx
    apply Word.lt_cases_of_isU64 at is64_wy
    unfold Word.toInt Word.isNegative Word.toNat; intro heq
    rw [← Word.eq_pointwise]
    omega

lemma toInt_lb {w : Word (Fin BB)} (is_U64_w : w.isU64) :
  -9223372036854775808 ≤ w.toInt := by
  apply Word.lt_cases_of_isU64 at is_U64_w
  simp [Word.toInt, Word.isNegative, Word.toNat] at *
  omega

lemma toInt_ub {w : Word (Fin BB)} (is_U64_w : w.isU64) :
  w.toInt < 9223372036854775808 := by
  apply Word.lt_cases_of_isU64 at is_U64_w
  simp [Word.toInt, Word.isNegative, Word.toNat] at *
  omega

lemma isU64_toInt {w : Word (Fin BB)} (is64_w : Word.isU64 w) : - 2^63 ≤ w.toInt ∧ w.toInt < 2^63 := by
  unfold Word.toInt Word.isNegative Word.toNat
  grind

lemma toBitVec64_toInt {w : Word (Fin BB)} (h_w_isU64 : w.isU64) :
    w.toBitVec64.toInt = w.toInt
  := by
    rw [BitVec.toInt, Word.toInt]
    split_ifs <;>
    rw [isNegative_msb h_w_isU64] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec64_toNat h_w_isU64] at * <;>
    omega

lemma isNegative_toInt {w : Word (Fin BB)} (is64_w : Word.isU64 w) :
  w.isNegative ↔ w.toInt < 0
    := by
  unfold Word.toInt Word.isNegative Word.toNat
  grind

lemma toInt_nneg_reconstruct {w : Word (Fin BB)} {x : ℤ} (is64_w : Word.isU64 w) (nneg : 0 ≤ x) :
  w.toInt = x →
    w = #v[⟨x.toNat % 65536, by omega⟩, ⟨ x.toNat / 65536 % 65536, by omega ⟩, ⟨ x.toNat / 4294967296 % 65536, by omega ⟩, ⟨ x.toNat / 281474976710656 % 65536, by omega ⟩ ] := by
  intro toInt; rw [← toInt]
  have nneg : ¬ w.isNegative := by rw [isNegative_toInt is64_w]; omega
  apply Word.lt_cases_of_isU64 at is64_w
  rw [← Word.eq_pointwise]
  simp_all [Word.toInt, Word.toNat, Fin.ext_iff]
  split_ands <;> omega

lemma sign_cases {w : Word (Fin BB)} (is64_w : Word.isU64 w) : w.toInt.sign = if w.isNegative then -1 else if w.toInt = 0 then 0 else 1 := by
  simp [Word.isNegative_toInt is64_w]
  exact Int.sign_cases w.toInt

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

lemma eq_pointwise {w w': DWord T} : (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ∧ (w[4] = w'[4]) ∧ (w[5] = w'[5]) ∧ (w[6] = w'[6]) ∧ (w[7] = w'[7]) ↔ w = w' := by
   constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `DWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : DWord T → Prop}
    (mk : ∀ x1 x2 x3 x4 x5 x6 x7 x8 : T, C #v[x1, x2, x3, x4, x5, x6, x7, x8]) (w : DWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U128

/-- `is128 w` means that each limb of the `DWord` is properly bounded. -/
def isU128 (w : DWord (Fin BB)) : Prop := ∀ i : Fin DWORD_SIZE, w[i].val < 2^16

@[aesop unsafe apply]
lemma isU128_of_cases {w : DWord (Fin BB)}
    (h0 : w[0].val < 2^16) (h1 : w[1].val < 2^16)
    (h2 : w[2].val < 2^16) (h3 : w[3].val < 2^16)
    (h4 : w[4].val < 2^16) (h5 : w[5].val < 2^16)
    (h6 : w[6].val < 2^16) (h7 : w[7].val < 2^16) : w.isU128
  := by intro i; fin_cases i <;> simpa

/-- Pull in bounds on a word's limbs given a `isU128` proof. -/
@[aesop unsafe forward, grind →]
lemma lt_cases_of_isU128 {w : DWord (Fin BB)} (hw : w.isU128) :
    w[0].val < 2^16 ∧ w[1].val < 2^16 ∧ w[2].val < 2^16 ∧ w[3].val < 2^16 ∧
    w[4].val < 2^16 ∧ w[5].val < 2^16 ∧ w[6].val < 2^16 ∧ w[7].val < 2^16 :=
  ⟨hw 0, hw 1, hw 2, hw 3, hw 4, hw 5, hw 6, hw 7⟩

end U128

section conversions

/-- Convert a `DWord` to a `Nat` by shifting and adding the limbs. -/
@[aesop unsafe forward]
def toNat (w : DWord (Fin BB)) : ℕ := w[0] + w[1] * 2^16 + w[2] * 2^32 + w[3] * 2^48 + w[4] * 2^64 + w[5] * 2^80 + w[6] * 2^96 + w[7] * 2^112

lemma eq_toNat_eq {wx wy : DWord (Fin BB)} (is128_wx : DWord.isU128 wx) (is128_wy : DWord.isU128 wy) :
  wx = wy ↔ wx.toNat = wy.toNat := by
  constructor
  . simp_all
  . apply DWord.lt_cases_of_isU128 at is128_wx
    apply DWord.lt_cases_of_isU128 at is128_wy
    unfold DWord.toNat; intro heq
    rw [← DWord.eq_pointwise]
    omega

/-- Convert a `DWord` to a `BitVec 128` by shifting and adding the limbs. -/
def toBitVec128 (w : DWord (Fin BB)) : BitVec 128 := BitVec.ofNat 128 w.toNat

lemma toBitVec128_toNat {w : DWord (Fin BB)} (hw : w.isU128) :
    w.toBitVec128.toNat = w.toNat := by
  simp only [toBitVec128, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU128 hw
  omega

/-- A 128-bit integer is negative if its msb equals one -/
@[grind] def isNegative (w : DWord (Fin BB)) : Prop := w[7] ≥ 32768
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

lemma isNegative_msb
  {w : DWord (Fin BB)}
  (h_w_isU128 : w.isU128) :
    w.isNegative ↔ (w.toBitVec128.msb = true) := by
  have := lt_cases_of_isU128 h_w_isU128
  simp [isNegative, toBitVec128, toNat, BitVec.msb_eq_decide]
  omega

/-- Obtain the low 64 bits of a `DWord` -/
def low (w : DWord (Fin BB)) : Word (Fin BB) := #v[w[0], w[1], w[2], w[3]]

lemma isU128_low_isU64 {w : DWord (Fin BB)} (hw : w.isU128) : w.low.isU64 := by aesop

lemma setWidth_eq_low {w : DWord (Fin BB)} (h_w_isU64 : w.isU128) :
    BitVec.setWidth 64 w.toBitVec128 = w.low.toBitVec64
  := by
    have ⟨ _, _, _, _, _, _, _, _ ⟩ := lt_cases_of_isU128 h_w_isU64
    simp [toBitVec128, ← BitVec.toNat_inj, low, DWord.toNat, Word.toBitVec64, Word.toNat]
    omega

/-- Obtain the high 64 bits of a `DWord` -/
def high (w : DWord (Fin BB)) : Word (Fin BB) := #v[w[4], w[5], w[6], w[7]]

lemma isU128_high_isU32 {w : DWord (Fin BB)} (hw : w.isU128) : w.high.isU64 := by aesop

lemma setWidth_rshift_eq_high {w : DWord (Fin BB)} (h_w_isU128 : w.isU128) :
    BitVec.setWidth 64 (w.toBitVec128 >>> 64) = w.high.toBitVec64
  := by
    have ⟨ _, _, _, _, _, _, _, _ ⟩ := lt_cases_of_isU128 h_w_isU128
    simp_all [toBitVec128, ← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow, high, DWord.toNat, Word.toBitVec64, Word.toNat]
    omega

/-- Convert a `DWord` to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : DWord (Fin BB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 128 else w.toNat

lemma eq_toInt_eq {wx wy : DWord (Fin BB)} (is128_wx : DWord.isU128 wx) (is128_wy : DWord.isU128 wy) :
  wx = wy ↔ wx.toInt = wy.toInt := by
  constructor
  . simp_all
  . apply DWord.lt_cases_of_isU128 at is128_wx
    apply DWord.lt_cases_of_isU128 at is128_wy
    unfold DWord.toInt DWord.isNegative DWord.toNat; intro heq
    rw [← DWord.eq_pointwise]
    omega

lemma isU128_toInt {w : DWord (Fin BB)} (is128_w : DWord.isU128 w) : - 2^127 ≤ w.toInt ∧ w.toInt < 2^127 := by
  unfold DWord.toInt DWord.isNegative DWord.toNat
  apply DWord.lt_cases_of_isU128 at is128_w
  omega

lemma toBitVec128_toInt {w : DWord (Fin BB)} (h_w_isU128 : w.isU128) :
    w.toBitVec128.toInt = w.toInt
  := by
    rw [BitVec.toInt, DWord.toInt]
    split_ifs <;>
    rw [isNegative_msb h_w_isU128] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec128_toNat h_w_isU128] at * <;>
    omega

lemma isNegative_toInt {w : DWord (Fin BB)} (is128_w : DWord.isU128 w) :
  w.isNegative ↔ w.toInt < 0
    := by
  unfold DWord.toInt DWord.isNegative DWord.toNat
  apply DWord.lt_cases_of_isU128 at is128_w
  omega

lemma sign_cases {w : DWord (Fin BB)} (is128_w : DWord.isU128 w) : w.toInt.sign = if w.isNegative then -1 else if w.toInt = 0 then 0 else 1 := by
  simp [DWord.isNegative_toInt is128_w]
  exact Int.sign_cases w.toInt

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

lemma eq_pointwise {w w': BHWord T} :
    (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ↔ w = w' := by
  constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `BHWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : BHWord T → Prop}
    (mk : ∀ x0 x1 x2 x3 : T, C #v[x0, x1, x2, x3]) (w : BHWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U32

/-- `isU32 w` means that each limb of the word is properly bounded. -/
def isU32 (w : BHWord (Fin BB)) : Prop := ∀ i : Fin BYTE_HWORD_SIZE, w[i].val < 256

@[aesop unsafe apply]
lemma isU32_of_cases {w : BHWord (Fin BB)}
    (h0 : w[0].val < 256) (h1 : w[1].val < 256)
    (h2 : w[2].val < 256) (h3 : w[3].val < 256) : w.isU32
  := by intro i; fin_cases i <;> simpa

/-- Pull in bounds on a `BHWord`s limbs given a `isU32` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU32 {w : BHWord (Fin BB)} (hbhw : w.isU32) :
    w[0].val < 256 ∧ w[1].val < 256 ∧ w[2].val < 256 ∧ w[3].val < 256
    :=
  ⟨hbhw 0, hbhw 1, hbhw 2, hbhw 3⟩

end U32

section conversions

/-- Convert a `BHWord` to a `Nat` by shifting and adding the limbs. -/
def toNat (w : BHWord (Fin BB)) : ℕ :=
  w[0] + w[1] * 2^8 + w[2] * 2^16 + w[3] * 2^24

lemma toNat_lt_of_isU32 {w : BHWord (Fin BB)} (hw : w.isU32) : w.toNat < 2^32 := by
  unfold toNat
  aesop (add 50% tactic (by omega))

/-- Convert a `BHWord` to a `BitVec 32` by shifting and adding the limbs. -/
def toBitVec32 (w : BHWord (Fin BB)) : BitVec 32 := BitVec.ofNat 32 w.toNat

lemma toBitVec32_toNat {w : BHWord (Fin BB)} (hw : w.isU32) :
    w.toBitVec32.toNat = w.toNat := by
  simp only [toBitVec32, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU32 hw
  omega

/-- A 32-bit integer is negative if its msb equals one -/
@[grind] def isNegative (w : BHWord (Fin BB)) : Prop := w[3] ≥ 128
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

lemma isNegative_msb
  {w : BHWord (Fin BB)}
  (h_w_isU32 : w.isU32) :
    w.isNegative ↔ (w.toBitVec32.msb = true) := by
  have := lt_cases_of_isU32 h_w_isU32
  simp [isNegative, BHWord.toBitVec32, BHWord.toNat, BitVec.msb_eq_decide]
  omega

lemma isNegative_BitVec.toInt
  {w : BHWord (Fin BB)}
  (h_w_isU32 : w.isU32) :
    w.isNegative ↔ ¬ 2 * w.toNat < 2^32 := by
  rw [isNegative_msb h_w_isU32]
  simp [BitVec.msb_eq_decide]
  rw [toBitVec32_toNat h_w_isU32]
  omega

/-- Convert a `BHWord` to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : BHWord (Fin BB)) : ℤ :=
  if (isNegative w) then w.toNat - 2^32 else w.toNat

lemma toBitVec32_toInt {w : BHWord (Fin BB)} (h_w_isU32 : w.isU32) :
    w.toBitVec32.toInt = w.toInt
  := by
    have := lt_cases_of_isU32 h_w_isU32
    have : w.toNat < 2^32 := by unfold BHWord.toNat; omega
    simp_all [toBitVec32, toInt, BitVec.toInt]
    split_ifs <;> rw [isNegative_BitVec.toInt h_w_isU32] at * <;> omega

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

lemma eq_pointwise {w w': BWord T} :
    (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ∧
    (w[4] = w'[4]) ∧ (w[5] = w'[5]) ∧ (w[6] = w'[6]) ∧ (w[7] = w'[7]) ↔ w = w' := by
  constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `BWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : BWord T → Prop}
    (mk : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : T, C #v[x0, x1, x2, x3, x4, x5, x6, x7]) (w : BWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U64

/-- `isU64 w` means that each limb of the `BWord` is properly bounded. -/
def isU64 (w : BWord (Fin BB)) : Prop := ∀ i : Fin BYTE_WORD_SIZE, w[i].val < 2^8

@[aesop unsafe apply]
lemma isU64_of_cases {w : BWord (Fin BB)}
    (h0 : w[0].val < 2^8) (h1 : w[1].val < 2^8)
    (h2 : w[2].val < 2^8) (h3 : w[3].val < 2^8)
    (h4 : w[4].val < 2^8) (h5 : w[5].val < 2^8)
    (h6 : w[6].val < 2^8) (h7 : w[7].val < 2^8) : w.isU64
  := by intro i; fin_cases i <;> simpa

/-- Pull in bounds on a `BWord`'s limbs given a `isU64` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU64 {w : BWord (Fin BB)} (hbw : w.isU64) :
    w[0].val < 2^8 ∧ w[1].val < 2^8 ∧ w[2].val < 2^8 ∧ w[3].val < 2^8 ∧
    w[4].val < 2^8 ∧ w[5].val < 2^8 ∧ w[6].val < 2^8 ∧ w[7].val < 2^8 :=
  ⟨hbw 0, hbw 1, hbw 2, hbw 3, hbw 4, hbw 5, hbw 6, hbw 7⟩

end U64

section conversions

/-- Convert a `BWord` to a `Word` by combining the limbs. -/
def toWord (w : BWord (Fin BB)) : Word (Fin BB) :=
  #v[w[0] + w[1] * 256, w[2] + w[3] * 256, w[4] + w[5] * 256, w[6] + w[7] * 256]

/-- Convert a `BWord` to a `Nat` by shifting and adding the limbs. -/
def toNat (w : BWord (Fin BB)) : ℕ := w[0] + w[1] * 2^8 + w[2] * 2^16 + w[3] * 2^24 + w[4] * 2^32 + w[5] * 2^40 + w[6] * 2^48 + w[7] * 2^56

lemma toNat_toWord
  {w : BWord (Fin BB)}
  (h_w_isU64 : w.isU64) :
    w.toNat = Word.toNat (w.toWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [toNat, toWord, Word.toNat]
  simp [Fin.add_def, Fin.mul_def]
  omega

lemma toWord_U64 {w : BWord (Fin BB)} (h_w_isU64 : w.isU64) : w.toWord.isU64
  := by
    have := lt_cases_of_isU64 h_w_isU64
    simp [toWord]
    apply Word.isU64_of_cases <;> simp <;> grind

/-- Convert a `BWord` to a `BitVec 64` by shifting and adding the limbs. -/
def toBitVec64 (w : BWord (Fin BB)) : BitVec 64 := BitVec.ofNat 64 w.toNat

lemma toBitVec64_toNat {w : BWord (Fin BB)} (hw : w.isU64) :
    w.toBitVec64.toNat = w.toNat := by
  simp only [toBitVec64, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU64 hw
  omega

lemma toWord_toBitVec64 {w : BWord (Fin BB)} (h_w_isU64 : w.isU64) :
    w.toWord.toBitVec64 = w.toBitVec64
  := by
    have := lt_cases_of_isU64 h_w_isU64
    rw [← BitVec.toNat_inj]
    simp [BWord.toBitVec64, Word.toBitVec64]; congr
    simp [BWord.toWord, Word.toNat, BWord.toNat]
    grind

/-- A 64-bit integer is negative if its msb equals one -/
@[grind] def isNegative (w : BWord (Fin BB)) : Prop := w[7] ≥ 128
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

lemma isNegative_toWord
  {w : BWord (Fin BB)}
  (h_w_isU64 : w.isU64) :
    w.isNegative ↔ Word.isNegative (w.toWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [isNegative, Word.isNegative, toWord]
  grind

lemma isNegative_msb
  {w : BWord (Fin BB)}
  (h_w_isU64 : w.isU64) :
    w.isNegative ↔ (w.toBitVec64.msb = true) := by
  have := lt_cases_of_isU64 h_w_isU64
  simp [isNegative, BWord.toBitVec64, BWord.toNat, BitVec.msb_eq_decide]
  omega

/-- Convert a `BWord` to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : BWord (Fin BB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 64 else w.toNat

lemma toInt_toWord
  {w : BWord (Fin BB)}
  (h_w_isU64 : w.isU64) :
    w.toInt = Word.toInt (w.toWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [toWord, toInt, toNat, Word.toInt, Word.toNat, isNegative, Word.isNegative]
  simp [Fin.le_def, Fin.add_def, Fin.mul_def]
  omega

lemma toBitVec64_toInt {w : BWord (Fin BB)} (h_w_isU64 : w.isU64) :
    w.toBitVec64.toInt = w.toInt
  := by
    rw [BitVec.toInt, BWord.toInt]
    split_ifs <;>
    rw [isNegative_msb h_w_isU64] at * <;>
    simp [BitVec.msb_eq_decide] at * <;>
    rw [toBitVec64_toNat h_w_isU64] at * <;>
    omega

/-- Obtain the low 32 bits of a `BWord` -/
def low (w : BWord (Fin BB)) : BHWord (Fin BB) := #v[w[0], w[1], w[2], w[3]]

lemma isU64_low_isU32 {w : BWord (Fin BB)} (hw : w.isU64) : w.low.isU32 := by aesop

lemma setWidth_eq_low {w : BWord (Fin BB)} (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 w.toBitVec64 = w.low.toBitVec32
  := by
    have ⟨ _, _, _, _ ⟩ := lt_cases_of_isU64 h_w_isU64
    simp [toBitVec64, ← BitVec.toNat_inj, low, BWord.toNat, BHWord.toBitVec32, BHWord.toNat]
    omega

/-- Obtain the high 32 bits of a `BWord` -/
def high (w : BWord (Fin BB)) : BHWord (Fin BB) := #v[w[4], w[5], w[6], w[7]]

lemma isU64_high_isU32 {w : BWord (Fin BB)} (hw : w.isU64) : w.high.isU32 := by aesop

lemma setWidth_rshift_eq_high {w : BWord (Fin BB)} (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 (w.toBitVec64 >>> 32) = w.high.toBitVec32
  := by
    have ⟨ _, _, _, _ ⟩ := lt_cases_of_isU64 h_w_isU64
    simp_all [toBitVec64, ← BitVec.toNat_inj, Nat.shiftRight_eq_div_pow, high, BWord.toNat, BHWord.toBitVec32, BHWord.toNat]
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

lemma eq_pointwise {w w': BDWord T} :
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
def isU128 (w : BDWord (Fin BB)) : Prop := ∀ i : Fin BYTE_DWORD_SIZE, w[i].val < 256

@[aesop unsafe apply]
lemma isU128_of_cases {w : BDWord (Fin BB)}
    (h0 : w[0].val < 256) (h1 : w[1].val < 256)
    (h2 : w[2].val < 256) (h3 : w[3].val < 256)
    (h4 : w[4].val < 256) (h5 : w[5].val < 256)
    (h6 : w[6].val < 256) (h7 : w[7].val < 256)
    (h8 : w[8].val < 256) (h9 : w[9].val < 256)
    (h10 : w[10].val < 256) (h11 : w[11].val < 256)
    (h12 : w[12].val < 256) (h13 : w[13].val < 256)
    (h14 : w[14].val < 256) (h15 : w[15].val < 256) : w.isU128
  := by intro i; fin_cases i <;> simpa

/-- Pull in bounds on a bytedword's limbs given a `isU128` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU128 {w : BDWord (Fin BB)} (hbdw : w.isU128) :
    w[0].val < 256 ∧ w[1].val < 256 ∧ w[2].val < 256 ∧ w[3].val < 256 ∧
    w[4].val < 256 ∧ w[5].val < 256 ∧ w[6].val < 256 ∧ w[7].val < 256 ∧
    w[8].val < 256 ∧ w[9].val < 256 ∧ w[10].val < 256 ∧ w[11].val < 256 ∧
    w[12].val < 256 ∧ w[13].val < 256 ∧ w[14].val < 256 ∧ w[15].val < 256
    :=
  ⟨hbdw 0, hbdw 1, hbdw 2, hbdw 3, hbdw 4, hbdw 5, hbdw 6, hbdw 7, hbdw 8, hbdw 9, hbdw 10, hbdw 11, hbdw 12, hbdw 13, hbdw 14, hbdw 15⟩

end U128

section conversions

/-- Obtain the low 64 bits of a `BDWord` -/
def low (w : BDWord (Fin BB)) : BWord (Fin BB) := #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]]

lemma isU128_low_isU64 {w : BDWord (Fin BB)} (hw : w.isU128) : w.low.isU64 := by aesop

/-- Obtain the high 64 bits of a `BDWord` -/
def high (w : BDWord (Fin BB)) : BWord (Fin BB) := #v[w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]]

lemma isU128_high_isU64 {w : BDWord (Fin BB)} (hw : w.isU128) : w.high.isU64 := by aesop

/-- Convert a bytedword to a `Nat` by shifting and adding the limbs. -/
def toNat (w : BDWord (Fin BB)) : ℕ :=
  w[0] + w[1] * 2^8 + w[2] * 2^16 + w[3] * 2^24 + w[4] * 2^32 + w[5] * 2^40 + w[6] * 2^48 + w[7] * 2^56 +
  w[8] * 2^64 + w[9] * 2^72 + w[10] * 2^80 + w[11] * 2^88 + w[12] * 2^96 + w[13] * 2^104 + w[14] * 2^112 + w[15] * 2^120

lemma toNat_lt_of_isU128 {w : BDWord (Fin BB)} (hw : w.isU128) : w.toNat < 2^128 := by
  unfold toNat
  aesop (add 50% tactic (by omega))

/-- Convert a bytedword to a `BitVec 128` by shifting and adding the limbs. -/
def toBitVec128 (w : BDWord (Fin BB)) : BitVec 128 := BitVec.ofNat 128 w.toNat

lemma toBitVec128_toNat {w : BDWord (Fin BB)} (hw : w.isU128) :
    w.toBitVec128.toNat = w.toNat := by
  simp only [toBitVec128, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU128 hw
  omega

/-- A 128-bit integer is negative if its msb equals one -/
@[grind] def isNegative (w : BDWord (Fin BB)) : Prop := w[15] ≥ 128
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

lemma isNegative_msb
  {w : BDWord (Fin BB)}
  (h_w_isU128 : w.isU128) :
    w.isNegative ↔ (w.toBitVec128.msb = true) := by
  have := lt_cases_of_isU128 h_w_isU128
  simp [isNegative, BDWord.toBitVec128, BDWord.toNat, BitVec.msb_eq_decide]
  omega

lemma isNegative_BitVec.toInt
  {w : BDWord (Fin BB)}
  (h_w_isU128 : w.isU128) :
    w.isNegative ↔ ¬ 2 * w.toNat < 2^128 := by
  rw [isNegative_msb h_w_isU128]
  simp [BitVec.msb_eq_decide]
  rw [toBitVec128_toNat h_w_isU128]
  omega

/-- Convert a bytedword to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : BDWord (Fin BB)) : ℤ :=
  if (isNegative w) then w.toNat - 2^128 else w.toNat

set_option maxRecDepth 200000
lemma toBitVec128_toInt {w : BDWord (Fin BB)} (h_w_isU128 : w.isU128) :
    w.toBitVec128.toInt = w.toInt
  := by
    have := lt_cases_of_isU128 h_w_isU128
    have : w.toNat < 2^128 := by unfold BDWord.toNat; omega
    simp_all [toBitVec128, toInt, BitVec.toInt]
    split_ifs <;> rw [isNegative_BitVec.toInt h_w_isU128] at * <;> omega

lemma low_as_extract {w : BDWord (Fin BB)} (h_w_isU128 : w.isU128) :
  (w.low).toBitVec64 = BitVec.extractLsb 63 0 (w.toBitVec128) := by
  have ⟨ w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15 ⟩ := lt_cases_of_isU128 h_w_isU128
  simp [BDWord.low, BWord.toBitVec64, BDWord.toBitVec128]
  simp [← BitVec.toNat_inj, BWord.toNat, BDWord.toNat]
  omega

lemma high_as_extract {w : BDWord (Fin BB)} (h_w_isU128 : w.isU128) :
  (w.high).toBitVec64 = BitVec.extractLsb 127 64 (w.toBitVec128) := by
  have ⟨ w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15 ⟩ := lt_cases_of_isU128 h_w_isU128
  simp [BDWord.high, BWord.toBitVec64, BDWord.toBitVec128]
  simp [← BitVec.toNat_inj, BWord.toNat, BDWord.toNat]
  omega

end conversions

end BDWord

namespace HWord

lemma sign_extend_32_to_64_msb {w : HWord (Fin BB)} :
  w.isU32 →
  BitVec.signExtend 64 w.toBitVec32 = Word.toBitVec64 #v[w[0], w[1], if w.toBitVec32.msb = true then 65535 else 0, if w.toBitVec32.msb = true then 65535 else 0]
    := by
  let sw : Word (Fin BB) := #v[w[0], w[1], if w.toBitVec32.msb = true then 65535 else 0, if w.toBitVec32.msb = true then 65535 else 0]
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
def extend (w : HWord (Fin BB)) (sgn : Bool) : Word (Fin BB) :=
  let ext := (if sgn then (if w.isNegative then (1 : Fin BB) else 0) else 0) * 65535
  #v[w[0], w[1], ext, ext]

lemma extend_U32_U64 {w : HWord (Fin BB)} (is_U32_w : w.isU32) (sgn : Bool) : (w.extend sgn).isU64 := by
  have := lt_cases_of_isU32 is_U32_w
  apply Word.isU64_of_cases <;>
  simp [extend] <;> (try split_ifs) <;> omega

lemma extend_true_is_signExtend {w : HWord (Fin BB)} :
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

lemma extend_false_is_setWidth {w : HWord (Fin BB)} :
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
def toBWord (w : Word (Fin BB)) : BWord (Fin BB) :=
  #v[w[0] % 256, w[0] / 256, w[1] % 256, w[1] / 256, w[2] % 256, w[2] / 256, w[3] % 256, w[3] / 256 ]

lemma toBWord_toU64
  {w : Word (Fin BB)}
  (h_w_isU64 : w.isU64) :
    w.toBWord.isU64 := by
  simp [Word.toBWord]
  apply Word.lt_cases_of_isU64 at h_w_isU64
  apply BWord.isU64_of_cases <;> simp <;> omega

lemma toNat_toBWord
  {w : Word (Fin BB)}
  (h_w_isU64 : w.isU64) :
    w.toNat = BWord.toNat (w.toBWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [toNat, toBWord, BWord.toNat]
  omega

lemma isNegative_toBWord
  {w : Word (Fin BB)}
  (h_w_isU64 : w.isU64) :
    w.isNegative ↔ BWord.isNegative (w.toBWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [isNegative, BWord.isNegative, toBWord, Fin.le_def]
  omega

lemma toInt_toBWord
  {w : Word (Fin BB)}
  (h_w_isU64 : w.isU64) :
    w.toInt = BWord.toInt (w.toBWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [toBWord, toInt, toNat, BWord.toInt, BWord.toNat, isNegative, BWord.isNegative, Fin.le_def]
  omega

lemma toBitVec64_toBWord
  {w : Word (Fin BB)}
  (h_w_isU64 : w.isU64) :
    w.toBWord.toBitVec64 = w.toBitVec64 := by
  rw [← BitVec.toNat_inj, BWord.toBitVec64_toNat (by apply toBWord_toU64 h_w_isU64), Word.toBitVec64_toNat h_w_isU64, Word.toNat_toBWord h_w_isU64]

lemma sign_extend_imm_toBitVec64 {x₀ x₁ x₂ x₃ : Fin BB} {x : ℕ} :
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
    . rw [← BitVec.toNat_inj, BitVec.toNat_setWidth, toBitVec64_toNat h_64 ] at h_eq
      simp_all [BitVec.toNat_ofNat, toNat]
      omega
    . rw [← BitVec.toInt_inj, toBitVec64_toInt h_64, toInt] at h_eq
      split_ifs at h_eq with h_neg <;>
      rw [isNegative_msb, BitVec.msb_eq_decide, toBitVec64_toNat h_64] at h_neg <;>
      subst imm_x <;>
      simp_all [BitVec.toNat_ofNat, toNat] <;>
      rw [Int.bmod_def] at h_eq <;>
      omega

/-- Sign-extension to 128 bits -/
def extend (w : Word (Fin BB)) (sgn : Bool) : DWord (Fin BB) :=
  let ext := (if sgn then (if w.isNegative then (1 : Fin BB) else 0) else 0) * 65535
  #v[w[0], w[1], w[2], w[3], ext, ext, ext, ext]

lemma extend_U64_U128 {w : Word (Fin BB)} (is_U64_w : w.isU64) (sgn : Bool) : (w.extend sgn).isU128 := by
  have := lt_cases_of_isU64 is_U64_w
  apply DWord.isU128_of_cases <;>
  simp [extend] <;> (try split_ifs) <;> omega

lemma extend_true_is_signExtend {w : Word (Fin BB)} :
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

lemma extend_false_is_setWidth {w : Word (Fin BB)} :
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

end Word

namespace BWord

/-- Sign-extension to 128 bits -/
def extend (w : BWord (Fin BB)) (sgn : Bool) : BDWord (Fin BB) :=
  let ext := (if sgn then (if w.isNegative then (1 : Fin BB) else 0) else 0) * 255
  #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], ext, ext, ext, ext, ext, ext, ext, ext]

lemma extend_U64_U128 {w : BWord (Fin BB)} (is_U64_w : w.isU64) (sgn : Bool) : (w.extend sgn).isU128 := by
  have := lt_cases_of_isU64 is_U64_w
  apply BDWord.isU128_of_cases <;>
  simp [extend] <;> (try split_ifs) <;> omega

lemma extend_true_is_signExtend {w : BWord (Fin BB)} :
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

lemma extend_false_is_setWidth {w : BWord (Fin BB)} :
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

lemma low_as_setWidth {w : BWord (Fin BB)} :
  w.isU64 →
  w.low.toBitVec32 = BitVec.setWidth 32 w.toBitVec64
    := by
  intro is_U64_w
  simp [BWord.low, BHWord.toBitVec32, BHWord.toNat, BWord.toBitVec64, BWord.toNat]
  simp [← BitVec.toNat_inj]
  omega

end BWord

namespace BHWord

/-- Sign-extension to 64 bits -/
def extend (w : BHWord (Fin BB)) (sgn : Bool) : BWord (Fin BB) :=
  let ext := (if sgn then (if w.isNegative then (1 : Fin BB) else 0) else 0) * 255
  #v[w[0], w[1], w[2], w[3], ext, ext, ext, ext]

lemma extend_U32_U64 {w : BHWord (Fin BB)} (is_U32_w : w.isU32) (sgn : Bool) : (w.extend sgn).isU64 := by
  have := lt_cases_of_isU32 is_U32_w
  apply BWord.isU64_of_cases <;>
  simp [extend] <;> (try split_ifs) <;> omega

lemma extend_true_is_signExtend {w : BHWord (Fin BB)} :
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

lemma extend_false_is_setWidth {w : BHWord (Fin BB)} :
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

lemma and_toBWord {a b : Word (Fin BB)} : a.isU64 → b.isU64 →
  a.toBitVec64 &&& b.toBitVec64 = a.toBWord.toBitVec64 &&& b.toBWord.toBitVec64
    := by
  intro h_a_64 h_b_64
  simp [Word.toBitVec64, BWord.toBitVec64]
  rw [Word.toNat_toBWord h_a_64, Word.toNat_toBWord h_b_64]

lemma or_toBWord {a b : Word (Fin BB)} : a.isU64 → b.isU64 →
  a.toBitVec64 ||| b.toBitVec64 = a.toBWord.toBitVec64 ||| b.toBWord.toBitVec64
    := by
  intro h_a_64 h_b_64
  simp [Word.toBitVec64, BWord.toBitVec64]
  rw [Word.toNat_toBWord h_a_64, Word.toNat_toBWord h_b_64]

lemma xor_toBWord {a b : Word (Fin BB)} : a.isU64 → b.isU64 →
  a.toBitVec64 ^^^ b.toBitVec64 = a.toBWord.toBitVec64 ^^^ b.toBWord.toBitVec64
    := by
  intro h_a_64 h_b_64
  simp [Word.toBitVec64, BWord.toBitVec64]
  rw [Word.toNat_toBWord h_a_64, Word.toNat_toBWord h_b_64]

end Word

end Bitwise

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
  repeat rw [Nat.mod_eq_of_lt (b := 2130706433) (by omega)]
  simp [ofNat_add, ofNat_mul]
  repeat rw [← BitVec.toNat_ushiftRight]
  repeat rw [this, ← BitVec.toNat_umod]; simp [-toNat_umod, -toNat_ushiftRight]
  bv_decide

end BitVec

end getByte

section cross_product

def cp {n : ℕ} (a b : Vector (Fin BB) n) (k : ℕ) (hk : k < n) : Fin BB :=
  let product := ((Vector.ofFn (fun i => a.get ⟨ i.val, by omega ⟩ * b.get ⟨k - i.val, by
                     have h : i.val < (k + 1) := i.isLt
                     omega⟩)) : Vector (Fin BB) (k + 1)).toList
  product.foldl (· + ·) 0

end cross_product
