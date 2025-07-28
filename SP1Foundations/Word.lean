import SP1Foundations.Unsigned
import SP1Foundations.Tactics

@[simp] abbrev BIT_WIDTH := 32
@[simp] abbrev BYTE_WORD_SIZE := 8
@[simp] abbrev WORD_SIZE := 4
@[simp] abbrev HALF_WORD_SIZE := 2

@[reducible] def HalfWord (T : Type) := Vector T HALF_WORD_SIZE
@[reducible] def Word (T : Type) := Vector T WORD_SIZE
@[reducible] def ByteWord (T : Type) := Vector T BYTE_WORD_SIZE

open BitVec

namespace HalfWord

/-- Prove two `HalfWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : HalfWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1
  | n + 2, h => by simp only [HALF_WORD_SIZE, add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `HalfWord`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : HalfWord T}
    (h : ∀ i : Fin HALF_WORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : HalfWord T) : w = #v[w[0], w[1]] := ext_cases rfl rfl

lemma eq_pointwise (w w': HalfWord T) : (w[0] = w'[0]) ∧ (w[1] = w'[1]) ↔ w = w' := by
   constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `HalfWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : HalfWord T → Prop}
    (mk : ∀ x1 x2 : T, C #v[x1, x2]) (w : HalfWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U32

/-- `isU32 w` means that each limb of the word is properly bounded. -/
def isU32 (w : HalfWord (Fin BB)) : Prop := ∀ i : Fin HALF_WORD_SIZE, w[i].val < 2^16

@[aesop unsafe apply]
lemma isU32_of_cases (w : HalfWord (Fin BB))
    (h0 : w[0].val < 2^16) (h1 : w[1].val < 2^16) : w.isU32
  | 0 => h0 | 1 => h1

/-- Pull in bounds on a word's limbs given a `isU64` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU32 {w : HalfWord (Fin BB)} (hw : w.isU32) :
    w[0].val < 2^16 ∧ w[1].val < 2^16 :=
  ⟨hw 0, hw 1⟩

end U32

section conversions

/-- Convert a halfword to a `Nat` by shifting and adding the limbs. -/
@[simp] def toNat (w : HalfWord (Fin BB)) : ℕ := w[0] + w[1] * 2^16

lemma toNat_lt_of_isU32 {w : HalfWord (Fin BB)} (hw : w.isU32) : w.toNat < 2^32 := by
  unfold toNat
  aesop (add 50% tactic (by omega))

lemma toNat_lt_of_cases_lt (w : HalfWord (Fin BB))
    (h0 : w[0].val < 2^16) (h1 : w[1].val < 2^16) : w.toNat < 2^32 := by
  unfold toNat; omega

lemma toNat_lt_of_forall_lt (w : HalfWord (Fin BB))
    (h : ∀ i : Fin HALF_WORD_SIZE, w[i] < 2^16) : w.toNat < 2^32 := by
  refine toNat_lt_of_cases_lt w (h 0) (h 1)

/-- Convert a halfword to a `BitVec 32` by shifting and adding the limbs. -/
def toBitVec32 (w : HalfWord (Fin BB)) : BitVec 32 := BitVec.ofNat 32 w.toNat

lemma toBitVec32_toNat {w : HalfWord (Fin BB)} (hw : w.isU32) :
    w.toBitVec32.toNat = w.toNat := by
  simp only [toBitVec32, toNat, BB_eq, WORD_SIZE, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU32 hw
  omega

/-- Convert a halfword to a `BitVec 64` by shifting and adding the limbs, with sign correction. -/
def toBitVec64 (w : HalfWord (Fin BB)) : BitVec 64 := BitVec.signExtend 64 w.toBitVec32

/-- A 32-bit integer is negative if its msb equals one -/
def isNegative (w : HalfWord (Fin BB)) : Prop := w[1] ≥ 32768
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

lemma isNegative_msb
  (w : HalfWord (Fin BB))
  (h_w_isU32 : w.isU32) :
    w.isNegative ↔ (w.toBitVec32.msb = true) := by
  have := lt_cases_of_isU32 h_w_isU32
  simp [isNegative, HalfWord.toBitVec32, HalfWord.toNat, BitVec.msb_eq_decide]
  omega

/-- Convert a halfword to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : HalfWord (Fin BB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 32 else w.toNat

lemma toBitVec32_toInt {w : HalfWord (Fin BB)} (h_w_isU64 : w.isU32) :
    w.toBitVec32.toInt = w.toInt
  := by
    have := lt_cases_of_isU32 h_w_isU64
    have := toNat_lt_of_isU32 h_w_isU64
    unfold toBitVec32 toInt BitVec.toInt
    simp_all only [Nat.reducePow, Int.reducePow, toNat_ofNat, Nat.cast_ofNat]
    rw [Nat.mod_eq_of_lt this]
    by_cases h_neg : w.isNegative <;> unfold isNegative at * <;>
    unfold toNat at * <;> simp_all <;> omega

lemma toBitVec64_toInt {w : HalfWord (Fin BB)} (h_w_isU32 : w.isU32) :
    w.toBitVec64.toInt = w.toInt
  := by
    have := lt_cases_of_isU32 h_w_isU32
    simp [toBitVec64, BitVec.toInt_signExtend]
    rw [toBitVec32_toInt h_w_isU32]
    unfold toInt isNegative toNat
    refine Int.bmod_eq_of_le ?_ ?_ <;> omega

end conversions

section add

lemma toBitVec32_as_sum (w : HalfWord (Fin BB)) : w.toBitVec32 =
    BitVec.ofNat 32 w[0] + BitVec.ofNat 32 (w[1] * 2^16) := by
  simp [toBitVec32, toNat, BitVec.ofNat_add]

lemma toNat_add_toNat (w v : HalfWord (Fin BB)) :
    w.toNat + v.toNat =
      ((w[0].val + v[0].val) + (w[1].val + v[1].val) * 2^16) := by
  simp only [toNat, BB_eq, WORD_SIZE, Nat.reducePow]
  omega

lemma toBitVec32_add_toBitVec32 (w v : HalfWord (Fin BB)) :
    w.toBitVec32 + v.toBitVec32 = BitVec.ofNat 32
      ((w[0].val + v[0].val) + (w[1].val + v[1].val) * 2^16) := by
  simp only [toBitVec32, ← BitVec.ofNat_add, toNat_add_toNat, BB_eq, WORD_SIZE, Nat.reducePow]

end add

end HalfWord

namespace Word

/-- Prove two `Word`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : Word T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1])
    (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3
  | n + 4, h => by simp only [WORD_SIZE, add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `Word`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : Word T}
    (h : ∀ i : Fin WORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : Word T) : w = #v[w[0], w[1], w[2], w[3]] := ext_cases rfl rfl rfl rfl

lemma eq_pointwise (w w': Word T) : (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ↔ w = w' := by
   constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `Word`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : Word T → Prop}
    (mk : ∀ x1 x2 x3 x4 : T, C #v[x1, x2, x3, x4]) (w : Word T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U64

/-- `isU64 w` means that each limb of the word is properly bounded. -/
def isU64 (w : Word (Fin BB)) : Prop := ∀ i : Fin WORD_SIZE, w[i].val < 2^16

@[aesop unsafe apply]
lemma isU64_of_cases (w : Word (Fin BB))
    (h0 : w[0].val < 2^16) (h1 : w[1].val < 2^16)
    (h2 : w[2].val < 2^16) (h3 : w[3].val < 2^16) : w.isU64
  | 0 => h0 | 1 => h1 | 2 => h2 | 3 => h3

/-- Pull in bounds on a word's limbs given a `isU64` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU64 {w : Word (Fin BB)} (hw : w.isU64) :
    w[0].val < 2^16 ∧ w[1].val < 2^16 ∧ w[2].val < 2^16 ∧ w[3].val < 2^16 :=
  ⟨hw 0, hw 1, hw 2, hw 3⟩

@[simp] -- common enough to want a lemma
lemma four_isU64 : Word.isU64 #v[4, 0, 0, 0] :=
  Word.isU64_of_cases _ (by trivial) (by trivial) (by trivial) (by trivial)

end U64

section conversions

/-- Convert a word to a `Nat` by shifting and adding the limbs. -/
@[simp] def toNat (w : Word (Fin BB)) : ℕ := w[0] + w[1] * 2^16 + w[2] * 2^32 + w[3] * 2^48

lemma toNat_lt_of_isU64 {w : Word (Fin BB)} (hw : w.isU64) : w.toNat < 2^64 := by
  unfold toNat
  aesop (add 50% tactic (by omega))

lemma toNat_lt_of_cases_lt (w : Word (Fin BB))
    (h0 : w[0].val < 2^16) (h1 : w[1].val < 2^16)
    (h2 : w[2].val < 2^16) (h3 : w[3].val < 2^16) : w.toNat < 2^64 := by
  unfold toNat; omega

lemma toNat_lt_of_forall_lt (w : Word (Fin BB))
    (h : ∀ i : Fin WORD_SIZE, w[i] < 2^16) : w.toNat < 2^64 := by
  refine toNat_lt_of_cases_lt w (h 0) (h 1) (h 2) (h 3)

/-- Convert a word to a `BitVec 64` by shifting and adding the limbs. -/
def toBitVec64 (w : Word (Fin BB)) : BitVec 64 := BitVec.ofNat 64 w.toNat

lemma toBitVec64_toNat {w : Word (Fin BB)} (hw : w.isU64) :
    w.toBitVec64.toNat = w.toNat := by
  simp only [toBitVec64, toNat, BB_eq, WORD_SIZE, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU64 hw
  omega

/-- Convert a word to a `BitVec 64` by shifting and adding the limbs, supplying a proof . -/
def toBitVec64LT (w : Word (Fin BB)) (h_w : w.isU64) : BitVec 64 :=
  BitVec.ofNatLT w.toNat (by
    simp [Word.toNat]
    have := h_w 0
    have := h_w 1
    have := h_w 2
    have := h_w 3
    simp at *
    linarith)

/-- A 64-bit integer is negative if its msb equals one -/
def isNegative (w : Word (Fin BB)) : Prop := w[3] ≥ 32768
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

lemma isNegative_msb
  (w : Word (Fin BB))
  (h_w_isU64 : w.isU64) :
    w.isNegative ↔ (w.toBitVec64.msb = true) := by
  have := lt_cases_of_isU64 h_w_isU64
  simp [isNegative, Word.toBitVec64, Word.toNat, BitVec.msb_eq_decide]
  omega

/-- Convert a word to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : Word (Fin BB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 64 else w.toNat

lemma toBitVec64_toInt {w : Word (Fin BB)} (h_w_isU64 : w.isU64) :
    w.toBitVec64.toInt = w.toInt
  := by
    have := lt_cases_of_isU64 h_w_isU64
    have := toNat_lt_of_isU64 h_w_isU64
    unfold toBitVec64 toInt BitVec.toInt
    simp_all only [Nat.reducePow, Int.reducePow, toNat_ofNat, Nat.cast_ofNat]
    rw [Nat.mod_eq_of_lt this]
    by_cases h_neg : w.isNegative <;> unfold isNegative at * <;>
    unfold toNat <;> simp_all <;> omega

/-- Obtain the low 32 bits of a `Word` -/
def low32 (w : Word (Fin BB)) : HalfWord (Fin BB) := #v[w[0], w[1]]

lemma isU64_low_isU32 {w : Word (Fin BB)} (hw : w.isU64) : w.low32.isU32 := by aesop

lemma setWidth_eq_low32 (w : Word (Fin BB )) (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 w.toBitVec64 = w.low32.toBitVec32
  := by
    have ⟨ _, _, _, _ ⟩ := lt_cases_of_isU64 h_w_isU64
    have := toNat_lt_of_isU64 h_w_isU64
    simp [Word.toNat] at this
    simp [toBitVec64, ← BitVec.toNat_inj, low32, Word.toNat, HalfWord.toBitVec32, HalfWord.toNat]
    omega

end conversions

section add

lemma toBitVec64_eq_add (w : Word (Fin BB)) : w.toBitVec64 =
    BitVec.ofNat 64 w[0] + BitVec.ofNat 64 (w[1] * 2^16) +
      BitVec.ofNat 64 (w[2] * 2^32) + BitVec.ofNat 64 (w[3] * 2^48) := by
  simp [toBitVec64, toNat, BitVec.ofNat_add]

lemma toNat_add_toNat (w v : Word (Fin BB)) :
    w.toNat + v.toNat =
      ((w[0].val + v[0].val) + (w[1].val + v[1].val) * 2^16 +
        (w[2].val + v[2].val) * 2^32 + (w[3].val + v[3].val) * 2^48) := by
  simp only [toNat, BB_eq, WORD_SIZE, Nat.reducePow]
  omega

lemma toBitVec64_add_toBitVec64 (w v : Word (Fin BB)) :
    w.toBitVec64 + v.toBitVec64 = BitVec.ofNat 64
      ((w[0].val + v[0].val) + (w[1].val + v[1].val) * 2^16 +
        (w[2].val + v[2].val) * 2^32 + (w[3].val + v[3].val) * 2^48) := by
  simp only [toBitVec64, ← BitVec.ofNat_add, toNat_add_toNat, BB_eq, WORD_SIZE, Nat.reducePow]

end add

end Word

namespace ByteWord

/-- Prove two `ByteWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : ByteWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3])
    (h4 : w[4] = w'[4]) (h5 : w[5] = w'[5]) (h6 : w[6] = w'[6]) (h7 : w[7] = w'[7]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3 | 4, _ => h4 | 5, _ => h5 | 6, _ => h6 | 7, _ => h7
  | n + 8, h => by simp only [BYTE_WORD_SIZE, add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `Word`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : ByteWord T}
    (h : ∀ i : Fin BYTE_WORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : ByteWord T) : w = #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]] := ext_cases rfl rfl rfl rfl rfl rfl rfl rfl

lemma eq_pointwise (w w': ByteWord T) :
    (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ∧
    (w[4] = w'[4]) ∧ (w[5] = w'[5]) ∧ (w[6] = w'[6]) ∧ (w[7] = w'[7]) ↔ w = w' := by
  constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `ByteWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : ByteWord T → Prop}
    (mk : ∀ x0 x1 x2 x3 x4 x5 x6 x7 : T, C #v[x0, x1, x2, x3, x4, x5, x6, x7]) (w : ByteWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U64

/-- `isU64 w` means that each limb of the word is properly bounded. -/
def isU64 (w : ByteWord (Fin BB)) : Prop := ∀ i : Fin BYTE_WORD_SIZE, w[i].val < 2^8

@[aesop unsafe apply]
lemma isU64_of_cases (w : ByteWord (Fin BB))
    (h0 : w[0].val < 2^8) (h1 : w[1].val < 2^8)
    (h2 : w[2].val < 2^8) (h3 : w[3].val < 2^8)
    (h4 : w[4].val < 2^8) (h5 : w[5].val < 2^8)
    (h6 : w[6].val < 2^8) (h7 : w[7].val < 2^8) : w.isU64
  | 0 => h0 | 1 => h1 | 2 => h2 | 3 => h3
  | 4 => h4 | 5 => h5 | 6 => h6 | 7 => h7

/-- Pull in bounds on a word's limbs given a `isU64` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU64 {w : ByteWord (Fin BB)} (hbw : w.isU64) :
    w[0].val < 2^8 ∧ w[1].val < 2^8 ∧ w[2].val < 2^8 ∧ w[3].val < 2^8 ∧
    w[4].val < 2^8 ∧ w[5].val < 2^8 ∧ w[6].val < 2^8 ∧ w[7].val < 2^8 :=
  ⟨hbw 0, hbw 1, hbw 2, hbw 3, hbw 4, hbw 5, hbw 6, hbw 7⟩

end U64

section conversions

/-- Convert a byteword to a `Word` by combining the limbs. -/
def toWord (w : ByteWord (Fin BB)) : Word (Fin BB) :=
  #v[w[0]! + 256 * w[1], w[2]! + 256 * w[3], w[4]! + 256 * w[5], w[6]! + 256 * w[7]]

/-- Convert a byteword to a `Nat` by shifting and adding the limbs. -/
@[simp] def toNat (w : ByteWord (Fin BB)) : ℕ := w[0] + w[1] * 2^8 + w[2] * 2^16 + w[3] * 2^24 + w[4] * 2^32 + w[5] * 2^40 + w[6] * 2^48 + w[7] * 2^56

lemma toNat_lt_of_isU64 {w : ByteWord (Fin BB)} (hw : w.isU64) : w.toNat < 2^64 := by
  unfold toNat
  aesop (add 50% tactic (by omega))

lemma toNat_lt_of_cases_lt (w : ByteWord (Fin BB))
    (h0 : w[0].val < 2^8) (h1 : w[1].val < 2^8)
    (h2 : w[2].val < 2^8) (h3 : w[3].val < 2^8)
    (h4 : w[4].val < 2^8) (h5 : w[5].val < 2^8)
    (h6 : w[6].val < 2^8) (h7 : w[7].val < 2^8) : w.toNat < 2^64 := by
  unfold toNat; omega

lemma toNat_lt_of_forall_lt (w : ByteWord (Fin BB))
    (h : ∀ i : Fin BYTE_WORD_SIZE, w[i] < 2^8) : w.toNat < 2^64 := by
  refine toNat_lt_of_cases_lt w (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7)

lemma toNat_toWord
  (w : ByteWord (Fin BB))
  (h_w_isU64 : w.isU64) :
    w.toNat = Word.toNat (w.toWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [toNat, toWord, Word.toNat]
  simp [Fin.add_def, Fin.mul_def]
  omega

/-- Convert a byteword to a `BitVec 64` by shifting and adding the limbs. -/
def toBitVec64 (w : ByteWord (Fin BB)) : BitVec 64 := BitVec.ofNat 64 w.toNat

lemma toBitVec64_toNat {w : ByteWord (Fin BB)} (hw : w.isU64) :
    w.toBitVec64.toNat = w.toNat := by
  simp only [toBitVec64, toNat, BB_eq, WORD_SIZE, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU64 hw
  omega

/-- A 64-bit integer is negative if its msb equals one -/
def isNegative (w : ByteWord (Fin BB)) : Prop := w[7] ≥ 128
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

lemma isNegative_toWord
  (w : ByteWord (Fin BB))
  (h_w_isU64 : w.isU64) :
    w.isNegative ↔ Word.isNegative (w.toWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [isNegative, Word.isNegative, toWord]
  simp [Fin.le_def, Fin.add_def, Fin.mul_def]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

lemma isNegative_msb
  (w : ByteWord (Fin BB))
  (h_w_isU64 : w.isU64) :
    w.isNegative ↔ (w.toBitVec64.msb = true) := by
  have := lt_cases_of_isU64 h_w_isU64
  simp [isNegative, ByteWord.toBitVec64, ByteWord.toNat, BitVec.msb_eq_decide]
  omega

/-- Convert a byteword to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : ByteWord (Fin BB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 64 else w.toNat

lemma toInt_toWord
  (w : ByteWord (Fin BB))
  (h_w_isU64 : w.isU64) :
    w.toInt = Word.toInt (w.toWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [toWord, toInt, Word.toInt, isNegative, Word.isNegative]
  simp [Fin.le_def, Fin.add_def, Fin.mul_def]
  omega

lemma toBitVec64_toInt {w : ByteWord (Fin BB)} (h_w_isU64 : w.isU64) :
    w.toBitVec64.toInt = w.toInt
  := by
    have := lt_cases_of_isU64 h_w_isU64
    have := toNat_lt_of_isU64 h_w_isU64
    unfold toBitVec64 toInt BitVec.toInt
    simp_all only [Nat.reducePow, Int.reducePow, toNat_ofNat, Nat.cast_ofNat]
    rw [Nat.mod_eq_of_lt this]
    by_cases h_neg : w.isNegative <;> unfold isNegative at * <;>
    unfold toNat at * <;> simp_all <;> omega

end conversions

section add

lemma toBitVec64_eq_add (w : ByteWord (Fin BB)) : w.toBitVec64 =
    BitVec.ofNat 64 w[0] + BitVec.ofNat 64 (w[1] * 2^8) +
    BitVec.ofNat 64 (w[2] * 2^16) + BitVec.ofNat 64 (w[3] * 2^24) +
    BitVec.ofNat 64 (w[4] * 2^32) + BitVec.ofNat 64 (w[5] * 2^40) +
    BitVec.ofNat 64 (w[6] * 2^48) + BitVec.ofNat 64 (w[7] * 2^56) := by
  simp [toBitVec64, toNat, BitVec.ofNat_add]

end add

end ByteWord

namespace HalfWord

lemma sign_extend_32_to_64_msb (x y : Fin BB) :
  let hw : HalfWord (Fin BB) := #v[x, y]
  hw.isU32 →
  BitVec.signExtend 64 hw.toBitVec32 = Word.toBitVec64 #v[x, y, if hw.toBitVec32.msb = true then 65535 else 0, if hw.toBitVec32.msb = true then 65535 else 0]
    := by
  intro hw hw_U32
  unfold signExtend
  rw [toBitVec32_toInt hw_U32, toInt]
  have := hw.lt_cases_of_isU32 hw_U32
  by_cases is_neg : hw.isNegative <;>
  [ rw [if_pos (by assumption)]; rw [if_neg (by assumption)] ] <;>
  rw [HalfWord.isNegative_msb _ hw_U32] at is_neg <;>
  [ rw [if_pos (by assumption)]; rw [if_neg (by assumption)] ] <;>
  rw [BitVec.msb_eq_decide, toBitVec32_toNat hw_U32] at is_neg <;>
  subst hw <;> simp at this <;> simp [HalfWord.toNat] at is_neg
  . rw [Word.toBitVec64, Word.toNat]
    simp_all [-Fin.coe_ofNat_eq_mod]
    rw [Fin.coe_ofNat_eq_mod]
    simp [← BitVec.toInt_inj]
    rw [BitVec.ofNat, BitVec.toInt]
    rw [if_neg]
    . bv_amicus_kerneli
      rw [Fin.ofNat]; zify
      simp_all [HalfWord.toNat]
      rw [Int.bmod_def]
      omega
    . simp only [Nat.reducePow, Fin.val_natCast, not_lt]
      bv_amicus_kerneli
      simp; omega
  . rw [Word.toBitVec64, Word.toNat]
    simp_all [HalfWord.toNat, -ofInt_natCast]
    simp [← BitVec.toInt_inj]
    rw [BitVec.ofNat, BitVec.toInt]
    rw [if_pos] <;> bv_amicus_kerneli
    . simp
      rw [Int.emod_eq_of_lt (by omega) (by omega)]
      rw [Int.bmod_eq_of_le (by omega) (by omega)]
    . simp; omega

end HalfWord

namespace Word

/-- Convert a word to a `ByteWord` by separating the limbs. -/
def toByteWord (w : Word (Fin BB)) : ByteWord (Fin BB) :=
  #v[w[0]! % 256, w[0] / 256, w[1]! % 256, w[1] / 256, w[2]! % 256, w[2] / 256, w[3]! % 256, w[3] / 256 ]

lemma toNat_toByteWord
  (w : Word (Fin BB))
  (h_w_isU64 : w.isU64) :
    w.toNat = ByteWord.toNat (w.toByteWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [toNat, toByteWord, ByteWord.toNat]
  omega

lemma isNegative_toByteWord
  (w : Word (Fin BB))
  (h_w_isU64 : w.isU64) :
    w.isNegative ↔ ByteWord.isNegative (w.toByteWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [isNegative, ByteWord.isNegative, toByteWord, Fin.le_def]
  omega

lemma toInt_toByteWord
  (w : Word (Fin BB))
  (h_w_isU64 : w.isU64) :
    w.toInt = ByteWord.toInt (w.toByteWord) := by
  have := w.lt_cases_of_isU64 h_w_isU64
  simp [toByteWord, toInt, ByteWord.toInt, isNegative, ByteWord.isNegative, Fin.le_def]
  omega

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

end Word
