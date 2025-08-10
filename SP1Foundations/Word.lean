import SP1Foundations.Unsigned
import SP1Foundations.Tactics

@[simp] notation "BIT_WIDTH" => 32
@[simp] notation "BYTE_DWORD_SIZE" => 16
@[simp] notation "BYTE_WORD_SIZE" => 8
@[simp] notation "WORD_SIZE" => 4
@[simp] notation "HWORD_SIZE" => 2

@[reducible] def HWord (T : Type) := Vector T HWORD_SIZE
@[reducible] def Word (T : Type) := Vector T WORD_SIZE
@[reducible] def ByteWord (T : Type) := Vector T BYTE_WORD_SIZE
@[reducible] def ByteDWord (T : Type) := Vector T BYTE_DWORD_SIZE

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

/-- `isU32 w` means that each limb of the word is properly bounded. -/
def isU32 (w : HWord (Fin BB)) : Prop := ∀ i : Fin HWORD_SIZE, w[i].val < 2^16

@[aesop unsafe apply]
lemma isU32_of_cases (w : HWord (Fin BB))
    (h0 : w[0].val < 2^16) (h1 : w[1].val < 2^16) : w.isU32
  := by intro i; fin_cases i <;> simpa

/-- Pull in bounds on a halfword's limbs given a `isU64` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU32 {w : HWord (Fin BB)} (hw : w.isU32) :
    w[0].val < 2^16 ∧ w[1].val < 2^16 :=
  ⟨hw 0, hw 1⟩

end U32

section conversions

/-- Convert a halfword to a `Nat` by shifting and adding the limbs. -/
def toNat (w : HWord (Fin BB)) : ℕ := w[0] + w[1] * 2^16

lemma toNat_lt_of_isU32 {w : HWord (Fin BB)} (hw : w.isU32) : w.toNat < 2^32 := by
  unfold toNat
  aesop (add 50% tactic (by omega))

lemma toNat_lt_of_cases_lt (w : HWord (Fin BB))
    (h0 : w[0].val < 2^16) (h1 : w[1].val < 2^16) : w.toNat < 2^32 := by
  unfold toNat; omega

lemma toNat_lt_of_forall_lt (w : HWord (Fin BB))
    (h : ∀ i : Fin HWORD_SIZE, w[i] < 2^16) : w.toNat < 2^32 := by
  refine toNat_lt_of_cases_lt w (h 0) (h 1)

/-- Convert a halfword to a `BitVec 32` by shifting and adding the limbs. -/
def toBitVec32 (w : HWord (Fin BB)) : BitVec 32 := BitVec.ofNat 32 w.toNat

lemma toBitVec32_toNat {w : HWord (Fin BB)} (hw : w.isU32) :
    w.toBitVec32.toNat = w.toNat := by
  simp only [toBitVec32, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU32 hw
  omega

/-- Convert a halfword to a `BitVec 64` by shifting and adding the limbs, with sign correction. -/
def toBitVec64 (w : HWord (Fin BB)) : BitVec 64 := BitVec.signExtend 64 w.toBitVec32

/-- A 32-bit integer is negative if its msb equals one -/
def isNegative (w : HWord (Fin BB)) : Prop := w[1] ≥ 32768
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

lemma isNegative_msb
  (w : HWord (Fin BB))
  (h_w_isU32 : w.isU32) :
    w.isNegative ↔ (w.toBitVec32.msb = true) := by
  have := lt_cases_of_isU32 h_w_isU32
  simp [isNegative, HWord.toBitVec32, HWord.toNat, BitVec.msb_eq_decide]
  omega

/-- Convert a halfword to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : HWord (Fin BB)) : ℤ :=
  if (isNegative w) then w.toNat - 2 ^ 32 else w.toNat

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

end conversions

section add

lemma toBitVec32_as_sum (w : HWord (Fin BB)) : w.toBitVec32 =
    BitVec.ofNat 32 w[0] + BitVec.ofNat 32 (w[1] * 2^16) := by
  simp [toBitVec32, toNat, BitVec.ofNat_add]

lemma toNat_add_toNat (w v : HWord (Fin BB)) :
    w.toNat + v.toNat =
      ((w[0].val + v[0].val) + (w[1].val + v[1].val) * 2^16) := by
  simp only [toNat, BB_eq, Nat.reducePow]
  omega

lemma toBitVec32_add_toBitVec32 (w v : HWord (Fin BB)) :
    w.toBitVec32 + v.toBitVec32 = BitVec.ofNat 32
      ((w[0].val + v[0].val) + (w[1].val + v[1].val) * 2^16) := by
  simp only [toBitVec32, ← BitVec.ofNat_add, toNat_add_toNat, BB_eq, Nat.reducePow]

end add

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
  := by intro i; fin_cases i <;> simpa

/-- Pull in bounds on a word's limbs given a `isU64` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU64 {w : Word (Fin BB)} (hw : w.isU64) :
    w[0].val < 2^16 ∧ w[1].val < 2^16 ∧ w[2].val < 2^16 ∧ w[3].val < 2^16 :=
  ⟨hw 0, hw 1, hw 2, hw 3⟩

lemma lt_cases_of_isU64_bv { w : Word (Fin BB) } (hw : w.isU64) :
  BitVec.ofNat 64 w[0] < 65536 ∧ BitVec.ofNat 64 w[1] < 65536 ∧
  BitVec.ofNat 64 w[2] < 65536 ∧ BitVec.ofNat 64 w[3] < 65536
    := by
  obtain ⟨ w0, w1, w2, w3 ⟩ := lt_cases_of_isU64 hw
  simp; omega

@[simp] -- common enough to want a lemma
lemma four_isU64 : Word.isU64 #v[4, 0, 0, 0] :=
  Word.isU64_of_cases _ (by trivial) (by trivial) (by trivial) (by trivial)

end U64

section conversions

/-- Convert a word to a `Nat` by shifting and adding the limbs. -/
def toNat (w : Word (Fin BB)) : ℕ := w[0] + w[1] * 2^16 + w[2] * 2^32 + w[3] * 2^48

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
  simp only [toBitVec64, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
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
def low (w : Word (Fin BB)) : HWord (Fin BB) := #v[w[0], w[1]]

lemma isU64_low_isU32 {w : Word (Fin BB)} (hw : w.isU64) : w.low.isU32 := by aesop

lemma setWidth_eq_low (w : Word (Fin BB )) (h_w_isU64 : w.isU64) :
    BitVec.setWidth 32 w.toBitVec64 = w.low.toBitVec32
  := by
    have ⟨ _, _, _, _ ⟩ := lt_cases_of_isU64 h_w_isU64
    have := toNat_lt_of_isU64 h_w_isU64
    simp [Word.toNat] at this
    simp [toBitVec64, ← BitVec.toNat_inj, low, Word.toNat, HWord.toBitVec32, HWord.toNat]
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
  simp only [toNat, BB_eq, Nat.reducePow]
  omega

lemma toBitVec64_add_toBitVec64 (w v : Word (Fin BB)) :
    w.toBitVec64 + v.toBitVec64 = BitVec.ofNat 64
      ((w[0].val + v[0].val) + (w[1].val + v[1].val) * 2^16 +
        (w[2].val + v[2].val) * 2^32 + (w[3].val + v[3].val) * 2^48) := by
  simp only [toBitVec64, ← BitVec.ofNat_add, toNat_add_toNat, BB_eq, Nat.reducePow]

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
  | n + 8, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

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
  := by intro i; fin_cases i <;> simpa

/-- Pull in bounds on a byteword's limbs given a `isU64` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU64 {w : ByteWord (Fin BB)} (hbw : w.isU64) :
    w[0].val < 2^8 ∧ w[1].val < 2^8 ∧ w[2].val < 2^8 ∧ w[3].val < 2^8 ∧
    w[4].val < 2^8 ∧ w[5].val < 2^8 ∧ w[6].val < 2^8 ∧ w[7].val < 2^8 :=
  ⟨hbw 0, hbw 1, hbw 2, hbw 3, hbw 4, hbw 5, hbw 6, hbw 7⟩

lemma lt_cases_of_isU64_bv { w : ByteWord (Fin BB) } (hw : w.isU64) :
  BitVec.ofNat 64 w[0] < 256 ∧ BitVec.ofNat 64 w[1] < 256 ∧
  BitVec.ofNat 64 w[2] < 256 ∧ BitVec.ofNat 64 w[3] < 256 ∧
  BitVec.ofNat 64 w[4] < 256 ∧ BitVec.ofNat 64 w[5] < 256 ∧
  BitVec.ofNat 64 w[6] < 256 ∧ BitVec.ofNat 64 w[7] < 256
    := by
  obtain ⟨ w0, w1, w2, w3, w4, w5, w6, w7 ⟩ := lt_cases_of_isU64 hw
  simp; omega

end U64

section conversions

/-- Convert a byteword to a `Word` by combining the limbs. -/
def toWord (w : ByteWord (Fin BB)) : Word (Fin BB) :=
  #v[w[0] + w[1] * 256, w[2] + w[3] * 256, w[4] + w[5] * 256, w[6] + w[7] * 256]

/-- Convert a byteword to a `Nat` by shifting and adding the limbs. -/
def toNat (w : ByteWord (Fin BB)) : ℕ := w[0] + w[1] * 2^8 + w[2] * 2^16 + w[3] * 2^24 + w[4] * 2^32 + w[5] * 2^40 + w[6] * 2^48 + w[7] * 2^56

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
  simp only [toBitVec64, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
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
  simp [toWord, toInt, toNat, Word.toInt, Word.toNat, isNegative, Word.isNegative]
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

namespace ByteDWord

/-- Prove two `ByteDWord`s equal by considering each index individually.
    Extensionality tactics will default to using this version. -/
@[ext] lemma ext_cases {w w' : ByteDWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3])
    (h4 : w[4] = w'[4]) (h5 : w[5] = w'[5]) (h6 : w[6] = w'[6]) (h7 : w[7] = w'[7])
    (h8 : w[8] = w'[8]) (h9 : w[9] = w'[9]) (h10 : w[10] = w'[10]) (h11 : w[11] = w'[11])
    (h12 : w[12] = w'[12]) (h13 : w[13] = w'[13]) (h14 : w[14] = w'[14]) (h15 : w[15] = w'[15]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1 | 2, _ => h2 | 3, _ => h3 | 4, _ => h4 | 5, _ => h5 | 6, _ => h6 | 7, _ => h7
  | 8, _ => h8 | 9, _ => h9 | 10, _ => h10 | 11, _ => h11 | 12, _ => h12 | 13, _ => h13 | 14, _ => h14 | 15, _ => h15
  | n + 16, h => by simp only [add_lt_iff_neg_right, not_lt_zero'] at h

/-- Prove two `Word`s equal by considering all bounded indices. -/
@[ext] lemma ext_forall {w w' : ByteDWord T}
    (h : ∀ i : Fin BYTE_DWORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

lemma eq_mk_getElem (w : ByteDWord T) : w = #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]]
  := ext_cases rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl

lemma eq_pointwise (w w': ByteDWord T) :
    (w[0] = w'[0]) ∧ (w[1] = w'[1]) ∧ (w[2] = w'[2]) ∧ (w[3] = w'[3]) ∧
    (w[4] = w'[4]) ∧ (w[5] = w'[5]) ∧ (w[6] = w'[6]) ∧ (w[7] = w'[7]) ∧
    (w[8] = w'[8]) ∧ (w[9] = w'[9]) ∧ (w[10] = w'[10]) ∧ (w[11] = w'[11]) ∧
    (w[12] = w'[12]) ∧ (w[13] = w'[13]) ∧ (w[14] = w'[14]) ∧ (w[15] = w'[15])
    ↔ w = w' := by
  constructor <;> intro h <;> [ apply ext_cases; skip ] <;> aesop

/-- Prove something about arbitrary `ByteWord`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : ByteDWord T → Prop}
    (mk : ∀ x0 x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 : T, C #v[x0, x1, x2, x3, x4, x5, x6, x7, x8, x9, x10, x11, x12, x13, x14, x15]) (w : ByteDWord T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section U128

/-- `isU128 w` means that each limb of the word is properly bounded. -/
def isU128 (w : ByteDWord (Fin BB)) : Prop := ∀ i : Fin BYTE_DWORD_SIZE, w[i].val < 256

@[aesop unsafe apply]
lemma isU128_of_cases (w : ByteDWord (Fin BB))
    (h0 : w[0].val < 256) (h1 : w[1].val < 256)
    (h2 : w[2].val < 256) (h3 : w[3].val < 256)
    (h4 : w[4].val < 256) (h5 : w[5].val < 256)
    (h6 : w[6].val < 256) (h7 : w[7].val < 256)
    (h8 : w[8].val < 256) (h9 : w[9].val < 256)
    (h10 : w[10].val < 256) (h11 : w[11].val < 256)
    (h12 : w[12].val < 256) (h13 : w[13].val < 256)
    (h14 : w[14].val < 256) (h15 : w[15].val < 256) : w.isU128
  := by intro i; fin_cases i <;> simpa

/-- Pull in bounds on a dword's limbs given a `isU64` proof. -/
@[aesop unsafe forward]
lemma lt_cases_of_isU128 {w : ByteDWord (Fin BB)} (hbdw : w.isU128) :
    w[0].val < 256 ∧ w[1].val < 256 ∧ w[2].val < 256 ∧ w[3].val < 256 ∧
    w[4].val < 256 ∧ w[5].val < 256 ∧ w[6].val < 256 ∧ w[7].val < 256 ∧
    w[8].val < 256 ∧ w[9].val < 256 ∧ w[10].val < 256 ∧ w[11].val < 256 ∧
    w[12].val < 256 ∧ w[13].val < 256 ∧ w[14].val < 256 ∧ w[15].val < 256
    :=
  ⟨hbdw 0, hbdw 1, hbdw 2, hbdw 3, hbdw 4, hbdw 5, hbdw 6, hbdw 7, hbdw 8, hbdw 9, hbdw 10, hbdw 11, hbdw 12, hbdw 13, hbdw 14, hbdw 15⟩

lemma lt_cases_of_isU128_bv { w : ByteDWord (Fin BB) } (hw : w.isU128) :
  BitVec.ofNat 64 w[0] < 256 ∧ BitVec.ofNat 64 w[1] < 256 ∧
  BitVec.ofNat 64 w[2] < 256 ∧ BitVec.ofNat 64 w[3] < 256 ∧
  BitVec.ofNat 64 w[4] < 256 ∧ BitVec.ofNat 64 w[5] < 256 ∧
  BitVec.ofNat 64 w[6] < 256 ∧ BitVec.ofNat 64 w[7] < 256 ∧
  BitVec.ofNat 64 w[8] < 256 ∧ BitVec.ofNat 64 w[9] < 256 ∧
  BitVec.ofNat 64 w[10] < 256 ∧ BitVec.ofNat 64 w[11] < 256 ∧
  BitVec.ofNat 64 w[12] < 256 ∧ BitVec.ofNat 64 w[13] < 256 ∧
  BitVec.ofNat 64 w[14] < 256 ∧ BitVec.ofNat 64 w[15] < 256
    := by
  obtain ⟨ w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15  ⟩ := lt_cases_of_isU128 hw
  simp; omega

end U128

section conversions

/-- Lower and higher bytewords -/
def low  (w : ByteDWord (Fin BB)) : ByteWord (Fin BB) := #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7]]
def high (w : ByteDWord (Fin BB)) : ByteWord (Fin BB) := #v[w[8], w[9], w[10], w[11], w[12], w[13], w[14], w[15]]

/-- Convert a bytedword to a `Nat` by shifting and adding the limbs. -/
def toNat (w : ByteDWord (Fin BB)) : ℕ :=
  w[0] + w[1] * (1 <<< 8) + w[2] * (1 <<< 16) + w[3] * (1 <<< 24) + w[4] * (1 <<< 32) + w[5] * (1 <<< 40) + w[6] * (1 <<< 48) + w[7] * (1 <<< 56) +
  w[8] * (1 <<< 64) + w[9] * (1 <<< 72) + w[10] * (1 <<< 80) + w[11] * (1 <<< 88) + w[12] * (1 <<< 96) + w[13] * (1 <<< 104) + w[14] * (1 <<< 112) + w[15] * (1 <<< 120)

lemma toNat_lt_of_isU128 {w : ByteDWord (Fin BB)} (hw : w.isU128) : w.toNat < (1 <<< 128) := by
  unfold toNat
  aesop (add 50% tactic (by omega))

lemma toNat_lt_of_cases_lt (w : ByteDWord (Fin BB))
    (h0 : w[0].val < 256) (h1 : w[1].val < 256)
    (h2 : w[2].val < 256) (h3 : w[3].val < 256)
    (h4 : w[4].val < 256) (h5 : w[5].val < 256)
    (h6 : w[6].val < 256) (h7 : w[7].val < 256)
    (h8 : w[8].val < 256) (h9 : w[9].val < 256)
    (h10 : w[10].val < 256) (h11 : w[11].val < 256)
    (h12 : w[12].val < 256) (h13 : w[13].val < 256)
    (h14 : w[14].val < 256) (h15 : w[15].val < 256) : w.toNat < (1 <<< 128) := by
  unfold toNat; omega

lemma toNat_lt_of_forall_lt (w : ByteDWord (Fin BB))
    (h : ∀ i : Fin BYTE_DWORD_SIZE, w[i] < 256) : w.toNat < (1 <<< 128) := by
  refine toNat_lt_of_cases_lt w (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7) (h 8) (h 9) (h 10) (h 11) (h 12) (h 13) (h 14) (h 15)

/-- Convert a byteword to a `BitVec 64` by shifting and adding the limbs. -/
def toBitVec128 (w : ByteDWord (Fin BB)) : BitVec 128 := BitVec.ofNat 128 w.toNat

lemma toBitVec128_toNat {w : ByteDWord (Fin BB)} (hw : w.isU128) :
    w.toBitVec128.toNat = w.toNat := by
  simp only [toBitVec128, toNat, BB_eq, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU128 hw
  omega

/-- A 64-bit integer is negative if its msb equals one -/
def isNegative (w : ByteDWord (Fin BB)) : Prop := w[15] ≥ 128
instance : Decidable (isNegative w) := by unfold isNegative; infer_instance

lemma isNegative_msb
  (w : ByteDWord (Fin BB))
  (h_w_isU128 : w.isU128) :
    w.isNegative ↔ (w.toBitVec128.msb = true) := by
  have := lt_cases_of_isU128 h_w_isU128
  simp [isNegative, ByteDWord.toBitVec128, ByteDWord.toNat, BitVec.msb_eq_decide]
  omega

lemma isNegative_BitVec.toInt
  (w : ByteDWord (Fin BB))
  (h_w_isU128 : w.isU128) :
    w.isNegative ↔ ¬ 2 * w.toNat < (1 <<< 128) := by
  rw [isNegative_msb _ h_w_isU128]
  simp [BitVec.msb_eq_decide]
  rw [toBitVec128_toNat h_w_isU128]
  omega

/-- Convert a byteword to an `Int` by shifting and adding the limbs, with sign correction. -/
def toInt (w : ByteDWord (Fin BB)) : ℤ :=
  if (isNegative w) then w.toNat - (1 <<< 128) else w.toNat

set_option maxRecDepth 200000
lemma toBitVec128_toInt {w : ByteDWord (Fin BB)} (h_w_isU128 : w.isU128) :
    w.toBitVec128.toInt = w.toInt
  := by
    have := lt_cases_of_isU128 h_w_isU128
    have := toNat_lt_of_isU128 h_w_isU128
    simp_all [toBitVec128, toInt, BitVec.toInt]
    split_ifs <;> rw [isNegative_BitVec.toInt _ h_w_isU128] at * <;> omega

end conversions

end ByteDWord

namespace HWord

lemma sign_extend_32_to_64_msb (w : HWord (Fin BB)) :
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
  simp [BitVec.toInt_signExtend_of_le.toInt_signExtend_of_lt]
  rw [toBitVec32_toInt is_U32_w, Word.toBitVec64_toInt is_U64_sw]
  simp [toInt, Word.toInt]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, HWord.toNat, Word.toNat] <;>
  rw [isNegative_msb] at * <;>
  simp_all; omega

end HWord

namespace Word

/-- Convert a word to a `ByteWord` by separating the limbs. -/
def toByteWord (w : Word (Fin BB)) : ByteWord (Fin BB) :=
  #v[w[0] % 256, w[0] / 256, w[1] % 256, w[1] / 256, w[2] % 256, w[2] / 256, w[3] % 256, w[3] / 256 ]

lemma toU64_toByteWord
  (w : Word (Fin BB))
  (h_w_isU64 : w.isU64) :
    w.toByteWord.isU64 := by
  simp [Word.toByteWord]
  apply Word.lt_cases_of_isU64 at h_w_isU64
  apply ByteWord.isU64_of_cases <;> simp <;> omega

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
  simp [toByteWord, toInt, toNat, ByteWord.toInt, ByteWord.toNat, isNegative, ByteWord.isNegative, Fin.le_def]
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

namespace ByteWord

/-- Sign-extension to 128 bits -/
def extend (w : ByteWord (Fin BB)) (sgn : Bool) : ByteDWord (Fin BB) :=
  let ext := (if sgn then (if w.isNegative then (1 : Fin BB) else 0) else 0) * 255
  #v[w[0], w[1], w[2], w[3], w[4], w[5], w[6], w[7], ext, ext, ext, ext, ext, ext, ext, ext]

lemma to128_extend {w : ByteWord (Fin BB)} (is_U64_w : w.isU64 ) (sgn : Bool) : (w.extend sgn).isU128 := by
  have := lt_cases_of_isU64 is_U64_w
  apply ByteDWord.isU128_of_cases <;>
  simp [extend] <;> (try split_ifs) <;> omega

lemma extend_true_is_signExtend (w : ByteWord (Fin BB)) :
  w.isU64 →
  (w.extend true).toBitVec128 = BitVec.signExtend 128 w.toBitVec64
    := by
  set sw := extend w true
  intro is_U64_w
  have is_U128_bdw : sw.isU128 := by
    have := lt_cases_of_isU64 is_U64_w
    subst sw; simp [extend]
    apply ByteDWord.isU128_of_cases <;> split_ifs <;> simp_all
  have is_neg : w.isNegative ↔ sw.isNegative := by
    subst sw
    simp [extend, isNegative, ByteDWord.isNegative]
    aesop
  rw [← BitVec.toInt_inj]
  simp [BitVec.toInt_signExtend_of_le.toInt_signExtend_of_lt]
  rw [toBitVec64_toInt is_U64_w, ByteDWord.toBitVec128_toInt is_U128_bdw]
  simp [toInt, ByteDWord.toInt]
  split_ifs <;> [ skip; tauto; tauto; skip ] <;>
  simp [sw, extend, ByteDWord.toNat, ByteWord.toNat] <;>
  simp_all; omega

lemma extend_false_is_setWidth (w : ByteWord (Fin BB)) :
  w.isU64 →
  (w.extend false).toBitVec128 = BitVec.setWidth 128 w.toBitVec64
    := by
  set sw := extend w false
  intro is_U64_w
  have is_U128_bdw : sw.isU128 := by
    have := lt_cases_of_isU64 is_U64_w
    subst sw; simp [extend]
    apply ByteDWord.isU128_of_cases <;> split_ifs <;> simp_all
  rw [← BitVec.toNat_inj]
  rw [ByteDWord.toBitVec128_toNat is_U128_bdw]
  rw [BitVec.setWidth_idem (by simp)]
  rw [ByteWord.toBitVec64_toNat is_U64_w]
  simp [sw, ByteDWord.toNat, extend, ByteWord.toNat]

end ByteWord

section Bitwise

namespace Word

lemma and_toByteWord {a b : Word (Fin BB)} : a.isU64 → b.isU64 →
  a.toBitVec64 &&& b.toBitVec64 = a.toByteWord.toBitVec64 &&& b.toByteWord.toBitVec64
    := by
  intro h_a_64 h_b_64
  simp [Word.toBitVec64, ByteWord.toBitVec64]
  rw [Word.toNat_toByteWord _ h_a_64, Word.toNat_toByteWord _ h_b_64]

lemma or_toByteWord {a b : Word (Fin BB)} : a.isU64 → b.isU64 →
  a.toBitVec64 ||| b.toBitVec64 = a.toByteWord.toBitVec64 ||| b.toByteWord.toBitVec64
    := by
  intro h_a_64 h_b_64
  simp [Word.toBitVec64, ByteWord.toBitVec64]
  rw [Word.toNat_toByteWord _ h_a_64, Word.toNat_toByteWord _ h_b_64]

lemma xor_toByteWord {a b : Word (Fin BB)} : a.isU64 → b.isU64 →
  a.toBitVec64 ^^^ b.toBitVec64 = a.toByteWord.toBitVec64 ^^^ b.toByteWord.toBitVec64
    := by
  intro h_a_64 h_b_64
  simp [Word.toBitVec64, ByteWord.toBitVec64]
  rw [Word.toNat_toByteWord _ h_a_64, Word.toNat_toByteWord _ h_b_64]

end Word

end Bitwise

section getByte

namespace BitVec

def getByte {n : ℕ} (bv : BitVec n) (i : ℕ) : ℕ := (bv.extractLsb (i * 8 + 7) (i * 8)).toNat

lemma getByte_is_byte : getByte bv i < 256 := by simp [getByte]; omega

lemma byte_decomp_128 (bv : BitVec 128) :
  bv = ByteDWord.toBitVec128
        #v[getByte bv 0, getByte bv 1, getByte bv 2, getByte bv 3,
           getByte bv 4, getByte bv 5, getByte bv 6, getByte bv 7,
           getByte bv 8, getByte bv 9, getByte bv 10, getByte bv 11,
           getByte bv 12, getByte bv 13, getByte bv 14, getByte bv 15]
    := by
  have : 256 = (256#128).toNat := by simp
  simp [getByte, ByteDWord.toBitVec128, ByteDWord.toNat]
  repeat rw [Nat.mod_eq_of_lt (b := 2013265921) (by omega)]
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
