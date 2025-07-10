import SP1Foundations.Unsigned

@[simp] abbrev BIT_WIDTH := 32
@[simp] abbrev WORD_BYTE_SIZE := 8
@[simp] abbrev WORD_SIZE := 4

@[reducible] def Word (T : Type) := Vector T WORD_SIZE
@[reducible] def ByteWord (T : Type) := Vector T WORD_BYTE_SIZE

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

/-- Prove something about arbitrary `Word`s by showing it for any two choices of limbs. -/
@[elab_as_elim] protected def inductionOn {C : Word T → Prop}
    (mk : ∀ x1 x2 x3 x4 : T, C #v[x1, x2, x3, x4]) (w : Word T) : C w := by
  rw [eq_mk_getElem w]; apply mk

section isU64

/-- `isU64 w` means that each limb of the word is properly bounded. -/
def isU64 (w : Word (Fin BB)) : Prop := ∀ i : Fin WORD_SIZE, w[i].val < 2^16

@[aesop unsafe apply]
lemma isU64_of_cases (w : Word (Fin BB))
    (h0 : w[0].val < 2^16) (h1 : w[1].val < 2^16)
    (h2 : w[2].val < 2^16) (h3 : w[3].val < 2^16) : w.isU64
  | 0 => h0 | 1 => h1 | 2 => h2 | 3 => h3

/-- Pull in bounds on a word's limbs given a `isU64` proof.
Used to automate  -/
@[aesop unsafe forward]
lemma lt_cases_of_isU64 {w : Word (Fin BB)} (hw : w.isU64) :
    w[0].val < 2^16 ∧ w[1].val < 2^16 ∧ w[2].val < 2^16 ∧ w[3].val < 2^16 :=
  ⟨hw 0, hw 1, hw 2, hw 3⟩

end isU64

section conversions

/-- Convert a word to a `Nat` by shifting and adding limbs. -/
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

lemma toBitVec64_eq_add (w : Word (Fin BB)) : w.toBitVec64 =
    BitVec.ofNat 64 w[0] + BitVec.ofNat 64 (w[1] * 2^16) +
      BitVec.ofNat 64 (w[2] * 2^32) + BitVec.ofNat 64 (w[3] * 2^48) := by
  simp [toBitVec64, toNat, BitVec.ofNat_add]

lemma toNat_toBitVec64 (w : Word (Fin BB)) (hw : w.isU64) :
    w.toBitVec64.toNat = w.toNat := by
  simp only [toBitVec64, toNat, BB_eq, WORD_SIZE, Nat.reducePow, BitVec.toNat_ofNat,
    Nat.mod_succ_eq_iff_lt, Nat.succ_eq_add_one, Nat.reduceAdd]
  have := lt_cases_of_isU64 hw
  omega

/-- Convert a word to a `Fin 2^64` by shifting and adding the limbs. -/
def toFin64 (w : Word (Fin BB)) : Fin (2^64) := BitVec.toFin w.toBitVec64

lemma toFin_toBitVec64 (w : Word (Fin BB)) :
    w.toBitVec64.toFin = w.toFin64 := rfl

end conversions

section add

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

lemma toFin64_add_toFin64 (w v : Word (Fin BB)) :
    w.toFin64 + v.toFin64 = Fin.ofNat (2^64)
      ((w[0].val + v[0].val) + (w[1].val + v[1].val) * 2^16 +
        (w[2].val + v[2].val) * 2^32 + (w[3].val + v[3].val) * 2^48) := by
  simp only [Nat.reducePow, toFin64, BB_eq, WORD_SIZE, Fin.ofNat_eq_cast]
  rw [← BitVec.toFin_add w.toBitVec64, toBitVec64_add_toBitVec64]
  rfl

lemma val_add_of_isU64 {w v : Word (Fin BB)} (hw : w.isU64) (hv : v.isU64)
    (i : Fin WORD_SIZE) : (w[i] + v[i]).val = w[i].val + v[i].val := by
  have := hw i; have := hv i
  simp [Fin.val_add] at *
  omega

end add

end Word
