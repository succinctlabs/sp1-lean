import SP1Foundations.Unsigned

@[simp] abbrev BIT_WIDTH := 32
@[simp] abbrev WORD_BYTE_SIZE := 4
@[simp] abbrev WORD_SIZE := 2

@[reducible] def Word (T : Type) := Vector T WORD_SIZE
@[reducible] def ByteWord (T : Type) := Vector T WORD_BYTE_SIZE

variable {T : Type}

/-- Prove two `Word`s equal by considering all bounded indices. -/
@[ext] lemma Word.ext_forall {w w' : Word T}
    (h : ∀ i : Fin WORD_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

/-- Prove two `Word`s equal by considering each index individually.
Extensionality tactics will default to using this version. -/
@[ext] lemma Word.ext_cases {w w' : Word T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1
  | n + 2, h => by simp at h

/-- Prove two `ByteWord`s equal by considering all bounded indices. -/
@[ext] lemma ByteWord.ext_forall {w w' : ByteWord T}
    (h : ∀ i : Fin WORD_BYTE_SIZE, w[i] = w'[i]) : w = w' :=
  Vector.ext fun i n => h ⟨i, n⟩

/-- Prove two `ByteWord`s equal by considering each index individually.
Extensionality tactics will default to using this version. -/
@[ext] lemma ByteWord.ext_cases {w w' : ByteWord T}
    (h0 : w[0] = w'[0]) (h1 : w[1] = w'[1])
    (h2 : w[2] = w'[2]) (h3 : w[3] = w'[3]) : w = w' :=
  Vector.ext fun
  | 0, _ => h0 | 1, _ => h1
  | 2, _ => h2 | 3, _ => h3
  | n + 4, h => by simp at h

/-- Prove something about arbitrary `Word`s by showing it for any two choices of limbs. -/
@[elab_as_elim] def Word.inductionOn {C : Word T → Prop}
    (mk : ∀ x1 x2 : T, C #v[x1, x2]) (w : Word T) : C w := by
  convert mk w[0] w[1]
  rw [← Array.toList_inj]
  obtain ⟨⟨ws⟩, h⟩ := w
  simp [WORD_SIZE, List.length_eq_two] at h
  obtain ⟨w1, w2, h⟩ := h
  simp [h]

/-- Prove something about arbitrary `Word`s by showing it for any two choices of limbs. -/
@[elab_as_elim] def ByteWord.inductionOn {C : ByteWord T → Prop}
    (mk : ∀ x1 x2 x3 x4 : T, C #v[x1, x2, x3, x4]) (w : ByteWord T) : C w := by
  convert mk w[0] w[1] w[2] w[3]
  rw [← Array.toList_inj]
  obtain ⟨⟨ws⟩, h⟩ := w
  sorry

section val_lt

-- Various lemmas about bounds that `aesop` should pull into context.

variable {bound : ℕ} (x : Word (BoundedBabyBear bound))

@[aesop safe forward]
lemma Word.val_zero_boundedBabyBear_lt : x[0].val < bound := x[0].in_range
@[aesop safe forward]
lemma Word.val_one_boundedBabyBear_lt : x[1].val < bound := x[1].in_range

@[aesop safe forward]
lemma ByteWord.val_zero_boundedBabyBear_lt : x[0].val < bound := x[0].in_range
@[aesop safe forward]
lemma ByteWord.val_one_boundedBabyBear_lt : x[0].val < bound := x[0].in_range
@[aesop safe forward]
lemma ByteWord.val_two_boundedBabyBear_lt : x[0].val < bound := x[0].in_range
@[aesop safe forward]
lemma ByteWord.val_three_boundedBabyBear_lt : x[0].val < bound := x[0].in_range

end val_lt

namespace Word

def toFin32_BB (w : Word BabyBear) : Fin (2^32) :=
  ⟨(w[0].val + w[1].val * 65536) % (2^32), by
    apply Nat.mod_lt
    norm_num⟩

def toFin32_U16 (w : Word U16) : Fin (2^32) :=
  ⟨w[0].val + w[1].val * 65536, by
    have wn0_in_range := w[0].in_range
    have wn1_in_range := w[1].in_range
    simp at *
    omega⟩

def toBV32_U16 (w : Word U16) : BitVec BIT_WIDTH :=
  BitVec.ofNatLT (w[0].val + w[1].val * base) (by
    have _ := w[0].in_range
    have _ := w[1].in_range
    simp at *
    omega)

@[reducible] def toNat (w : Word (BabyBear)) : ℕ :=
  w[0].val + base * w[1].val

lemma toNat_add_toNat (a b : Word (BabyBear)) :
    a.toNat + b.toNat = (a[0] + b[0]) + base * (a[1] + b[1]) := by
  simp [Word.toNat]
  omega

theorem toFin32_U16_val {w : Word U16} : (w.toFin32_U16).val =
  w[0].val + w[1].val * 65536 := by
  simp [toFin32_U16, base]

def isUInt32 (w : Word (BabyBear)) : Prop :=
  w[0].val < base ∧ w[1].val < base

end Word
