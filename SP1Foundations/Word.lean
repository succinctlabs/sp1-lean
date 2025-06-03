import SP1Foundations.Unsigned

abbrev WORD_SIZE := 2

abbrev Word (T : Type) := Vector T WORD_SIZE

namespace Word

@[elab_as_elim] -- induction rule for words
def inductionOn {α : Type} {C : Word α → Prop}
    (mk : ∀ x1 x2 : α, C #v[x1, x2]) (w : Word α) : C w := by
  convert mk w[0] w[1]
  rw [← Array.toList_inj]
  obtain ⟨⟨ws⟩, h⟩ := w
  simp [WORD_SIZE, List.length_eq_two] at h
  obtain ⟨w1, w2, h⟩ := h
  simp [h]

def toFin32_BB (w : Word BabyBear) : Fin (2^32) :=
  ⟨(w[0].val + w[1].val * 65536) % (2^32), by
    apply Nat.mod_lt
    norm_num⟩

def toFin32_U16 (w : Word U16) : Fin (2^32) :=
  ⟨w[0].val.val + w[1].val.val * 65536, by
    let wn0 : Nat := w[0].val.val
    let wn1 : Nat := w[1].val.val
    show wn0 + wn1 * 65536 < 2^32
    have wn0_in_range : wn0 < 65536 := w[0].in_range
    have wn1_in_range : wn1 < 65536 := w[1].in_range
    simp at *
    omega⟩

@[reducible] def toNat (w : Word (BabyBear)) : ℕ :=
  w[0].val + base * w[1].val

lemma toNat_add_toNat (a b : Word (BabyBear)) :
    a.toNat + b.toNat = (a[0] + b[0]) + base * (a[1] + b[1]) := by
  simp [Word.toNat]
  sorry
  -- omega

theorem toFin32_U16_val {w : Word U16} : (w.toFin32_U16).val =
  w[0].val.val + w[1].val.val * 65536 := by
  simp [toFin32_U16, base]

def isUInt32 (w : Word (BabyBear)) : Prop :=
  w[0].val < base ∧ w[1].val < base

end Word
