import Mathlib

macro "WORD_SIZE" : term => `(4)

@[simp]
def _root_.ZMod.toUInt8 (x : ZMod p) : UInt8 := x.val.toUInt8

@[reducible]
def Word (T : Type) := Vector T WORD_SIZE

instance {T : Type} [Zero T] : Zero (Word T) where
  zero := #v[0, 0, 0, 0]

instance {T : Type} [Zero T] [One T] : One (Word T) where
  one := #v[1, 0, 0, 0]

abbrev p := 2013265921
variable [Fact (Nat.Prime p)] [NoZeroDivisors (Fin p)]

def Word.is_u32 (w : Word (Fin p)) : Prop :=
  ∀ x ∈ w, x < 256

def Word.toNat (w : Word (Fin p)) : ℕ :=
  w[0].val + 256 * w[1].val + 65536 * w[2].val + 16777216 * w[3].val

-- def Word.to_UInt32 (w : Word (Fin p)) : UInt32 :=
--   UInt32.ofNat (w[0].1 + 256 * w[1].1 + 65536 * w[2].1 + 16777216 * w[3].1)

-- def Word.zmod_to_UInt8 (w : Word (Fin p)) : Word UInt8 :=
--   w.map fun x => x.val.toUInt8

-- def Word.UInt8_to_UInt32 (w : Word UInt8) : UInt32 :=
--   -- ⟨w[3].1 ++ w[2].1 ++ w[1].1 ++ w[0].1⟩
--   (w[3].toUInt32 <<< 24) +
--     (w[2].toUInt32 <<< 16) +
--     (w[1].toUInt32 <<< 8) +
--     w[0].toUInt32

-- def UInt32_to_UInt8_word (u : UInt32) : Word (UInt8) :=
--   #v[ (u &&& 0xFF).toNat
--     , ((u >>> 8) &&& 0xFF).toNat
--     , ((u >>> 16) &&& 0xFF).toNat
--     , ((u >>> 24) &&& 0xFF).toNat
--     ]

structure AddOperation (T : Type) where
  value : Word T
  carry : Vector T 3

@[elab_as_elim]
def Word.inductionOn {α : Type} {C : Word α → Prop}
    (mk : ∀ x1 x2 x3 x4 : α, C #v[x1, x2, x3, x4]) (w : Word α) : C w := sorry

@[elab_as_elim]
def AddOperation.inductionOn {α : Type} {C : AddOperation α → Prop}
    (mk : ∀ x1 x2 x3 x4 c1 c2 c3 : α, C ⟨#v[x1, x2, x3, x4], #v[c1, c2, c3]⟩)
    (op : AddOperation α) : C op := sorry

def AddOperation.spec
    (cols : AddOperation (Fin p))
    (a : Word (Fin p))
    (b : Word (Fin p)) : Prop :=
  let a32 := a.toNat
  let b32 := b.toNat
  let c32 := cols.value.toNat
  cols.value.is_u32 ∧ (a32 + b32) % 2^32 = c32

def AddOperation.constraints
    (cols : AddOperation (Fin p))
    (a : Word (Fin p))
    (b : Word (Fin p)) : Prop :=
  let overflow_0 := a[0] + b[0] - cols.value[0]
  let overflow_1 := a[1] + b[1] - cols.value[1] + cols.carry[0]
  let overflow_2 := a[2] + b[2] - cols.value[2] + cols.carry[1]
  let overflow_3 := a[3] + b[3] - cols.value[3] + cols.carry[2]

  (overflow_0 * (overflow_0 - 256)) = 0 ∧
  (overflow_1 * (overflow_1 - 256)) = 0 ∧
  (overflow_2 * (overflow_2 - 256)) = 0 ∧
  (overflow_3 * (overflow_3 - 256)) = 0 ∧

  (cols.carry[0] * (overflow_0 - 256)) = 0 ∧
  (cols.carry[1] * (overflow_1 - 256)) = 0 ∧
  (cols.carry[2] * (overflow_2 - 256)) = 0 ∧

  ((cols.carry[0] - 1) * overflow_0) = 0 ∧
  ((cols.carry[1] - 1) * overflow_1) = 0 ∧
  ((cols.carry[2] - 1) * overflow_2) = 0 ∧

  (cols.carry[0] * (cols.carry[0] - 1)) = 0 ∧
  (cols.carry[1] * (cols.carry[1] - 1)) = 0 ∧
  (cols.carry[2] * (cols.carry[2] - 1)) = 0 ∧

  a.is_u32 ∧ b.is_u32 ∧ cols.value.is_u32 -- slice range checks


theorem AddOperation.correct [Fact (Nat.Prime p)] (cols : AddOperation (Fin p))
    (a : Word (Fin p)) (b : Word (Fin p)) :
    cols.constraints a b → cols.spec a b := by
  have hp' : 512 < p := by trivial
  induction a using Word.inductionOn with | mk a1 a2 a3 a4 =>
  induction b using Word.inductionOn with | mk b1 b2 b3 b4 =>
  induction cols using AddOperation.inductionOn with | mk v1 v2 v3 v4 c1 c2 c3 =>
  -- Break up word indexing `getElem` ops and split on multiplication being zero
  simp only [constraints, mul_eq_zero, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ]
  -- Intro all the individual hyps
  rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, hrange⟩
  refine ⟨hrange.2.2, ?_⟩
  simp [Word.is_u32] at hrange
  simp only [Word.toNat, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, Nat.reducePow]
  -- Split on cases of the carry values
  cases h11 <;> cases h12 <;> cases h13
  · subst_eqs
    simp [sub_eq_zero] at *
    induction h4 with | inl h4 => ?_ | inr h4 => ?_
    · simp [Fin.add_def, Fin.ext_iff, Fin.sub_def] at *
      simp [← h4, ← h8, ← h9, ← h10]
      have : (256 : Fin p).val = 256 := rfl
      simp only [Fin.lt_iff_val_lt_val, this] at hrange
      have h1 : a1.val + b1.val < p := by omega
      have h2 : a2.val + b2.val < p := by omega
      have h3 : a3.val + b3.val < p := by omega
      have h4 : a4.val + b4.val < p := by omega
      rw [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2,
        Nat.mod_eq_of_lt h3, Nat.mod_eq_of_lt h4]
      ring_nf
      refine Nat.mod_eq_of_lt ?_
      sorry
    sorry
  sorry; sorry; sorry; sorry; sorry; sorry; sorry
