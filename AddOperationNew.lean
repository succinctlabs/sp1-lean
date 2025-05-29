import Mathlib

macro "WORD_SIZE" : term => `(2)
macro "BASE" : term => `(2 ^ 16)

@[reducible]
def Word (T : Type) := Vector T WORD_SIZE

abbrev p := 2013265921
variable [Fact (Nat.Prime p)] [(NoZeroDivisors (Fin p))]

def Word.is_u32 (w : Word (Fin p)) : Prop :=
  ∀ x ∈ w, x < BASE

def Word.toNat (w : Word (Fin p)) : ℕ :=
  w[0].val + BASE * w[1].val

structure AddOperation (T : Type) where
  value : Word T

@[elab_as_elim]
def Word.inductionOn {α : Type} {C : Word α → Prop}
    (mk : ∀ x1 x2 : α, C #v[x1, x2]) (w : Word α) : C w := sorry

@[elab_as_elim]
def AddOperation.inductionOn {α : Type} {C : AddOperation α → Prop}
    (mk : ∀ x1 x2 : α, C ⟨#v[x1, x2]⟩)
    (op : AddOperation α) : C op := sorry

def AddOperation.spec
    (cols : AddOperation (Fin p))
    (a : Word (Fin p))
    (b : Word (Fin p)) : Prop :=
  let a32 := a.toNat
  let b32 := b.toNat
  let c32 := cols.value.toNat
  a.is_u32 → b.is_u32 →
    (a32 + b32) % 2^32 = c32

def AddOperation.constraints
    (cols : AddOperation (Fin p))
    (a : Word (Fin p))
    (b : Word (Fin p)) : Prop :=
  let carry0 := 0
  let carry1 := (a[0] + b[0] - cols.value[0] + carry0) * BASE⁻¹
  let carry2 := (a[1] + b[1] - cols.value[1] + carry1) * 2013235201
  -- actual constraints
  carry1 * (carry1 - 1) = 0 ∧
  carry2 * (carry2 - 1) = 0 ∧
  cols.value.is_u32 -- slice range checks

-- set_option maxRecDepth 1000000000000000
-- set_option maxHeartbeats 5000000000 in

theorem AddOperation.correct (cols : AddOperation (Fin p))
    (a : Word (Fin p)) (b : Word (Fin p)) :
    cols.constraints a b → cols.spec a b := by
  induction a using Word.inductionOn with | mk a1 a2 =>
  induction b using Word.inductionOn with | mk b1 b2 =>
  induction cols using AddOperation.inductionOn with | mk v1 v2 =>
  simp [constraints, spec, Word.is_u32, Word.toNat, mul_eq_zero]
  intros h1 h2 h3 h4 h5 h6 h7 h8

  cases a1 with | mk a1 ha1 =>
  cases a2 with | mk a2 ha2 =>
  cases b1 with | mk b1 hb1 =>
  cases b2 with | mk b2 hb2 =>
  cases v1 with | mk v1 hv1 =>
  cases v2 with | mk v2 hv2 =>
  simp only

  have hinv : (2013235201 : Fin p).val = 2013235201 := rfl
  have hpow : (2 ^ 16 : Fin p).val = 2 ^ 16 := rfl

  simp only [Fin.lt_iff_val_lt_val, hpow] at h3 h4 h5 h6 h7 h8
  -- clear hpow hinv

  cases h1 with
  | inl h1 => cases h2 with
    | inl h2 => {
      simp [p] at *
      rw [h1] at h2
      simp [Fin.add_def, Fin.sub_def, Fin.mul_def, hinv] at h1 h2
      omega
    }
    | inr h2 => {
      simp [p, Nat.mod_mod] at *
      rw [h1, zero_mul, add_zero] at h2
      rw [sub_eq_zero] at h1 h2


    }
  | inr h1 => cases h2 with
    | inl h2 => {
      simp [p] at *
      sorry --omega
    }
    | inr h2 => {
      simp [p] at *
      sorry
    }
