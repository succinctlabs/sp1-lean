import Mathlib

/-!
# Misc Lemmas Used in Verification

File for random lemmas that don't fit anywhere else (e.g. lemmas about nat).
Would be good to eventually contribute these back to mathlib.
-/

section grind

grind_pattern Fin.coe_ofNat_eq_mod => (@Fin.val m (OfNat.ofNat n))

end grind

@[simp] lemma Std.ExtDHashMap.insert_inj' {α β}
    [BEq α] [LawfulBEq α] [EquivBEq α]
    [Hashable α] [LawfulHashable α]
    (m m' : Std.ExtDHashMap α β)
    (x : α) (y y' : β x) :
    m.insert x y = m'.insert x y' ↔
      (y = y' ∧ ∀ x', x ≠ x' → m.get? x' = m'.get? x') := by
  simp [Std.ExtDHashMap.ext_get?_iff,
    Std.ExtDHashMap.get?_insert]
  refine ⟨fun h => ?_, fun h k => ?_⟩
  · refine ⟨by simpa using h x, fun x' hx' => ?_⟩
    simpa [beq_iff_eq, hx'] using h x'
  · split_ifs <;> aesop

@[simp] lemma Std.ExtDHashMap.insert_inj {α β}
    [BEq α] [LawfulBEq α] [EquivBEq α]
    [Hashable α] [LawfulHashable α]
    (m : Std.ExtDHashMap α β)
    (x : α) (y y' : β x) :
    m.insert x y = m.insert x y' ↔ y = y' := by
  simp [Std.ExtDHashMap.ext_get?_iff,
    Std.ExtDHashMap.get?_insert]
  refine ⟨fun h => ?_, fun h k => ?_⟩
  · simpa using h x
  · split_ifs <;> simp [h]

instance Fin.noZeroDivisors_of_prime (p : ℕ)
    [hp : Fact (Nat.Prime (p + 1))] : NoZeroDivisors (Fin (p + 1)) := by
  refine IsDomain.to_noZeroDivisors (ZMod (p + 1))

lemma Nat.mod_eq_zero_iff_of_lt (x y : ℕ) (h : x < y) : x % y = 0 ↔ x = 0 := by
  have : x / y = 0 := by aesop
  rw [Nat.mod_def, this, mul_zero, Nat.sub_zero]

@[simp] theorem Std.ExtDHashMap.insert_insert [BEq α] [Hashable α] [LawfulBEq α]
    {m : Std.ExtDHashMap α β} (a : α) (b b' : β a) :
    (m.insert a b).insert a b' = m.insert a b' := by
  refine Std.ExtDHashMap.ext_get? fun a' => ?_
  simp [Std.ExtDHashMap.get?_insert]
  by_cases h : a = a'
  · induction h
    simp
  · simp [h]

@[simp] theorem Std.ExtDHashMap.insert_insert_comm [BEq α] [Hashable α] [LawfulBEq α]
    (m : Std.ExtDHashMap α β) (a a' : α) (b : β a) (b' : β a') (h : a ≠ a') :
    (m.insert a b).insert a' b' = (m.insert a' b').insert a b := by
  refine Std.ExtDHashMap.ext_get? fun x => ?_
  simp [get?_insert]
  split_ifs
  · refine (h ?_).elim
    aesop
  · aesop
  · aesop
  · aesop

instance : Fintype (BitVec n) where
  elems := Finset.image (BitVec.ofFin) Finset.univ
  complete := by
    intro x
    simp [Finset.mem_image]

section toBatteries

namespace LawfulMonadStateOf

variable {σ : Type _} {m : Type _ → Type _} [Monad m] [LawfulMonad m]
  [MonadStateOf σ m] [LawfulMonadStateOf σ m]

attribute [simp] get_bind_const get_bind_get_bind get_bind_set_bind set_bind_get set_bind_set

section modify

section back

theorem modify_bind_get_bind_of_forall_eq (f : σ → σ)
    (g : σ → α) (mx : α → m β) (x : α) (h : ∀ s, g (f s) = x) :
    (do modify f; let s ← get; mx (g s)) =
      (do modify f; mx x) := by
  simp [modify_eq, h]

@[simp]
lemma insert_insert_insert_cancel {α : Type _} {β : α → Type _}
  [BEq α] [LawfulBEq α] [Hashable α] (m : Std.ExtDHashMap α β)
    (a₁ a₂ : α) {v v' : β a₁} (w : β a₂) :
    ((m.insert a₁ v).insert a₂ w).insert a₁ v' =
      (m.insert a₂ w).insert a₁ v' := by
  refine Std.ExtDHashMap.ext_get? ?_
  intro k
  aesop (add safe (by rw [Std.ExtDHashMap.get?_insert]))

end back

end modify
