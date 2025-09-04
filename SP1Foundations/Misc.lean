import Mathlib

/-!
# Misc Lemmas Used in Verification

File for random lemmas that don't fit anywhere else (e.g. lemmas about nat).
Would be good to eventually contribute these back to mathlib.
-/

section grind

grind_pattern Fin.coe_ofNat_eq_mod => (@Fin.val m (OfNat.ofNat n))

end grind

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

end LawfulMonadStateOf

namespace StateT

/-- `StateT` is has lawful state operations. This is applied for `StateM` as well do
to the reducibility of that definition. -/
instance {m σ} [Monad m] [LawfulMonad m] : LawfulMonadStateOf σ (StateT σ m) where
  modifyGet_eq f := StateT.ext fun s => by simp
  get_bind_const mx := StateT.ext fun s => by simp
  get_bind_get_bind mx := StateT.ext fun s => by simp
  get_bind_set_bind mx := StateT.ext fun s => by simp
  set_bind_get s := StateT.ext fun s => by simp
  set_bind_set s s' := StateT.ext fun s => by simp

end StateT

namespace StateCpsT

instance {σ m} : LawfulMonadStateOf σ (StateCpsT σ m) where
  modifyGet_eq _ := rfl
  get_bind_const _ := rfl
  get_bind_get_bind _ := rfl
  get_bind_set_bind _ := rfl
  set_bind_get _ := rfl
  set_bind_set _ _ := rfl

end StateCpsT

namespace EStateM

instance {σ ε} : LawfulMonadStateOf σ (EStateM ε σ) where
  modifyGet_eq _ := rfl
  get_bind_const _ := rfl
  get_bind_get_bind _ := rfl
  get_bind_set_bind _ := rfl
  set_bind_get _ := rfl
  set_bind_set _ _ := rfl

end EStateM

namespace ReaderT

instance {m σ ρ} [Monad m] [LawfulMonad m] [MonadStateOf σ m] [LawfulMonadStateOf σ m] :
    LawfulMonadStateOf σ (ReaderT ρ m) where
  modifyGet_eq f := ReaderT.ext fun ctx => by
    simp [← liftM_modifyGet, LawfulMonadStateOf.modifyGet_eq, ← liftM_get]
  get_bind_const mx := ReaderT.ext fun ctx => by
    simp [← liftM_modifyGet, ← liftM_get]
  get_bind_get_bind mx := ReaderT.ext fun ctx => by
    simp [← liftM_modifyGet, ← liftM_get]
  get_bind_set_bind mx := ReaderT.ext fun ctx => by
    simp [← liftM_modifyGet, ← liftM_get, ← liftM_set]
  set_bind_get s := ReaderT.ext fun ctx => by
    simp [← liftM_modifyGet, ← liftM_get, ← liftM_set]
  set_bind_set s s' := ReaderT.ext fun ctx => by
    simp [← liftM_modifyGet, ← liftM_get, ← liftM_set]

end ReaderT

end toBatteries
