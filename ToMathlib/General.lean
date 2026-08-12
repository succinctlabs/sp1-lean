import Mathlib.Tactic
import Mathlib.Data.ZMod.Basic
import Std.Data.ExtDHashMap
import Std.Data.ExtHashMap
set_option linter.unusedSimpArgs false

/-!
# Lemmas to be ported to Mathlib

The catch-all of the `ToMathlib/` tree: general-purpose lemmas and instances that belong in Mathlib
rather than in this project, but have no home there yet. Nothing here mentions Clean or SP1, and by
the tree's import rule nothing here may import project code.

Current contents: kernel-safe `Int.toNat`/`%` normalization (the plain shape blows the kernel's
stack once `2 ^ N` unfolds definitionally for `N ≥ 15`), `Std.ExtDHashMap` insert algebra, `Fin`
no-zero-divisors over a prime, a `Fintype (BitVec n)` instance, and `LawfulMonadStateOf` instances
for `StateT`/`StateCpsT`/`EStateM`/`ReaderT`.

The gap against upstream: Mathlib has `Int.toNat_emod`-style lemmas but not the `natCast` composite
this project needs; the `ExtDHashMap` insert lemmas post-date the container's Mathlib coverage; and
the `LawfulMonadStateOf` instances exist for some transformers upstream but not for the whole set
the Sail model runs in. Each is a candidate PR on its own; when one lands, delete the declaration
here and let the importer pick up the Mathlib name.
-/

section grind

grind_pattern Fin.coe_ofNat_eq_mod => (@Fin.val m (OfNat.ofNat n))

end grind

namespace Int

-- Kernel-rfl-safe normalization for `((↑b : ℤ) % ↑n).toNat = b % n`. The
-- kernel's defeq check on this shape unfolds `2^N` definitionally and blows
-- the stack once `N ≥ 15`; routing through `Int.toNat_emod` + `Int.toNat_natCast`
-- keeps the proof term shallow. The kernel-deep-recursion pattern (and its opaque-variable
-- fix) is catalogued in `docs/agents/proof-patterns.md`.
lemma toNat_natCast_emod_natCast (b n : ℕ) :
    ((b : ℤ) % (n : ℤ)).toNat = b % n := by
  rw [Int.toNat_emod (by positivity) (by positivity), Int.toNat_natCast, Int.toNat_natCast]

lemma toNat_natCast_emod_pow_two (b k : ℕ) :
    ((b : ℤ) % (2 ^ k : ℤ)).toNat = b % 2 ^ k := by
  rw [show ((2 : ℤ) ^ k) = ((2 ^ k : ℕ) : ℤ) by push_cast; rfl]
  exact toNat_natCast_emod_natCast _ _

end Int

@[simp] lemma Std.ExtDHashMap.insert_inj' {α β}
    [BEq α] [LawfulBEq α]
    [Hashable α] [LawfulHashable α]
    (m m' : Std.ExtDHashMap α β)
    (x : α) (y y' : β x) :
    m.insert x y = m'.insert x y' ↔
      (y = y' ∧ ∀ x', x ≠ x' → m.get? x' = m'.get? x') := by
  simp [Std.ExtDHashMap.ext_get?_iff, Std.ExtDHashMap.get?_insert]
  refine ⟨fun h => ?_, fun h k => ?_⟩
  · refine ⟨by simpa using h x, fun x' hx' => ?_⟩
    simpa [beq_iff_eq, hx'] using h x'
  · split_ifs <;> aesop

@[simp] lemma Std.ExtDHashMap.insert_inj {α β}
    [BEq α] [LawfulBEq α]
    [Hashable α] [LawfulHashable α]
    (m : Std.ExtDHashMap α β)
    (x : α) (y y' : β x) :
    m.insert x y = m.insert x y' ↔ y = y' := by
  simp [Std.ExtDHashMap.ext_get?_iff, Std.ExtDHashMap.get?_insert]
  refine ⟨fun h => ?_, fun h k => ?_⟩
  · simpa using h x
  · split_ifs <;> simp [h]

instance Fin.noZeroDivisors_of_prime (p : ℕ)
    [hp : Fact (Nat.Prime (p + 1))] : NoZeroDivisors (Fin (p + 1)) :=
  IsDomain.to_noZeroDivisors (ZMod (p + 1))

@[simp] theorem Std.ExtDHashMap.insert_insert [BEq α] [Hashable α] [LawfulBEq α]
    {m : Std.ExtDHashMap α β} (a : α) (b b' : β a) :
    (m.insert a b).insert a b' = m.insert a b' := by
  refine Std.ExtDHashMap.ext_get? fun a' => ?_
  simp [Std.ExtDHashMap.get?_insert]
  by_cases h : a = a' <;> simp [h]

@[simp] theorem Std.ExtDHashMap.insert_insert_comm [BEq α] [Hashable α] [LawfulBEq α]
    (m : Std.ExtDHashMap α β) (a a' : α) (b : β a) (b' : β a') (h : a ≠ a') :
    (m.insert a b).insert a' b' = (m.insert a' b').insert a b := by
  refine Std.ExtDHashMap.ext_get? fun x => ?_
  simp [get?_insert]
  split_ifs
  · exact (h (by aesop)).elim
  all_goals rfl

instance : Fintype (BitVec n) where
  elems := Finset.image BitVec.ofFin Finset.univ
  complete x := by simp [Finset.mem_image]

section toBatteries

namespace LawfulMonadStateOf

variable {σ : Type _} {m : Type _ → Type _} [Monad m]
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
  refine Std.ExtDHashMap.ext_get? fun k => ?_
  aesop (add safe (by rw [Std.ExtDHashMap.get?_insert]))

end back

end modify

end LawfulMonadStateOf

namespace StateT

/-- `StateT` has lawful state operations. This applies to `StateM` as well, due to the
reducibility of that definition. -/
instance {m σ} [Monad m] [LawfulMonad m] : LawfulMonadStateOf σ (StateT σ m) where
  modifyGet_eq f := StateT.ext fun s => by simp
  get_bind_const mx := StateT.ext fun s => by simp
  get_bind_get_bind mx := StateT.ext fun s => by simp
  get_bind_set_bind mx := StateT.ext fun s => by simp
  set_bind_get _ := StateT.ext fun s => by simp
  set_bind_set _ _ := StateT.ext fun s => by simp

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

instance {m σ ρ} [Monad m] [MonadStateOf σ m] [LawfulMonadStateOf σ m] :
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
