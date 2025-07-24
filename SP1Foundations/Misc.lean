import Mathlib

/-!
# Misc Lemmas Used in Verification

File for random lemmas that don't fit anywhere else (e.g. lemmas about nat).
Would be good to eventually contribute these back to mathlib.
-/

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

macro "simpM" : tactic => `(tactic| simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet])

instance : Fintype (BitVec n) where
  elems := Finset.image (BitVec.ofFin) Finset.univ
  complete := by
    intro x
    simp [Finset.mem_image]

section toBatteries

/-- The namespaced `MonadStateOf.get` is equal to the `MonadState` provided `get`. -/
@[simp] theorem monadStateOf_get_eq_get [MonadStateOf σ m] :
    (MonadStateOf.get : m σ) = get := rfl

/-- The namespaced `MonadStateOf.modifyGet` is equal to the `MonadState` provided `modifyGet`. -/
@[simp] theorem monadStateOf_modifyGet_eq_modifyGet [MonadStateOf σ m]
    (f : σ → α × σ) : (MonadStateOf.modifyGet f : m α) = modifyGet f := rfl

/-- Class for well behaved state monads, extending the base `MonadState` type.
Requires that `modifyGet` is equal to the same definition with only `get` and `set`,
that `get` is idempotent if the result isn't used, and that `get` after `set` returns
exactly the value that was previously `set`. -/
class LawfulMonadStateOf (σ : Type _) (m : Type _ → Type _)
    [Monad m] [LawfulMonad m] [MonadStateOf σ m] where
  /-- `modifyGet f` is equal to getting the state, modifying it, and returning a result. -/
  modifyGet_eq {α} (f : σ → α × σ) :
    modifyGet (m := m) f = do let z ← f <$> get; set z.2; return z.1
  /-- Discarding the result of `get` is the same as never getting the state. -/
  get_bind_const {α} (mx : m α) : (do let _ ← get; mx) = mx
  /-- Calling `get` twice is the same as just using the first retreived state value. -/
  get_bind_get_bind {α} (mx : σ → σ → m α) :
    (do let s ← get; let s' ← get; mx s s') = (do let s ← get; mx s s)
  /-- Setting the monad state to its current value has no effect. -/
  get_bind_set_bind {α} (mx : σ → PUnit → m α) :
    (do let s ← get; let u ← set s; mx s u) = (do let s ← get; mx s PUnit.unit)
  /-- Setting and then returning the monad state is the same as returning the set value. -/
  set_bind_get (s : σ) : (do set (m := m) s; get) = (do set s; return s)
  /-- Setting the monad twice is the same as just setting to the final state. -/
  set_bind_set (s s' : σ) : (do set (m := m) s; set s') = set s'

namespace LawfulMonadStateOf

variable {σ : Type _} {m : Type _ → Type _} [Monad m] [LawfulMonad m]
  [MonadStateOf σ m] [LawfulMonadStateOf σ m]

attribute [simp] get_bind_const get_bind_get_bind get_bind_set_bind set_bind_get set_bind_set

@[simp] theorem get_seqRight (mx : m α) : get *> mx = mx := by
  rw [seqRight_eq_bind, get_bind_const]

@[simp] theorem seqLeft_get (mx : m α) : mx <* get = mx := by
  simp only [seqLeft_eq_bind, get_bind_const, bind_pure]

@[simp] theorem get_map_const (x : α) :
    (fun _ => x) <$> get (m := m) = pure x := by
  rw [map_eq_pure_bind, get_bind_const]

theorem get_bind_get : (do let _ ← get (m := m); get) = get := get_bind_const get

@[simp] theorem get_bind_set :
    (do let s ← get (m := m); set s) = return PUnit.unit := by
  simpa only [bind_pure_comp, id_map', get_map_const] using
    get_bind_set_bind (σ := σ) (m := m) (fun _ _ => return PUnit.unit)

@[simp] theorem get_bind_map_set (f : σ → PUnit → α) :
    (do let s ← get (m := m); f s <$> set s) = (do return f (← get) PUnit.unit) := by
  simp [map_eq_pure_bind, bind_assoc, -bind_pure_comp]

@[simp] theorem set_bind_get_bind (s : σ) (f : σ → m α) :
    (do set s; let s' ← get; f s') = (do set s; f s) := by
  rw [← bind_assoc, set_bind_get, bind_assoc, pure_bind]

@[simp] theorem set_bind_map_get (f : σ → α) (s : σ) :
    (do set (m := m) s; f <$> get) = (do set (m := m) s; pure (f s)) := by
  simp [map_eq_pure_bind, -bind_pure_comp]

@[simp] theorem set_bind_set_bind (s s' : σ) (mx : m α) :
    (do set s; set s'; mx) = (do set s'; mx) := by
  rw [← bind_assoc, set_bind_set]

@[simp] theorem set_bind_map_set (s s' : σ) (f : PUnit → α) :
    (do set (m := m) s; f <$> set s') = (do f <$> set s') := by
  simp [map_eq_pure_bind, ← bind_assoc, -bind_pure_comp]

section modify

theorem modifyGetThe_eq (f : σ → α × σ) :
    modifyGetThe σ (m := m) f = do let z ← f <$> get; set z.2; return z.1 := modifyGet_eq f

theorem modify_eq (f : σ → σ) :
    modify (m := m) f = (do set (f (← get))) := by simp [modify, modifyGet_eq]

theorem modifyThe_eq (f : σ → σ) :
    modifyThe σ (m := m) f = (do set (f (← get))) := modify_eq f

theorem getModify_eq (f : σ → σ) :
    getModify (m := m) f = do let s ← get; set (f s); return s := by
  rw [getModify, modifyGet_eq, bind_map_left]

/-- Version of `modifyGet_eq` that preserves an call to `modify`. -/
theorem modifyGet_eq' (f : σ → α × σ) :
    modifyGet (m := m) f = do let s ← get; modify (Prod.snd ∘ f); return (f s).fst := by
  simp [modify_eq, modifyGet_eq]

@[simp] theorem modify_id : modify (m := m) id = pure PUnit.unit := by
  simp [modify_eq]

@[simp] theorem getModify_id : getModify (m := m) id = get := by
  simp [getModify_eq]

@[simp] theorem set_bind_modify (s : σ) (f : σ → σ) :
    (do set (m := m) s; modify f) = set (f s) := by simp [modify_eq]

@[simp] theorem set_bind_modify_bind (s : σ) (f : σ → σ) (mx : PUnit → m α) :
    (do set s; let u ← modify f; mx u) = (do set (f s); mx PUnit.unit) := by
  simp [modify_eq, ← bind_assoc]

@[simp] theorem set_bind_modifyGet (s : σ) (f : σ → α × σ) :
    (do set (m := m) s; modifyGet f) = (do set (f s).2; return (f s).1) := by simp [modifyGet_eq]

@[simp] theorem set_bind_modifyGet_bind (s : σ) (f : σ → α × σ) (mx : α → m β) :
    (do set s; let x ← modifyGet f; mx x) = (do set (f s).2; mx (f s).1) := by simp [modifyGet_eq]

@[simp] theorem set_bind_getModify (s : σ) (f : σ → σ) :
    (do set (m := m) s; getModify f) = (do set (f s); return s) := by simp [getModify_eq]

@[simp] theorem set_bind_getModify_bind (s : σ) (f : σ → σ) (mx : σ → m α) :
    (do set s; let x ← getModify f; mx x) = (do set (f s); mx s) := by
  simp [getModify_eq, ← bind_assoc]

@[simp] theorem modify_bind_modify (f g : σ → σ) :
    (do modify (m := m) f; modify g) = modify (g ∘ f) := by simp [modify_eq]

@[simp] theorem modify_bind_modifyGet (f : σ → σ) (g : σ → α × σ) :
    (do modify (m := m) f; modifyGet g) = modifyGet (g ∘ f) := by
  simp [modify_eq, modifyGet_eq]

@[simp] theorem getModify_bind_modify (f : σ → σ) (g : σ → σ → σ) :
    (do let s ← getModify (m := m) f; modify (g s)) =
      (do let s ← get; modify (g s ∘ f)) := by
  simp [modify_eq, getModify_eq]

theorem modify_comm_of_comp_comm {f g : σ → σ} (h : f ∘ g = g ∘ f) :
    (do modify (m := m) f; modify g) = (do modify (m := m) g; modify f) := by
  simp [modify_bind_modify, h]

theorem modify_bind_get (f : σ → σ) :
    (do modify (m := m) f; get) = (do let s ← get; modify f; return (f s)) := by
  simp [modify_eq]

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

section MonadLift

@[simp] theorem liftM_get {m n}  [MonadStateOf σ m] [MonadLift m n] :
    (liftM (get (m := m)) : n _) = get := rfl

@[simp] theorem liftM_set {m n} [MonadStateOf σ m] [MonadLift m n]
    (s : σ) : (liftM (set (m := m) s) : n _) = set s := rfl

@[simp] theorem liftM_modify {m n} [MonadStateOf σ m] [MonadLift m n]
    (f : σ → σ) : (liftM (modify (m := m) f) : n _) = modify f := rfl

@[simp] theorem liftM_modifyGet {m n} [MonadStateOf σ m] [MonadLift m n]
    (f : σ → α × σ) : (liftM (modifyGet (m := m) f) : n _) = modifyGet f := rfl

@[simp] theorem liftM_getModify {m n} [MonadStateOf σ m] [MonadLift m n]
    (f : σ → σ) : (liftM (getModify (m := m) f) : n _) = getModify f := rfl

end MonadLift

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

namespace EStateM

open Backtrackable

variable {ε σ α β : Type _}

@[simp] lemma run_pure (x : α) :
    (pure x : EStateM ε σ α).run s = EStateM.Result.ok x s := rfl

@[simp] lemma run'_pure (x : α) :
    (pure x : EStateM ε σ α).run' s = some x := rfl

@[simp] lemma run_bind (x : EStateM ε σ α) (f : α → EStateM ε σ β) :
    (x >>= f).run s = match x.run s with
    | .ok a s => (f a).run s
    | .error e s => .error e s := rfl

@[simp] lemma run'_bind (x : EStateM ε σ α) (f : α → EStateM ε σ β) :
    (x >>= f).run' s = match x.run s with
    | .ok a s => (f a).run' s
    | .error _ _ => none := by
  rw [run', run_bind]
  match x.run s with | .ok _ _ => rfl | .error _ _ => rfl

-- run_map already exists

@[simp] lemma run'_map (f : α → β) (x : EStateM ε σ α) :
    (f <$> x).run' s = Option.map f (x.run' s) := by
  rw [run', run', run_map]
  match x.run s with | .ok _ _ => rfl | .error _ _ => rfl

@[simp] lemma run_seq (f : EStateM ε σ (α → β)) (x : EStateM ε σ α) :
    (f <*> x).run s = match f.run s with
    | .ok g s => EStateM.Result.map g (x.run s)
    | .error e s => .error e s := by
  simp only [seq_eq_bind, run_bind, run_map]
  match f.run s with | .ok _ _ => rfl | .error _ _ => rfl

@[simp] lemma run'_seq (f : EStateM ε σ (α → β)) (x : EStateM ε σ α) :
    (f <*> x).run' s = match f.run s with
    | .ok g s => Option.map g (x.run' s)
    | .error _ _ => none := by
  simp only [seq_eq_bind, run'_bind, run'_map]
  match f.run s with | .ok _ _ => rfl | .error _ _ => rfl

@[simp] lemma run_seqLeft (x : EStateM ε σ α) (y : EStateM ε σ β) :
    (x <* y).run s = match x.run s with
    | .ok v s => Result.map (fun _ => v) (y.run s)
    | .error e s => .error e s := by
  simp [seqLeft_eq_bind]

@[simp] lemma run'_seqLeft (x : EStateM ε σ α) (y : EStateM ε σ β) :
    (x <* y).run' s = match x.run s with
    | .ok v s => Option.map (fun _ => v) (y.run' s)
    | .error _ _ => none := by
  simp [seqLeft_eq_bind]

@[simp] lemma run_seqRight (x : EStateM ε σ α) (y : EStateM ε σ β) :
    (x *> y).run s = match x.run s with
    | .ok _ s => y.run s
    | .error e s => .error e s := rfl

@[simp] lemma run'_seqRight (x : EStateM ε σ α) (y : EStateM ε σ β) :
    (x *> y).run' s = match x.run s with
    | .ok _ s => y.run' s
    | .error _ _ => none := by
  rw [run', run_seqRight]
  match x.run s with | .ok _ _ => rfl | .error _ _ => rfl

@[simp] lemma run_get :
    (get : EStateM ε σ σ).run s = EStateM.Result.ok s s := rfl

@[simp] lemma run'_get :
    (get : EStateM ε σ σ).run' s = some s := rfl

@[simp] lemma run_set (v : σ) :
    (set v : EStateM ε σ PUnit).run s = EStateM.Result.ok PUnit.unit v := rfl

@[simp] lemma run'_set (v : σ) :
    (set v : EStateM ε σ PUnit).run' s = some PUnit.unit := rfl

@[simp] lemma run_modify (f : σ → σ) :
    (modify f : EStateM ε σ PUnit).run s = EStateM.Result.ok PUnit.unit (f s) := rfl

@[simp] lemma run'_modify (f : σ → σ) :
    (modify f : EStateM ε σ PUnit).run' s = some PUnit.unit := rfl

@[simp] lemma run_modifyGet (f : σ → α × σ) :
    (modifyGet f : EStateM ε σ α).run s = EStateM.Result.ok (f s).1 (f s).2 := rfl

@[simp] lemma run'_modifyGet (f : σ → α × σ) :
    (modifyGet f : EStateM ε σ α).run' s = some (f s).1 := rfl

@[simp] lemma run_getModify (f : σ → σ) :
    (getModify f : EStateM ε σ σ).run s = EStateM.Result.ok s (f s) := rfl

@[simp] lemma run'_getModify (f : σ → σ) :
    (getModify f : EStateM ε σ σ).run' s = some s := rfl

@[simp] lemma run_throw (e : ε) :
    (throw e : EStateM ε σ α).run s = EStateM.Result.error e s := rfl

@[simp] lemma run'_throw (e : ε) :
    (throw e : EStateM ε σ α).run' s = none := rfl

@[simp] lemma run_orElse {δ} [h : Backtrackable δ σ] (x₁ x₂ : EStateM ε σ α) :
    (x₁ <|> x₂).run s = match x₁.run s with
    | .ok x s => .ok x s
    | .error _ s' => x₂.run (restore s' (save s)) := by
  show (EStateM.orElse _ _).run _ = _
  unfold EStateM.orElse
  simp only [EStateM.run]
  match x₁ s with | .ok _ _ => rfl | .error _ _ => simp

@[simp] lemma run'_orElse {δ} [h : Backtrackable δ σ] (x₁ x₂ : EStateM ε σ α) :
    (x₁ <|> x₂).run' s = match x₁.run s with
    | .ok x _ => some x
    | .error _ s' => x₂.run' (restore s' (save s)) := by
  rw [run', run_orElse]
  match x₁.run s with | .ok _ _ =>  rfl | .error _ s' => rfl

@[simp] lemma run_tryCatch {δ} [h : Backtrackable δ σ]
    (body : EStateM ε σ α) (handler : ε → EStateM ε σ α) :
    (tryCatch body handler).run s = match body.run s with
    | .ok x s => .ok x s
    | .error e s' => (handler e).run (restore s' (save s)) := by
  show (EStateM.tryCatch _ _).run _ = _
  unfold EStateM.tryCatch
  simp only [EStateM.run]
  match body s with | .ok _ _ => rfl | .error _ _ => rfl

@[simp] lemma run'_tryCatch {δ} [h : Backtrackable δ σ]
    (body : EStateM ε σ α) (handler : ε → EStateM ε σ α) :
    (tryCatch body handler).run' s = match body.run s with
    | .ok x _ => some x
    | .error e s' => (handler e).run' (restore s' (save s)) := by
  rw [run', run_tryCatch]
  match body.run s with | .ok _ _ =>  rfl | .error _ s' => rfl

@[simp] lemma run_adaptExcept (f : ε → ε) (x : EStateM ε σ α) :
    (adaptExcept f x).run s = match x.run s with
    | .ok x s => .ok x s
    | .error e s => .error (f e) s := by
  show (EStateM.adaptExcept _ _).run _ = _
  unfold EStateM.adaptExcept
  simp only [EStateM.run]
  match x s with | .ok _ _ => rfl | .error _ _ => rfl

@[simp] lemma run'_adaptExcept (f : ε → ε) (x : EStateM ε σ α) :
    (adaptExcept f x).run' s = x.run' s := by
  rw [run', run', run_adaptExcept]
  match x.run s with | .ok v s => rfl | .error _ _ => rfl

end EStateM

end toBatteries
