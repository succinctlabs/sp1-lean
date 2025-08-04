import Lean.Language.Basic

variable {ε σ α β : Type}

theorem EStateM.run_bind (x : EStateM ε σ α) (f : α → EStateM ε σ β) (s : σ) :
    (x >>= f).run s = match x.run s with
    | .ok a s => (f a).run s
    | .error e s => .error e s := rfl

theorem EStateM.run_bind' (x : EStateM ε σ α) (f : α → EStateM ε σ β) (s : σ) :
    (x >>= f).run s = (x.run s).rec (fun a s => (f a).run s) (fun e s => .error e s) := by
  show (match x.run s with
    | .ok a s => (f a).run s
    | .error e s => .error e s) = _
  cases x.run s <;> rfl

theorem EStateM.run_pure (x : α) :
    (pure x : EStateM ε σ α).run s = EStateM.Result.ok x s := rfl

example (n : Fin _) (s : Unit) :
    EStateM.run (do
      let _ ←
        (match
          (match ((BitVec.ofNat 1 (n * 30292 : Fin 30293)))[0]'Nat.one_pos with
          | true => true
          | false => true) with
        | true => pure ()
        | false => pure () : EStateM Unit Unit Unit)
      return ()) s = EStateM.Result.ok () s := by
  rw [EStateM.run_bind] -- (kernel) deep recursion detected
  -- rw [EStateM.run_bind'] -- no errors
  -- simp [EStateM.run_bind] -- no errors

  cases (BitVec.ofNat 1 (n * _).val)[0]
  · simp only [EStateM.run_pure]
  · simp only [EStateM.run_pure]
