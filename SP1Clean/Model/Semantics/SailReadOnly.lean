import SP1Clean.Model.Semantics.SailExecuteFrame

/-! # State frames for Sail reads and early returns

These partial-correctness lemmas concern the actual Sail state monad. They include early returns
from `SailME` and bounded loops; an unsuccessful underlying Sail action cannot yield a successful
composite action. No totality or memory-presence premise is needed.
-/

namespace SP1Clean.SailFrame
open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Defs
open SP1Clean.Advance SP1Clean.TryStepReduction

/-- Every successful result of this action leaves the entire input state unchanged. -/
def ReadOnlyAt {α : Type} (source : SailState) (action : SailM α) : Prop :=
  ∀ value target, action.run source = .ok value target → target = source

namespace ReadOnlyAt

/-- A known state-preserving run supplies a frame by determinism. -/
theorem of_run {α : Type} {source : SailState} {action : SailM α} {value : α}
    (ran : action.run source = .ok value source) : ReadOnlyAt source action := by
  intro other target actual
  rw [ran] at actual
  cases actual
  rfl

/-- Pure results leave the state unchanged. -/
theorem pure {α : Type} (source : SailState) (value : α) :
    ReadOnlyAt source (Pure.pure value) := of_run rfl

/-- Sequential read-only actions compose at the same source. -/
theorem bind {α β : Type} {source : SailState} {action : SailM α} {next : α → SailM β}
    (first : ReadOnlyAt source action) (rest : ∀ value, ReadOnlyAt source (next value)) :
    ReadOnlyAt source (action >>= next) := by
  intro value target ran
  obtain ⟨middle, result, step, suffix⟩ := run_bind_success _ _ source target value ran
  obtain rfl := first result middle step
  exact rest result value target suffix

/-- A known prefix result selects the only reachable continuation. -/
theorem bind_of_run {α β : Type} {source : SailState} {action : SailM α} {next : α → SailM β}
    {value : α} (ran : action.run source = .ok value source)
    (rest : ReadOnlyAt source (next value)) : ReadOnlyAt source (action >>= next) := by
  intro result target actual
  rw [run_bind_of_run source action value ran] at actual
  exact rest result target actual

/-- A known lifted result selects the reachable early-return continuation. -/
theorem bindE_of_run {α β γ : Type} {source : SailState} {action : SailM α}
    {next : α → SailME γ β} {value : α} (ran : action.run source = .ok value source)
    (rest : ReadOnlyAt source (ExceptT.run (next value))) :
    ReadOnlyAt source (ExceptT.run ((liftM action : SailME γ α) >>= next)) := by
  change ReadOnlyAt source (ExceptT.run (liftM action : SailME γ α) >>= _)
  apply bind_of_run (value := Except.ok value) ?_ rest
  change (action >>= fun value =>
    Pure.pure (Except.ok (ε := Sail.Error exception ⊕ γ) value)).run source = _
  rw [run_bind_of_run source action value ran]
  rfl

/-- An underlying Sail exception has no successful result. -/
theorem throw {α : Type} (source : SailState) (error : Sail.Error exception) :
    ReadOnlyAt source (throw error : SailM α) := by
  intro value target ran
  cases ran

/-- Lifting a read-only action into Sail's early-return monad preserves its frame. -/
theorem lift {α β : Type} {source : SailState} {action : SailM α}
    (frame : ReadOnlyAt source action) :
    ReadOnlyAt source (ExceptT.run (liftM action : SailME β α)) := by
  change ReadOnlyAt source (action >>= fun value =>
    Pure.pure (Except.ok (ε := Sail.Error exception ⊕ β) value))
  exact frame.bind fun _ => pure source _

/-- Early-return bind composes frames, including the short-circuiting branch. -/
theorem bindE {α β γ : Type} {source : SailState} {action : SailME γ α}
    {next : α → SailME γ β} (first : ReadOnlyAt source (ExceptT.run action))
    (rest : ∀ value, ReadOnlyAt source (ExceptT.run (next value))) :
    ReadOnlyAt source (ExceptT.run (action >>= next)) := by
  change ReadOnlyAt source (ExceptT.run action >>= _)
  apply first.bind
  intro result
  cases result
  · exact pure source _
  · exact rest _

/-- Eliminating the early-return layer does not introduce state changes. -/
theorem runE {α : Type} {source : SailState} {action : SailME α α}
    (frame : ReadOnlyAt source (ExceptT.run action)) :
    ReadOnlyAt source (SailME.run action) := by
  change ReadOnlyAt source (ExceptT.run action >>= _)
  apply frame.bind
  intro result
  rcases result with (error | value)
  · cases error
    · exact throw source _
    · exact pure source _
  · exact pure source _

/-- A bounded early-return loop preserves state whenever its body and condition do. -/
theorem untilE {α β : Type} (source : SailState) (fuel : ℕ) (condition : α → SailME β Bool)
    (initial : α) (body : α → SailME β α)
    (test : ∀ value, ReadOnlyAt source (ExceptT.run (condition value)))
    (step : ∀ value, ReadOnlyAt source (ExceptT.run (body value))) :
    ReadOnlyAt source (ExceptT.run (untilFuelM fuel condition initial body)) := by
  unfold untilFuelM
  induction fuel generalizing initial with
  | zero => exact pure source _
  | succ fuel ih =>
    apply (step initial).bindE
    intro value
    apply (test value).bindE
    intro done
    cases done
    · exact ih value
    · exact pure source _

end ReadOnlyAt
end SP1Clean.SailFrame
