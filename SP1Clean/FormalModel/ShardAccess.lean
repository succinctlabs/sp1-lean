import SP1Clean.FormalModel.ShardPreservation
import SP1Clean.Model.Core.ExecutionAccess

/-! # Access projection at every admissible ordinary occurrence

Both source and target of each instruction are the actual complete path states. Configuration,
ROM and byte availability are derived independently from Sail/host preservation. The conclusion
uses the same transition view and access plan consumed by the deterministic compiler.
-/

namespace SP1Clean.FormalModel.Shard
open Model.Core Machine Semantics

/-- Native admissibility preserves the exact complete byte domain at every actual cut. -/
theorem AdmissibleExecution.memory_domain_prefix {limits : ResourceLimits} {characteristic : ℕ}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits characteristic image source target events)
    {cut : ℕ} {current : ExecutionState}
    (replay : executionTrajectory (policy characteristic image) (image.toGuestProgram execution.1.1.1.1)
      source.realize events cut = some current) (address : ℕ) :
    (current.sail.mem.get? address).isSome ↔ address < NativeLayout.sailMemory.upper :=
  execution.1.2.1.memory_domain_prefix execution.1.1.1.1 execution.1.2.2 execution.2.choose_spec.1
    (fun _ selected => selected) (by rfl) execution.1.1.configured execution.1.1.romLoaded replay address

/-- Every ordinary position in the capstone domain has a successful canonical access projection. -/
theorem AdmissibleExecution.project_at {limits : ResourceLimits} {characteristic : ℕ}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits characteristic image source target events)
    {cut : ℕ} (ordinary : events[cut]? = some .ordinary) :
    ∃ current next view plan,
      executionTrajectory (policy characteristic image) (image.toGuestProgram execution.1.1.1.1)
        source.realize events cut = some current ∧
      ExecutionStep (policy characteristic image) (image.toGuestProgram execution.1.1.1.1) current .ordinary next ∧
      projectSP1Transition? (image.toGuestProgram execution.1.1.1.1)
        ⟨current.sail, ⟨.ordinary, next.sail⟩⟩ = some view ∧
      view.accessPlan? = some plan ∧ plan.WellFormed ∧ plan.length ≤ 3 := by
  obtain ⟨current, next, replay, step⟩ := execution.1.2.1.step_at ordinary
  have frame := execution.1.frame_prefix replay
  have encoded := execution.2.choose_spec.1 cut current .ordinary ordinary replay
  obtain ⟨view, plan, projected, generated, wellFormed, length⟩ :=
    step.project_ordinary frame.1 frame.2.1 (execution.1.2.2 cut current ordinary replay) (encoded.2 rfl)
      (execution.1.memory_present_prefix replay)
  exact ⟨current, next, view, plan, replay, step, projected, generated, wellFormed, length⟩

end SP1Clean.FormalModel.Shard
