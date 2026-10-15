import SP1Clean.FormalModel.ShardAccess
import SP1Clean.Proofs.Completeness.InstructionEvent

/-! # Canonical ordinary compilation from the complete shard semantics

Every ordinary occurrence in an admissible mixed path compiles through the existing transition
view, access extractor and refresh-aware scheduler. The only extra input is the compiler's running
frontier. Its invariant is preserved for the next row, rather than becoming a capstone premise.
This removes extractor readiness. The five R-type adapter tables also have derived event validity
below; the remaining families and full mixed-table assembly remain separate compiler obligations.
-/

namespace SP1Clean.TraceGen
open Model.Core Machine Semantics FormalModel.Shard

/-- The existing compiler succeeds at every actual ordinary occurrence. Its output retains the
canonical plan, ordered timestamps, valid refreshes and the next frontier invariant. -/
theorem admissibleExecution_compile_at {limits : ResourceLimits} {characteristic : ℕ}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits characteristic image source target events)
    {cut : ℕ} (ordinary : events[cut]? = some .ordinary) (frontier : AccessFrontier) :
    ∃ current next view result,
      executionTrajectory (policy characteristic image) (image.toGuestProgram execution.1.1.1.1)
        source.realize events cut = some current ∧
      ExecutionStep (policy characteristic image) (image.toGuestProgram execution.1.1.1.1) current .ordinary next ∧
      projectSP1Transition? (image.toGuestProgram execution.1.1.1.1)
        ⟨current.sail, ⟨.ordinary, next.sail⟩⟩ = some view ∧
      compileInstructionEvent? view frontier current.clock = some result ∧
      result.plan.WellFormed ∧ result.plan.length ≤ 3 ∧
      (frontier.BoundedAt current.clock →
        (∀ touch ∈ result.stamped, touch.previous < touch.current current.clock) ∧
        (∀ bump ∈ result.memoryBumps, bump.WellFormed) ∧
        result.nextFrontier.BoundedAt (current.clock + ordinaryClkInc)) := by
  obtain ⟨current, next, view, plan, replay, step, projected, accesses, wellFormed, length⟩ :=
    execution.project_at ordinary
  obtain ⟨result, generated⟩ := instructionEventReady_iff.mp
    (instructionEventReady_of_projection projected accesses frontier current.clock)
  have same : result.plan = plan := Option.some.inj
    ((compileInstructionEvent?_accessPlan generated).symm.trans accesses)
  have resultWellFormed : result.plan.WellFormed := same ▸ wellFormed
  refine ⟨current, next, view, result, replay, step, projected, generated, resultWellFormed,
    same ▸ length, ?_⟩
  intro bounded
  have phase := (execution.2.choose_spec.1 cut current .ordinary ordinary replay).1
  have clock := execution.1.2.1.clock_at ordinary replay
  have final := execution.2.choose_spec.2.2.2.2.1
  have currentLt : current.clock + 1 < 2 ^ 48 := by
    change current.clock + 8 ≤ target.clock at clock
    change target.clock < 2 ^ 48 at final
    omega
  exact ⟨compileInstructionEvent?_timestamps generated resultWellFormed bounded,
    compileInstructionEvent?_memoryBumps_wellFormed generated resultWellFormed bounded phase currentLt,
    compileInstructionEvent?_frontier_bounded_next generated bounded⟩

/-- At every actual ordinary occurrence, the five R-type adapter tables already receive valid
compiler events. The clock phase is obtained from the fixed native profile, PC bounds from the
committed ROM, and operand/timestamp facts from the shared extractor and scheduler. This staged
result leaves the semantic domain unchanged and makes no all-instruction completeness claim. -/
theorem admissibleExecution_compile_at_rtype_valid
    {limits : ResourceLimits} {characteristic : ℕ}
    {image : ProgramImage} {source target : ExecutionSnapshot} {events : List ExecutionEvent}
    (execution : AdmissibleExecution limits characteristic image source target events)
    {cut : ℕ} (ordinary : events[cut]? = some .ordinary) (frontier : AccessFrontier) :
    ∃ current next view result,
      executionTrajectory (policy characteristic image) (image.toGuestProgram execution.1.1.1.1)
        source.realize events cut = some current ∧
      ExecutionStep (policy characteristic image) (image.toGuestProgram execution.1.1.1.1)
        current .ordinary next ∧
      projectSP1Transition? (image.toGuestProgram execution.1.1.1.1)
        ⟨current.sail, ⟨.ordinary, next.sail⟩⟩ = some view ∧
      compileInstructionEvent? view frontier current.clock = some result ∧
      (frontier.BoundedAt current.clock →
        view.chipId ∈ [.add, .sub, .subw, .mul, .divRem] →
        result.routed.id.Valid result.routed.event) := by
  obtain ⟨current, next, view, result, replay, step, projected, generated, _⟩ :=
    admissibleExecution_compile_at execution ordinary frontier
  refine ⟨current, next, view, result, replay, step, projected, generated, ?_⟩
  intro bounded family
  have phase := (execution.2.choose_spec.1 cut current .ordinary ordinary replay).1
  exact compileInstructionEvent?_rtype_valid projected generated family phase bounded

end SP1Clean.TraceGen
