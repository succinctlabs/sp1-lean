import SP1Clean.FormalModel.Shard
import SP1Clean.FormalModel.Contracts.ResourceBoundary

/-! # Numeric monotonicity and composition of the fixed shard resource domain

These laws reuse the complete path and its resource observer. Append requires an explicit
combined numeric budget: two individually legal shards need not fit one shard's work ceiling.
-/

namespace SP1Clean.FormalModel.Shard
open Model.Core Machine

variable {limits larger : ResourceLimits} {characteristic : ℕ} {image : ProgramImage}
  {source left right target : ExecutionSnapshot} {events first second : List ExecutionEvent}

/-- Increasing numeric ceilings preserves the fixed semantic profile. -/
theorem nativeProfile_mono (profile : nativeProfile limits characteristic image source target events)
    (more : limits.LE larger) : nativeProfile larger characteristic image source target events := by
  obtain ⟨valid, encoded, usage, incoming, outgoing, clocks, pc⟩ := profile
  exact ⟨valid, encoded, usage.mono more, incoming.mono more, outgoing.mono more, clocks, pc⟩

theorem AdmissibleExecution.mono
    (execution : AdmissibleExecution limits characteristic image source target events)
    (more : limits.LE larger) : AdmissibleExecution larger characteristic image source target events :=
  ⟨execution.1, nativeProfile_mono execution.2 more⟩

/-- Identity shards impose only source validity and actual incoming occupancy, never a clock phase. -/
theorem admissibleExecution_identity_iff :
    AdmissibleExecution limits characteristic image source source [] ↔
      ExecutionSourceValid image source ∧ source.realize.resources.Fits limits := by
  constructor
  · rintro ⟨execution, valid, _, _, incoming, _⟩
    exact ⟨execution.1, incoming⟩
  · rintro ⟨valid, occupancy⟩
    refine ⟨⟨valid, .nil _, ExecutionPath.writesPermitted_nil⟩,
      valid.1.1, ExecutionPath.encoded_nil, ResourceUsage.zero_fits limits, occupancy, occupancy, ?_, ?_⟩
    · exact valid.2.2.1
    · exact valid.2.2.2

/-- The same tape has literal event and elapsed-clock bounds in the public domain. -/
theorem AdmissibleExecution.work
    (execution : AdmissibleExecution limits characteristic image source target events) :
    events.length ≤ limits.events ∧ target.clock - source.clock ≤ limits.ticks := by
  obtain ⟨valid, _, fits, _⟩ := execution.2
  have path := execution.1.2.1
  have count := fits .events
  have ticks := fits .ticks
  rw [path.resources_events] at count
  rw [path.resources_ticks] at ticks
  change events.length ≤ limits.events at count
  change (events.map ExecutionEvent.duration).sum ≤ limits.ticks at ticks
  rw [execution.1.clock]
  exact ⟨count, by omega⟩

/-- Every admissible path passes the concrete verifier's finite endpoint checks. -/
theorem AdmissibleExecution.boundaryBounds
    (execution : AdmissibleExecution limits characteristic image source target events) :
    ResourceBoundary.Bounds limits source target := by
  obtain ⟨_, _, _, incoming, outgoing, clocks, pc⟩ := execution.2
  rw [source.resources_realize] at incoming
  rw [target.resources_realize] at outgoing
  exact ⟨incoming, outgoing, by have := execution.1.clock; omega,
    execution.work.2, clocks, pc⟩

/-- Join complete boundaries and check the combined work/occupancy against one numeric budget. -/
theorem AdmissibleExecution.append
    (firstPath : AdmissibleExecution limits characteristic image source left first)
    (secondPath : AdmissibleExecution limits characteristic image right target second)
    (same : left.equivalent right = true)
    (combined : ∀ valid : image.Valid,
      ((executionResources (policy characteristic image) (image.toGuestProgram valid) source.realize first).combine
        (executionResources (policy characteristic image) (image.toGuestProgram valid) right.realize second)).Fits
          limits) :
    AdmissibleExecution limits characteristic image source target (first ++ second) := by
  obtain ⟨valid, firstEncoded, _, incoming, _⟩ := firstPath.2
  obtain ⟨_, secondEncoded, _, _, outgoing, clocks, pc⟩ := secondPath.2
  have sameState := (ExecutionSnapshot.equivalent_iff _ _).mp same
  have bound := combined valid
  rw [← sameState] at secondEncoded bound
  refine ⟨firstPath.1.append secondPath.1 same, valid, ?_, ?_, incoming, outgoing, clocks, pc⟩
  · exact (ExecutionPath.encoded_append_iff firstPath.1.2.1).mpr ⟨firstEncoded, secondEncoded⟩
  · rw [firstPath.1.2.1.resources_append]
    exact bound

end SP1Clean.FormalModel.Shard
