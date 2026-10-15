import SP1Clean.Model.Core.SourceExecution
import SP1Clean.Model.Core.ExecutionWritePolicy
import SP1Clean.Model.Core.ExecutionEncoding
import SP1Clean.Model.Core.ExecutionResources

/-! # Complete-state semantics for the native shard capstone

This contract reuses the existing execution path and finite snapshots. It neither evaluates a
second machine nor replaces the official Sail step. All eight concrete host calls are part of
`ExecutionPath`. A shard may start at any checked local source, continue, halt, or be empty.
Padding and ledger administration are absent from the semantic event tape.

`Executes` is the semantic spine, including the ordinary write-byte policy and before resource
restrictions. The policy observes each actual replayed source, so same-value ROM writes are
excluded independently of circuit or compiler success. `nativeProfile` fixes encoding conditions
and semantic resource measurements from data-only numeric limits. Physical capacity proofs and
complete boundary/host installation remain separate implementation obligations; this contract
contains no compiler readiness or supplied grounding certificate.
See `Soundness/Shard/Contract` for the two end-to-end targets.
-/

namespace SP1Clean.FormalModel.Shard

open Model.Core Machine

/-- Native host policy uses the AIR characteristic and the checked image's protected ROM bytes. -/
def policy (characteristic : ℕ) (image : ProgramImage) : HostPolicy :=
  ⟨{ readOnly := image.readOnly }, characteristic⟩

/-- One permitted local execution, including literal equality with the complete outgoing realization.
Ordinary write permission is mandatory independently of the remaining resource profile. -/
def Executes (characteristic : ℕ) (image : ProgramImage)
    (source target : ExecutionSnapshot) (events : List ExecutionEvent) : Prop :=
  ∃ valid : ExecutionSourceValid image source,
    ExecutionPath (policy characteristic image) (image.toGuestProgram valid.1.1)
      source.realize events target.realize ∧
    ExecutionPath.WritesPermitted (policy characteristic image) (image.toGuestProgram valid.1.1)
      source.realize events

/-- Fixed native resource domain over the existing complete replay. The image proof selects the
same committed program as `Executes`; it supplies no row or compiler evidence. -/
noncomputable def nativeProfile (limits : ResourceLimits) (characteristic : ℕ) (image : ProgramImage)
    (source target : ExecutionSnapshot) (events : List ExecutionEvent) : Prop :=
  ∃ valid : image.Valid,
    ExecutionPath.Encoded (policy characteristic image) (image.toGuestProgram valid) source.realize events ∧
    (executionResources (policy characteristic image) (image.toGuestProgram valid)
      source.realize events).Fits limits ∧
    source.realize.resources.Fits limits ∧ target.realize.resources.Fits limits ∧
    target.clock < NativeLayout.clocks.upper ∧ target.pc.toNat < NativeLayout.guestMemory.upper

/-- Both capstone directions use this one fixed domain, indexed only by numeric instance data. -/
noncomputable def AdmissibleExecution (limits : ResourceLimits) (characteristic : ℕ) (image : ProgramImage)
    (source target : ExecutionSnapshot) (events : List ExecutionEvent) : Prop :=
  Executes characteristic image source target events ∧
    nativeProfile limits characteristic image source target events

namespace Executes

variable {characteristic : ℕ} {image : ProgramImage}
  {source left right target : ExecutionSnapshot} {first second : List ExecutionEvent}

/-- Empty shards preserve the entire state, including stopped hosts and untouched memory. -/
theorem nil_iff : Executes characteristic image source target [] ↔
    ExecutionSourceValid image source ∧ source.equivalent target = true := by
  constructor
  · rintro ⟨valid, path, _⟩
    exact ⟨valid, (ExecutionSnapshot.equivalent_iff _ _).mpr
      (ExecutionPath.nil_iff.mp path).symm⟩
  · rintro ⟨valid, same⟩
    exact ⟨valid, ExecutionPath.nil_iff.mpr
      ((ExecutionSnapshot.equivalent_iff _ _).mp same).symm, ExecutionPath.writesPermitted_nil⟩

/-- Semantic composition uses the executable full-boundary comparison. Resource limits are
intentionally separate: two legal shards need not fit in a single shard. -/
theorem append (firstPath : Executes characteristic image source left first)
    (secondPath : Executes characteristic image right target second)
    (same : left.equivalent right = true) :
    Executes characteristic image source target (first ++ second) := by
  obtain ⟨sourceValid, firstPath, firstPermission⟩ := firstPath
  obtain ⟨_, secondPath, secondPermission⟩ := secondPath
  rw [← (ExecutionSnapshot.equivalent_iff _ _).mp same] at secondPath secondPermission
  exact ⟨sourceValid, firstPath.append secondPath, firstPermission.append secondPermission firstPath⟩

/-- Event duration, rather than padding or table height, determines the endpoint clock. -/
theorem clock (execution : Executes characteristic image source target first) :
    target.clock = source.clock + (first.map ExecutionEvent.duration).sum :=
  execution.2.1.clock

/-- A stopped incoming host admits only an identity execution. -/
theorem of_halted (execution : Executes characteristic image source target first)
    (halted : source.host.exitCode ≠ none) :
    first = [] ∧ source.equivalent target = true := by
  obtain ⟨empty, same⟩ := execution.2.1.of_halted halted
  exact ⟨empty, (ExecutionSnapshot.equivalent_iff _ _).mpr same.symm⟩

end Executes

end SP1Clean.FormalModel.Shard
