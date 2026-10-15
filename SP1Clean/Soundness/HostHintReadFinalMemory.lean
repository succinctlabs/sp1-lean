import SP1Clean.Soundness.HostHintReadHostAgreement
import SP1Clean.Soundness.HostHintReadBookkeeping
import SP1Clean.Soundness.HostHintReadExit
import SP1Clean.Soundness.HostHintReadTerminalAgreement
import SP1Clean.Soundness.CoreMemoryFrame

/-! # Complete native Memory observations at the outgoing boundary

The physical final inventory covers every actual instruction and host RAM access. At locations
without a final record, the original event frames preserve the complete source value. Thus the
same execution has a value at every native register/RAM location, with no touched-location or
frame premise supplied by the caller. Byte permissions and replay also exclude all out-of-window
entries. Runtime output/cycles and registers outside the instruction bookkeeping footprint are
also preserved. The semantic tape determines all three retirement/nextPC slots, and every newly
halted endpoint has the public Exit value. The actual optional terminal status agrees with the
verifier's supplied endpoint. Complete supplied-snapshot equality remains open.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding
open LeanRV64D.Defs (Register)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance finalMemoryLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance finalMemoryLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem no_push_of_empty {α : Type*} (events : List α) (facts : α → RowFacts p)
    (loc : MemLoc) (empty : pushesAt (events.map facts) loc = 0) :
    ∀ event ∈ events, ∀ message ∈ (facts event).memPushes, MemoryMsg.locOf message ≠ loc := by
  intro event member message pushed same
  have present : message ∈ pushesAt (events.map facts) loc :=
    mem_pushesAt.mpr ⟨_, List.mem_map_of_mem member, pushed, same⟩
  rw [empty] at present
  exact Multiset.notMem_zero _ present

/-- A missing physical final record means no active event pushes this location. Strict
chronology excludes hidden cycles, including cycles containing physical refresh rows. -/
theorem source_no_push_of_final_none (valid : image.Valid)
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (loc : MemLoc)
    (absent : LocalCore.memoryFinalFrontier
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc = none) :
    ∀ event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)),
      ∀ message ∈ (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).memPushes,
        MemoryMsg.locOf message ≠ loc := by
  obtain ⟨ordered, rows, _, _, _, chronology, projection⟩ :=
    source_ordered_memory_rows valid witness constraints balanced
  have empty := pushesAt_zero_of_final_none rows _ _ _ _ chronology.rowOK
    (fun row member pull pullMem => (chronology.priorBounds row member pull pullMem).1)
    (frontier_balance witness constraints balanced rows projection)
    (fun pair member => congrArg Prod.fst (LocalCore.memoryRefreshes_preserve _ pair member))
    chronology.refreshOrder loc absent
  rw [(projection loc).1] at empty
  exact no_push_of_empty _ _ loc empty

/-- The source value survives at every location omitted by the physical final frontier. -/
theorem GroundingCarrier.untouched_memory (valid : image.Valid)
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (target : ExecutionState)
    (replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target)
    (loc : MemLoc) (value : BitVec 64) (content : locContent source.sail.realize loc = some value)
    (absent : LocalCore.memoryFinalFrontier
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc = none) :
    locContent target.sail loc = some value := by
  have grounded := carrier.ground valid constraints balanced
  have current := grounded.1
  have start : LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline loc
      (StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput)) (Target.bitVecToWord (p := p) value) := by
    rw [← carrier.timeline_start, localValueAtG_stepStart_iff (carrier.trajectory_zero valid),
      Target.toBitVec64_bitVecToWord]
    exact content
  have preserved := carrier.frame_of_no_push current (fun event member => by
    cases event with
    | instruction row => exact (carrier.instruction_engineFacts valid constraints balanced member).2
    | syscall row => exact (carrier.syscall_engineFacts valid constraints balanced member).2
    | halt row => exact (carrier.halt_engineFacts valid constraints balanced member).2)
    loc (Target.bitVecToWord (p := p) value) (source_no_push_of_final_none valid witness constraints balanced loc absent) start
  have atEnd : carrier.trajectory valid carrier.events.length = some target.sail := by
    simp only [GroundingCarrier.trajectory, GroundingCarrier.pairedTrajectory,
      ExecutionCarrier.pairedTrajectory, executionTrajectory, List.take_length, replay, Option.map_some]
  rw [← carrier.finalClock, ← carrier.events_length,
    localValueAtG_stepStart_iff atEnd, Target.toBitVec64_bitVecToWord] at preserved
  exact preserved

/-- Every register and every native RAM cell has its exact final value. Locations absent from
the final inventory retain their source value, including RAM below the register-reserved window. -/
theorem GroundingCarrier.final_memory (valid : image.Valid)
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (target : ExecutionState)
    (replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target)
    (loc : MemLoc) (bound : loc.busAddress < 2 ^ 48) :
    locContent target.sail loc = some
      (match LocalCore.memoryFinalFrontier
          (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc with
        | some message => Word.toBitVec64 message.value
        | none => source.sail.memorySnapshot.read loc) := by
  cases present : LocalCore.memoryFinalFrontier
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc with
  | some message =>
      have value := (carrier.ground valid constraints balanced).2.2 loc message present
      have atEnd : carrier.trajectory valid carrier.events.length = some target.sail := by
        simp only [GroundingCarrier.trajectory, GroundingCarrier.pairedTrajectory,
          ExecutionCarrier.pairedTrajectory, executionTrajectory, List.take_length, replay, Option.map_some]
      rw [← carrier.finalClock, ← carrier.events_length] at value
      exact (localValueAtG_stepStart_iff atEnd).mp value
  | none =>
      have ordering := HostHintQueueBoundary.projected_orderingChannels witness
        (source_interface source.host.io.hints) constraints balanced
      have sourceValid := (LocalCore.public_contract_of_byte _ ordering.sourceChecks ordering.verifierByte).2.1
      exact carrier.untouched_memory valid constraints balanced target replay loc _
        (sourceValid.memory.locContent_of_address_lt loc bound) present

/-- The finite source has no out-of-window entries, and every actual event preserves their absence. -/
theorem GroundingCarrier.final_memory_domain (valid : image.Valid)
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {target : ExecutionState}
    (replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target) (address : ℕ) (outside : 2 ^ 48 ≤ address) :
    target.sail.mem.get? address = none := by
  rw [carrier.memory_outside valid constraints balanced replay address outside]
  exact (source.sail.memory.toSailMemory_get? (2 ^ 48) address).trans (if_neg (by omega))


end SP1Clean.Soundness.HostHintReadCPU
