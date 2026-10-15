import SP1Clean.Soundness.HostBankCPUReplay
import SP1Clean.Soundness.HostHintReadExecutionPath

/-! # Final commitment banks of the actual local execution

Both physical bank histories agree with the same paired replay already constructed from the
mixed AIR. No bank/CPU order, successful execution, or final-bank equality is a caller premise.
This strengthens the installed source-hint theorem; complete outgoing snapshot and Exit binding,
WRITE/VERIFY installation, and constructive completeness remain separate obligations.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance bankAgreementLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance bankAgreementClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

/-- Any replay of the carrier's actual tape ends in the two authenticated bank vectors. -/
theorem GroundingCarrier.final_banks (valid : image.Valid)
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) (target : ExecutionState)
    (replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target) :
    target.host.committed = bankFinal.committed ∧ target.host.deferred = bankFinal.deferred := by
  have agrees (deferred : Bool) := HostBankCPUReplay.replay_bank deferred witness constraints balanced
    carrier.exhaustive carrier.cpuWalk ⟨{ readOnly := image.readOnly }, p⟩ rfl
    (image.toGuestProgram valid) target replay
  exact ⟨agrees false, agrees true⟩

/-- Raw installed AIR proves one local path with final PC, clock, Memory frontier and both banks.
Nonzero sources and repeated overwrites are preserved without resetting state at shard cuts. -/
theorem source_execution_with_banks (valid : image.Valid)
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ events target, ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events target ∧
      events.Perm ((LocalCore.executionRows
        (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map ExecutionRow.event) ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? LeanRV64D.Defs.Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) ∧
      (∀ loc message, LocalCore.memoryFinalFrontier
          (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc = some message →
        locContent target.sail loc = some (Word.toBitVec64 message.value)) ∧
      target.host.committed = bankFinal.committed ∧ target.host.deferred = bankFinal.deferred := by
  obtain ⟨carrier⟩ := source_grounding_carrier valid witness constraints balanced
  obtain ⟨target, path, clock, pc, memory⟩ := carrier.execution valid constraints balanced
  exact ⟨carrier.events, target, path, carrier.exhaustive.map ExecutionRow.event, clock, pc, memory,
    carrier.final_banks valid constraints balanced target path.replay⟩

end SP1Clean.Soundness.HostHintReadCPU
