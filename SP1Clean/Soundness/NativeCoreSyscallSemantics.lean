import SP1Clean.Soundness.NativeCoreTrajectory
import SP1Clean.Soundness.SyscallInputs

/-! # Semantic syscall events in the native core

The combined AIR's syscall component, finished Byte/Program ledgers, and incoming Memory currency
derive the complete row law and source observations. Grounding's step fact then supplies the target
observations on the carrier's own trajectory, yielding an `EventStep` for the chosen host.

This is a post-grounding bridge. It does not prove the host step/frame facts, enforce the selected
full syscall codes, or model host RAM writes. Those remain required before unconditional native
boot-to-HALT soundness can be claimed.
-/

namespace SP1Clean.Soundness.NativeCore

open LeanRV64D.Defs Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core
open SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance syscallSemantics_fact24 : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance syscallSemantics_fact17 : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem syscall_member {image : ProgramImage}
    {witness : EnsembleWitness (ensemble (p := p) image)} {row : SyscallInstrsChip.Inputs (ZMod p)}
    (member : ExecutionRow.syscall row ∈ executionRows witness) :
    ∃ physical ∈ (systemTable witness 3).table,
      syscallInstrsRow witness.data physical = row ∧ row.is_real = 1 := by
  have active : row ∈ activeSystemRows (systemTable witness 3) (syscallInstrsRow witness.data) (·.is_real) := by
    simpa [executionRows] using member
  obtain ⟨mapped, real⟩ := List.mem_filter.mp active
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  exact ⟨physical, physicalMem, rfl, of_decide_eq_true real⟩

/-- Every active syscall has the native chip contract and bounded operand words, once its incoming
Memory records are grounded. The caller supplies no chip assumptions or Program facts. -/
theorem syscallRows_contract {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : SyscallInstrsChip.Inputs (ZMod p)} (member : ExecutionRow.syscall row ∈ executionRows witness)
    (currency : ∀ mp ∈ (syscallRowFacts row).memPulls, MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1) :
    SyscallInstrsChip.Spec row ∧ SyscallInstrsChip.PulledFacts row := by
  obtain ⟨physical, physicalMem, rfl, _⟩ := syscall_member member
  have finished := (finishedChannel_guarantees image witness constraints balanced).2 _ (systemTable_mem witness 3)
  exact syscallInstrsRow_contract_of_component _ witness.data (systemTable_component witness 3)
    (systemTable_constraints witness constraints 3) finished.1 finished.2 physicalMem currency

/-- Row-local AIR semantics for every active syscall, including a PC increment across a 16-bit
limb boundary. Code-profile restrictions and host effects are separate from this row law. -/
theorem syscallRows_rowLaw {image : ProgramImage}
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : SyscallInstrsChip.Inputs (ZMod p)} (member : ExecutionRow.syscall row ∈ executionRows witness)
    (currency : ∀ mp ∈ (syscallRowFacts row).memPulls, MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1) :
    (syscallEventOfRow row).RowLaw := by
  obtain ⟨spec, pulled⟩ := syscallRows_contract witness constraints balanced member currency
  obtain ⟨_, _, _, real⟩ := syscall_member member
  exact rowLaw_of_spec_and_pulledFacts row spec spec.selectorsValid pulled real

/-- The native Program ledger and incoming Memory values authenticate an active syscall's source. -/
theorem syscallRows_sourceValues {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : SyscallInstrsChip.Inputs (ZMod p)} (member : ExecutionRow.syscall row ∈ executionRows witness)
    {traj : Trajectory} {initial source : SailState} {tl : Timeline} {n : ℕ}
    (atSource : traj n = some source)
    (pc : source.regs.get? Register.PC = some (StateMsg.pcBits (syscallRowFacts row).statePull))
    (time : StateMsg.timeNat (syscallRowFacts row).statePull = tl.start n)
    (currency : ∀ mp ∈ (syscallRowFacts row).memPulls,
      LocalValueAtG traj initial tl (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    Machine.AboutToExecuteEcall (image.toGuestProgram valid) source ∧
      source.regs.get? Register.PC = some (syscallEventOfRow row).pc ∧
      source.get_reg? 5#5 = some (syscallEventOfRow row).rawCode ∧
      source.get_reg? 10#5 = some (syscallEventOfRow row).arg1 ∧
      source.get_reg? 11#5 = some (syscallEventOfRow row).arg2 := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := syscall_member member
  exact syscallRow_sourceValues _ _
    (syscall_program_committed valid witness constraints balanced physicalMem real)
    atSource pc time currency

private theorem syscall_returnCoordinates_of_facts (row : SyscallInstrsChip.Inputs (ZMod p))
    (program : Target.GuestProgram)
    (committed : Target.committedInROM program (rowOfMsg (SyscallInstrsChip.programMessage row)))
    (clock : ((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ row.state.clk_16_24.val < 2 ^ 8) :
    Semantics.MemoryMsg.locOf (SyscallInstrsChip.memPushedMessage row row.op_a 4 row.op_a_value) = MemLoc.reg 5#5 ∧
      Semantics.MemoryMsg.timeNat (SyscallInstrsChip.memPushedMessage row row.op_a 4 row.op_a_value) =
        StateMsg.timeNat (syscallRowFacts row).statePull + 4 := by
  have opA : row.op_a = 5 :=
    congrArg (fun r : ProgramChip.ProgramRow (ZMod p) => r.op_a) (committed.ecall_of_opcode rfl).2
  exact ⟨(syscallRow_locOf_reg row (i := 5#5) opA.symm row.op_a_memory row.op_a_value 4).2,
    (syscallRow_memPush_time row clock.1 clock.2 row.op_a row.op_a_value 4 (by norm_num) 4 rfl).1⟩

private theorem syscall_returnCoordinates {image : ProgramImage} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : SyscallInstrsChip.Inputs (ZMod p)} (member : ExecutionRow.syscall row ∈ executionRows witness) :
    Semantics.MemoryMsg.locOf (SyscallInstrsChip.memPushedMessage row row.op_a 4 row.op_a_value) = MemLoc.reg 5#5 ∧
      Semantics.MemoryMsg.timeNat (SyscallInstrsChip.memPushedMessage row row.op_a 4 row.op_a_value) =
        StateMsg.timeNat (syscallRowFacts row).statePull + 4 := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := syscall_member member
  have committed := syscall_program_committed valid witness constraints balanced physicalMem real
  have clock := syscallInstrsRow_cpuState_bounds_of_component _ witness.data (systemTable_component witness 3)
    ((finishedChannel_guarantees image witness constraints balanced).2 _ (systemTable_mem witness 3)).1 physicalMem real
  exact syscall_returnCoordinates_of_facts _ _ committed clock

/-- Incoming currency and the host step fact yield an actual syscall transition on the constructed
trajectory. AIR laws, committed ECALL, register observations, and event position are all derived. -/
theorem GroundingCarrier.syscall_eventStep_of_currency {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (handler : Machine.ExecutableSyscallHandler) {row : SyscallInstrsChip.Inputs (ZMod p)}
    (member : ExecutionRow.syscall row ∈ executionRows witness)
    (state : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid handler)
      carrier.timeline (syscallRowFacts row).statePull)
    (currency : ∀ mp ∈ (syscallRowFacts row).memPulls, MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid handler) image.initialSailState carrier.timeline
        (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    (step : LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid handler)
      image.initialSailState carrier.timeline (syscallRowFacts row)) :
    ∃ n source target, carrier.trajectory valid handler n = some source ∧
      StateMsg.timeNat (syscallRowFacts row).statePull = carrier.timeline.start n ∧
      carrier.trajectory valid handler (n + 1) = some target ∧
      Machine.EventStep handler.withHalt.relation (image.toGuestProgram valid)
        source (.syscall (syscallEventOfRow row)) target := by
  have advanced := step state currency
  obtain ⟨n, source, atSource, time, pc, _⟩ := state
  have law := syscallRows_rowLaw witness constraints balanced member (fun mp mem =>
    ⟨(currency mp mem).1, (currency mp mem).2.1⟩)
  have observations := syscallRows_sourceValues valid witness constraints balanced member atSource pc time
    (fun mp mem => (currency mp mem).2.2)
  obtain ⟨⟨k, target, atTarget, targetTime, targetPc, _⟩, pushes⟩ := advanced
  have same : k = n + 1 := start_injective carrier.timeline
    (targetTime.symm.trans (carrier.originalTimeStep member n time))
  subst k
  obtain ⟨location, writeTime⟩ := syscall_returnCoordinates valid witness constraints balanced member
  have returned := (pushes (SyscallInstrsChip.memPushedMessage row row.op_a 4 row.op_a_value)
    (by rw [syscallRowFacts_memPushes]; exact List.mem_cons_self)).2.2
  change microValueG _ _ _ _ _ = some (Word.toBitVec64 row.op_a_value) at returned
  have gap := carrier.timeline.gap n
  rw [location, writeTime, time,
    microValueG_reg_post (n := n) le_rfl (by omega), atTarget, Option.bind_some] at returned
  have run := atTarget
  rw [carrier.trajectory_syscall valid handler member time, atSource, Option.bind_some] at run
  exact ⟨n, source, target, atSource, time, atTarget, .syscall observations.1
    ⟨law, ⟨observations.2.1, observations.2.2.1, observations.2.2.2.1,
      observations.2.2.2.2, targetPc, returned⟩, run⟩⟩

/-- Every active syscall in a grounded carrier is a semantic event for the chosen host.
The only row-specific premise left is that host's step fact; alignment, source currency,
row semantics, and both endpoint observations are recovered internally. -/
theorem GroundingCarrier.syscall_eventStep_of_grounded {image : ProgramImage} (valid : image.Valid)
    {witness : EnsembleWitness (ensemble (p := p) image)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (handler : Machine.ExecutableSyscallHandler)
    (grounded : ∀ row ∈ carrier.rows, GroundedG (image.toGuestProgram valid)
      (carrier.trajectory valid handler) image.initialSailState carrier.timeline row)
    {row : SyscallInstrsChip.Inputs (ZMod p)} (member : ExecutionRow.syscall row ∈ executionRows witness)
    (step : LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid handler)
      image.initialSailState carrier.timeline (syscallRowFacts row)) :
    ∃ n source target, carrier.trajectory valid handler n = some source ∧
      StateMsg.timeNat (syscallRowFacts row).statePull = carrier.timeline.start n ∧
      carrier.trajectory valid handler (n + 1) = some target ∧
      Machine.EventStep handler.withHalt.relation (image.toGuestProgram valid)
        source (.syscall (syscallEventOfRow row)) target := by
  have originalMem := List.mem_map_of_mem (f := ExecutionRow.facts witness.data)
    (carrier.exhaustive.mem_iff.mpr member)
  obtain ⟨alignedRow, alignedMem, aligned⟩ := forall₂_exists_right carrier.aligned.flip _ originalMem
  have facts := grounded alignedRow alignedMem
  exact carrier.syscall_eventStep_of_currency valid constraints balanced handler member
    (localStateTruthG_congr aligned.pullTime.symm aligned.pullPc.symm facts.1)
    (aligned.pullCurrency facts.1 (fun mp mem =>
      ⟨(facts.2 mp mem).1.1, (facts.2 mp mem).1.2.1, (facts.2 mp mem).2⟩)) step

end SP1Clean.Soundness.NativeCore
