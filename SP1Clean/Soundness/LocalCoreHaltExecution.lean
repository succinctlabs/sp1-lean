import SP1Clean.Soundness.LocalCoreInstructionExecution
import SP1Clean.Soundness.CoreHaltExecution

/-! # Stateful HALT grounding for local shards

The actual Program ledger authenticates ECALL. HALT's own assertions and incoming Memory
currency then determine the complete host transition on the carrier's paired replay. This closes
the HALT step/frame obligation without a boot assumption or a caller-supplied HALT successor.
ROM preservation and active SyscallInstrs effects remain explicit obligations.
-/

namespace SP1Clean.Soundness.LocalCore

open SP1Clean.Soundness.NativeCore (ExecutionRow haltEventOfRow)
open Circuit Air.Flat SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem halt_member {image : ProgramImage} {source : ExecutionSnapshot}
    {witness : EnsembleWitness (ensemble (p := p) image source)} {row : HaltChip.Inputs (ZMod p)}
    (member : ExecutionRow.halt row ∈ executionRows witness) :
    ∃ physical ∈ (systemTable witness 2).table,
      haltRow witness.data physical = row ∧ row.is_real = 1 := by
  have active : row ∈ activeSystemRows (systemTable witness 2) (haltRow witness.data) (·.is_real) := by
    simpa [executionRows] using member
  exact NativeCore.activeSystemRows_member _ _ _ active

/-- Every active HALT fetch belongs to the checked image, by the actual Program balance. -/
theorem halt_program_committed_of_balance {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    {row : HaltChip.Inputs (ZMod p)} (member : ExecutionRow.halt row ∈ executionRows witness) :
    Target.committedInROM (image.toGuestProgram valid) (rowOfMsg (HaltChip.programMessage row)) := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := halt_member member
  let row := haltRow witness.data physical
  let message := HaltChip.programMessage row
  let interaction := programChannel.pulledIfValue row.is_real message
  have emitted : interaction ∈ witness.interactionsWith programChannel.toRaw := by
    apply EnsembleWitness.mem_interactionsWith.mpr
    refine Or.inr ⟨systemTable witness 2, systemTable_mem witness 2, List.mem_flatMap.mpr ⟨physical, physicalMem, ?_⟩⟩
    rw [← typedInteractionValuesWith_raw,
      haltRow_typedProgram_of_component _ witness.data (systemTable_component witness 2)]
    exact List.mem_cons_self
  exact program_pull_committed_of_balance valid witness constraints balanced message interaction emitted
    (by change -row.is_real = -1; rw [real]) rfl

/-- Every active HALT fetch belongs to the checked image, by the actual Program balance. -/
theorem halt_program_committed {image : ProgramImage} {source : ExecutionSnapshot} (valid : image.Valid)
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : HaltChip.Inputs (ZMod p)} (member : ExecutionRow.halt row ∈ executionRows witness) :
    Target.committedInROM (image.toGuestProgram valid) (rowOfMsg (HaltChip.programMessage row)) := by
  exact halt_program_committed_of_balance valid witness constraints
    (balanced _ (by simp [ensemble, PublicVerifier.install, baseEnsemble, sp1Ensemble_channels])) member

/-- HALT's own assertions fix the zero code and three zero exit limbs; Byte fixes the clock. -/
theorem haltRows_staticFacts_of_byte {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (bytes : ∀ table ∈ witness.tables, table.ChannelGuarantees witness.data byteChannel.toRaw)
    {row : HaltChip.Inputs (ZMod p)} (member : ExecutionRow.halt row ∈ executionRows witness) :
    Word.toBitVec64 row.x5_memory.prev_value = 0 ∧
      (row.x10_memory.prev_value[1] = 0 ∧ row.x10_memory.prev_value[2] = 0 ∧ row.x10_memory.prev_value[3] = 0) ∧
      (((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ row.state.clk_16_24.val < 2 ^ 8) := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := halt_member member
  have checked := systemTable_constraints witness constraints 2 physical physicalMem
  rw [systemTable_component witness 2] at checked
  have realEval : Expression.eval (Environment.fromArray physical witness.data)
      (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs (ZMod p)).is_real = 1 := by
    simpa only [haltRow_eq, circuit_norm] using real
  have shallow := shallowConstraints_of_componentConstraints HaltChip.circuit _ checked
  have zero := HaltChip.codeZero_of_shallow _ _ _ shallow realEval
  have high := HaltChip.exitHighZero_of_shallow _ _ _ shallow realEval
  refine ⟨?_, ?_, haltRow_cpuState_bounds_of_component _ witness.data (systemTable_component witness 2)
    (bytes _ (systemTable_mem witness 2))
    physicalMem real⟩
  · simpa only [haltRow_eq] using zero
  · simpa only [haltRow_eq] using high

/-- HALT's own assertions fix the zero code and three zero exit limbs; Byte fixes the clock. -/
theorem haltRows_staticFacts {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : HaltChip.Inputs (ZMod p)} (member : ExecutionRow.halt row ∈ executionRows witness) :
    Word.toBitVec64 row.x5_memory.prev_value = 0 ∧
      (row.x10_memory.prev_value[1] = 0 ∧ row.x10_memory.prev_value[2] = 0 ∧ row.x10_memory.prev_value[3] = 0) ∧
      (((row.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧ row.state.clk_16_24.val < 2 ^ 8) := by
  exact haltRows_staticFacts_of_byte witness constraints
    (fun table present => ((finishedChannel_guarantees image source witness constraints balanced).2 table present).1) member

/-- A physical HALT row, at a grounded prefix, executes on the actual current host and records
its exit. The complete successor preserves the rest of the host and Sail state literally. -/
theorem GroundingCarrier.halt_step {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy) (field : policy.characteristic = p)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : HaltChip.Inputs (ZMod p)} (member : ExecutionRow.halt row ∈ executionRows witness)
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid policy) carrier.timeline
      (haltRowFacts row).statePull)
    (currency : ∀ mp ∈ (haltRowFacts row).memPulls, MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid policy) source.sail.realize carrier.timeline
        (MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    {n : ℕ} {whole : ExecutionState} (paired : carrier.pairedTrajectory valid policy n = some whole)
    (time : StateMsg.timeNat (HaltChip.statePulledMessage row) = carrier.timeline.start n) :
    ExecutionStep policy (image.toGuestProgram valid) whole (.syscall (haltEventOfRow row))
      ⟨{ whole.sail with regs := whole.sail.regs.insert LeanRV64D.Defs.Register.PC Machine.haltPc },
        { whole.host with exitCode := some ((Word.toBitVec64 row.x10_memory.prev_value).setWidth 32) },
        whole.clock + Machine.syscallSchedule.duration⟩ := by
  obtain ⟨m, state, present, atIndex, pc, rom, _⟩ := pull
  have same : m = n := start_injective carrier.timeline (atIndex.symm.trans time)
  subst m
  have sail : whole.sail = state := by
    simpa only [trajectory, paired, Option.map_some, Option.some.injEq] using present
  have before : carrier.trajectory valid policy n = some whole.sail := by
    simp only [trajectory, paired, Option.map_some]
  have atPc : whole.sail.regs.get? LeanRV64D.Defs.Register.PC =
      some (StateMsg.pcBits (HaltChip.statePulledMessage row)) := by rwa [sail]
  have committed := halt_program_committed valid witness constraints balanced member
  have fetch : (image.toGuestProgram valid).fetchWord (StateMsg.pcBits (HaltChip.statePulledMessage row)) =
      some Target.ECALL_ENC := (committed.ecall_of_opcode rfl).1
  have running := carrier.pairedTrajectory_running_of_fetch valid policy constraints balanced member paired atPc fetch
  obtain ⟨covered, _⟩ := List.getElem?_eq_some_iff.mp (carrier.event_at member time)
  have clock := (carrier.pairedTrajectory_clock valid policy constraints balanced (Nat.le_of_lt covered) paired).trans time.symm
  have facts := haltRows_staticFacts witness constraints balanced member
  exact HaltChip.executionStep_of_currency row policy field _ whole facts.1 facts.2.1 running clock atPc fetch
    (by rwa [sail]) before time currency

/-- Incoming State truth and Memory currency discharge HALT replay's actual host guards. -/
theorem GroundingCarrier.trajectory_halt {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy) (field : policy.characteristic = p)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : HaltChip.Inputs (ZMod p)} (member : ExecutionRow.halt row ∈ executionRows witness)
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid policy) carrier.timeline
      (haltRowFacts row).statePull)
    (currency : ∀ mp ∈ (haltRowFacts row).memPulls, MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid policy) source.sail.realize carrier.timeline
        (MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    (n : ℕ) (time : StateMsg.timeNat (HaltChip.statePulledMessage row) = carrier.timeline.start n) :
    carrier.trajectory valid policy (n + 1) = (carrier.trajectory valid policy n).map
      (fun state => { state with regs := state.regs.insert LeanRV64D.Defs.Register.PC Machine.haltPc }) := by
  have stateTruth := pull
  obtain ⟨m, state, present, atIndex, _⟩ := pull
  have same : m = n := start_injective carrier.timeline (atIndex.symm.trans time)
  subst m
  change (carrier.pairedTrajectory valid policy n).map ExecutionState.sail = some state at present
  obtain ⟨whole, paired, _⟩ := Option.map_eq_some_iff.mp present
  have step := carrier.halt_step valid policy field constraints balanced member stateTruth currency paired time
  change (carrier.pairedTrajectory valid policy (n + 1)).map ExecutionState.sail = _
  rw [carrier.pairedTrajectory_succ valid policy member time, paired, Option.bind_some]
  rw [show (ExecutionRow.halt row).event = .syscall (haltEventOfRow row) from rfl, step.replay]
  simp only [trajectory, paired, Option.map_some]

/-- Every active HALT row supplies step/frame facts on the paired local replay. -/
theorem GroundingCarrier.halt_engineFacts {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy) (field : policy.characteristic = p)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {row : HaltChip.Inputs (ZMod p)} (member : ExecutionRow.halt row ∈ executionRows witness) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
        (haltRowFacts row) ∧
      FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
        (haltRowFacts row) :=
  halt_engineFactsG_of_currencyStep row (haltRows_staticFacts witness constraints balanced member).2.2 _ _ _ _
    (fun n time => carrier.originalTimeStep member n time)
    (carrier.trajectory_halt valid policy field constraints balanced member)

/-- Local grounding now constructs ordinary and HALT semantics internally. Only ROM protection
and the active SyscallInstrs effects remain semantic premises; no successful replay is assumed. -/
theorem GroundingCarrier.ground_of_host_steps {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : image.Valid) {witness : EnsembleWitness (ensemble (p := p) image source)}
    (carrier : GroundingCarrier witness) (policy : HostPolicy) (field : policy.characteristic = p)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (codeMemoryCompatible : ∀ {n : ℕ} {state next : SailState},
      carrier.trajectory valid policy n = some state → Target.SailStep state next →
      Target.RomLoaded (image.toGuestProgram valid) state → Target.RomLoaded (image.toGuestProgram valid) next)
    (syscall : ∀ row, ExecutionRow.syscall row ∈ executionRows witness →
      LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
          (syscallRowFacts row) ∧
        FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid policy) source.sail.realize carrier.timeline
          (syscallRowFacts row)) :
    (∀ row ∈ carrier.rows, GroundedG (image.toGuestProgram valid) (carrier.trajectory valid policy)
      source.sail.realize carrier.timeline row) ∧
      LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid policy) carrier.timeline
        (finalBoundaryStateMessage witness.publicInput) ∧
      (∀ loc message, memoryFinalFrontier witness loc = some message →
        LocalValueAtG (carrier.trajectory valid policy) source.sail.realize carrier.timeline loc
          (StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput)) message.value) :=
  carrier.ground_of_system_steps valid policy constraints balanced codeMemoryCompatible
    (fun _ member => carrier.halt_engineFacts valid policy field constraints balanced member) syscall

end SP1Clean.Soundness.LocalCore
