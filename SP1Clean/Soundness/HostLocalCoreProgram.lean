import SP1Clean.Soundness.HostLocalCore
import SP1Clean.Soundness.LocalCoreProgram
import SP1Clean.Soundness.SyscallGrounding
import SP1Clean.Soundness.CoreTouches
import SP1Clean.Soundness.SyscallInputs

/-! # Program authentication and register reads in the host assembly

The original Program ledger is preserved when host auxiliaries do not emit fetches. Its own
balance authenticates every instruction against the fixed image, including the wrapper's full
ECALL operand indices. At a grounded prefix, the three register touches then read the exact
code and arguments emitted by that physical wrapper. Memory balance remains in the extended AIR.
-/

namespace SP1Clean.Soundness.HostLocalCore

open Circuit Air.Flat Channels Model.Core Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance programLt24 : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance programLt17 : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {auxiliary : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
    {names : ((tables image source auxiliary).map (·.circuit.name)).Nodup}

/-- The extended AIR authenticates every active Program pull using the fixed image provider. -/
theorem program_pull_committed (valid : image.Valid)
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (silent : ∀ component ∈ auxiliary, programChannel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    (message : ProgramMsg (ZMod p)) (interaction : Interaction (ZMod p))
    (member : interaction ∈ witness.interactionsWith programChannel.toRaw)
    (active : interaction.mult = -1) (payload : interaction.msg = (toElements message).toArray) :
    Target.committedInROM (image.toGuestProgram valid) (rowOfMsg message) := by
  apply LocalCore.program_pull_committed_of_balance valid (localWitness witness)
    (localWitness_constraints witness constraints) ?_
    message interaction ?_ active payload
  · change BalancedInteractions ((localWitness witness).interactionsWith programChannel.toRaw)
    rw [localWitness_program witness silent]
    exact balanced
  · rwa [localWitness_program witness silent]

private theorem wrapper_program_values (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (physical : Array (ZMod p)) :
    HostCallLedger.producer.operations.interactionValuesWith programChannel.toRaw (Environment.fromArray physical witness.data) =
      [programChannel.pulledIfValue (HostCallLedger.input (Environment.fromArray physical witness.data)).instruction.is_real
        (SyscallInstrsChip.programMessage (HostCallLedger.input (Environment.fromArray physical witness.data)).instruction)] := by
  have typed := syscallInstrsRow_typedProgram_of_component
    (LocalCore.systemTable (localWitness witness) 3) witness.data
    (LocalCore.systemTable_component (localWitness witness) 3) physical
  have raw := congrArg (List.map TypedInteraction.raw) typed
  rw [typedInteractionValuesWith_raw] at raw
  simp only [List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_raw, LocalCore.systemTable_component] at raw
  rw [HostCallProjection.input_original]
  change HostCallLedger.producer.operations.interactionValuesWith programChannel.toRaw (Environment.fromArray physical witness.data) = _
  rw [Operations.interactionValuesWith, ← HostCallProjection.other_interactions programChannel.toRaw
    (by simp [programChannel, byteChannel, Channel.toRaw])
    (by simp [programChannel, memoryChannel, Channel.toRaw])
    (by simp [programChannel, HostCallChip.channel, Channel.toRaw])]
  exact raw

/-- Every actual wrapper call carries the checked image's ECALL fetch and register indices. -/
theorem hostCall_program_committed (valid : image.Valid)
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (silent : ∀ component ∈ auxiliary, programChannel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    (env : Environment (ZMod p)) (member : env ∈ HostCallLedger.activeRows (hostCallTable witness) witness.data) :
    Target.committedInROM (image.toGuestProgram valid)
      (rowOfMsg (SyscallInstrsChip.programMessage (HostCallLedger.input env).instruction)) := by
  have real := HostCallLedger.activeRows_is_real _ _ _ member
  obtain ⟨mapped, _⟩ := List.mem_filter.mp member
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp mapped
  apply program_pull_committed valid witness silent constraints balanced _
    (programChannel.pulledIfValue (HostCallLedger.input (Environment.fromArray physical witness.data)).instruction.is_real
      (SyscallInstrsChip.programMessage (HostCallLedger.input (Environment.fromArray physical witness.data)).instruction))
  · apply EnsembleWitness.mem_interactionsWith.mpr
    refine Or.inr ⟨hostCallTable witness, hostCallTable_mem witness, List.mem_flatMap.mpr ⟨physical, physicalMem, ?_⟩⟩
    rw [hostCallTable_component, wrapper_program_values witness]
    exact List.mem_cons_self
  · change -(HostCallLedger.input (Environment.fromArray physical witness.data)).instruction.is_real = -1
    rw [real]
  · rfl

private theorem local_executionRow_time
    (witness : EnsembleWitness (LocalCore.ensemble (p := p) image source))
    (constraints : witness.Constraints) (ordering : LocalCore.OrderingChannels witness)
    {cpu : List (NativeCore.ExecutionRow p)}
    (exhaustive : cpu.Perm (LocalCore.executionRows witness))
    (walk : Walk.IsWalk (NativeCore.ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu)
    (prior rest : List (NativeCore.ExecutionRow p)) (event : NativeCore.ExecutionRow p)
    (split : cpu = prior ++ event :: rest) :
    StateMsg.timeNat (event.edge witness.data).1 = source.clock + (prior.map NativeCore.ExecutionRow.duration).sum := by
  have steps : ∀ row ∈ cpu,
      StateMsg.timeNat (row.canonEdge witness.data).2 =
        StateMsg.timeNat (row.canonEdge witness.data).1 + row.duration := by
    intro row member
    have good := LocalCore.executionRows_good_of_orderingChannels witness constraints ordering (exhaustive.mem_iff.mp member)
    dsimp only [NativeCore.ExecutionRow.canonEdge]
    rw [timeNat_canonState good.1.1, timeNat_canonState good.2.1]
    exact (LocalCore.executionRows_advancing_of_orderingChannels witness constraints ordering (exhaustive.mem_iff.mp member)).2
  have clock := statePullTime_of_stateWalk_durations _ NativeCore.ExecutionRow.duration walk steps prior event rest split
  have member : event ∈ cpu := by rw [split]; exact List.mem_append_right _ List.mem_cons_self
  have good := LocalCore.executionRows_good_of_orderingChannels witness constraints ordering (exhaustive.mem_iff.mp member)
  dsimp only [NativeCore.ExecutionRow.canonEdge] at clock
  have sourceTime : StateMsg.timeNat (initialBoundaryStateMessage witness.publicInput) = source.clock :=
    (LocalCore.source_state_encoding_of_checks witness ordering.sourceChecks).1
  exact (timeNat_canonState good.1.1).symm.trans
    (clock.trans (congrArg (fun time => time + (prior.map NativeCore.ExecutionRow.duration).sum) sourceTime))

/-- The actual CPU prefix determines the next row's clock from the checked incoming source.
This uses only State/Byte ordering; Memory remains in the extended ledger. -/
theorem executionRow_time
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (constraints : witness.Constraints) (ordering : LocalCore.OrderingChannels (localWitness witness))
    {cpu : List (NativeCore.ExecutionRow p)}
    (exhaustive : cpu.Perm (LocalCore.executionRows (localWitness witness)))
    (walk : Walk.IsWalk (NativeCore.ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu)
    (prior rest : List (NativeCore.ExecutionRow p)) (event : NativeCore.ExecutionRow p)
    (split : cpu = prior ++ event :: rest) :
    StateMsg.timeNat (event.edge witness.data).1 = source.clock + (prior.map NativeCore.ExecutionRow.duration).sum := by
  rw [← event.edge_setData (localWitness witness).data witness.data]
  apply local_executionRow_time (localWitness witness) (localWitness_constraints witness constraints)
    ordering exhaustive ?_ prior rest event split
  have edges : NativeCore.ExecutionRow.canonEdge (localWitness witness).data =
      NativeCore.ExecutionRow.canonEdge witness.data := funext fun row => row.canonEdge_setData _ _
  simpa only [edges, localWitness_publicInput] using walk

private theorem registers_of_currency (row : SyscallInstrsChip.Inputs (ZMod p))
    (operands : row.op_a = 5 ∧ row.op_b = 10 ∧ row.op_c = 11)
    (trajectory : Trajectory) (initial current : SailState) (timeline : Timeline) (n : ℕ)
    (atState : trajectory n = some current)
    (atTime : StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) = timeline.start n)
    (currency : ∀ mp ∈ (syscallRowFacts row).memPulls,
      LocalValueAtG trajectory initial timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    current.get_reg? 5 = some (Word.toBitVec64 row.op_a_memory.prev_value) ∧
      current.get_reg? 10 = some (Word.toBitVec64 row.op_b_memory.prev_value) ∧
      current.get_reg? 11 = some (Word.toBitVec64 row.op_c_memory.prev_value) := by
  obtain ⟨a, b, c⟩ := syscallRowFacts_currency_split_values row currency
  have locA := (syscallRow_locOf_reg row (i := 5) operands.1.symm row.op_a_memory row.op_a_value 4).1
  have locB := (syscallRow_locOf_reg row (i := 10) operands.2.1.symm row.op_b_memory row.op_b_memory.prev_value 3).1
  have locC := (syscallRow_locOf_reg row (i := 11) operands.2.2.symm row.op_c_memory row.op_c_memory.prev_value 2).1
  rw [locA, atTime] at a
  rw [locB, atTime] at b
  rw [locC, atTime] at c
  exact ⟨(TimedGrounding.localValueAtG_stepStart_iff atState).mp a,
    TimedGrounding.localValueAtG_regRead_of_traj (k := 3) atState (by decide) b,
    TimedGrounding.localValueAtG_regRead_of_traj (k := 2) atState (by decide) c⟩

/-- The grounding engine's incoming currency supplies the actual full host-call observations.
No caller selects register indices or separately authenticates the instruction fetch. -/
theorem hostCall_registers (valid : image.Valid)
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (silent : ∀ component ∈ auxiliary, programChannel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    (env : Environment (ZMod p)) (member : env ∈ HostCallLedger.activeRows (hostCallTable witness) witness.data)
    (trajectory : Trajectory) (initial current : SailState) (timeline : Timeline) (n : ℕ)
    (atState : trajectory n = some current)
    (atTime : StateMsg.timeNat (SyscallInstrsChip.statePulledMessage (HostCallLedger.input env).instruction) = timeline.start n)
    (currency : ∀ mp ∈ (syscallRowFacts (HostCallLedger.input env).instruction).memPulls,
      LocalValueAtG trajectory initial timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    (HostReadContext.ofSail current).register 5 = some (Word.toBitVec64 (HostCallLedger.call env).code) ∧
      (HostReadContext.ofSail current).register 10 = some (Word.toBitVec64 (HostCallLedger.call env).arg1) ∧
      (HostReadContext.ofSail current).register 11 = some (Word.toBitVec64 (HostCallLedger.call env).arg2) := by
  have committed := hostCall_program_committed valid witness silent constraints balanced env member
  have operands := NativeCore.syscall_operands_of_committed _ _ committed
  exact registers_of_currency _ operands trajectory initial current timeline n atState atTime currency

/-- The actual wrapper instruction has its whole-chip contract and operand bounds within
the incoming grounding invariant. Program balance remains separate from the full Memory ledger. -/
theorem hostCall_contract
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (interface : AuxiliaryInterface auxiliary)
    (silent : ∀ component ∈ auxiliary, programChannel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    (bytes : witness.BalancedChannel byteChannel.toRaw)
    (env : Environment (ZMod p)) (member : env ∈ HostCallLedger.activeRows (hostCallTable witness) witness.data)
    (currency : ∀ mp ∈ (syscallRowFacts (HostCallLedger.input env).instruction).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1) :
    SyscallInstrsChip.Spec (HostCallLedger.input env).instruction ∧
      SyscallInstrsChip.PulledFacts (HostCallLedger.input env).instruction := by
  have active : (HostCallLedger.input env).instruction ∈
      activeSystemRows (LocalCore.systemTable (localWitness witness) 3) (syscallInstrsRow (localWitness witness).data) (·.is_real) := by
    rw [← hostCallTable_projection witness]
    exact List.mem_map_of_mem member
  obtain ⟨physical, physicalMem, same, _⟩ := NativeCore.activeSystemRows_member _ _ _ active
  have checked := localWitness_constraints witness constraints
  have byte := localWitness_byte witness interface constraints bytes
  have balance : (localWitness witness).BalancedChannel programChannel.toRaw := by
    change BalancedInteractions ((localWitness witness).interactionsWith programChannel.toRaw)
    rw [localWitness_program witness silent]
    exact balanced
  have program := LocalCore.program_guarantees_of_balance image source (localWitness witness) checked balance
  have contract := syscallInstrsRow_contract_of_component _ (localWitness witness).data (LocalCore.systemTable_component (localWitness witness) 3)
    (LocalCore.systemTable_constraints (localWitness witness) checked 3)
    (byte _ (LocalCore.systemTable_mem (localWitness witness) 3))
    (program.2 _ (LocalCore.systemTable_mem (localWitness witness) 3)) physicalMem (by rwa [same])
  rw [same] at contract
  exact contract

/-- The actual host wrapper inherits its instruction row law and semantic clock, using
incoming operand bounds and the preserved Program and Byte balances. -/
theorem hostCall_eventLaw
    (witness : EnsembleWitness (ensemble image source auxiliary channels names))
    (interface : AuxiliaryInterface auxiliary)
    (silent : ∀ component ∈ auxiliary, programChannel.toRaw ∉ component.circuit.channels)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel programChannel.toRaw)
    (bytes : witness.BalancedChannel byteChannel.toRaw)
    (env : Environment (ZMod p)) (member : env ∈ HostCallLedger.activeRows (hostCallTable witness) witness.data)
    (currency : ∀ mp ∈ (syscallRowFacts (HostCallLedger.input env).instruction).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1) :
    (syscallEventOfRow (HostCallLedger.input env).instruction).RowLaw ∧
      (syscallEventOfRow (HostCallLedger.input env).instruction).clock =
        StateMsg.timeNat (SyscallInstrsChip.statePulledMessage (HostCallLedger.input env).instruction) := by
  have contract := hostCall_contract witness interface silent constraints balanced bytes env member currency
  have real := HostCallLedger.activeRows_is_real _ _ _ member
  exact ⟨rowLaw_of_spec_and_pulledFacts _ contract.1 contract.1.selectorsValid contract.2 real,
    syscallEvent_startsAt _ (Fact.out (p := 2 ^ 24 < p)) contract.1 real⟩

end SP1Clean.Soundness.HostLocalCore
