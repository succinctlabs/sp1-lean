import SP1Clean.Soundness.HostQueueCallProjection
import SP1Clean.Soundness.CoreExecutionEvents
import SP1Clean.Soundness.HaltGrounding

/-! # Host queue contents at an actual CPU prefix

The full physical HostCall handoff identifies the queue actions on the decoded CPU tape.
Strict CPU and queue order then identify their prefixes. Successful paired replay of such a
prefix determines the current host hints; the queue history supplies the matching frontier.
Replay success remains the induction hypothesis, not an assumed success of the current call.
-/

namespace SP1Clean.Soundness.HostQueueCPUReplay

open Circuit Air.Flat Model.Core HostHintReadLocal HostQueueOrder HostQueueCPUOrder
open NativeCore Semantics HostQueueCallProjection

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance replayLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

noncomputable def stampedCPU (data : ProverData (ZMod p)) (row : ExecutionRow p) :
    Option (ℕ × HintQueue.Event) :=
  (queueEvent? row.event).map fun event => (StateMsg.timeNat (row.edge data).1, event)

omit [Fact (2 ^ 25 < p)] in
private theorem syscall_queue (row : SyscallInstrsChip.Inputs (ZMod p)) :
    queueEvent? (.syscall (syscallEventOfRow row)) = queueCallEvent?
      (Word.toBitVec64 row.op_a_memory.prev_value) (Word.toBitVec64 row.op_c_memory.prev_value)
      (Word.toBitVec64 row.op_a_value) := by
  simp only [queueEvent?, rawCode_syscallEventOfRow, arg2_syscallEventOfRow, result_syscallEventOfRow]
  rfl

private theorem wrapper_projection (data : ProverData (ZMod p)) (input : HostCallChip.Inputs (ZMod p))
    (flag : ZMod p) : stampedCPU data (.syscall input.instruction) = stamped (input.message flag) := by
  simp only [stampedCPU, ExecutionRow.event, syscall_queue, stamped, project, HostCallChip.Inputs.message]
  rfl

private theorem syscall_projection (data : ProverData (ZMod p)) (env : Environment (ZMod p)) :
    stampedCPU data (.syscall (HostCallLedger.input env).instruction) = stamped (HostCallLedger.call env) :=
  wrapper_projection data (HostCallLedger.input env) _

private theorem syscall_safe (env : Environment (ZMod p)) :
    QueueProjectionSafe (ExecutionRow.syscall (HostCallLedger.input env).instruction).event ↔
      safe (HostCallLedger.call env) := by
  simp only [QueueProjectionSafe, ExecutionRow.event, rawCode_syscallEventOfRow,
    safe, HostCallLedger.call, HostCallChip.Inputs.message, Word.toBitVec64, Word.toNat]

/-- Every active legacy HALT row carries the actual zero syscall code. -/
theorem halt_code {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (LocalCore.ensemble (p := p) image source)) (constraints : witness.Constraints)
    (row : HaltChip.Inputs (ZMod p))
    (member : row ∈ activeSystemRows (LocalCore.systemTable witness 2) (haltRow witness.data) (·.is_real)) :
    Word.toBitVec64 row.x5_memory.prev_value = 0 := by
  obtain ⟨physical, physicalMem, rfl, real⟩ := activeSystemRows_member _ _ _ member
  have checked := LocalCore.systemTable_constraints witness constraints 2 physical physicalMem
  rw [LocalCore.systemTable_component witness 2] at checked
  have realEval : Expression.eval (Environment.fromArray physical witness.data)
      (varFromOffset HaltChip.Inputs 0 : Var HaltChip.Inputs (ZMod p)).is_real = 1 := by
    simpa only [haltRow_eq, circuit_norm] using real
  have zero := HaltChip.codeZero_of_shallow _ _ _
    (shallowConstraints_of_componentConstraints HaltChip.circuit _ checked) realEval
  simpa only [haltRow_eq] using zero

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
  {names : ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ resources))).map (·.circuit.name)).Nodup}

/-- Erase silent instruction families while retaining every wrapper occurrence. -/
theorem filterMap_inventory {Instruction Halt Wrapper Row Message Label : Type*}
    (instruction : Instruction → Row) (halt : Halt → Row) (wrapper : Wrapper → Row)
    (call : Wrapper → Message) (project : Row → Option Label) (label : Message → Option Label)
    (instructions : List Instruction) (haltRows : List Halt) (wrappers : List Wrapper)
    (ordinary : ∀ row ∈ instructions, project (instruction row) = none)
    (halting : ∀ row ∈ haltRows, project (halt row) = none)
    (syscall : ∀ row, project (wrapper row) = label (call row)) :
    ((instructions.map instruction ++ haltRows.map halt ++ wrappers.map wrapper).filterMap project) =
      (wrappers.map call).filterMap label := by
  have halts : (haltRows.map halt).filterMap project = [] := by
    rw [List.filterMap_map]
    apply List.filterMap_eq_nil_iff.mpr
    intro row member
    exact halting row member
  have ord : (instructions.map instruction).filterMap project = [] := by
    simp only [List.filterMap_map]
    apply List.filterMap_eq_nil_iff.mpr
    exact ordinary
  rw [List.filterMap_append, List.filterMap_append, ord, halts, List.nil_append, List.nil_append]
  simp only [List.filterMap_map, Function.comp_def, syscall]

private theorem inventory_projection (data : ProverData (ZMod p))
    (instructions : List (DecodedInstructionRow p)) (haltRows : List (HaltChip.Inputs (ZMod p)))
    (wrappers : List (Environment (ZMod p)))
    (codeZero : ∀ row ∈ haltRows, Word.toBitVec64 row.x5_memory.prev_value = 0) :
    ((instructions.map ExecutionRow.instruction ++ haltRows.map ExecutionRow.halt ++
      (wrappers.map fun env => ExecutionRow.syscall (HostCallLedger.input env).instruction)).filterMap
        (stampedCPU data)) = (wrappers.map HostCallLedger.call).filterMap stamped := by
  apply filterMap_inventory
  · intro row _
    simp only [stampedCPU, ExecutionRow.event, queueEvent?, Option.map_none]
  · intro row member
    simp only [stampedCPU, ExecutionRow.event, queueEvent?, haltEventOfRow,
      codeZero row member, queueCallEvent?, SyscallKind.code, BitVec.reduceEq, ↓reduceIte, Option.map_none]
  · exact syscall_projection data

private theorem cpu_inventory
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (constraints : witness.Constraints) :
    ((LocalCore.executionRows (HostLocalCore.localWitness witness)).filterMap (stampedCPU witness.data)) =
      (HostCallLedger.calls (HostLocalCore.hostCallTable witness) witness.data).filterMap stamped := by
  rw [LocalCore.executionRows, ← HostLocalCore.hostCallTable_projection, List.map_map]
  exact inventory_projection witness.data _ _ _ (fun row member => halt_code (HostLocalCore.localWitness witness)
    (HostLocalCore.localWitness_constraints witness constraints) row member)

/-- Every actual CPU event in the installed registry is safe for nonallocating queue replay.
The absence of WRITE follows from the complete physical handoff, not a caller restriction. -/
theorem cpu_safe
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (calls : witness.BalancedChannel HostCallChip.channel.toRaw)
    (bytes : witness.BalancedChannel Channels.byteChannel.toRaw)
    (specs : ∀ table ∈ queueTables witness, table.Spec witness.data) :
    ∀ row ∈ LocalCore.executionRows (HostLocalCore.localWitness witness), QueueProjectionSafe row.event := by
  have safeCalls := (calls_projection witness interface constraints bytes specs).1
  have handoff := HostLocalHandoff.calls_perm_of_balancedChannel witness (resources_hostCall_silent interface)
    constraints calls
  intro row member
  cases row with
  | instruction row => trivial
  | halt row =>
    have active : row ∈ activeSystemRows (LocalCore.systemTable (HostLocalCore.localWitness witness) 2)
        (haltRow (HostLocalCore.localWitness witness).data) (·.is_real) := by
      simpa [LocalCore.executionRows] using member
    have zero := halt_code (HostLocalCore.localWitness witness)
      (HostLocalCore.localWitness_constraints witness constraints) row active
    simpa only [ExecutionRow.event, QueueProjectionSafe, haltEventOfRow, zero, SyscallKind.code] using
      (by decide : (0 : BitVec 64) ≠ 2)
  | syscall row =>
    have active : row ∈ activeSystemRows (LocalCore.systemTable (HostLocalCore.localWitness witness) 3)
        (syscallInstrsRow (HostLocalCore.localWitness witness).data) (·.is_real) := by
      simpa [LocalCore.executionRows] using member
    rw [← HostLocalCore.hostCallTable_projection] at active
    obtain ⟨env, envMem, rfl⟩ := List.mem_map.mp active
    exact (syscall_safe env).mpr (safeCalls _ (handoff.mem_iff.mp (List.mem_map_of_mem envMem)))

private theorem stampedCPU_time (data : ProverData (ZMod p)) (row : ExecutionRow p)
    (stamp : ℕ × HintQueue.Event) (present : stampedCPU data row = some stamp) :
    stamp.1 = StateMsg.timeNat (row.edge data).1 := by
  obtain ⟨event, _, rfl⟩ := Option.map_eq_some_iff.mp present
  rfl

private theorem ordered_projection (data : ProverData (ZMod p))
    (cpu : List (ExecutionRow p)) (path : List (Row (p := p)))
    (same : (cpu.filterMap (stampedCPU data)).Perm (path.map fun row => (eventTime row, HostQueueHistory.event row)))
    (cpuSorted : (cpu.map fun row => StateMsg.timeNat (row.edge data).1).Pairwise (· < ·))
    (queueSorted : (path.map eventTime).Pairwise (· < ·)) :
    cpu.filterMap (stampedCPU data) = path.map fun row => (eventTime row, HostQueueHistory.event row) := by
  apply same.eq_of_pairwise (le := fun a b => a.1 < b.1)
  · intro a b _ _ forward backward
    exact (Nat.lt_asymm forward backward).elim
  · apply (List.pairwise_map.mp cpuSorted).filterMap
    intro a b ordered x hx y hy
    rw [stampedCPU_time data a x hx, stampedCPU_time data b y hy]
    exact ordered
  · exact List.pairwise_map.mpr (List.pairwise_map.mp queueSorted)

/-- The ordered CPU tape projects to exactly the ordered queue actions, including their labels.
Ordinary instructions and queue-preserving host calls are erased only after their accounting proof. -/
theorem cpu_projection
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (calls : witness.BalancedChannel HostCallChip.channel.toRaw)
    (bytes : witness.BalancedChannel Channels.byteChannel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostLocalCore.localWitness witness))
    (specs : ∀ table ∈ queueTables witness, table.Spec witness.data)
    {cpu : List (ExecutionRow p)}
    (cpuExhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness witness)))
    (cpuWalk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu)
    {path : List (Row (p := p))} {initial final : HostHintQueue.State (ZMod p)}
    (queueExhaustive : path.Perm (TransitionView.readIndexedRows indices (queueTables witness) witness.data))
    (queueWalk : Walk.IsWalk edge initial final path) :
    cpu.filterMap (stampedCPU witness.data) = path.map fun row => (eventTime row, HostQueueHistory.event row) := by
  have handoff := HostLocalHandoff.calls_perm_of_balancedChannel witness (resources_hostCall_silent interface)
    constraints calls
  have projected := (cpuExhaustive.filterMap (stampedCPU witness.data)).trans
    ((List.Perm.of_eq (cpu_inventory witness constraints)).trans
      ((handoff.filterMap stamped).trans ((calls_projection witness interface constraints bytes specs).2.trans
        (queueExhaustive.map (fun row => (eventTime row, HostQueueHistory.event row))).symm)))
  have edgeData : ExecutionRow.canonEdge (HostLocalCore.localWitness witness).data =
      ExecutionRow.canonEdge witness.data := funext fun row => row.canonEdge_setData _ _
  have publicInput : (HostLocalCore.localWitness witness).publicInput = witness.publicInput := rfl
  have cpuSorted := LocalCore.ordered_times_pairwise (HostLocalCore.localWitness witness)
    (HostLocalCore.localWitness_constraints witness constraints) ordering cpuExhaustive
    (by simpa only [edgeData, publicInput] using cpuWalk)
  simp_rw [ExecutionRow.edge_setData _ (HostLocalCore.localWitness witness).data witness.data] at cpuSorted
  exact ordered_projection witness.data cpu path projected cpuSorted
    (times_pairwise queueWalk (fun row member => rows_spec _ witness.data (queueTables_aligned witness) specs row
      (queueExhaustive.mem_iff.mp member)))

end SP1Clean.Soundness.HostQueueCPUReplay
