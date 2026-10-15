import SP1Clean.Soundness.HostHintQueueHistory
import ToMathlib.ListChronology

/-! # Queue history in CPU event order

The queue token's successor is stamped with the incoming CPU event clock. Actual unit HostCall
pulls identify complete calls in the physical instruction wrapper. Strict ordering of both walks
then puts the queue clocks in the CPU walk as a subsequence, independent of table permutations.
This uses the extended witness's own balance; it does not project away host Memory effects or
assume successful host replay. WRITE/hook queue edges are outside the present handler registry.
-/

namespace SP1Clean.Soundness.HostQueueCPUOrder

open Circuit Air.Flat Model.Core HostHintQueue HostQueueOrder HostHintReadLocal NativeCore Semantics

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance cpuClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance cpuLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The complete handoff read from the same physical queue-handler row. -/
def call (row : Row (p := p)) : HostCallChip.Message (ZMod p) :=
  match row.1 with
  | none => (HostHintReadCoverage.input row.2).call
  | some _ => (valueFromOffset HostHintLengthChip.Inputs 0 row.2).call

def eventTime (row : Row (p := p)) : ℕ := time (edge row).2

private theorem read_edge (env : Environment (ZMod p)) :
    edge (none, env) = ((HostHintReadCoverage.input env).previous, (HostHintReadCoverage.input env).next) := rfl

private theorem length_edge (empty : Bool) (env : Environment (ZMod p)) :
    edge (some empty, env) = ((valueFromOffset HostHintLengthChip.Inputs 0 env).previous,
      (valueFromOffset HostHintLengthChip.Inputs 0 env).next) := rfl

private theorem length_component (empty : Bool) :
    (view (p := p) (some empty)).component = { circuit := HostHintLengthChip.circuit empty } := rfl

/-- Queue transitions stamp the successor with the call's incoming CPU clock. -/
theorem call_time (row : Row (p := p)) :
    clkNat (call row).clk_high (call row).clk_low = eventTime row := by
  rcases row with ⟨index, env⟩
  cases index with
  | none => simp only [call, eventTime, read_edge, time, HostHintReadChip.Inputs.next]
  | some empty => simp only [call, eventTime, length_edge, time, HostHintLengthChip.Inputs.next]

private theorem call_interactions (row : Row (p := p)) :
    (view row.1).component.operations.interactionValuesWith HostCallChip.channel.toRaw row.2 =
      [HostCallChip.channel.pulledValue (call row)] := by
  rcases row with ⟨index, env⟩
  cases index with
  | none => exact HostHintReadHandoff.handler_values env
  | some empty =>
    have evalCall (input : Var HostHintLengthChip.Inputs (ZMod p)) :
        eval env input.call = (eval env input).call := by
      cases input
      simp only [circuit_norm]
    have values := (HostCallReceivers.hintLength (p := p) empty).interactions env
    rw [length_component]
    simpa only [HostCallReceivers.hintLength, evalCall, eval_varFromOffset_valueFromOffset, call] using values

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {resources : List (Component (ZMod p))} {channels : List (RawChannel (ZMod p))}
  {names : ((HostLocalCore.tables image source
    ((HostHintReadHandoff.receiver :: HostCallReceivers.available).map (·.component) ++
      (HostHintReadHandoff.wordResources ++ resources))).map (·.circuit.name)).Nodup}

private theorem call_mem
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (row : Row (p := p)) (member : row ∈ TransitionView.readIndexedRows indices (queueTables witness) witness.data) :
    call row ∈ HostLocalHandoff.calls witness := by
  have inside : HostCallChip.channel.pulledValue (call row) ∈
      (queueTables witness).flatMap (·.interactionsWith witness.data HostCallChip.channel.toRaw) := by
    rw [TransitionView.readIndexedRows_interactions indices (fun index => (view index).component)
      _ witness.data _ (queueTables_aligned witness)]
    apply List.mem_flatMap.mpr
    refine ⟨row, member, ?_⟩
    change HostCallChip.channel.pulledValue (call row) ∈
      (view row.1).component.operations.interactionValuesWith HostCallChip.channel.toRaw row.2
    rw [call_interactions]
    exact List.mem_singleton_self _
  obtain ⟨table, tableMem, present⟩ := List.mem_flatMap.mp inside
  apply ReceiverView.message_mem_of_pull_mem _ _ witness.data (HostLocalHandoff.receiverTables_aligned witness) _
  refine List.mem_flatMap.mpr ⟨table, ?_, present⟩
  rcases List.mem_cons.mp tableMem with rfl | member
  · exact List.getElem_mem _
  · exact List.mem_of_mem_drop member

/-- Every queue event is an actual active syscall, with the same complete call, not just a clock.
The physical environment is retained for subsequent register and Memory grounding. -/
theorem call_cpu
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel HostCallChip.channel.toRaw)
    (row : Row (p := p)) (member : row ∈ TransitionView.readIndexedRows indices (queueTables witness) witness.data) :
    ∃ env ∈ HostCallLedger.activeRows (HostLocalCore.hostCallTable witness) witness.data,
      HostCallLedger.call env = call row ∧
      ExecutionRow.syscall (HostCallLedger.input env).instruction ∈
        LocalCore.executionRows (HostLocalCore.localWitness witness) ∧
      StateMsg.timeNat ((ExecutionRow.syscall (HostCallLedger.input env).instruction).edge witness.data).1 =
        eventTime row := by
  have registered := call_mem witness row member
  have produced := (HostLocalHandoff.calls_perm_of_balancedChannel witness (resources_hostCall_silent interface)
    constraints balanced).mem_iff.mpr registered
  obtain ⟨env, active, same⟩ := List.mem_map.mp produced
  refine ⟨env, active, same, ?_, ?_⟩
  · apply List.mem_append_right
    apply List.mem_map.mpr
    refine ⟨(HostCallLedger.input env).instruction, ?_, rfl⟩
    rw [← HostLocalCore.hostCallTable_projection witness]
    exact List.mem_map_of_mem (f := fun env => (HostCallLedger.input env).instruction) active
  · have clock := congrArg (fun message : HostCallChip.Message (ZMod p) =>
      clkNat message.clk_high message.clk_low) same
    exact clock.trans (call_time row)

/-- Matching a queue event's clock in the CPU inventory recovers its exact physical instruction
and full call. Clock uniqueness is derived from this ensemble's State/Byte projection. -/
theorem call_cpu_at
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel HostCallChip.channel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostLocalCore.localWitness witness))
    (row : Row (p := p)) (member : row ∈ TransitionView.readIndexedRows indices (queueTables witness) witness.data)
    (cpu : ExecutionRow p) (cpuMember : cpu ∈ LocalCore.executionRows (HostLocalCore.localWitness witness))
    (clock : StateMsg.timeNat (cpu.edge witness.data).1 = eventTime row) :
    ∃ env ∈ HostCallLedger.activeRows (HostLocalCore.hostCallTable witness) witness.data,
      HostCallLedger.call env = call row ∧ cpu = .syscall (HostCallLedger.input env).instruction := by
  obtain ⟨env, active, same, physical, atTime⟩ := call_cpu witness interface constraints balanced row member
  have unique := LocalCore.executionRows_times_nodup_of_orderingChannels (HostLocalCore.localWitness witness)
    (HostLocalCore.localWitness_constraints witness constraints)
    ordering
  simp_rw [ExecutionRow.edge_setData _ (HostLocalCore.localWitness witness).data witness.data] at unique
  exact ⟨env, active, same, List.inj_on_of_nodup_map unique cpuMember physical (clock.trans atTime.symm)⟩

/-- The actual queue-token walk is strictly ordered by CPU event times. -/
theorem times_pairwise {path : List (Row (p := p))} {initial final : State (ZMod p)}
    (walk : Walk.IsWalk edge initial final path)
    (valid : ∀ row ∈ path, (view row.1).component.Spec row.2) :
    (path.map eventTime).Pairwise (· < ·) :=
  RankedGrounding.targetRanks_pairwise_of_isWalk edge time walk
    (fun row member => view_strict row.1 row.2 (valid row member))

/-- Queue events occur in the same order in every exhaustive CPU walk. The subsequence includes
each physical queue occurrence exactly once; ordinary and queue-silent host events may intervene. -/
theorem clocks_sublist
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel HostCallChip.channel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostLocalCore.localWitness witness))
    (specs : ∀ table ∈ queueTables witness, table.Spec witness.data)
    {path : List (Row (p := p))} {initial final : State (ZMod p)}
    (queueExhaustive : path.Perm (TransitionView.readIndexedRows indices (queueTables witness) witness.data))
    (queueWalk : Walk.IsWalk edge initial final path)
    {cpu : List (ExecutionRow p)}
    (cpuExhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness witness)))
    (cpuWalk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu) :
    (path.map eventTime).Sublist (cpu.map fun row => StateMsg.timeNat (row.edge witness.data).1) := by
  have queueSorted := times_pairwise queueWalk
    (fun row member => rows_spec _ witness.data (queueTables_aligned witness) specs row (queueExhaustive.mem_iff.mp member))
  have edgeData : ExecutionRow.canonEdge (HostLocalCore.localWitness witness).data =
      ExecutionRow.canonEdge witness.data := funext fun row => row.canonEdge_setData _ _
  have publicInput : (HostLocalCore.localWitness witness).publicInput = witness.publicInput := rfl
  have cpuSorted := LocalCore.ordered_times_pairwise (HostLocalCore.localWitness witness)
    (HostLocalCore.localWitness_constraints witness constraints) ordering cpuExhaustive
    (by simpa only [edgeData, publicInput] using cpuWalk)
  simp_rw [ExecutionRow.edge_setData _ (HostLocalCore.localWitness witness).data witness.data] at cpuSorted
  apply List.sublist_of_subperm_of_pairwise _ queueSorted cpuSorted
  apply List.subperm_of_subset (queueSorted.imp ne_of_lt)
  intro stamp member
  obtain ⟨row, rowMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨env, _, _, physical, clock⟩ := call_cpu witness interface constraints balanced row
    (queueExhaustive.mem_iff.mp rowMember)
  exact List.mem_map.mpr ⟨.syscall (HostCallLedger.input env).instruction, cpuExhaustive.mem_iff.mpr physical, clock⟩

/-- Queue events selected by an actual CPU prefix, preserving the queue path's physical rows. -/
noncomputable def beforeCPU (data : ProverData (ZMod p)) (prior : List (ExecutionRow p))
    (path : List (Row (p := p))) : List (Row (p := p)) :=
  path.filter (fun row => decide (eventTime row ∈ prior.map (fun cpu => StateMsg.timeNat (cpu.edge data).1)))

/-- At a matched CPU event, the preceding CPU events select exactly the preceding queue events. -/
theorem beforeCPU_eq_prior (data : ProverData (ZMod p))
    {path queuePrior queueRest : List (Row (p := p))} {row : Row (p := p)}
    {cpuPrior cpuRest : List (ExecutionRow p)} {cpu : ExecutionRow p}
    (queueSplit : path = queuePrior ++ row :: queueRest)
    (queueSorted : (path.map eventTime).Pairwise (· < ·))
    (cpuSorted : ((cpuPrior ++ cpu :: cpuRest).map fun event => StateMsg.timeNat (event.edge data).1).Pairwise (· < ·))
    (included : (path.map eventTime).Sublist
      ((cpuPrior ++ cpu :: cpuRest).map fun event => StateMsg.timeNat (event.edge data).1))
    (clock : StateMsg.timeNat (cpu.edge data).1 = eventTime row) :
    beforeCPU data cpuPrior path = queuePrior := by
  rw [beforeCPU, List.filter_mem_prefix_eq_filter_lt _ eventTime path
    (List.pairwise_map.mp cpuSorted) included.subset, clock, queueSplit]
  exact List.filter_lt_eq_prefix eventTime (List.pairwise_map.mp (queueSplit ▸ queueSorted))

/-- Semantic queue history now supplies current bytes and frontier at a CPU position, without
an independently chosen queue prefix. Equality with the evolving host state remains a replay lemma. -/
theorem current_at_cpu (data : ProverData (ZMod p))
    {hints : List Bytes} {final : State (ZMod p)} {upper : HintQueue.Store}
    {path : List (Row (p := p))} (history : HostHintQueueHistory.History hints final upper path)
    (queueSorted : (path.map eventTime).Pairwise (· < ·))
    (row : Row (p := p)) (member : row ∈ path)
    {cpuPrior cpuRest : List (ExecutionRow p)} {cpu : ExecutionRow p}
    (cpuSorted : ((cpuPrior ++ cpu :: cpuRest).map fun event => StateMsg.timeNat (event.edge data).1).Pairwise (· < ·))
    (included : (path.map eventTime).Sublist
      ((cpuPrior ++ cpu :: cpuRest).map fun event => StateMsg.timeNat (event.edge data).1))
    (clock : StateMsg.timeNat (cpu.edge data).1 = eventTime row) :
    ∃ store current, HintQueue.Extends store upper ∧
      HintQueue.replay? ((beforeCPU data cpuPrior path).map HostQueueHistory.event) hints = some current ∧
      (edge row).1.Binds store current := by
  obtain ⟨prior, rest, split⟩ := List.mem_iff_append.mp member
  have selected := beforeCPU_eq_prior data split queueSorted cpuSorted included clock
  obtain ⟨_, _, _, bounded, _, _, prefixes⟩ := history
  obtain ⟨store, current, _, extended, replayed, binding⟩ := prefixes prior row rest split
  exact ⟨store, current, extended.trans bounded, selected ▸ replayed, binding⟩

/-- Before each queue syscall, its current bytes/frontier are determined by queue events in the
preceding CPU prefix. This does not assume or assert that the complete host replay succeeds. -/
def CurrentQueues (data : ProverData (ZMod p)) (hints : List Bytes) (upper : HintQueue.Store)
    (cpu : List (ExecutionRow p)) (path : List (Row (p := p))) : Prop :=
  ∀ prior event rest, cpu = prior ++ event :: rest →
    ∀ row ∈ path, StateMsg.timeNat (event.edge data).1 = eventTime row →
      ∃ store current, HintQueue.Extends store upper ∧
        HintQueue.replay? ((beforeCPU data prior path).map HostQueueHistory.event) hints = some current ∧
        (edge row).1.Binds store current

theorem currentQueues_of_order (data : ProverData (ZMod p))
    {hints : List Bytes} {final : State (ZMod p)} {upper : HintQueue.Store}
    {path : List (Row (p := p))} {cpu : List (ExecutionRow p)}
    (history : HostHintQueueHistory.History hints final upper path)
    (queueSorted : (path.map eventTime).Pairwise (· < ·))
    (cpuSorted : (cpu.map fun event => StateMsg.timeNat (event.edge data).1).Pairwise (· < ·))
    (included : (path.map eventTime).Sublist (cpu.map fun event => StateMsg.timeNat (event.edge data).1)) :
    CurrentQueues data hints upper cpu path := by
  intro prior event rest split row member clock
  exact current_at_cpu data history queueSorted row member (split ▸ cpuSorted) (split ▸ included) clock

private theorem ordered_history
    (witness : EnsembleWitness (ensemble image source HostCallReceivers.available resources channels names))
    (interface : ExtensionInterface HostCallReceivers.available resources)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannel HostCallChip.channel.toRaw)
    (ordering : LocalCore.OrderingChannels (HostLocalCore.localWitness witness))
    (specs : ∀ table ∈ queueTables witness, table.Spec witness.data)
    {hints : List Bytes} {upper : HintQueue.Store}
    {path : List (Row (p := p))} {initial final : State (ZMod p)}
    (history : HostHintQueueHistory.History hints final upper path)
    (queueExhaustive : path.Perm (TransitionView.readIndexedRows indices (queueTables witness) witness.data))
    (queueWalk : Walk.IsWalk edge initial final path)
    {cpu : List (ExecutionRow p)}
    (cpuExhaustive : cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness witness)))
    (cpuWalk : Walk.IsWalk (ExecutionRow.canonEdge witness.data)
      (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu) :
    (path.map eventTime).Sublist (cpu.map fun row => StateMsg.timeNat (row.edge witness.data).1) ∧
      CurrentQueues witness.data hints upper cpu path := by
  have included := clocks_sublist witness interface constraints balanced ordering specs
    queueExhaustive queueWalk cpuExhaustive cpuWalk
  have queueSorted := times_pairwise queueWalk
    (fun row member => rows_spec _ witness.data (queueTables_aligned witness) specs row (queueExhaustive.mem_iff.mp member))
  have edgeData : ExecutionRow.canonEdge (HostLocalCore.localWitness witness).data =
      ExecutionRow.canonEdge witness.data := funext fun row => row.canonEdge_setData _ _
  have publicInput : (HostLocalCore.localWitness witness).publicInput = witness.publicInput := rfl
  have cpuSorted := LocalCore.ordered_times_pairwise (HostLocalCore.localWitness witness)
    (HostLocalCore.localWitness_constraints witness constraints) ordering cpuExhaustive
    (by simpa only [edgeData, publicInput] using cpuWalk)
  simp_rw [ExecutionRow.edge_setData _ (HostLocalCore.localWitness witness).data witness.data] at cpuSorted
  exact ⟨included, currentQueues_of_order witness.data history queueSorted cpuSorted included⟩

/-- The installed source-only queue registry determines both exhaustive paths and their order
agreement from raw constraints and full balance. It retains arbitrary local CPU endpoints.
Successful whole-host replay, Memory grounding, and outgoing snapshot binding remain separate. -/
theorem source_history {final : State (ZMod p)} {bankFinal : HostState}
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ cpu : List (ExecutionRow p), ∃ path : List (Row (p := p)),
      cpu.Perm (LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))) ∧
      Walk.IsWalk (ExecutionRow.canonEdge witness.data)
        (initialBoundaryStateMessage witness.publicInput) (finalBoundaryStateMessage witness.publicInput) cpu ∧
      path.Perm (TransitionView.readIndexedRows indices (queueTables (HostHintQueueBoundary.projected witness)) witness.data) ∧
      Walk.IsWalk edge (SP1Clean.HostHintQueueBoundary.initial source.host.io.hints) final path ∧
      HostHintQueueHistory.History source.host.io.hints final (HintQueue.ofList source.host.io.hints).1 path ∧
      (path.map eventTime).Sublist (cpu.map fun row => StateMsg.timeNat (row.edge witness.data).1) ∧
      CurrentQueues witness.data source.host.io.hints (HintQueue.ofList source.host.io.hints).1 cpu path := by
  let retained := HostHintQueueBoundary.projected witness
  have checks : retained.Constraints := by exact HostHintQueueBoundary.projected_constraints witness constraints
  have interface := source_interface (p := p) source.host.io.hints
  have ordering := HostHintQueueBoundary.projected_orderingChannels witness interface constraints balanced
  have callBalance := HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced
  obtain ⟨cpu, cpuExhaustive, cpuWalk⟩ := HostLocalCore.executionRows_ordered_of_orderingChannels retained checks ordering
  obtain ⟨path, exhaustive, walk, history⟩ := HostHintQueueHistory.source_history witness constraints balanced
  refine ⟨cpu, path, cpuExhaustive, ?_, exhaustive, walk, history, ?_⟩
  · simpa only [retained, HostHintQueueBoundary.projected_data, HostHintQueueBoundary.projected_publicInput] using cpuWalk
  have included := ordered_history retained interface checks callBalance ordering
    (queue_specs retained interface _ (HostHintQueueBoundary.source_authentication witness constraints) checks
      (HostHintQueueBoundary.record_channels witness balanced))
    history (by simpa only [retained, HostHintQueueBoundary.projected_data] using exhaustive) walk cpuExhaustive cpuWalk
  simpa only [retained, HostHintQueueBoundary.projected_data] using included

end SP1Clean.Soundness.HostQueueCPUOrder
