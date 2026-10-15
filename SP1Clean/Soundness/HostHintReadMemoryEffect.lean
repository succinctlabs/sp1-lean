import SP1Clean.Soundness.HostHintReadTrajectory
import SP1Clean.Soundness.HostFootprint
import SP1Clean.Soundness.HostExecutionEffect

/-! # Hint execution and complete grounding effects

The complete physical word inventory identifies every updated Sail RAM cell, including the
mandatory padding word. Canonical RAM keys derive destination alignment; cells outside that
inventory are unchanged. The installed AIR derives a real host execution at the exact next
paired-replay position, authenticating the complete event including its PC and recombined clock.
HINT_LEN observes the actual queue and has a proved empty added-word footprint. Both calls share
the timed grounding argument, retaining the instruction's registers and all host RAM accesses.
Complete outgoing snapshot agreement remains a separate whole-shard obligation.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal TimedGrounding

private theorem hint_word_written {execution : HostExecution} {address : ℕ} {bytes : Bytes}
    (written : execution.effect.write = some ⟨address, hintWriteBytes bytes⟩)
    (source : SailState) (pc : BitVec 64) (cell : RamCell) (entry : ℕ × BitVec 64)
    (member : entry ∈ HintQueue.wordWrites address bytes) (atAddress : cell.baseAddr.toNat = entry.1) :
    locContent (execution.apply source pc) (.ram cell) = some entry.2 := by
  obtain ⟨index, bound, rfl⟩ := List.mem_map.mp member
  have inside := List.mem_range.mp bound
  have full : 8 * index + 8 ≤ (hintWriteBytes bytes).length := by
    rw [HintQueue.wordCount_length]
    omega
  have read := hostExecution_written_word written source pc index full cell (by
    simpa only [Nat.mul_comm] using atAddress)
  rw [read]
  apply congrArg some
  change Word.bytesValue _ = Word.bytesValue (HintQueue.wordBytes bytes index)
  apply congrArg Word.bytesValue
  apply Vector.ext
  intro slot small
  have value := HintQueue.wordValue_byte bytes inside ⟨slot, small⟩
  rw [HintQueue.wordValue, Word.bytesValue_extract] at value
  simpa only [HostMemoryWrite.wordBytes, Vector.getElem_ofFn, Fin.getElem_fin, Nat.mul_comm]
    using value.symm

private theorem hint_cell_covered (address : ℕ) (bytes : Bytes) (aligned : address % 8 = 0)
    (cell : RamCell)
    (covered : cell.toNat ∈ (MemorySpan.mk address (hintWriteBytes bytes).length).cells) :
    ∃ word, (cell.baseAddr.toNat, word) ∈ HintQueue.wordWrites address bytes := by
  rw [MemorySpan.mem_cells, HintQueue.wordCount_length] at covered
  dsimp only at covered
  have quotient := Nat.mod_add_div address 8
  rw [aligned] at quotient
  have bound : cell.toNat - address / 8 < HintQueue.wordCount bytes := by omega
  refine ⟨HintQueue.wordValue bytes (cell.toNat - address / 8), List.mem_map.mpr
    ⟨cell.toNat - address / 8, List.mem_range.mpr bound, ?_⟩⟩
  congr 1
  rw [RamCell.baseAddr_toNat]
  omega

private theorem hint_write_frame {execution : HostExecution} {address : ℕ} {bytes : Bytes}
    (written : execution.effect.write = some ⟨address, hintWriteBytes bytes⟩)
    (aligned : address % 8 = 0) (source : SailState) (pc : BitVec 64) (cell : RamCell)
    (outside : ∀ entry ∈ HintQueue.wordWrites address bytes, entry.1 ≠ cell.baseAddr.toNat) :
    locContent (execution.apply source pc) (.ram cell) = locContent source (.ram cell) := by
  have excluded : cell.toNat ∉ (MemorySpan.mk address (hintWriteBytes bytes).length).cells := by
    intro covered
    obtain ⟨word, member⟩ := hint_cell_covered address bytes aligned cell covered
    exact outside _ member rfl
  apply locContent_ram_congr_cell
  intro slot
  change (execution.effect.applyMemory source.mem).get? (cell.baseAddr.toNat + slot.val) = _
  simp only [HostEffect.applyMemory, written]
  apply HostMemoryWrite.read_outside
  have outsideByte := MemorySpan.byte_outside ⟨address, (hintWriteBytes bytes).length⟩
    cell.toNat slot.val slot.isLt excluded
  simpa only [RamCell.baseAddr_toNat] using outsideByte

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance effectLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem word_cell (row : HintReadCoverage.Row (p := p))
    (facts : HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram) :
    ∃ cell : RamCell, MemoryMsg.locOf (touch row).2 = .ram cell ∧
      cell.baseAddr.toNat = (HintReadWrites.produced row).1 := by
  have lower := facts.ram.1
  rw [facts.canonical.2.2] at lower
  change 2 ^ 16 ≤ (MemoryMsg.locOf (touch row).2).busAddress at lower
  cases located : MemoryMsg.locOf (touch row).2 with
  | reg index =>
    rw [located] at lower
    change 2 ^ 16 ≤ index.toNat at lower
    have bounded := index.isLt
    omega
  | ram cell =>
    refine ⟨cell, rfl, ?_⟩
    have address := address_loc row facts
    simpa only [located, MemLoc.busAddress, RamCell.baseAddr_toNat] using address.symm

omit [Fact (2 ^ 25 < p)] in
private theorem write_alignment (rows : List (HintReadCoverage.Row (p := p)))
    (facts : ∀ row ∈ rows, HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram)
    (address : ℕ) (bytes : Bytes)
    (inventory : (rows.map HintReadWrites.produced).Perm (HintQueue.wordWrites address bytes)) :
    address % 8 = 0 := by
  have first : (address, HintQueue.wordValue bytes 0) ∈ HintQueue.wordWrites address bytes := by
    apply List.mem_map.mpr
    exact ⟨0, List.mem_range.mpr (HintQueue.wordCount_pos bytes), by simp⟩
  obtain ⟨row, member, same⟩ := List.mem_map.mp (inventory.mem_iff.mpr first)
  obtain ⟨cell, _, atAddress⟩ := word_cell row (facts row member)
  have base : cell.baseAddr.toNat = address := atAddress.trans (congrArg Prod.fst same)
  rw [← base, RamCell.baseAddr_toNat]
  omega

omit [Fact (2 ^ 25 < p)] in
/-- The complete physical inventory realizes every pushed RAM word and preserves every other
RAM cell. No assumption about overwritten values or previous Memory records is needed. -/
theorem hint_memory_effect (input : HostHintReadChip.Inputs (ZMod p)) (host : HostState)
    (bytes : Bytes) (rest : List Bytes) (rows : List (HintReadCoverage.Row (p := p)))
    (facts : ∀ row ∈ rows, HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram)
    (inventory : (rows.map HintReadWrites.produced).Perm
      (HintQueue.wordWrites (Address.toNat input.span.start) bytes))
    (source : SailState) (pc : BitVec 64) :
    (∀ row ∈ rows, locContent ((HostHintReadChip.execution input host bytes rest).apply source pc)
        (MemoryMsg.locOf (touch row).2) = some (Word.toBitVec64 (touch row).2.value)) ∧
      (∀ cell : RamCell, (∀ row ∈ rows, MemoryMsg.locOf (touch row).2 ≠ .ram cell) →
        locContent ((HostHintReadChip.execution input host bytes rest).apply source pc) (.ram cell) =
          locContent source (.ram cell)) := by
  constructor
  · intro row member
    obtain ⟨cell, located, address⟩ := word_cell row (facts row member)
    rw [located]
    exact hint_word_written (execution := HostHintReadChip.execution input host bytes rest) rfl
      source pc cell (HintReadWrites.produced row)
      (inventory.mem_iff.mp (List.mem_map_of_mem member)) address
  · intro cell outside
    apply hint_write_frame (execution := HostHintReadChip.execution input host bytes rest) rfl
      (write_alignment rows facts _ bytes inventory) source pc cell
    intro entry member same
    obtain ⟨row, rowMem, rowEq⟩ := List.mem_map.mp (inventory.mem_iff.mpr member)
    obtain ⟨actual, located, address⟩ := word_cell row (facts row rowMem)
    have equalAddress : actual.baseAddr.toNat = cell.baseAddr.toNat :=
      address.trans ((congrArg Prod.fst rowEq).trans same)
    have equal : actual = cell := by
      apply BitVec.eq_of_toNat_eq
      rw [RamCell.baseAddr_toNat, RamCell.baseAddr_toNat] at equalAddress
      omega
    exact outside row rowMem (located.trans (congrArg MemLoc.ram equal))

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

omit [Fact (2 ^ 25 < p)] in
private theorem hint_event (wrapper : HostCallChip.Inputs (ZMod p)) (flag : ZMod p)
    (input : HostHintReadChip.Inputs (ZMod p)) (host : HostState) (bytes : Bytes) (rest : List Bytes)
    (same : wrapper.message flag = input.call)
    (code : Word.toBitVec64 (wrapper.message flag).code = SyscallKind.hintRead.code)
    (law : (syscallEventOfRow wrapper.instruction).RowLaw)
    (clock : ℕ) (atClock : clock = (syscallEventOfRow wrapper.instruction).clock) :
    (HostHintReadChip.execution input host bytes rest).toEvent clock
      (StateMsg.pcBits (SyscallInstrsChip.statePulledMessage wrapper.instruction)) =
        syscallEventOfRow wrapper.instruction := by
  have raw : (syscallEventOfRow wrapper.instruction).rawCode = SyscallKind.hintRead.code := code
  have next := law.2.2.1
  simp only [Machine.CoreSyscallEvent.PcLaw, Machine.CoreSyscallEvent.syscallId, raw,
    SyscallKind.code, Machine.haltSyscallId] at next
  change (syscallEventOfRow wrapper.instruction).nextPc = (syscallEventOfRow wrapper.instruction).pc + 4 at next
  have arg1 : Word.toBitVec64 input.call.arg1 = (syscallEventOfRow wrapper.instruction).arg1 := by
    rw [← same]; rfl
  have arg2 : Word.toBitVec64 input.call.arg2 = (syscallEventOfRow wrapper.instruction).arg2 := by
    rw [← same]; rfl
  have result : Word.toBitVec64 input.call.result = (syscallEventOfRow wrapper.instruction).result := by
    rw [← same]; rfl
  have pc : StateMsg.pcBits (SyscallInstrsChip.statePulledMessage wrapper.instruction) =
      (syscallEventOfRow wrapper.instruction).pc := rfl
  have stamp : clock = (syscallEventOfRow wrapper.instruction).clock := atClock
  simp only [HostExecution.toEvent, HostHintReadChip.execution, HostExecution.nextPc,
    reduceCtorEq, ↓reduceIte, arg1, arg2, result, pc, stamp, ← raw, ← next]

omit [Fact (2 ^ 25 < p)] in
private theorem length_event (wrapper : HostCallChip.Inputs (ZMod p)) (flag : ZMod p)
    (input : HostHintLengthChip.Inputs (ZMod p)) (host : HostState)
    (same : wrapper.message flag = input.call)
    (code : Word.toBitVec64 (wrapper.message flag).code = SyscallKind.hintLength.code)
    (law : (syscallEventOfRow wrapper.instruction).RowLaw)
    (clock : ℕ) (atClock : clock = (syscallEventOfRow wrapper.instruction).clock) :
    (HostHintLengthChip.execution input host).toEvent clock
      (StateMsg.pcBits (SyscallInstrsChip.statePulledMessage wrapper.instruction)) =
        syscallEventOfRow wrapper.instruction := by
  have raw : (syscallEventOfRow wrapper.instruction).rawCode = SyscallKind.hintLength.code := code
  have next := law.2.2.1
  simp only [Machine.CoreSyscallEvent.PcLaw, Machine.CoreSyscallEvent.syscallId, raw,
    SyscallKind.code, Machine.haltSyscallId] at next
  change (syscallEventOfRow wrapper.instruction).nextPc = (syscallEventOfRow wrapper.instruction).pc + 4 at next
  have arg1 : Word.toBitVec64 input.call.arg1 = (syscallEventOfRow wrapper.instruction).arg1 := by
    rw [← same]; rfl
  have arg2 : Word.toBitVec64 input.call.arg2 = (syscallEventOfRow wrapper.instruction).arg2 := by
    rw [← same]; rfl
  have result : Word.toBitVec64 input.call.result = (syscallEventOfRow wrapper.instruction).result := by
    rw [← same]; rfl
  have pc : StateMsg.pcBits (SyscallInstrsChip.statePulledMessage wrapper.instruction) =
      (syscallEventOfRow wrapper.instruction).pc := rfl
  have stamp : clock = (syscallEventOfRow wrapper.instruction).clock := atClock
  simp only [HostExecution.toEvent, HostHintLengthChip.execution, HostExecution.nextPc,
    reduceCtorEq, ↓reduceIte, arg1, arg2, result, pc, stamp, ← raw, ← next]

private theorem source_memory_effect
    (witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (env : Environment (ZMod p))
    (handler : env ∈ (handlerTable (HostHintQueueBoundary.projected witness)).table.map
      (Environment.fromArray · witness.data))
    (clock : StateMsg.timeNat (event.edge witness.data).1 = HostQueueCPUOrder.eventTime (none, env))
    (host : HostState) (bytes : Bytes) (remaining : List Bytes)
    (inventory : ((TransitionView.readIndexedRows HintReadCoverage.variants
      (HostHintReadPartition.tablesFor (HostHintReadPartition.callClock env)
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data
        (wordTables_aligned (HostHintQueueBoundary.projected witness))) witness.data).map HintReadWrites.produced).Perm
      (HintQueue.wordWrites (Address.toNat (HostHintReadCoverage.input env).span.start) bytes))
    (state : SailState) (pc : BitVec 64) :
    (∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event,
      locContent ((HostHintReadChip.execution (HostHintReadCoverage.input env) host bytes remaining).apply state pc)
        (MemoryMsg.locOf (touch row).2) = some (Word.toBitVec64 (touch row).2.value)) ∧
    (∀ cell : RamCell, (∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event, MemoryMsg.locOf (touch row).2 ≠ .ram cell) →
      locContent ((HostHintReadChip.execution (HostHintReadCoverage.input env) host bytes remaining).apply state pc)
        (.ram cell) = locContent state (.ram cell)) := by
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have interface := source_interface (p := p) source.host.io.hints
  have calls := HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced
  have ordering := HostHintQueueBoundary.projected_orderingChannels witness interface constraints balanced
  have selected := handler_wordsAt (HostHintQueueBoundary.projected witness) interface checks calls ordering
  simp only [HostHintQueueBoundary.projected_data] at selected
  have selected := selected event member env handler clock
  have writes : ((wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
      (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).map HintReadWrites.produced).Perm
      (HintQueue.wordWrites (Address.toNat (HostHintReadCoverage.input env).span.start) bytes) := by
    rw [selected]
    exact inventory
  have accesses := source_word_touches witness constraints balanced
  simp only [HostHintQueueBoundary.projected_data] at accesses
  exact hint_memory_effect (HostHintReadCoverage.input env) host bytes remaining _
    (fun row present => accesses row (List.mem_filter.mp present).1)
    writes state pc

/-- The physical HINT_READ executes at its exact position on paired replay. Its semantic
successor realizes all grouped RAM pushes and preserves every other RAM cell. The only semantic
antecedents are the incoming State and operand currency supplied by timed grounding. -/
theorem GroundingCarrier.hintRead_step (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (env : Environment (ZMod p))
    (handler : env ∈ (handlerTable (HostHintQueueBoundary.projected witness)).table.map
      (Environment.fromArray · witness.data))
    (clock : StateMsg.timeNat (event.edge witness.data).1 = HostQueueCPUOrder.eventTime (none, env))
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (event.facts witness.data).statePull)
    (currency : ∀ mp ∈ (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ∃ n current next, carrier.ordered[n]? = some event ∧
      carrier.pairedTrajectory valid n = some current ∧ carrier.pairedTrajectory valid (n + 1) = some next ∧
      ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current event.event next ∧
      (∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event,
        locContent next.sail (MemoryMsg.locOf (touch row).2) = some (Word.toBitVec64 (touch row).2.value)) ∧
      (∀ cell : RamCell, (∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event, MemoryMsg.locOf (touch row).2 ≠ .ram cell) →
        locContent next.sail (.ram cell) = locContent current.sail (.ram cell)) := by
  obtain ⟨n, current, _, bytes, remaining, atIndex, paired, _, _, _, ran, inventory⟩ :=
    carrier.hintRead_run valid constraints balanced event member env handler clock pull
      (fun mp present => (currency mp present).2.2)
  have time := ExecutionCarrier.time_of_ordered_at carrier atIndex
  change StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n at time
  have before : carrier.trajectory valid n = some current.sail := by
    simp only [GroundingCarrier.trajectory, paired, Option.map_some]
  obtain ⟨m, state, present, atTime, atPc, rom, _⟩ := pull
  have sameIndex : m = n := start_injective carrier.timeline (atTime.symm.trans time)
  subst m
  have sail : current.sail = state := Option.some.inj (before.symm.trans present)
  rw [← sail] at atPc rom
  have covered : n ≤ carrier.events.length := by
    have bound := (List.getElem?_eq_some_iff.mp atIndex).1
    simpa only [ExecutionCarrier.events, List.length_map] using Nat.le_of_lt bound
  have currentTime : current.clock = carrier.timeline.start n := by
    rw [carrier.timeline_events constraints balanced, eventTimeline_start_le _ _ _ covered]
    exact replayEvents?_clock paired
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have interface := source_interface (p := p) source.host.io.hints
  have calls := HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced
  have ordering := HostHintQueueBoundary.projected_orderingChannels witness interface constraints balanced
  have program := HostHintQueueBoundary.projected_core_balancedChannel witness balanced programChannel.toRaw
    (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])
  have byteBalance := (HostHintQueueBoundary.record_channels witness balanced).byte
  have handlerMember : (none, env) ∈ TransitionView.readIndexedRows HostQueueOrder.indices
      (queueTables (HostHintQueueBoundary.projected witness)) witness.data := by
    obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp handler
    simp only [TransitionView.readIndexedRows, HostQueueOrder.indices, queueTables,
      List.zip_cons_cons, List.flatMap_cons]
    exact List.mem_append_left _ (List.mem_map_of_mem physicalMem)
  have matched := HostQueueCPUOrder.call_cpu_at (HostHintQueueBoundary.projected witness) interface checks calls ordering
  simp only [HostHintQueueBoundary.projected_data] at matched
  obtain ⟨physical, active, sameCall, sameEvent⟩ := matched (none, env) handlerMember event member clock
  have original : ∀ mp ∈ (syscallRowFacts (HostCallLedger.input physical).instruction).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
    intro mp present
    apply currency mp
    apply List.mem_append_left
    simpa only [sameEvent, ExecutionRow.facts] using present
  have instructionTime : StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
      (HostCallLedger.input physical).instruction) = carrier.timeline.start n := by
    simpa only [sameEvent, ExecutionRow.facts, syscallRowFacts_statePull] using time
  have registers := HostLocalCore.hostCall_registers valid (HostHintQueueBoundary.projected witness)
    (source_program_silent source) checks program
  simp only [HostHintQueueBoundary.projected_data] at registers
  have registers := registers physical active _ source.sail.realize current.sail _ n
    before instructionTime (fun mp present => (original mp present).2.2)
  have law := HostLocalCore.hostCall_eventLaw (HostHintQueueBoundary.projected witness)
    (auxiliaryInterface interface) (source_program_silent source) checks program byteBalance
  simp only [HostHintQueueBoundary.projected_data] at law
  have law := law physical active
    (fun mp present => ⟨(original mp present).1, (original mp present).2.1⟩)
  have observed := (current.host.run_eq_some_iff _ _ _).mp ran
  have code := Option.some.inj (registers.1.symm.trans observed.2.1)
  have label := hint_event (HostCallLedger.input physical) _ (HostHintReadCoverage.input env)
    current.host bytes remaining sameCall code law.1 current.clock
    (currentTime.trans (instructionTime.symm.trans law.2.symm))
  have committed := HostLocalCore.hostCall_program_committed valid (HostHintQueueBoundary.projected witness)
    (source_program_silent source) checks program
  simp only [HostHintQueueBoundary.projected_data] at committed
  have committed := committed physical active
  have fetched := (committed.ecall_of_opcode rfl).1
  change (image.toGuestProgram valid).fetchWord
    (StateMsg.pcBits (SyscallInstrsChip.statePulledMessage (HostCallLedger.input physical).instruction)) =
      some Target.ECALL_ENC at fetched
  change current.sail.regs.get? LeanRV64D.Defs.Register.PC =
    some (StateMsg.pcBits (event.facts witness.data).statePull) at atPc
  have sourcePc : StateMsg.pcBits (event.facts witness.data).statePull =
      StateMsg.pcBits (SyscallInstrsChip.statePulledMessage (HostCallLedger.input physical).instruction) := by
    rw [sameEvent]; rfl
  let execution := HostHintReadChip.execution (HostHintReadCoverage.input env) current.host bytes remaining
  let next : ExecutionState := ⟨execution.apply current.sail (StateMsg.pcBits (event.facts witness.data).statePull),
    execution.effect.state, current.clock + Machine.syscallSchedule.duration⟩
  have step : ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current event.event next := by
    have stepped : current.host.step ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        current.clock current.sail = some (execution.effect.state, next.sail,
          syscallEventOfRow (HostCallLedger.input physical).instruction) := by
      have loaded := InstructionBytes.check_of_romLoaded rom fetched
      simp only [HostState.step, atPc, Bind.bind, Option.bind_some, sourcePc, fetched, loaded,
        and_self, ↓reduceIte, ran]
      simp only [next, execution, sourcePc, label]
    rw [sameEvent]
    exact ExecutionStep.syscall stepped
  have after : carrier.pairedTrajectory valid (n + 1) = some next := by
    change ExecutionCarrier.pairedTrajectory carrier _ _ _ (n + 1) = _
    rw [ExecutionCarrier.pairedTrajectory_succ carrier _ _ _ member time]
    change (carrier.pairedTrajectory valid n).bind _ = _
    rw [paired, Option.bind_some, step.replay]
  have effect := source_memory_effect witness constraints balanced event member env handler clock
    current.host bytes remaining inventory current.sail (StateMsg.pcBits (event.facts witness.data).statePull)
  exact ⟨n, current, next, atIndex, paired, after, step, effect⟩

private theorem length_not_read (event : ExecutionRow p) (wrapper : HostCallChip.Inputs (ZMod p))
    (flag : ZMod p) (same : event = .syscall wrapper.instruction)
    (code : Word.toBitVec64 (wrapper.message flag).code = SyscallKind.hintLength.code) :
    ∀ row, event = .syscall row → (syscallEventOfRow row).rawCode ≠ SyscallKind.hintRead.code := by
  intro row rowEq
  have sameRow := ExecutionRow.syscall.inj (same.symm.trans rowEq)
  rw [← sameRow]
  change Word.toBitVec64 (wrapper.message flag).code ≠ SyscallKind.hintRead.code
  rw [code]
  decide

/-- The physical HINT_LEN executes at its paired-replay position and preserves RAM. Its empty
added-word footprint follows from authenticated HINT_READ ownership and CPU clock uniqueness. -/
theorem GroundingCarrier.hintLength_step (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (empty : Bool) (env : Environment (ZMod p))
    (handler : (some empty, env) ∈ TransitionView.readIndexedRows HostQueueOrder.indices
      (queueTables (HostHintQueueBoundary.projected witness)) witness.data)
    (clock : StateMsg.timeNat (event.edge witness.data).1 = HostQueueCPUOrder.eventTime (some empty, env))
    (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (event.facts witness.data).statePull)
    (currency : ∀ mp ∈ (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ∃ n current next, carrier.ordered[n]? = some event ∧
      carrier.pairedTrajectory valid n = some current ∧ carrier.pairedTrajectory valid (n + 1) = some next ∧
      ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current event.event next ∧
      (∀ cell : RamCell, locContent next.sail (.ram cell) = locContent current.sail (.ram cell)) ∧
      wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event = [] := by
  obtain ⟨n, current, atIndex, paired, ran⟩ :=
    carrier.hintLength_run valid constraints balanced event member empty env handler clock pull
      (fun mp present => (currency mp present).2.2)
  have time := ExecutionCarrier.time_of_ordered_at carrier atIndex
  change StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n at time
  have before : carrier.trajectory valid n = some current.sail := by
    simp only [GroundingCarrier.trajectory, paired, Option.map_some]
  obtain ⟨m, state, present, atTime, atPc, rom, _⟩ := pull
  have sameIndex : m = n := start_injective carrier.timeline (atTime.symm.trans time)
  subst m
  have sail : current.sail = state := Option.some.inj (before.symm.trans present)
  rw [← sail] at atPc rom
  have covered : n ≤ carrier.events.length := by
    have bound := (List.getElem?_eq_some_iff.mp atIndex).1
    simpa only [ExecutionCarrier.events, List.length_map] using Nat.le_of_lt bound
  have currentTime : current.clock = carrier.timeline.start n := by
    rw [carrier.timeline_events constraints balanced, eventTimeline_start_le _ _ _ covered]
    exact replayEvents?_clock paired
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have interface := source_interface (p := p) source.host.io.hints
  have calls := HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced
  have ordering := HostHintQueueBoundary.projected_orderingChannels witness interface constraints balanced
  have program := HostHintQueueBoundary.projected_core_balancedChannel witness balanced programChannel.toRaw
    (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])
  have byteBalance := (HostHintQueueBoundary.record_channels witness balanced).byte
  have matched := HostQueueCPUOrder.call_cpu_at (HostHintQueueBoundary.projected witness) interface checks calls ordering
  simp only [HostHintQueueBoundary.projected_data] at matched
  obtain ⟨physical, active, sameCall, sameEvent⟩ := matched (some empty, env) handler event member clock
  have original : ∀ mp ∈ (syscallRowFacts (HostCallLedger.input physical).instruction).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
    intro mp present
    apply currency mp
    apply List.mem_append_left
    simpa only [sameEvent, ExecutionRow.facts] using present
  have instructionTime : StateMsg.timeNat (SyscallInstrsChip.statePulledMessage
      (HostCallLedger.input physical).instruction) = carrier.timeline.start n := by
    simpa only [sameEvent, ExecutionRow.facts, syscallRowFacts_statePull] using time
  have registers := HostLocalCore.hostCall_registers valid (HostHintQueueBoundary.projected witness)
    (source_program_silent source) checks program
  simp only [HostHintQueueBoundary.projected_data] at registers
  have registers := registers physical active _ source.sail.realize current.sail _ n
    before instructionTime (fun mp present => (original mp present).2.2)
  have law := HostLocalCore.hostCall_eventLaw (HostHintQueueBoundary.projected witness)
    (auxiliaryInterface interface) (source_program_silent source) checks program byteBalance
  simp only [HostHintQueueBoundary.projected_data] at law
  have law := law physical active
    (fun mp present => ⟨(original mp present).1, (original mp present).2.1⟩)
  have observed := (current.host.run_eq_some_iff _ _ _).mp ran
  have code := Option.some.inj (registers.1.symm.trans observed.2.1)
  have label := length_event (HostCallLedger.input physical) _ (valueFromOffset HostHintLengthChip.Inputs 0 env)
    current.host sameCall code law.1 current.clock
    (currentTime.trans (instructionTime.symm.trans law.2.symm))
  have committed := HostLocalCore.hostCall_program_committed valid (HostHintQueueBoundary.projected witness)
    (source_program_silent source) checks program
  simp only [HostHintQueueBoundary.projected_data] at committed
  have committed := committed physical active
  have fetched := (committed.ecall_of_opcode rfl).1
  change (image.toGuestProgram valid).fetchWord
    (StateMsg.pcBits (SyscallInstrsChip.statePulledMessage (HostCallLedger.input physical).instruction)) =
      some Target.ECALL_ENC at fetched
  change current.sail.regs.get? LeanRV64D.Defs.Register.PC =
    some (StateMsg.pcBits (event.facts witness.data).statePull) at atPc
  have sourcePc : StateMsg.pcBits (event.facts witness.data).statePull =
      StateMsg.pcBits (SyscallInstrsChip.statePulledMessage (HostCallLedger.input physical).instruction) := by
    rw [sameEvent]; rfl
  let execution := HostHintLengthChip.execution (valueFromOffset HostHintLengthChip.Inputs 0 env) current.host
  let next : ExecutionState := ⟨execution.apply current.sail (StateMsg.pcBits (event.facts witness.data).statePull),
    execution.effect.state, current.clock + Machine.syscallSchedule.duration⟩
  have step : ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current event.event next := by
    have stepped : current.host.step ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        current.clock current.sail = some (execution.effect.state, next.sail,
          syscallEventOfRow (HostCallLedger.input physical).instruction) := by
      have loaded := InstructionBytes.check_of_romLoaded rom fetched
      simp only [HostState.step, atPc, Bind.bind, Option.bind_some, sourcePc, fetched, loaded,
        and_self, ↓reduceIte, ran]
      simp only [next, execution, sourcePc, label]
    rw [sameEvent]
    exact ExecutionStep.syscall stepped
  have after : carrier.pairedTrajectory valid (n + 1) = some next := by
    change ExecutionCarrier.pairedTrajectory carrier _ _ _ (n + 1) = _
    rw [ExecutionCarrier.pairedTrajectory_succ carrier _ _ _ member time]
    change (carrier.pairedTrajectory valid n).bind _ = _
    rw [paired, Option.bind_some, step.replay]
  have noWords := source_wordsAt_nil_of_not_read witness constraints balanced event member
    (length_not_read event (HostCallLedger.input physical) _ sameEvent code)
  exact ⟨n, current, next, atIndex, paired, after, step, fun _ => rfl, noWords⟩

private theorem register_push_truth (row : SyscallInstrsChip.Inputs (ZMod p))
    (real : row.is_real = 1) (spec : SyscallInstrsChip.Spec row)
    (pulled : SyscallInstrsChip.PulledFacts row) (operand : row.op_a = 5)
    (trajectory : Trajectory) (initial next : SailState) (timeline : Timeline) (n : ℕ)
    (after : trajectory (n + 1) = some next)
    (time : StateMsg.timeNat (syscallRowFacts row).statePull = timeline.start n)
    (result : next.get_reg? 5 = some (syscallEventOfRow row).result)
    (currency : ∀ mp ∈ (syscallRowFacts row).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG trajectory initial timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ∀ message ∈ (syscallRowFacts row).memPushes, LocalMemTruthG trajectory initial timeline message := by
  have bounds := spec.2.1 real
  change StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) = timeline.start n at time
  obtain ⟨timeA, boundA⟩ := syscallRow_memPush_time row bounds.1 bounds.2
    row.op_a row.op_a_value 4 (by norm_num) 4 rfl
  obtain ⟨timeB, boundB⟩ := syscallRow_memPush_time row bounds.1 bounds.2
    row.op_b row.op_b_memory.prev_value 3 (by norm_num) 3 rfl
  obtain ⟨timeC, boundC⟩ := syscallRow_memPush_time row bounds.1 bounds.2
    row.op_c row.op_c_memory.prev_value 2 (by norm_num) 2 rfl
  have currB := currency _ (by rw [syscallRowFacts_memPulls]; exact List.mem_cons_of_mem _ List.mem_cons_self)
  have currC := currency _ (by
    rw [syscallRowFacts_memPulls]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
  intro message member
  rw [syscallRowFacts_memPushes] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · refine ⟨(pulled real).2.2.2.2.2.2.2.2.2.2.2, boundA, ?_⟩
    have located := (syscallRow_locOf_reg row (i := 5) operand.symm row.op_a_memory row.op_a_value 4).2
    change microValueG trajectory initial timeline _ _ = _
    rw [located, timeA, time, microValueG_reg_post (n := n) le_rfl (by have := timeline.gap n; omega),
      after, Option.bind_some]
    exact result
  · refine ⟨currB.1, boundB, ?_⟩
    rw [LocalValueAtG, timeB]
    exact currB.2.2
  · refine ⟨currC.1, boundC, ?_⟩
    rw [LocalValueAtG, timeC]
    exact currC.2.2

omit [Fact (2 ^ 25 < p)] in
private theorem word_push_truth (row : HintReadCoverage.Row (p := p))
    (facts : HostRamTouches.AccessFacts (HintReadCoverage.rowInput row).ram)
    (trajectory : Trajectory) (initial next : SailState) (timeline : Timeline) (n : ℕ)
    (after : trajectory (n + 1) = some next)
    (aligned : TouchOK (timeline.start n) (touch row).1 (touch row).2)
    (current : LocalValueAtG trajectory initial timeline (MemoryMsg.locOf (touch row).1.1)
      (touch row).1.2 (touch row).1.1.value)
    (written : locContent next (MemoryMsg.locOf (touch row).2) = some (Word.toBitVec64 (touch row).2.value)) :
    LocalMemTruthG trajectory initial timeline (touch row).2 := by
  refine ⟨facts.value, facts.pushLow, ?_⟩
  rcases aligned.push_kind with ⟨sameValue, sameTime⟩ | atWrite
  · rw [LocalValueAtG, sameTime, sameValue, aligned.loc_eq]
    exact current
  · obtain ⟨cell, located, _⟩ := word_cell row facts
    rw [located, writeOffset] at atWrite
    change microValueG trajectory initial timeline _ _ = _
    rw [located, atWrite, microValueG_ram_post (n := n) le_rfl (by have := timeline.gap n; omega),
      after, Option.bind_some]
    rwa [located] at written

omit [Fact (2 ^ 25 < p)] in
private theorem hint_frame [Fact (2 ^ 17 < p)]
    (row : SyscallInstrsChip.Inputs (ZMod p)) (operand : row.op_a = 5)
    (words : List (HintReadCoverage.Row (p := p)))
    (trajectory : Trajectory) (initial current next : SailState) (timeline : Timeline) (n : ℕ)
    (before : trajectory n = some current) (after : trajectory (n + 1) = some next)
    (result : next.get_reg? 5 = some (syscallEventOfRow row).result)
    (registers : ∀ index : BitVec 5, index ≠ 5 → next.get_reg? index = current.get_reg? index)
    (written : ∀ word ∈ words, locContent next (MemoryMsg.locOf (touch word).2) =
      some (Word.toBitVec64 (touch word).2.value))
    (unchanged : ∀ cell : RamCell, (∀ word ∈ words, MemoryMsg.locOf (touch word).2 ≠ .ram cell) →
      locContent next (.ram cell) = locContent current (.ram cell)) :
    ∀ loc value,
      (∀ message ∈ (syscallRowFacts row).memPushes ++ words.map (fun word => (touch word).2),
        MemoryMsg.locOf message = loc → message.value = value) →
      LocalValueAtG trajectory initial timeline loc (timeline.start n) value →
      LocalValueAtG trajectory initial timeline loc (timeline.start (n + 1)) value := by
  intro loc value pushes currency
  have content := (localValueAtG_stepStart_iff before).mp currency
  apply (localValueAtG_stepStart_iff after).mpr
  cases loc with
  | reg index =>
    by_cases isReturn : index = 5
    · subst index
      have located := (syscallRow_locOf_reg row (i := 5) operand.symm row.op_a_memory row.op_a_value 4).2
      have valueEq : row.op_a_value = value := pushes _
        (List.mem_append_left _ (by rw [syscallRowFacts_memPushes]; exact List.mem_cons_self)) located
      change next.get_reg? 5 = _
      have returned : next.get_reg? 5 = some (Word.toBitVec64 row.op_a_value) := result
      rwa [valueEq] at returned
    · change next.get_reg? index = _
      rw [registers index isReturn]
      exact content
  | ram cell =>
    by_cases touched : ∃ word ∈ words, MemoryMsg.locOf (touch word).2 = .ram cell
    · obtain ⟨word, member, located⟩ := touched
      have valueEq := pushes _ (List.mem_append_right _ (List.mem_map_of_mem member)) located
      have wordValue := written word member
      rwa [located, valueEq] at wordValue
    · rw [unchanged cell (by simpa only [not_exists, not_and] using touched)]
      exact content

omit [Fact (2 ^ 25 < p)] in
private theorem syscall_state_push (row : SyscallInstrsChip.Inputs (ZMod p))
    (program : Target.GuestProgram) (trajectory : Trajectory) (next : SailState) (timeline : Timeline) (n : ℕ)
    (after : trajectory (n + 1) = some next)
    (time : StateMsg.timeNat (syscallRowFacts row).statePush = timeline.start (n + 1))
    (pc : next.regs.get? LeanRV64D.Defs.Register.PC = some (syscallEventOfRow row).nextPc)
    (loaded : Target.RomLoaded program next) (configured : Target.SailConfigured next) :
    LocalStateTruthG program trajectory timeline (syscallRowFacts row).statePush :=
  ⟨n + 1, next, after, time, pc, loaded, configured⟩

/-- Shared timed assembly for an authenticated physical syscall and its complete semantic effects.
The actual instruction contract supplies register touches, while all grouped RAM effects remain
in the original extended ledger. Handler-specific dispatch is the remaining premise. -/
theorem GroundingCarrier.syscall_engineFacts_of_effects (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (physical : Environment (ZMod p))
    (active : physical ∈ HostCallLedger.activeRows (HostLocalCore.hostCallTable (HostHintQueueBoundary.projected witness)) witness.data)
    (sameEvent : event = .syscall (HostCallLedger.input physical).instruction)
    (effect : ∀ (_ : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (event.facts witness.data).statePull)
    (_ : ∀ mp ∈ (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value),
    ∃ n current next, carrier.ordered[n]? = some event ∧
      carrier.pairedTrajectory valid n = some current ∧ carrier.pairedTrajectory valid (n + 1) = some next ∧
      ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current event.event next ∧
      (∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event,
        locContent next.sail (MemoryMsg.locOf (touch row).2) = some (Word.toBitVec64 (touch row).2.value)) ∧
      (∀ cell : RamCell, (∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event, MemoryMsg.locOf (touch row).2 ≠ .ram cell) →
        locContent next.sail (.ram cell) = locContent current.sail (.ram cell))) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
      (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) ∧
    FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
      (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) := by
  let facts := eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
    (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event
  suffices advance : ∀ (pull : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid)
      carrier.timeline facts.statePull)
      (currency : ∀ mp ∈ facts.memPulls, MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
        LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value),
      (LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline facts.statePush ∧
        ∀ message ∈ facts.memPushes, LocalMemTruthG (carrier.trajectory valid) source.sail.realize carrier.timeline message) ∧
      (∀ loc value, (∀ message ∈ facts.memPushes, MemoryMsg.locOf message = loc → message.value = value) →
        LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline loc (StateMsg.timeNat facts.statePull) value →
        LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline loc (StateMsg.timeNat facts.statePush) value) by
    exact ⟨fun pull currency => (advance pull currency).1, fun pull currency => (advance pull currency).2⟩
  intro pull currency
  obtain ⟨n, current, next, atIndex, paired, pairedNext, step, written, unchanged⟩ :=
    effect pull currency
  have time := ExecutionCarrier.time_of_ordered_at carrier atIndex
  have nextTime := ExecutionCarrier.originalTimeStep carrier member n time
  change StateMsg.timeNat facts.statePull = carrier.timeline.start n at time
  change StateMsg.timeNat facts.statePush = carrier.timeline.start (n + 1) at nextTime
  have before : carrier.trajectory valid n = some current.sail := by
    simp only [GroundingCarrier.trajectory, paired, Option.map_some]
  have after : carrier.trajectory valid (n + 1) = some next.sail := by
    simp only [GroundingCarrier.trajectory, pairedNext, Option.map_some]
  obtain ⟨m, state, present, atTime, _, loaded, configured⟩ := pull
  have sameIndex : m = n := start_injective carrier.timeline (atTime.symm.trans time)
  subst m
  have sail : state = current.sail := Option.some.inj (present.symm.trans before)
  rw [sail] at loaded configured
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have interface := source_interface (p := p) source.host.io.hints
  have program := HostHintQueueBoundary.projected_core_balancedChannel witness balanced programChannel.toRaw
    (by simp [LocalCore.baseEnsemble, sp1Ensemble_channels])
  have byteBalance := (HostHintQueueBoundary.record_channels witness balanced).byte
  have original : ∀ mp ∈ (syscallRowFacts (HostCallLedger.input physical).instruction).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value := by
    intro mp present
    apply currency mp
    apply List.mem_append_left
    simpa only [sameEvent, ExecutionRow.facts] using present
  have contract := HostLocalCore.hostCall_contract (HostHintQueueBoundary.projected witness)
    (auxiliaryInterface interface) (source_program_silent source) checks program byteBalance
  simp only [HostHintQueueBoundary.projected_data] at contract
  have contract := contract physical active
    (fun mp present => ⟨(original mp present).1, (original mp present).2.1⟩)
  have committed := HostLocalCore.hostCall_program_committed valid (HostHintQueueBoundary.projected witness)
    (source_program_silent source) checks program
  simp only [HostHintQueueBoundary.projected_data] at committed
  have committed := committed physical active
  have operands := NativeCore.syscall_operands_of_committed _ _ committed
  have effects := hostStep_effect (show ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩
      (image.toGuestProgram valid) current (.syscall (syscallEventOfRow (HostCallLedger.input physical).instruction)) next by
    simpa only [sameEvent, ExecutionRow.event] using step)
  have instructionTime : StateMsg.timeNat (syscallRowFacts (HostCallLedger.input physical).instruction).statePull =
      carrier.timeline.start n := by simpa only [facts, eventFacts, sameEvent, ExecutionRow.facts] using time
  have registers := register_push_truth (HostCallLedger.input physical).instruction
    (HostCallLedger.activeRows_is_real _ witness.data physical active) contract.1 contract.2 operands.1
    (carrier.trajectory valid) source.sail.realize next.sail carrier.timeline n after instructionTime
    effects.1.2.2.2.2.2 original
  have cpuTime : StateMsg.timeNat (event.facts witness.data).statePull = carrier.timeline.start n := by
    simpa only [facts, eventFacts] using time
  constructor
  · constructor
    · have successor := syscall_state_push (HostCallLedger.input physical).instruction
        (image.toGuestProgram valid) (carrier.trajectory valid) next.sail carrier.timeline n after
        (by simpa only [facts, eventFacts, sameEvent, ExecutionRow.facts] using nextTime)
        effects.1.2.2.2.2.1 (romLoaded_of_readOnly image valid effects.2.2.2 loaded) (effects.2.2.1 configured)
      simpa only [facts, eventFacts, sameEvent, ExecutionRow.facts] using successor
    · intro message messageMem
      change message ∈ (event.facts witness.data).memPushes ++
        (wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).map (fun row => (touch row).2) at messageMem
      rcases List.mem_append.mp messageMem with originalMem | wordMem
      · apply registers message
        simpa only [sameEvent, ExecutionRow.facts] using originalMem
      · obtain ⟨row, rowMem, rfl⟩ := List.mem_map.mp wordMem
        have accesses := source_word_touches witness constraints balanced
        simp only [HostHintQueueBoundary.projected_data] at accesses
        have access := accesses row (List.mem_filter.mp rowMem).1
        have aligned := (source_touches_at valid witness constraints balanced event row rowMem).1
        rw [ExecutionRow.edge_eq_facts, cpuTime] at aligned
        exact word_push_truth row access (carrier.trajectory valid) source.sail.realize next.sail
          carrier.timeline n after aligned
          (currency _ (List.mem_append_right _ (List.mem_map_of_mem rowMem))).2.2 (written row rowMem)
  · intro loc value pushes currentValue
    rw [time] at currentValue
    rw [nextTime]
    apply hint_frame (HostCallLedger.input physical).instruction operands.1 _
      (carrier.trajectory valid) source.sail.realize current.sail next.sail carrier.timeline n
      before after effects.1.2.2.2.2.2 effects.2.1 written unchanged loc value ?_ currentValue
    simpa only [facts, eventFacts, sameEvent, ExecutionRow.facts] using pushes

private theorem GroundingCarrier.queue_engineFacts_of_effects (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (queueRow : HostQueueOrder.Row (p := p))
    (queueMember : queueRow ∈ TransitionView.readIndexedRows HostQueueOrder.indices
      (queueTables (HostHintQueueBoundary.projected witness)) witness.data)
    (clock : StateMsg.timeNat (event.edge witness.data).1 = HostQueueCPUOrder.eventTime queueRow)
    (effect : ∀ (_ : LocalStateTruthG (image.toGuestProgram valid) (carrier.trajectory valid) carrier.timeline
      (event.facts witness.data).statePull)
    (_ : ∀ mp ∈ (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event).memPulls,
      MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG (carrier.trajectory valid) source.sail.realize carrier.timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value),
    ∃ n current next, carrier.ordered[n]? = some event ∧
      carrier.pairedTrajectory valid n = some current ∧ carrier.pairedTrajectory valid (n + 1) = some next ∧
      ExecutionStep ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid) current event.event next ∧
      (∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event,
        locContent next.sail (MemoryMsg.locOf (touch row).2) = some (Word.toBitVec64 (touch row).2.value)) ∧
      (∀ cell : RamCell, (∀ row ∈ wordsAt witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
          (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event, MemoryMsg.locOf (touch row).2 ≠ .ram cell) →
        locContent next.sail (.ram cell) = locContent current.sail (.ram cell))) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
      (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) ∧
    FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
      (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) := by
  have checks := HostHintQueueBoundary.projected_constraints witness constraints
  have interface := source_interface (p := p) source.host.io.hints
  have calls := HostHintQueueBoundary.projected_hostCall_balancedChannel witness balanced
  have ordering := HostHintQueueBoundary.projected_orderingChannels witness interface constraints balanced
  have matched := HostQueueCPUOrder.call_cpu_at (HostHintQueueBoundary.projected witness) interface checks calls ordering
  simp only [HostHintQueueBoundary.projected_data] at matched
  obtain ⟨physical, active, _, sameEvent⟩ := matched queueRow queueMember event member clock
  exact carrier.syscall_engineFacts_of_effects valid constraints balanced event member physical active sameEvent effect

/-- Every matched physical HINT_READ supplies the existing timed engine's complete step and
frame obligations on paired replay. Register, RAM, ROM, and configuration effects are derived
from this witness; no semantic effect or successful-current-step premise is supplied by the caller. -/
theorem GroundingCarrier.hintRead_engineFacts (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (env : Environment (ZMod p))
    (handler : env ∈ (handlerTable (HostHintQueueBoundary.projected witness)).table.map
      (Environment.fromArray · witness.data))
    (clock : StateMsg.timeNat (event.edge witness.data).1 = HostQueueCPUOrder.eventTime (none, env)) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
      (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) ∧
    FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
      (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) := by
  apply carrier.queue_engineFacts_of_effects valid constraints balanced event member (none, env) ?_ clock
    (fun pull currency => carrier.hintRead_step valid constraints balanced event member env handler clock pull currency)
  obtain ⟨physical, physicalMem, rfl⟩ := List.mem_map.mp handler
  simp only [TransitionView.readIndexedRows, HostQueueOrder.indices, queueTables,
    List.zip_cons_cons, List.flatMap_cons]
  exact List.mem_append_left _ (List.mem_map_of_mem physicalMem)

/-- Both physical HINT_LEN variants supply the existing timed engine's complete step and
frame obligations on paired replay. Register, RAM, ROM, and configuration effects are derived
from this witness; no semantic effect or successful-current-step premise is supplied by the caller. -/
theorem GroundingCarrier.hintLength_engineFacts (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (empty : Bool) (env : Environment (ZMod p))
    (handler : (some empty, env) ∈ TransitionView.readIndexedRows HostQueueOrder.indices
      (queueTables (HostHintQueueBoundary.projected witness)) witness.data)
    (clock : StateMsg.timeNat (event.edge witness.data).1 = HostQueueCPUOrder.eventTime (some empty, env)) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
      (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) ∧
    FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
      (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) := by
  apply carrier.queue_engineFacts_of_effects valid constraints balanced event member (some empty, env) handler clock
  intro pull currency
  obtain ⟨n, current, next, atIndex, before, after, step, unchanged, noWords⟩ :=
    carrier.hintLength_step valid constraints balanced event member empty env handler clock pull currency
  refine ⟨n, current, next, atIndex, before, after, step, ?_, fun cell _ => unchanged cell⟩
  rw [noWords]
  simp only [List.not_mem_nil, false_implies, implies_true]

omit [Fact (2 ^ 25 < p)] in
private theorem read_handler_member (first : Table (ZMod p)) (others : List (Table (ZMod p)))
    (data : ProverData (ZMod p))
    (env : Environment (ZMod p))
    (member : (none, env) ∈ TransitionView.readIndexedRows HostQueueOrder.indices (first :: others) data) :
    env ∈ first.table.map (Environment.fromArray · data) := by
  cases others with
  | nil => simpa [TransitionView.readIndexedRows, HostQueueOrder.indices, List.mem_map] using member
  | cons second rest =>
    cases rest <;>
      simpa [TransitionView.readIndexedRows, HostQueueOrder.indices, List.mem_map] using member

/-- Every physical queue handler supplies the full timed step/frame contract. HINT_READ and
both HINT_LEN variants are coordinated internally on the same complete execution carrier. -/
theorem GroundingCarrier.queue_engineFacts (valid : image.Valid)
    {witness : EnsembleWitness (HostHintQueueBoundary.ensemble image source final bankFinal HostCallReceivers.available
      (sourceResources source.host.io.hints) channels
      (source_unique_names image source source.host.io.hints))} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (event : ExecutionRow p)
    (member : event ∈ LocalCore.executionRows (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))
    (queueRow : HostQueueOrder.Row (p := p))
    (queueMember : queueRow ∈ TransitionView.readIndexedRows HostQueueOrder.indices
      (queueTables (HostHintQueueBoundary.projected witness)) witness.data)
    (clock : StateMsg.timeNat (event.edge witness.data).1 = HostQueueCPUOrder.eventTime queueRow) :
    LocalStepFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
      (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) ∧
    FrameFactG (image.toGuestProgram valid) (carrier.trajectory valid) source.sail.realize carrier.timeline
      (eventFacts witness.data (TransitionView.readIndexedRows HintReadCoverage.variants
        (wordTables (HostHintQueueBoundary.projected witness)) witness.data) event) := by
  rcases queueRow with ⟨index, env⟩
  cases index with
  | none =>
    exact carrier.hintRead_engineFacts valid constraints balanced event member env
      (read_handler_member _ _ witness.data env queueMember) clock
  | some empty =>
    exact carrier.hintLength_engineFacts valid constraints balanced event member empty env queueMember clock

end SP1Clean.Soundness.HostHintReadCPU
