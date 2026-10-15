import SP1Clean.Soundness.HostHintReadFinalMemory
import SP1Clean.Model.Core.MemoryFinalCheck

/-! # Finite outgoing-memory checks against the installed CPU replay

The existing final-record inventory and complete location theorem suffice to check a supplied
memory snapshot without replaying Sail in the checker. Both recorded and untouched values matter.
Passing the finite check identifies every GPR and the literal bounded Sail RAM map, including the
absence of keys outside the native window.

The check still has to be enforced by the native boundary circuits. These are implementation
lemmas for that binding, not an added caller premise of the released execution theorem, and not
a complete outgoing Sail/host snapshot certificate.
-/

namespace SP1Clean.Soundness.HostHintReadCPU

open Circuit Air.Flat Channels Model.Core Semantics NativeCore HostHintReadLocal
open LeanRV64D.Defs (Register)

private theorem realizes_of_observations (snapshot : MemorySnapshot) (state : SailState)
    (observed : ∀ loc, loc.busAddress < 2 ^ 48 →
      locContent state loc = some (snapshot.read loc)) : snapshot.Realizes state := by
  refine ⟨fun index => observed (.reg index) (by
    change index.toNat < 2 ^ 48
    have := index.isLt
    omega), ?_⟩
  intro address bound
  let cell : RamCell := BitVec.ofNat 61 (address / 8)
  have cellNat : cell.toNat = address / 8 := Nat.mod_eq_of_lt (by omega)
  have word := observed (.ram cell) (by simp only [MemLoc.busAddress, cellNat]; omega)
  have byte := byte_of_ramWord64?_eq_some word ⟨address % 8, Nat.mod_lt _ (by decide)⟩
  have packed (word : BitVec 64) (index : Fin 8) :
      (wordBytes word)[index] = word.extractLsb' (8 * index.val) 8 := by
    fin_cases index <;> rfl
  rw [packed, MemorySnapshot.read, ByteMemory.readWord_byte, RamCell.baseAddr_toNat, cellNat,
    show address / 8 * 8 + address % 8 = address by omega] at byte
  exact byte

private theorem memory_eq_of_realizes (snapshot : MemorySnapshot) (state : SailState)
    (realizes : snapshot.Realizes state)
    (outside : ∀ address, 2 ^ 48 ≤ address → state.mem.get? address = none) :
    state.mem = snapshot.memory.toSailMemory (2 ^ 48) := by
  apply Std.ExtHashMap.ext_getElem?
  intro address
  change state.mem.get? address = (snapshot.memory.toSailMemory (2 ^ 48)).get? address
  rw [ByteMemory.toSailMemory_get?]
  split
  next bound => exact realizes.2 address bound
  next unbounded => exact outside address (by omega)

private theorem mapped_frontier {α : Type*} (records : List α) (location : α → MemLoc)
    (value : α → BitVec 64) (loc : MemLoc) :
    (((records.map (fun record => (location record, value record))).filter
      (fun record => decide (record.1 = loc))).head?).map Prod.snd =
      ((records.filter (fun record => decide (location record = loc))).head?).map value := by
  simp only [List.filter_map, Function.comp_def, List.head?_map, Option.map_map]

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]
local instance snapshotClockBound : Fact (2 ^ 24 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance snapshotLimbBound : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

variable {image : ProgramImage} {source : ExecutionSnapshot}
  {final : HostHintQueue.State (ZMod p)} {bankFinal : HostState} {channels : List (RawChannel (ZMod p))}

/-- Decode every original final-record occurrence; no record is discarded or filled in. -/
noncomputable def finalMemoryValues
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)) : List (MemLoc × BitVec 64) :=
  (FinalMemoryEnsemble.records
    (LocalCore.finalWitness (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)))).map
      (fun record => (MemoryMsg.locOf record, Word.toBitVec64 record.value))

/-- A successful finite target check identifies all integer registers and the entire Sail RAM
map on the already-derived execution. Its enforcement by the native AIR remains separate. -/
theorem GroundingCarrier.memory_of_checkFinal (valid : image.Valid)
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (targetMemory : MemorySnapshot)
    (checked : source.sail.memorySnapshot.checkFinal targetMemory (finalMemoryValues witness) = true)
    {target : ExecutionState}
    (replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target) :
    targetMemory.Realizes target.sail ∧ target.sail.mem = targetMemory.memory.toSailMemory (2 ^ 48) := by
  have observed : ∀ loc, loc.busAddress < 2 ^ 48 →
      locContent target.sail loc = some (targetMemory.read loc) := by
    intro loc bound
    have values := MemorySnapshot.read_of_checkFinal checked loc bound
    rw [finalMemoryValues, mapped_frontier] at values
    change ((LocalCore.memoryFinalFrontier
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc).map
        (fun record => Word.toBitVec64 record.value)).getD (source.sail.memorySnapshot.read loc) =
      targetMemory.read loc at values
    rw [carrier.final_memory valid constraints balanced target replay loc bound, ← values]
    cases LocalCore.memoryFinalFrontier (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc <;> rfl
  have realizes := realizes_of_observations targetMemory target.sail observed
  exact ⟨realizes, memory_eq_of_realizes targetMemory target.sail realizes
    (carrier.final_memory_domain valid constraints balanced replay)⟩

/-- The finite comparison accepts exactly the complete Memory observations of this execution.
Final-record bounds and uniqueness come from the installed AIR, not the check's caller. -/
theorem GroundingCarrier.checkFinal_iff (valid : image.Valid)
    {witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels)} (carrier : GroundingCarrier witness)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (targetMemory : MemorySnapshot) {target : ExecutionState}
    (replay : replayEvents? ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
      source.realize carrier.events = some target) :
    source.sail.memorySnapshot.checkFinal targetMemory (finalMemoryValues witness) = true ↔
      (∀ index, target.sail.get_reg? index = some (targetMemory.read (.reg index))) ∧
        target.sail.mem = targetMemory.memory.toSailMemory (2 ^ 48) := by
  constructor
  · intro checked
    have agrees := carrier.memory_of_checkFinal valid constraints balanced targetMemory checked replay
    exact ⟨agrees.1.1, agrees.2⟩
  rintro ⟨registers, ram⟩
  have realizes : targetMemory.Realizes target.sail := ⟨registers, by
    intro address bound
    rw [ram, ByteMemory.toSailMemory_get?, if_pos bound]⟩
  have records := HostLocalCore.final_records_canonical_nodup (HostHintQueueBoundary.projected witness)
    (auxiliaryInterface (source_interface source.host.io.hints))
    (source_boundary_silent source _ (by simp))
    (HostHintQueueBoundary.projected_constraints witness constraints)
    (HostHintQueueBoundary.record_channels witness balanced).byte
    (HostHintQueueBoundary.projected_core_balancedChannel witness balanced _ (by simp [LocalCore.baseEnsemble]))
  apply (MemorySnapshot.checkFinal_iff_reads _ _ _ ?_ ?_).mpr
  · intro loc bound
    rw [finalMemoryValues, mapped_frontier]
    change ((LocalCore.memoryFinalFrontier
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc).map
        (fun record => Word.toBitVec64 record.value)).getD (source.sail.memorySnapshot.read loc) =
      targetMemory.read loc
    have same := Option.some.inj ((carrier.final_memory valid constraints balanced target replay loc bound).symm.trans
      (realizes.locContent_of_address_lt loc bound))
    generalize LocalCore.memoryFinalFrontier
      (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc = selected at same ⊢
    cases selected <;> exact same
  · simpa only [finalMemoryValues, List.map_map, Function.comp_def] using records.2
  · intro record member
    obtain ⟨message, present, rfl⟩ := List.mem_map.mp member
    exact MemLoc.busAddress_lt_two_pow_48 (records.1 message present).1

/-- The installed AIR yields one local execution with complete host reconstruction and every
native Memory value and the complete RAM domain, including untouched locations. Sail runtime,
register frames, all retirement/nextPC effects, and the actual HALT's public exit code are retained;
the optional terminal status agrees with the supplied host. The finite Memory endpoint check is
characterized on this same path. Its AIR enforcement and complete target equality remain open. -/
theorem source_execution_with_memory (valid : image.Valid)
    (witness : HostHintReadBanks.Witness (p := p) (image := image) (source := source)
      (final := final) (bankFinal := bankFinal) (channels := channels))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ∃ events target hints, ExecutionPath ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events target ∧
      ExecutionPath.WritesPermitted ⟨{ readOnly := image.readOnly }, p⟩ (image.toGuestProgram valid)
        source.realize events ∧
      events.Perm ((LocalCore.executionRows
        (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness))).map ExecutionRow.event) ∧
      target.clock = StateMsg.timeNat (finalBoundaryStateMessage witness.publicInput) ∧
      target.sail.regs.get? LeanRV64D.Defs.Register.PC =
        some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput)) ∧
      (∀ loc, loc.busAddress < 2 ^ 48 → locContent target.sail loc = some
        (match LocalCore.memoryFinalFrontier
            (HostLocalCore.localWitness (HostHintQueueBoundary.projected witness)) loc with
          | some message => Word.toBitVec64 message.value
          | none => source.sail.memorySnapshot.read loc)) ∧
      (∀ address, 2 ^ 48 ≤ address → target.sail.mem.get? address = none) ∧
      (target.sail.cycleCount = source.sail.cycleCount ∧ target.sail.sailOutput = source.sail.output) ∧
      target.sail.regs.get? Register.nextPC = nextPcAfter events
        (source.sail.registers.get? Register.nextPC)
        (some (StateMsg.pcBits (finalBoundaryStateMessage witness.publicInput))) ∧
      (target.sail.regs.get? Register.minstret_increment =
        (if events.countP Machine.ExecutionEvent.isOrdinary = 0
          then source.sail.registers.get? Register.minstret_increment
          else some (retirementEnabled source.sail.realize)) ∧
        target.sail.regs.get? Register.minstret = (source.sail.registers.get? Register.minstret).map
          (fun value => value + BitVec.ofNat 64
            (if retirementEnabled source.sail.realize then events.countP Machine.ExecutionEvent.isOrdinary else 0))) ∧
      (∀ R : Register, R ≠ Register.PC → R ≠ Register.nextPC → R ≠ Register.minstret →
        R ≠ Register.minstret_increment → (∀ index : BitVec 5, R ≠ reg_idx_to_Register index) →
          target.sail.regs.get? R = source.sail.registers.get? R) ∧
      HintQueue.decode? (HintQueue.ofList source.host.io.hints).1 (Address.toNat final.head) = some hints ∧
      target.host = { source.host with
        io.hints := hints
        committed := bankFinal.committed
        deferred := bankFinal.deferred
        exitCode := bankFinal.exitCode } ∧
      (∀ code : BitVec 32, source.host.exitCode = none → target.host.exitCode = some code →
        code.toNat = witness.publicInput.exit_code.val) ∧
      (∀ candidate : MemorySnapshot,
        source.sail.memorySnapshot.checkFinal candidate (finalMemoryValues witness) = true ↔
          (∀ index, target.sail.get_reg? index = some (candidate.read (.reg index))) ∧
            target.sail.mem = candidate.memory.toSailMemory (2 ^ 48)) := by
  obtain ⟨carrier⟩ := source_grounding_carrier valid witness constraints balanced
  obtain ⟨target, path, clock, pc, _⟩ := carrier.execution valid constraints balanced
  obtain ⟨hints, decoded, host⟩ := carrier.final_host valid constraints balanced target path
  have terminal : carrier.events.foldl hostExitAfter source.host.exitCode = bankFinal.exitCode :=
    path.host_exit.symm.trans (carrier.final_terminal valid constraints balanced path)
  rw [terminal] at host
  have nextPc := carrier.nextPC valid constraints balanced path.replay
  rw [pc] at nextPc
  exact ⟨carrier.events, target, hints, path, carrier.writesPermitted valid constraints balanced, carrier.exhaustive.map ExecutionRow.event, clock, pc,
    carrier.final_memory valid constraints balanced target path.replay,
    carrier.final_memory_domain valid constraints balanced path.replay,
    carrier.runtime valid constraints balanced path.replay,
    nextPc, carrier.retirement valid constraints balanced path.replay,
    carrier.other_registers valid constraints balanced path.replay, decoded, host,
    (fun _ running halted => carrier.final_exit valid constraints balanced path running halted),
    fun candidate => carrier.checkFinal_iff valid constraints balanced candidate path.replay⟩


end SP1Clean.Soundness.HostHintReadCPU
