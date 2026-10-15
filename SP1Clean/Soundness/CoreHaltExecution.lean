import SP1Clean.Soundness.HaltGrounding
import SP1Clean.Soundness.CoreExecutionEvents
import SP1Clean.Model.Core.HostHalt

/-! # HALT from grounded observations

The legacy HALT row's asserted code and exit range, together with the engine's incoming Memory
currency, determine an actual transition of the complete stateful host. This common argument
does not choose a trajectory, reset the host, or use a row's result as an oracle.
-/

namespace SP1Clean.Soundness

open SP1Clean.Soundness.NativeCore (haltEventOfRow)
open SP1Clean.Channels SP1Clean.Model.Core SP1Clean.Semantics TimedGrounding LeanRV64D.Defs

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem halt_register_current {row : HaltChip.Inputs (ZMod p)}
    {trajectory : Trajectory} {initial state : SailState} {timeline : Timeline} {n : ℕ}
    (before : trajectory n = some state)
    (time : StateMsg.timeNat (HaltChip.statePulledMessage row) = timeline.start n)
    (block : Circuits.Types.RegisterAccessCols (ZMod p)) (idx : BitVec 5)
    (current : LocalValueAtG trajectory initial timeline
      (MemoryMsg.locOf (HaltChip.memPulledMessage row block idx.toNat))
      (StateMsg.timeNat (HaltChip.statePulledMessage row)) block.prev_value) :
    state.get_reg? idx = some (Word.toBitVec64 block.prev_value) := by
  rw [time] at current
  have location := MemoryMsg.locOf_register (HaltChip.memPulledMessage row block idx.toNat) idx rfl rfl rfl
  have content := (localValueAtG_stepStart_iff before).mp current
  rwa [location] at content

/-- The three pulled records are the actual current x5/x10/x11, with a bounded exit word. -/
theorem HaltChip.registers_of_currency (row : HaltChip.Inputs (ZMod p))
    {trajectory : Trajectory} {initial state : SailState} {timeline : Timeline} {n : ℕ}
    (before : trajectory n = some state)
    (time : StateMsg.timeNat (HaltChip.statePulledMessage row) = timeline.start n)
    (currency : ∀ mp ∈ (haltRowFacts row).memPulls, MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG trajectory initial timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    state.get_reg? 5 = some (Word.toBitVec64 row.x5_memory.prev_value) ∧
      state.get_reg? 10 = some (Word.toBitVec64 row.x10_memory.prev_value) ∧
      state.get_reg? 11 = some (Word.toBitVec64 row.x11_memory.prev_value) ∧
      Word.isU64 row.x10_memory.prev_value := by
  have a := currency _ (show (HaltChip.memPulledMessage row row.x5_memory 5,
    StateMsg.timeNat (HaltChip.statePulledMessage row)) ∈ (haltRowFacts row).memPulls from by
      simp [haltRowFacts, HaltChip.memoryPairs])
  have b := currency _ (show (HaltChip.memPulledMessage row row.x10_memory 10,
    StateMsg.timeNat (HaltChip.statePulledMessage row)) ∈ (haltRowFacts row).memPulls from by
      simp [haltRowFacts, HaltChip.memoryPairs])
  have c := currency _ (show (HaltChip.memPulledMessage row row.x11_memory 11,
    StateMsg.timeNat (HaltChip.statePulledMessage row)) ∈ (haltRowFacts row).memPulls from by
      simp [haltRowFacts, HaltChip.memoryPairs])
  exact ⟨halt_register_current before time _ 5 a.2.2,
    halt_register_current before time _ 10 b.2.2,
    halt_register_current before time _ 11 c.2.2, b.1⟩

/-- Checked row data and grounded observations produce the complete HALT step, including the
new exit status. The field characteristic is explicitly the host policy's characteristic. -/
theorem HaltChip.executionStep_of_currency (row : HaltChip.Inputs (ZMod p))
    (policy : HostPolicy) (field : policy.characteristic = p) (program : Target.GuestProgram)
    (source : ExecutionState)
    (zero : Word.toBitVec64 row.x5_memory.prev_value = 0)
    (high : row.x10_memory.prev_value[1] = 0 ∧ row.x10_memory.prev_value[2] = 0 ∧
      row.x10_memory.prev_value[3] = 0)
    (running : source.host.exitCode = none)
    (clock : source.clock = StateMsg.timeNat (HaltChip.statePulledMessage row))
    (pc : source.sail.regs.get? Register.PC = some (StateMsg.pcBits (HaltChip.statePulledMessage row)))
    (fetch : program.fetchWord (StateMsg.pcBits (HaltChip.statePulledMessage row)) = some Target.ECALL_ENC)
    (rom : Target.RomLoaded program source.sail)
    {trajectory : Trajectory} {initial : SailState} {timeline : Timeline} {n : ℕ}
    (before : trajectory n = some source.sail)
    (time : StateMsg.timeNat (HaltChip.statePulledMessage row) = timeline.start n)
    (currency : ∀ mp ∈ (haltRowFacts row).memPulls, MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG trajectory initial timeline (MemoryMsg.locOf mp.1) mp.2 mp.1.value) :
    ExecutionStep policy program source (.syscall (haltEventOfRow row))
      ⟨{ source.sail with regs := source.sail.regs.insert Register.PC Machine.haltPc },
        { source.host with exitCode := some ((Word.toBitVec64 row.x10_memory.prev_value).setWidth 32) },
        source.clock + Machine.syscallSchedule.duration⟩ := by
  obtain ⟨code, a0, a1, small⟩ := HaltChip.registers_of_currency row before time currency
  rw [zero] at code
  have exitBound := HaltChip.exit_lt_of_highZero _ small high
  have bounds : (Word.toBitVec64 row.x10_memory.prev_value).toNat < policy.characteristic ∧
      (Word.toBitVec64 row.x10_memory.prev_value).toNat < 2 ^ 32 := by
    rw [field]
    have := Fact.out (p := 2 ^ 25 < p)
    omega
  have step := ExecutionStep.halt source _ _ _ running pc fetch
    (InstructionBytes.check_of_romLoaded rom fetch) code a0 a1 bounds
  have event : (source.host.haltExecution (Word.toBitVec64 row.x10_memory.prev_value)
      (Word.toBitVec64 row.x11_memory.prev_value)).toEvent source.clock
        (StateMsg.pcBits (HaltChip.statePulledMessage row)) = haltEventOfRow row := by
    simp only [HostState.haltExecution, HostExecution.toEvent, HostExecution.nextPc,
      haltEventOfRow, clock, zero, ↓reduceIte, SyscallKind.code]
  rwa [event] at step

end SP1Clean.Soundness
