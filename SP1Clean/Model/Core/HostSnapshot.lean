import SP1Clean.Model.Core.ExecutionSnapshot

/-! # Executing host effects on complete finite snapshots

The executable host path reads the finite register map and sparse RAM, never the dense Sail
realization. Applying a returned write preserves all other Sail/runtime fields and threads the
actual host result. The commuting theorem covers the complete padded write and exact state,
including bookkeeping; the native memory-policy window is explicit.
-/

namespace SP1Clean.Model.Core

open LeanRV64D.Defs SP1Clean.Soundness.Target SP1Clean.Machine

/-- Sparse observations agree with every partial observation made by the Sail adapter. -/
def SailSnapshot.readContext (snapshot : SailSnapshot) : HostReadContext where
  register := snapshot.skeleton.get_reg?
  byte address := if address < 2 ^ 48 then some (snapshot.memory.read address) else none

private theorem readContext_withMemory (state : SailState) (memory : Std.ExtHashMap ℕ (BitVec 8))
    (read : ℕ → Option (BitVec 8)) (agrees : ∀ address, read address = memory.get? address) :
    (⟨state.get_reg?, read⟩ : HostReadContext) = HostReadContext.ofSail { state with mem := memory } := by
  simp only [HostReadContext.ofSail]
  congr 1
  exact funext agrees

theorem SailSnapshot.readContext_eq (snapshot : SailSnapshot) :
    snapshot.readContext = HostReadContext.ofSail snapshot.realize :=
  readContext_withMemory snapshot.skeleton _ _
    (fun address => (snapshot.memory.toSailMemory_get? (2 ^ 48) address).symm)

/-- Sparse bulk writes realize the exact Sail insertions, including final hint padding. -/
theorem HostMemoryWrite.realize (write : HostMemoryWrite) (memory : ByteMemory) (limit : ℕ)
    (bounded : write.address + write.bytes.length ≤ limit) :
    (memory.writeBytes write.address write.bytes).toSailMemory limit =
      (memory.toSailMemory limit).insertMany write.entries := by
  apply Std.ExtHashMap.ext_getElem?
  intro address
  change ((memory.writeBytes write.address write.bytes).toSailMemory limit).get? address =
    ((memory.toSailMemory limit).insertMany write.entries).get? address
  by_cases inside : write.address ≤ address ∧ address < write.address + write.bytes.length
  · have index : address - write.address < write.bytes.length := by omega
    have equal : address = write.address + (address - write.address) := by omega
    rw [equal, write.read_written _ _ index, ByteMemory.toSailMemory_get?,
      if_pos (by omega), ByteMemory.read_writeBytes_inside _ _ _ _ index]
  · have outside : address < write.address ∨ write.address + write.bytes.length ≤ address := by omega
    rw [write.read_outside _ address outside, ByteMemory.toSailMemory_get?,
      ByteMemory.read_writeBytes_of_outside _ _ _ _ outside, ByteMemory.toSailMemory_get?]

/-- Apply only the returned architectural/RAM effects; all other Sail fields are retained. -/
def HostExecution.applySnapshot (execution : HostExecution) (source : SailSnapshot)
    (pc : BitVec 64) : SailSnapshot :=
  { source with
    registers := (source.registers.insert Register.x5 execution.result).insert Register.PC (execution.nextPc pc)
    memory := match execution.effect.write with
      | none => source.memory
      | some write => source.memory.writeBytes write.address write.bytes }

theorem HostExecution.applySnapshot_realize (execution : HostExecution) (source : SailSnapshot)
    (pc : BitVec 64)
    (bounded : ∀ write, execution.effect.write = some write →
      write.address + write.bytes.length ≤ 2 ^ 48) :
    (execution.applySnapshot source pc).realize = execution.apply source.realize pc := by
  cases write : execution.effect.write with
  | none => simp only [applySnapshot, HostExecution.apply, HostEffect.applyMemory, write,
      SailSnapshot.realize, SailSnapshot.skeleton]
  | some value =>
      simp only [applySnapshot, write, SailSnapshot.realize, SailSnapshot.skeleton,
        HostExecution.apply, HostEffect.applyMemory]
      rw [value.realize _ _ (bounded value write)]

/-- Execute one ECALL directly on finite boundary data. It does not accept claimed effects. -/
def ExecutionSnapshot.hostStep? (source : ExecutionSnapshot) (policy : HostPolicy)
    (program : GuestProgram) : Option (ExecutionSnapshot × CoreSyscallEvent) := do
  let pc ← source.sail.registers.get? Register.PC
  if program.fetchWord pc = some ECALL_ENC ∧
      InstructionBytes.check source.sail.readContext.byte pc ECALL_ENC = true then do
    let execution ← source.host.run policy source.sail.readContext
    some (⟨execution.applySnapshot source.sail pc, execution.effect.state,
      source.clock + syscallSchedule.duration⟩, execution.toEvent source.clock pc)
  else none

/-- The finite interpreter and the Sail host adapter commute on the full execution state.
The policy bound is a profile parameter, not a witness-dependent readiness condition. -/
theorem ExecutionSnapshot.hostStep?_realize (source : ExecutionSnapshot) (policy : HostPolicy)
    (program : GuestProgram) (upper : policy.memory.upper = 2 ^ 48) :
    (source.hostStep? policy program).map (fun result => (result.1.realize, result.2)) =
      (source.host.step policy program source.clock source.realize.sail).map
        (fun (host, sail, event) => (⟨sail, host, source.clock + syscallSchedule.duration⟩, event)) := by
  change (source.hostStep? policy program).map (fun result => (result.1.realize, result.2)) =
    (source.host.step policy program source.clock source.sail.realize).map
      (fun (host, sail, event) => (⟨sail, host, source.clock + syscallSchedule.duration⟩, event))
  have pcEq : source.sail.realize.regs.get? Register.PC = source.sail.registers.get? Register.PC := rfl
  have byteEq : source.sail.readContext.byte = source.sail.realize.mem.get? :=
    congrArg HostReadContext.byte source.sail.readContext_eq
  simp only [hostStep?, HostState.step, pcEq, byteEq]
  rw [source.sail.readContext_eq]
  cases pc : source.sail.registers.get? Register.PC with
  | none => simp only [bind, Option.bind_none, Option.map_none]
  | some value =>
      simp only [bind, Option.bind_some]
      split
      · cases ran : source.host.run policy (HostReadContext.ofSail source.sail.realize) with
        | none => rfl
        | some execution =>
            have bounded (write : HostMemoryWrite) (present : execution.effect.write = some write) :
                write.address + write.bytes.length ≤ 2 ^ 48 := by
              have executed := ((source.host.run_eq_some_iff _ _ _).mp ran).2.2.2.2.2
              have permitted := source.host.executeKind_write_permitted executed write present
              have bound := ((policy.memory.permits_iff _ _).mp permitted).2.1
              simpa only [upper] using bound
            simp only [Option.bind_some, Option.map_some]
            exact congrArg (fun sail => some (ExecutionState.mk sail execution.effect.state
              (source.clock + syscallSchedule.duration), execution.toEvent source.clock value))
              (execution.applySnapshot_realize source.sail value bounded)
      · rfl

/-- A computed finite host transition is a genuine complete-state semantic transition. -/
theorem ExecutionSnapshot.hostStep?_sound {source target : ExecutionSnapshot} {policy : HostPolicy}
    {program : GuestProgram} {event : CoreSyscallEvent} (upper : policy.memory.upper = 2 ^ 48)
    (success : source.hostStep? policy program = some (target, event)) :
    ExecutionStep policy program source.realize (.syscall event) target.realize := by
  have same := source.hostStep?_realize policy program upper
  rw [success, Option.map_some] at same
  obtain ⟨⟨host, sail, actualEvent⟩, ran, equal⟩ := Option.map_eq_some_iff.mp same.symm
  obtain ⟨stateEq, eventEq⟩ := Prod.mk.inj equal
  change actualEvent = event at eventEq
  rw [← stateEq, ← eventEq]
  exact .syscall ran

/-- Every successful Sail host step from a represented source has a computed finite successor.
There is no compiler-readiness witness and the returned sparse history is chosen by execution. -/
theorem ExecutionSnapshot.hostStep?_complete {source : ExecutionSnapshot} {policy : HostPolicy}
    {program : GuestProgram} {host : HostState} {sail : SailState} {event : CoreSyscallEvent}
    (upper : policy.memory.upper = 2 ^ 48)
    (success : source.host.step policy program source.clock source.realize.sail = some (host, sail, event)) :
    ∃ target, source.hostStep? policy program = some (target, event) ∧
      target.realize = ⟨sail, host, source.clock + syscallSchedule.duration⟩ := by
  have same := source.hostStep?_realize policy program upper
  rw [success, Option.map_some] at same
  obtain ⟨⟨target, actualEvent⟩, ran, equal⟩ := Option.map_eq_some_iff.mp same
  obtain ⟨stateEq, eventEq⟩ := Prod.mk.inj equal
  change actualEvent = event at eventEq
  exact ⟨target, by simpa only [eventEq] using ran, stateEq⟩

end SP1Clean.Model.Core
