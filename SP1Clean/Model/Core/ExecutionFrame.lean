import SP1Clean.Model.Core.ExecutionWritePolicy
import SP1Clean.Model.Core.ProgramImage
import SP1Clean.Model.Semantics.SailInstructionFrame

/-! # Configuration and instruction memory throughout native execution

The existing path threads the complete Sail, host and clock state. Its ordinary-write policy
and the host interpreter's checked writes preserve protected bytes at every cut. A policy that
protects the committed image therefore preserves ROM and platform configuration throughout.

Every executed position has a committed word which official Sail fetch returns unchanged.
Empty, final and beyond-final boundaries retain ROM without acquiring a next-fetch obligation.
No circuit row, compiler readiness or separately supplied intermediate invariant is used.
-/

namespace SP1Clean.Model.Core
open Machine Soundness.Target LeanRV64D.Defs LeanRV64D.Functions

/-- Every byte of a fetched image word belongs to the image's protected region. -/
theorem ProgramImage.readOnly_of_fetch (image : ProgramImage) (valid : image.Valid)
    {pc : BitVec 64} {word : BitVec 32}
    (fetched : (image.toGuestProgram valid).fetchWord pc = some word) (index : Fin 4) :
    image.readOnly (pc.toNat + index) = true := by
  obtain ⟨entry, found, _⟩ := Option.map_eq_some_iff.mp fetched
  have member : entry ∈ image.rom := List.mem_of_find?_eq_some found
  have atPc : entry.1 = pc := by simpa using List.find?_some found
  apply (image.readOnly_iff _).mpr
  exact ⟨entry, member, by rw [atPc]; omega, by rw [atPc]; have := index.isLt; omega⟩

/-- Preserving the image's protected bytes preserves its complete committed instruction memory. -/
theorem ProgramImage.romLoaded_of_readOnly (image : ProgramImage) (valid : image.Valid)
    {source target : SailState}
    (preserved : ∀ address, image.readOnly address = true → target.mem.get? address = source.mem.get? address)
    (loaded : RomLoaded (image.toGuestProgram valid) source) :
    RomLoaded (image.toGuestProgram valid) target := by
  intro pc word fetched index
  exact (preserved _ (image.readOnly_of_fetch valid fetched index)).trans (loaded pc word fetched index)

/-- The concrete host adapter preserves platform registers for every host-call kind. -/
theorem HostExecution.configured (execution : HostExecution) (state : SailState) (pc : BitVec 64)
    (configured : SailConfigured state) : SailConfigured (execution.apply state pc) := by
  refine Advance.SailConfigured.congr configured ?_ ?_
  · exact SailState.isInitialized_insert _ (SailState.isInitialized_insert state configured.init _ _) _ _
  · intro reg member
    have pcOther : ¬ ((Register.PC == reg) = true) := by
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have returnOther : ¬ ((Register.x5 == reg) = true) := by
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    change ((state.regs.insert Register.x5 execution.result).insert Register.PC (execution.nextPc pc)).get? reg = _
    rw [Std.ExtDHashMap.get?_insert, dif_neg pcOther, Std.ExtDHashMap.get?_insert, dif_neg returnOther]

/-- A successful host call binds its observations and frames configuration and protected bytes.
The full emitted write is checked, including HINT_READ's mandatory padding. -/
theorem ExecutionStep.syscall_sail_frame {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : CoreSyscallEvent}
    (step : ExecutionStep policy program source (.syscall event) target) :
    event.MatchesStates source.sail target.sail ∧
      (∀ index : BitVec 5, index ≠ 5 → target.sail.get_reg? index = source.sail.get_reg? index) ∧
      (SailConfigured source.sail → SailConfigured target.sail) ∧
      (∀ address, policy.memory.readOnly address = true →
        target.sail.mem.get? address = source.sail.mem.get? address) := by
  cases step with
  | syscall success =>
    obtain ⟨pc, execution, atPc, _, ran, _, targetEq, eventEq⟩ := HostState.step_observations success
    rw [targetEq, eventEq]
    exact ⟨execution.matchesStates ran atPc _, execution.register_frame source.sail pc,
      execution.configured source.sail pc, execution.preserves_readOnly ran pc⟩

/-- Both semantic step constructors preserve configuration and the policy's protected bytes. -/
theorem ExecutionStep.frame {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (step : ExecutionStep policy program source event target)
    (configured : SailConfigured source.sail) (loaded : RomLoaded program source.sail)
    (permitted : event = .ordinary → InstructionWrite.PermittedAt policy.memory.readOnly program source.sail) :
    SailConfigured target.sail ∧ ∀ address, policy.memory.readOnly address = true →
      target.sail.mem.get? address = source.sail.mem.get? address := by
  cases step with
  | ordinary _ _ normal => exact Advance.ordinary_normal_frame configured loaded (permitted rfl) normal
  | syscall success =>
    have frame := (ExecutionStep.syscall success).syscall_sail_frame
    exact ⟨frame.2.2.1 configured, frame.2.2.2⟩

/-- Each actual event authenticates a committed instruction and its official Sail fetch. -/
theorem ExecutionStep.fetch_eq {policy : HostPolicy} {program : GuestProgram}
    {source target : ExecutionState} {event : ExecutionEvent}
    (step : ExecutionStep policy program source event target)
    (configured : SailConfigured source.sail) (loaded : RomLoaded program source.sail)
    (permitted : event = .ordinary → InstructionWrite.PermittedAt policy.memory.readOnly program source.sail) :
    ∃ pc word, source.sail.regs.get? Register.PC = some pc ∧ program.fetchWord pc = some word ∧
      (fetch ()).run source.sail = .ok (FetchResult.F_Base word) source.sail := by
  suffices ∃ pc word, source.sail.regs.get? Register.PC = some pc ∧ program.fetchWord pc = some word by
    obtain ⟨pc, word, atPc, fetched⟩ := this
    exact ⟨pc, word, atPc, fetched, Advance.fetch_eq_of_romLoaded configured loaded atPc fetched⟩
  cases step with
  | ordinary =>
    obtain ⟨pc, word, _, atPc, fetched, _⟩ := permitted rfl
    exact ⟨pc, word, atPc, fetched⟩
  | syscall success =>
    obtain ⟨pc, _, atPc, fetched, _⟩ := HostState.step_observations success
    exact ⟨pc, ECALL_ENC, atPc, fetched⟩

namespace ExecutionPath
variable {image : ProgramImage} (valid : image.Valid) {policy : HostPolicy}
  {source target : ExecutionState} {events : List ExecutionEvent}

/-- Mixed paths preserve configuration, ROM and every protected byte. The coverage premise only
relates the policy's protected region to the image; the native shard policy satisfies it directly. -/
theorem frame (path : ExecutionPath policy (image.toGuestProgram valid) source events target)
    (permitted : WritesPermitted policy (image.toGuestProgram valid) source events)
    (protectsRom : ∀ address, image.readOnly address = true → policy.memory.readOnly address = true)
    (configured : SailConfigured source.sail) (loaded : RomLoaded (image.toGuestProgram valid) source.sail) :
    SailConfigured target.sail ∧ RomLoaded (image.toGuestProgram valid) target.sail ∧
      ∀ address, policy.memory.readOnly address = true →
        target.sail.mem.get? address = source.sail.mem.get? address := by
  induction path with
  | nil => exact ⟨configured, loaded, fun _ _ => rfl⟩
  | cons step _ ih =>
    have permission := (writesPermitted_cons_iff step).mp permitted
    have next := step.frame configured loaded permission.1
    have rom := image.romLoaded_of_readOnly valid
      (fun address selected => next.2 address (protectsRom address selected)) loaded
    obtain ⟨cfg, loaded, preserved⟩ := ih permission.2 next.1 rom
    exact ⟨cfg, loaded, fun address selected =>
      (preserved address selected).trans (next.2 address selected)⟩

/-- Every replayed prefix, including endpoint extension, inherits the same independent invariant. -/
theorem frame_prefix (path : ExecutionPath policy (image.toGuestProgram valid) source events target)
    (permitted : WritesPermitted policy (image.toGuestProgram valid) source events)
    (protectsRom : ∀ address, image.readOnly address = true → policy.memory.readOnly address = true)
    (configured : SailConfigured source.sail) (loaded : RomLoaded (image.toGuestProgram valid) source.sail)
    {cut : ℕ} {current : ExecutionState}
    (replay : executionTrajectory policy (image.toGuestProgram valid) source events cut = some current) :
    SailConfigured current.sail ∧ RomLoaded (image.toGuestProgram valid) current.sail ∧
      ∀ address, policy.memory.readOnly address = true →
        current.sail.mem.get? address = source.sail.mem.get? address := by
  obtain ⟨middle, left, _, allowed, _⟩ := permitted.split path cut
  have same : middle = current := Option.some.inj (left.replay.symm.trans replay)
  subst current
  exact left.frame valid allowed protectsRom configured loaded

/-- Every executed position has an actual prefix state and a matching official/committed fetch.
The strict bound deliberately excludes unused final boundaries and empty identities. -/
theorem fetch_at (path : ExecutionPath policy (image.toGuestProgram valid) source events target)
    (permitted : WritesPermitted policy (image.toGuestProgram valid) source events)
    (protectsRom : ∀ address, image.readOnly address = true → policy.memory.readOnly address = true)
    (configured : SailConfigured source.sail) (loaded : RomLoaded (image.toGuestProgram valid) source.sail)
    (cut : ℕ) (active : cut < events.length) :
    ∃ current pc word, executionTrajectory policy (image.toGuestProgram valid) source events cut = some current ∧
      current.sail.regs.get? Register.PC = some pc ∧ (image.toGuestProgram valid).fetchWord pc = some word ∧
      (fetch ()).run current.sail = .ok (FetchResult.F_Base word) current.sail := by
  obtain ⟨middle, left, right, allowed, remaining⟩ := permitted.split path cut
  have preserved := left.frame valid allowed protectsRom configured loaded
  cases suffix : events.drop cut with
  | nil =>
    have length := congrArg List.length suffix
    simp only [List.length_drop, List.length_nil] at length
    omega
  | cons event rest =>
    rw [suffix] at right remaining
    cases right with
    | cons step _ =>
      obtain ⟨pc, word, fetched⟩ := step.fetch_eq preserved.1 preserved.2.1
        ((writesPermitted_cons_iff step).mp remaining).1
      exact ⟨middle, pc, word, left.replay, fetched⟩

end ExecutionPath
end SP1Clean.Model.Core
