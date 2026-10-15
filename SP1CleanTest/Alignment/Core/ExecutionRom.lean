import SP1Clean.FormalModel.ShardPreservation
import SP1Clean.Model.Core.ExecutionResources
import SP1Clean.Model.Core.HostSnapshot
import SP1Clean.Model.SP1Field
import SP1Clean.Model.Semantics.SailControlExecute
import SP1Clean.Proofs.Sail.InstructionDecode

/-! # ROM and fetch on mixed semantic paths

A padded HINT_READ changes data memory and consumes an actual queue item, then a normally
retiring JALR or branch executes from the preserved next word. Prefixes retain configuration and
ROM, including the held endpoint; every executed position has an official Sail fetch. These
fixtures construct semantic steps without circuit rows. Native evaluation checks finite input
and host-interpreter data, never dense Sail memory or ordinary execution.
-/

namespace SP1CleanTest.Core.ExecutionRom
open SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target SP1Clean.Machine
open Sail LeanRV64D.Defs LeanRV64D.Functions

private def image (word : BitVec 32) : ProgramImage :=
  ⟨[(65536, 0x73), (65540, word)], 65536, [(70008, 99)]⟩

private def initialHost : HostState := { io := ⟨[[1, 2, 3, 4, 5, 6, 7, 8], [9]], [10]⟩ }

private def source (word : BitVec 32) (left right : BitVec 64) : ExecutionSnapshot where
  sail := {
    registers := (((((configuredState 65536).regs.insert .x2 left).insert .x3 right).insert
      .x5 241).insert .x10 70000).insert .x11 8
    memory := (image word).initialMemory }
  host := initialHost
  clock := 17

private def hint : SP1Clean.Model.Core.HostExecution :=
  ⟨.hintRead, 70000, 8, 241, ⟨{ initialHost with io.hints := [[9]] },
    some ⟨70000, [1, 2, 3, 4, 5, 6, 7, 8] ++ List.replicate 8 0⟩⟩⟩

private def middle (word : BitVec 32) (left right : BitVec 64) : ExecutionSnapshot :=
  ⟨hint.applySnapshot (source word left right).sail 65536, hint.effect.state, 281⟩

private def tape : List ExecutionEvent := [.syscall (hint.toEvent 17 65536), .ordinary]

private def hostCheck (policy : HostPolicy) (program : GuestProgram)
    (before after : ExecutionSnapshot) (event : CoreSyscallEvent) : Bool :=
  ((before.hostStep? policy program).map fun result =>
    result.1.equivalent after && decide (result.2 = event)).getD false

private theorem hostStep_of_check {policy : HostPolicy} {program : GuestProgram}
    {before after : ExecutionSnapshot} {event : CoreSyscallEvent}
    (upper : policy.memory.upper = 2 ^ 48) (checked : hostCheck policy program before after event = true) :
    ExecutionStep policy program before.realize (.syscall event) after.realize := by
  cases found : before.hostStep? policy program with
  | none => simp only [hostCheck, found, Option.map_none, Option.getD_none, Bool.false_eq_true] at checked
  | some result =>
    simp only [hostCheck, found, Option.map_some, Option.getD_some, Bool.and_eq_true, decide_eq_true_eq] at checked
    have step := ExecutionSnapshot.hostStep?_sound upper found
    rw [(ExecutionSnapshot.equivalent_iff _ _).mp checked.1, checked.2] at step
    exact step

private theorem middle_pc (word : BitVec 32) (left right : BitVec 64) :
    (middle word left right).sail.realize.regs.get? Register.PC = some 65540 := by
  exact Std.ExtDHashMap.get?_insert_self

private theorem middle_left (word : BitVec 32) (left right : BitVec 64) :
    (middle word left right).sail.realize.get_reg? 2 = some left := by
  change ((((((((configuredState 65536).regs.insert .x2 left).insert .x3 right).insert
    .x5 241).insert .x10 70000).insert .x11 8).insert .x5 241).insert .PC 65540).get? .x2 = some left
  simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, reduceCtorEq, ↓reduceDIte, cast_eq]

private theorem middle_right (word : BitVec 32) (left right : BitVec 64) :
    (middle word left right).sail.realize.get_reg? 3 = some right := by
  change ((((((((configuredState 65536).regs.insert .x2 left).insert .x3 right).insert
    .x5 241).insert .x10 70000).insert .x11 8).insert .x5 241).insert .PC 65540).get? .x3 = some right
  simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, reduceCtorEq, ↓reduceDIte, cast_eq]

private theorem check_of_registers (left right : SailState) (equal : left.regs = right.regs)
    (readOnly : ℕ → Bool) (decoded : instruction)
    (checked : InstructionWrite.check readOnly left.get_reg? decoded = true) :
    InstructionWrite.check readOnly right.get_reg? decoded = true := by
  have registers : left.get_reg? = right.get_reg? := by
    funext index
    simp only [SailState.get_reg?, equal]
  rw [← registers]
  exact checked

private def Preserved (word : BitVec 32) (left right : BitVec 64) : Prop :=
  ∃ valid : ExecutionSourceValid (image word) (source word left right), ∃ target,
    ExecutionPath (FormalModel.Shard.policy SP1Prime (image word)) ((image word).toGuestProgram valid.1.1)
      (source word left right).realize tape target ∧
    (∀ cut, ∃ current, executionTrajectory (FormalModel.Shard.policy SP1Prime (image word))
        ((image word).toGuestProgram valid.1.1) (source word left right).realize tape cut = some current ∧
      SailConfigured current.sail ∧ RomLoaded ((image word).toGuestProgram valid.1.1) current.sail) ∧
    (∀ cut < tape.length, ∃ current pc instructionWord,
      executionTrajectory (FormalModel.Shard.policy SP1Prime (image word)) ((image word).toGuestProgram valid.1.1)
        (source word left right).realize tape cut = some current ∧
      current.sail.regs.get? Register.PC = some pc ∧
      ((image word).toGuestProgram valid.1.1).fetchWord pc = some instructionWord ∧
      (fetch ()).run current.sail = .ok (FetchResult.F_Base instructionWord) current.sail)

private theorem mixed (word : BitVec 32) (left right : BitVec 64) (decoded : instruction)
    (valid : ExecutionSourceValid (image word) (source word left right))
    (hostChecked : hostCheck (FormalModel.Shard.policy SP1Prime (image word))
      ((image word).toGuestProgram valid.1.1) (source word left right) (middle word left right)
      (hint.toEvent 17 65536) = true)
    (parsed : InstructionDecode.decode word = some decoded) (notEcall : word ≠ ECALL_ENC)
    (allowed : InstructionWrite.check (image word).readOnly (middle word left right).sail.skeleton.get_reg?
      decoded = true)
    (executeFrame : ∀ state, SailConfigured state → state.get_reg? 2 = some left →
      state.get_reg? 3 = some right → state.regs.get? Register.PC = some 65540 →
      state.regs.get? Register.nextPC = some 65544 → ∃ next,
      (execute decoded).run state = .ok (.Retire_Success ()) next ∧
        SailConfigured next ∧ next.mem = state.mem) : Preserved word left right := by
  have first := hostStep_of_check (by rfl : (FormalModel.Shard.policy SP1Prime (image word)).memory.upper = 2 ^ 48)
    hostChecked
  have middleFrame := first.syscall_sail_frame
  have cfg := middleFrame.2.2.1 valid.configured
  have rom := (image word).romLoaded_of_readOnly valid.1.1 middleFrame.2.2.2 valid.romLoaded
  have atPc := middle_pc word left right
  have fetched : ((image word).toGuestProgram valid.1.1).fetchWord 65540 = some word := rfl
  have decode := SailDecode.instructionDecode_agrees word decoded parsed
  obtain ⟨next, normal, _⟩ := Advance.retire_frame_of_observed_execute cfg rom atPc fetched decode (by
    intro state cfg registers pc nextPc
    exact executeFrame state cfg ((registers 2).trans (middle_left word left right))
      ((registers 3).trans (middle_right word left right)) pc nextPc)
  have ordinary : ExecutionStep (FormalModel.Shard.policy SP1Prime (image word))
      ((image word).toGuestProgram valid.1.1) (middle word left right).realize .ordinary
      ⟨next, (middle word left right).host, 289⟩ := by
    apply ExecutionStep.ordinary rfl ?_ normal
    rintro ⟨pc, current, ecall⟩
    have same := Option.some.inj (atPc.symm.trans current)
    rw [← same, fetched] at ecall
    exact notEcall (Option.some.inj ecall)
  have path := ExecutionPath.cons first (.cons ordinary (.nil _))
  have permission : InstructionWrite.PermittedAt (image word).readOnly
      ((image word).toGuestProgram valid.1.1) (middle word left right).sail.realize :=
    ⟨65540, word, decoded, atPc, fetched, decode,
      check_of_registers (middle word left right).sail.skeleton (middle word left right).sail.realize
        rfl _ _ allowed⟩
  have permitted : ExecutionPath.WritesPermitted (FormalModel.Shard.policy SP1Prime (image word))
      ((image word).toGuestProgram valid.1.1) (source word left right).realize tape := by
    apply (ExecutionPath.writesPermitted_cons_iff first).mpr
    refine ⟨(fun impossible => nomatch impossible), ?_⟩
    exact (ExecutionPath.writesPermitted_cons_iff ordinary).mpr
      ⟨fun _ => permission, ExecutionPath.writesPermitted_nil⟩
  refine ⟨valid, _, path, ?_, ?_⟩
  · intro cut
    obtain ⟨current, replay, _, _⟩ := path.replay_split cut
    have frame := path.frame_prefix valid.1.1 permitted (fun _ selected => selected)
      valid.configured valid.romLoaded replay
    exact ⟨current, replay, frame.1, frame.2.1⟩
  · exact path.fetch_at valid.1.1 permitted (fun _ selected => selected) valid.configured valid.romLoaded

/-- Padded host RAM writes preserve the following JALR word; its odd base is masked by Sail. -/
theorem hintThenJalr : Preserved 0x000100e7 65553 0 := by
  apply mixed _ _ _ (.JALR (0, .Regidx 2, .Regidx 1))
    ((checkExecutionSource_iff _ _).mp (by native_decide)) (by native_decide) rfl (by decide) (by native_decide)
  intro state cfg left _ _ nextPc
  have ran := Advance.execute_JALR_reaches 0 2 1 65540 65553 state cfg.init cfg.toValidMemConfig
    nextPc left (by decide)
  exact ⟨_, ran, (Advance.jalr_execute_frame state cfg _ _ _ _ _ ran).2⟩

/-- A taken branch after HINT_READ needs its current fetch but no instruction at its destination. -/
theorem hintThenBranch : Preserved 0x00310463 7 7 := by
  apply mixed _ _ _ (.BTYPE (8, .Regidx 3, .Regidx 2, .BEQ))
    ((checkExecutionSource_iff _ _).mp (by native_decide)) (by native_decide) rfl (by decide) (by native_decide)
  intro state cfg left right pc nextPc
  have ran := Advance.execute_BTYPE_reaches 8 2 3 .BEQ 65540 65548 7 7 state cfg.init pc nextPc
    left right (fun _ => rfl) (by decide) (by decide)
  exact ⟨_, ran, (Advance.branch_execute_frame state cfg _ _ _ _ _ _ ran).2⟩

/-- The same mixed semantic fixture counts one host event and one ordinary event at their actual costs. -/
theorem mixedResourceWork :
    ∃ valid : ExecutionSourceValid (image 0x000100e7) (source 0x000100e7 65553 0),
      executionResources (FormalModel.Shard.policy SP1Prime (image 0x000100e7))
        ((image 0x000100e7).toGuestProgram valid.1.1) (source 0x000100e7 65553 0).realize tape .events = 2 ∧
      executionResources (FormalModel.Shard.policy SP1Prime (image 0x000100e7))
        ((image 0x000100e7).toGuestProgram valid.1.1) (source 0x000100e7 65553 0).realize tape .ticks = 272 := by
  obtain ⟨valid, _, path, _⟩ := hintThenJalr
  exact ⟨valid, path.resources_events, path.resources_ticks⟩

/-- The concrete intermediate boundary consumed one hint and overwrote the old padding byte. -/
theorem paddedHostEffect :
    (middle 0x000100e7 65553 0).host.io.hints = [[9]] ∧
      (middle 0x000100e7 65553 0).host.io.publicOutput = [10] ∧
      (source 0x000100e7 65553 0).sail.memory.read 70008 = 99 ∧
      (middle 0x000100e7 65553 0).sail.memory.read 70008 = 0 := by native_decide

private theorem jalr_source_valid : ExecutionSourceValid (image 0x000100e7) (source 0x000100e7 65553 0) := by
  apply (checkExecutionSource_iff _ _).mp
  native_decide

/-- The complete-boundary shard contract supplies the invariant for an active host shard. -/
theorem hintShardPreservesRom :
    ∃ execution : FormalModel.Shard.Executes SP1Prime (image 0x000100e7)
        (source 0x000100e7 65553 0) (middle 0x000100e7 65553 0) [.syscall (hint.toEvent 17 65536)],
      SailConfigured (middle 0x000100e7 65553 0).sail.realize ∧
      RomLoaded ((image 0x000100e7).toGuestProgram execution.1.1.1) (middle 0x000100e7 65553 0).sail.realize := by
  have step := hostStep_of_check
    (policy := FormalModel.Shard.policy SP1Prime (image 0x000100e7))
    (program := (image 0x000100e7).toGuestProgram jalr_source_valid.1.1)
    (before := source 0x000100e7 65553 0) (after := middle 0x000100e7 65553 0)
    (event := hint.toEvent 17 65536) rfl (by native_decide)
  have execution : FormalModel.Shard.Executes SP1Prime (image 0x000100e7)
      (source 0x000100e7 65553 0) (middle 0x000100e7 65553 0) [.syscall (hint.toEvent 17 65536)] := by
    refine ⟨jalr_source_valid, .cons step (.nil _), ?_⟩
    exact (ExecutionPath.writesPermitted_cons_iff step).mpr
      ⟨(fun impossible => nomatch impossible), ExecutionPath.writesPermitted_nil⟩
  exact ⟨execution, execution.frame.1, execution.frame.2.1⟩

/-- HINT_READ cannot write its last padding byte when that byte is protected, even if already zero. -/
theorem rejectsProtectedPadding :
    hostCheck
      { FormalModel.Shard.policy SP1Prime (image 0x000100e7) with
        memory.readOnly := fun address => (image 0x000100e7).readOnly address || address == 70015 }
      ((image 0x000100e7).toGuestProgram jalr_source_valid.1.1)
      (source 0x000100e7 65553 0) (middle 0x000100e7 65553 0) (hint.toEvent 17 65536) = false := by
  native_decide

/-- A claimed prefix with any corrupted byte of the later ordinary word contradicts path preservation. -/
theorem rejectsCorruptedPrefix (target : ExecutionState)
    (path : ExecutionPath (FormalModel.Shard.policy SP1Prime (image 0x000100e7))
      ((image 0x000100e7).toGuestProgram jalr_source_valid.1.1)
      (source 0x000100e7 65553 0).realize tape target)
    (permitted : ExecutionPath.WritesPermitted (FormalModel.Shard.policy SP1Prime (image 0x000100e7))
      ((image 0x000100e7).toGuestProgram jalr_source_valid.1.1) (source 0x000100e7 65553 0).realize tape)
    (cut : ℕ) (offset : Fin 4) :
    executionTrajectory (FormalModel.Shard.policy SP1Prime (image 0x000100e7))
      ((image 0x000100e7).toGuestProgram jalr_source_valid.1.1) (source 0x000100e7 65553 0).realize tape cut ≠
        some { (middle 0x000100e7 65553 0).realize with
          sail.mem := (middle 0x000100e7 65553 0).sail.realize.mem.insert (65540 + offset) 255 } := by
  intro corrupted
  have rom := (path.frame_prefix jalr_source_valid.1.1 permitted (fun _ selected => selected)
    jalr_source_valid.configured jalr_source_valid.romLoaded corrupted).2.1
  have byte := rom 65540 0x000100e7 rfl offset
  change ((middle 0x000100e7 65553 0).sail.realize.mem.insert (65540 + offset) 255).get? (65540 + offset) = _ at byte
  have inserted : ((middle 0x000100e7 65553 0).sail.realize.mem.insert (65540 + offset) 255).get?
      (65540 + offset) = some 255 := Std.ExtHashMap.getElem?_insert_self
  have distinct : ∀ index : Fin 4, (0x000100e7#32).extractLsb' (8 * index) 8 ≠ 255 := by decide +kernel
  exact distinct offset (Option.some.inj (inserted.symm.trans byte)).symm

end SP1CleanTest.Core.ExecutionRom
