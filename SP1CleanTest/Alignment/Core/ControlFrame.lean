import SP1Clean.Model.Semantics.SailControlExecute
import SP1Clean.Model.Semantics.SailControlFrame
import SP1Clean.Model.Core.SourceExecution
import SP1Clean.Proofs.Sail.InstructionDecode

/-! # Normally retiring control flow without circuit rows

Each fixture authenticates a single committed instruction, constructs its official retirement
from the Sail execute lemma, and applies the independent normal-retirement frame theorem.
No successor instruction is present for outgoing jumps. Native evaluation checks only finite
source data and operands; the retirement and preservation proofs run through the Lean kernel.
-/

namespace SP1CleanTest.Core.ControlFrame

open SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target LeanRV64D.Defs LeanRV64D.Functions

private def image (word : BitVec 32) : ProgramImage := ⟨[(65536, word)], 65536, []⟩

private def source (word : BitVec 32) (left right : BitVec 64) : ExecutionSnapshot where
  sail := { registers := ((configuredState 65536).regs.insert .x2 left).insert .x3 right
            memory := (image word).initialMemory }
  host := {}
  clock := 17

private def RetiresWithFrame (word : BitVec 32) (left right : BitVec 64) : Prop :=
  ∃ target, SailRetiresNormally (source word left right).sail.realize target ∧
    SailConfigured target ∧ target.mem = (source word left right).sail.realize.mem

private theorem source_left (word : BitVec 32) (left right : BitVec 64) :
    (source word left right).sail.realize.get_reg? 2 = some left := by
  change (((configuredState 65536).regs.insert .x2 left).insert .x3 right).get? .x2 = some left
  simp only [Std.ExtDHashMap.get?_insert, beq_iff_eq, reduceCtorEq, ↓reduceDIte, cast_eq]

private theorem source_right (word : BitVec 32) (left right : BitVec 64) :
    (source word left right).sail.realize.get_reg? 3 = some right := by
  change (((configuredState 65536).regs.insert .x2 left).insert .x3 right).get? .x3 = some right
  exact Std.ExtDHashMap.get?_insert_self

private theorem retires (word : BitVec 32) (left right : BitVec 64) (decoded : instruction)
    (checked : checkExecutionSource (image word) (source word left right) = true)
    (parsed : InstructionDecode.decode word = some decoded)
    (control : Advance.ControlFlowInstruction decoded)
    (executeFrame : ∀ state, SailConfigured state →
      (∀ index, state.get_reg? index = (source word left right).sail.realize.get_reg? index) →
      state.regs.get? Register.PC = some 65536 →
      state.regs.get? Register.nextPC = some 65540 → ∃ next,
      (execute decoded).run state = .ok (.Retire_Success ()) next ∧
        SailConfigured next ∧ next.mem = state.mem) : RetiresWithFrame word left right := by
  have valid := (checkExecutionSource_iff _ _).mp checked
  have pc : (source word left right).pc = 65536 := by
    simp only [ExecutionSnapshot.pc, source, configuredState, Std.ExtDHashMap.get?_insert,
      beq_iff_eq, reduceCtorEq, ↓reduceDIte, Option.getD_some, cast_eq]
  have atPc : (source word left right).sail.realize.regs.get? Register.PC = some 65536 := by
    simpa only [pc] using valid.pc
  have fetched : ((image word).toGuestProgram valid.1.1).fetchWord 65536 = some word := rfl
  have decoded := SailDecode.instructionDecode_agrees word decoded parsed
  obtain ⟨target, normal, _⟩ := Advance.retire_frame_of_observed_execute
    valid.configured valid.romLoaded atPc fetched decoded executeFrame
  exact ⟨target, normal,
    Advance.control_normal_frame valid.configured valid.romLoaded atPc fetched decoded control normal⟩

/-- JAL may finish beyond the only committed word; it does not need a terminal fetch. -/
theorem jalLeavesRom : RetiresWithFrame 0x008000ef 0 0 := by
  apply retires _ _ _ (.JAL (8, .Regidx 1)) (by native_decide) rfl trivial
  intro state cfg _ pc nextPc
  have ran := Advance.execute_JAL_reaches 8 1 65536 state cfg.init pc nextPc (by decide)
  exact ⟨_, ran, (Advance.jal_execute_frame state cfg _ _ _ _ ran).2⟩

/-- The JAL link may be discarded at x0 without changing the memory frame. -/
theorem jalToZero : RetiresWithFrame 0x0000006f 0 0 := by
  apply retires _ _ _ (.JAL (0, .Regidx 0)) (by native_decide) rfl trivial
  intro state cfg _ pc nextPc
  have ran := Advance.execute_JAL_reaches 0 0 65536 state cfg.init pc nextPc (by decide)
  exact ⟨_, ran, (Advance.jal_execute_frame state cfg _ _ _ _ ran).2⟩

/-- JALR accepts an odd base after clearing bit zero; its outgoing PC needs no further fetch. -/
theorem jalrMasksLowBit : RetiresWithFrame 0x000100e7 65545 0 := by
  apply retires _ _ _ (.JALR (0, .Regidx 2, .Regidx 1)) (by native_decide) rfl trivial
  intro state cfg registers _ nextPc
  have base : state.get_reg? 2 = some 65545 :=
    (registers 2).trans (source_left _ _ _)
  have ran := Advance.execute_JALR_reaches 0 2 1 65536 65545 state cfg.init
    cfg.toValidMemConfig nextPc base (by decide)
  exact ⟨_, ran, (Advance.jalr_execute_frame state cfg _ _ _ _ _ ran).2⟩

/-- A taken branch retires into a boundary outside the finite ROM image. -/
theorem branchTaken : RetiresWithFrame 0x00310463 7 7 := by
  apply retires _ _ _ (.BTYPE (8, .Regidx 3, .Regidx 2, .BEQ)) (by native_decide) rfl trivial
  intro state cfg registers pc nextPc
  have left : state.get_reg? 2 = some 7 := (registers 2).trans (source_left _ _ _)
  have right : state.get_reg? 3 = some 7 := (registers 3).trans (source_right _ _ _)
  have ran := Advance.execute_BTYPE_reaches 8 2 3 .BEQ 65536 65544 7 7 state cfg.init pc nextPc
    left right (fun _ => rfl) (by decide) (by decide)
  exact ⟨_, ran, (Advance.branch_execute_frame state cfg _ _ _ _ _ _ ran).2⟩

/-- An untaken branch does not demand alignment of its unused branch destination. -/
theorem branchNotTakenMisalignedOffset : RetiresWithFrame 0x00310163 7 8 := by
  apply retires _ _ _ (.BTYPE (2, .Regidx 3, .Regidx 2, .BEQ)) (by native_decide) rfl trivial
  intro state cfg registers pc nextPc
  have left : state.get_reg? 2 = some 7 := (registers 2).trans (source_left _ _ _)
  have right : state.get_reg? 3 = some 8 := (registers 3).trans (source_right _ _ _)
  have ran := Advance.execute_BTYPE_reaches 2 2 3 .BEQ 65536 65540 7 8 state cfg.init pc nextPc
    left right (by decide) (fun _ => rfl) (by decide)
  exact ⟨_, ran, (Advance.branch_execute_frame state cfg _ _ _ _ _ _ ran).2⟩

end SP1CleanTest.Core.ControlFrame
