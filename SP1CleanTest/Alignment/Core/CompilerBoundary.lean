import SP1Clean.Proofs.Completeness.SemanticAccess
import SP1Clean.Model.Machine.ConfiguredState
import SP1Clean.Model.Semantics.SailControlExecute

/-! # Control-flow compiler boundary counterexamples

These fixtures isolate a real remaining validity obligation without changing the public semantic
domain. A last-slot JAL retires at the official Sail execute stage, but its link is 2^48. For x0,
the link circuit is disabled and the event contract is too strong; for a nonzero destination,
the enabled native link arithmetic imposes a genuine 48-bit AIR restriction. An untaken branch
likewise need not bound its unselected candidate. These are execute-stage and event-contract
counterexamples, not a claim that the complete mixed capstone has been instantiated.
-/

namespace SP1CleanTest.Core.CompilerBoundary
open SP1Clean SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Soundness.Target
open SP1Clean.TraceGen LeanRV64D.Defs LeanRV64D.Functions

private def lastPc : BitVec 64 := BitVec.ofNat 64 (2 ^ 48 - 4)

private def image : ProgramImage := ⟨[(lastPc, 0x000000EF)], lastPc, []⟩

/-- The checked loader accepts the final four-byte instruction slot, including JAL x1, 0. -/
theorem lastSlot_image_valid : image.Valid := by native_decide

private def staged (pc : BitVec 64) : SailState :=
  { configuredState pc with regs := (configuredState pc).regs.insert Register.nextPC (pc + 4#64) }

private theorem staged_initialized (pc : BitVec 64) : (staged pc).isInitialized :=
  SailState.isInitialized_insert _ (cfgState_init pc) _ _

private theorem staged_pc (pc : BitVec 64) : (staged pc).regs.get? Register.PC = some pc := by
  change ((configuredState pc).regs.insert Register.nextPC (pc + 4#64)).get? Register.PC = some pc
  rw [Std.ExtDHashMap.get?_insert, dif_neg (by decide)]
  exact cfgState_pc pc

private def jalTarget (rd : BitVec 5) : SailState :=
  if rd = 0 then
    { staged lastPc with regs := (staged lastPc).regs.insert Register.nextPC lastPc }
  else
    { staged lastPc with regs := (((staged lastPc).regs.insert Register.nextPC lastPc).insert
      (reg_idx_to_Register rd) (bitVecToRegidxVal rd (lastPc + 4#64))) }

/-- Official Sail JAL execute succeeds for every destination at the top instruction slot.
In particular Sail does not require the link value to be a 48-bit program counter. -/
theorem lastSlot_jal_executes (rd : BitVec 5) :
    (execute (.JAL (0, .Regidx rd))).run (staged lastPc) =
      .ok (.Retire_Success ()) (jalTarget rd) := by
  exact Advance.execute_JAL_reaches 0 rd lastPc (staged lastPc)
      (staged_initialized lastPc) (staged_pc lastPc)
      (by simp only [staged, Std.ExtDHashMap.get?_insert_self]) (by decide)

private def lastEvent (rd : ℕ) : JTypeEvent where
  clk := 1
  pc := 2 ^ 48 - 4
  opcode := 46
  opA := rd
  immB := 0
  immC := 0
  prevA := 0
  prevTsA := 0

private def compiledJal (rd : BitVec 5) : Option CompiledInstructionEvent :=
  compileInstructionEvent?
    ⟨lastPc, if rd = 0 then 0x0000006F else 0x000000EF,
      .JAL (0, .Regidx rd), ⟨.JAL, decide (rd = 0)⟩, .jal,
      instructionAccessPlan? (.JAL (0, .Regidx rd)) (staged lastPc) (jalTarget rd)⟩
    AccessFrontier.initial 1

private def jalFields (event : JTypeEvent) : List ℕ :=
  [event.clk, event.pc, event.opcode, event.opA, event.immB, event.immC, event.prevA, event.prevTsA]

private def compiledJalFields (rd : BitVec 5) : Option (List ℕ) := do
  let result ← compiledJal rd
  let event ← result.routed.forId? .jal
  pure (jalFields event)

/-- The actual compiler applied to the same official-execute source/target pairs emits all eight
fields of the rejected event for both the discarded and enabled link forms. -/
theorem lastSlot_compiled_events :
    (compiledJalFields 0, compiledJalFields 1) =
      (some (jalFields (lastEvent 0)), some (jalFields (lastEvent 1))) := by
  native_decide

/-- All ordinary JAL event fields are valid for both x0 and a genuine link destination. -/
theorem lastEvent_wellFormed (rd : ℕ) (small : rd < 32) : (lastEvent rd).WellFormedJal := by
  constructor <;> simp [lastEvent]
  exact small

/-- The actual self-jump destination is representable and aligned. Only the link condition fails. -/
theorem lastEvent_target (rd : ℕ) :
    (lastEvent rd).jalTarget < 2 ^ 48 ∧ (lastEvent rd).jalTarget % 4 = 0 := by
  norm_num [lastEvent, JTypeEvent.jalTarget]

/-- This is the named repair obligation for deriving full JAL validity at the semantic boundary:
`JalTargets` currently rejects every last-slot self-jump, including the link-discarding x0 form. -/
theorem lastEvent_not_valid (rd : ℕ) : ¬ InstructionChipId.jal.Valid (lastEvent rd) := by
  simp [InstructionChipId.Valid, JTypeEvent.JalTargets, lastEvent]

private def untakenEvent : ITypeEvent where
  clk := 1
  pc := 2 ^ 48 - 8
  opcode := 41
  opA := 0
  opB := 0
  imm := 16
  b := 0
  prevA := 0
  prevTsA := 4
  prevTsB := 0

/-- The untaken BNE x0, x0, +16 has a valid selected next PC, while its unselected target is
outside the 48-bit window and violates the stronger existing event predicate. -/
theorem untakenBranch_selected_valid_candidate_invalid :
    untakenEvent.branchTaken = false ∧
      untakenEvent.branchNextPc < 2 ^ 48 ∧ untakenEvent.branchNextPc % 4 = 0 ∧
      ¬ untakenEvent.BranchTargets := by
  unfold ITypeEvent.BranchTargets
  native_decide

/-- Official Sail also executes that untaken branch: no target-address check is imposed on the
candidate that the instruction does not select. -/
theorem untakenBranch_executes :
    ∃ target, (execute (.BTYPE (16, .Regidx 0, .Regidx 0, .BNE))).run
      (staged (BitVec.ofNat 64 (2 ^ 48 - 8))) = .ok (.Retire_Success ()) target := by
  exact ⟨_, Advance.execute_BTYPE_reaches 16 0 0 .BNE _ _ 0 0 _
    (staged_initialized _) (staged_pc _)
    (by simp only [staged, Std.ExtDHashMap.get?_insert_self])
    (by simp [SailState.get_reg?]) (by simp [SailState.get_reg?])
    (by decide) (fun _ => rfl) (by decide)⟩

end SP1CleanTest.Core.CompilerBoundary
