import SP1Clean.Proofs.Completeness.SemanticAccess
import SP1Clean.Alignment.Chips.BranchChip.Bridge
import SP1Clean.Model.SP1Field
import Clean.Air.WitnessGeneration
import ToClean.Air.EnsembleBuild

/-! # A decoded branch, its official Sail step, and its compiler-built local circuit

The checked image contains `BEQ x1, x2, +4092` at 65536. Both operands start at zero.
Every event and circuit cell below comes from the actual semantic event compiler and Clean's
witness builder. The canonical projection is identified with that compiler input for the same
normally retiring official Sail transition. Acceptance means one local Branch table's constraints;
no provider construction, channel balance, or complete shard relation is claimed.
-/

namespace SP1Clean.Audit.BranchCompilerRoundTrip

open Circuit Air.Flat SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Soundness.Target
open SP1Clean.TraceGen LeanRV64D.Defs LeanRV64D.Functions

/-- A single full-width BEQ word at the native guest-memory lower bound. -/
def image : ProgramImage := ⟨[(65536, 0x7e208ee3)], 65536, []⟩

/-- The finite loader checks accept the branch image. -/
theorem image_valid : image.Valid := by native_decide

/-- The semantic program constructed by the checked-image loader. -/
def program : GuestProgram := image.toGuestProgram image_valid

/-- Canonical Sail initialization, including the actual ROM bytes and zeroed registers. -/
noncomputable def source : SailState := image.initialSailState

/-- Configuration, initialization, entry PC and loaded memory follow from image validation. -/
theorem source_loaded : IsInitialState program source := image.initialSailState_loaded image_valid

/-- The actual source PC is the committed entry point. -/
theorem source_pc : source.regs.get? Register.PC = some 65536#64 := source_loaded.pc

/-- Both compared registers, like every initial integer register, contain zero. -/
theorem source_registers (index : BitVec 5) : source.get_reg? index = some 0#64 :=
  image.initialSailState_registersZero index

/-- Fetching the committed source address returns the exact BEQ encoding. -/
theorem program_fetch : program.fetchWord 65536#64 = some 0x7e208ee3#32 := by native_decide

/-- Actual generated Sail decoding, valid in every configured state used by the retirement ladder. -/
theorem decode_branch (state : SailState) (cfg : SailConfigured state) :
    (ext_decode 0x7e208ee3#32).run state =
      .ok (.BTYPE (4092#13, .Regidx 2#5, .Regidx 1#5, .BEQ)) state := by
  conv_lhs => whnf
  rw [SailDecode.cePause_apply]
  conv_lhs => whnf
  rw [SailDecode.ceZicfilp_bind_apply state cfg.init cfg.priv cfg.mseccfg_disabled]
  conv_lhs => whnf
  rfl

/-- A computable normal form of the canonical access plan, with both source observations proved below. -/
def plan : InstructionAccessPlan :=
  [⟨.opB, .reg 2#5, 0#64, 0#64⟩, ⟨.opA, .reg 1#5, 0#64, 0#64⟩]

/-- Executable normal form of the canonical projection, authenticated by `projected`. -/
def view : SP1TransitionView where
  pc := 65536
  word := 0x7e208ee3
  decoded := .BTYPE (4092, .Regidx 2, .Regidx 1, .BEQ)
  routeKey := ⟨.BEQ, false⟩
  chipId := .branch
  accessPlan? := some plan

/-- Branch plans read their operands from the actual source; the target cannot alter the compiler input. -/
theorem actual_access_plan (target : SailState) :
    instructionAccessPlan? view.decoded source target = some plan := by
  change Option.map _ ((source.get_reg? 2#5).bind _) = some plan
  simp only [source_registers, Option.bind_some]
  rfl

/-- The real decoder and access extractor produce this view for the actual source and any target. -/
theorem projected (target : SailState) :
    projectSP1Transition? program ⟨source, ⟨.ordinary, target⟩⟩ = some view := by
  unfold projectSP1Transition?
  simp only [source_pc, Option.bind_eq_bind, Option.bind_some, program_fetch]
  rw [decodeLocated?_eq_some_of source_pc program_fetch (decode_branch source source_loaded.configured)]
  change some { view with accessPlan? := instructionAccessPlan? view.decoded source target } = some view
  rw [actual_access_plan]
  rfl

/-- The deterministic compiler at the canonical first frontier and ordinary clock. -/
def compiled? : Option CompiledInstructionEvent := compileInstructionEvent? view AccessFrontier.initial 1

/-- This concrete canonical compiler input succeeds. -/
theorem compiled_present : compiled?.isSome = true := by native_decide

/-- Extracted from the real compiler, without a fallback event. -/
def compiled : CompiledInstructionEvent := compiled?.get compiled_present

/-- The extracted result is exactly the successful compiler output. -/
theorem compiled_eq : compiled? = some compiled := Option.some_get compiled_present |>.symm

/-- The compiler routes its payload to the Branch table. -/
theorem branch_present : (compiled.routed.forId? .branch).isSome = true := by native_decide

/-- The exact payload of the compiler's routed result. -/
def event : ITypeEvent := (compiled.routed.forId? .branch).get branch_present

/-- Both the registry identity and dependent payload are preserved by extraction. -/
theorem compiled_routed : compiled.routed = ⟨.branch, event⟩ := by rfl

/-- Every existing local Branch completeness obligation is discharged on the compiled event. -/
theorem event_valid : event.WellFormedBranch ∧ event.IsBranch ∧ event.BranchTargets := by
  refine ⟨?_, ?_, ?_⟩
  · constructor <;> native_decide
  · unfold ITypeEvent.IsBranch
    native_decide
  · unfold ITypeEvent.BranchTargets
    native_decide

/-- The full thirteen-bit positive offset survives compilation, and the equal-operand branch is taken. -/
theorem event_target : event.imm = 4092 ∧ event.branchTaken = true ∧ event.branchNextPc = 69628 := by
  native_decide

/-- Local row generation needs no external provider table data. -/
def data : ProverData (ZMod SP1Prime) := fun _ _ => #[]

/-- The actual circuit witness generated from the identical compiled event. -/
def row : Array (ZMod SP1Prime) :=
  BranchChip.component.buildRow event.toBranchInputs data (ProverHint.empty _)

/-- The environment reads the actual generated row cells. -/
def env : Environment (ZMod SP1Prime) := Environment.fromArray row data

/-- Typed circuit output decoded from the generated physical row. -/
def columns : BranchChip.Columns (ZMod SP1Prime) := BranchChip.component.rowOutput env

/-- The existing Branch semantic adapter applied to that same input/output row. -/
def rowView : Trace.RowView (ZMod SP1Prime) := BranchChip.rowView event.toBranchInputs columns

/-- The witnessed next-PC cells commit exactly the semantic branch target. -/
theorem row_target : sndPcOf (SP1Clean.Soundness.stateAccess rowView) = 69628#64 := by
  native_decide

/-- One circuit-built Branch table, with the compiled event and no padding. -/
def table : Table (ZMod SP1Prime) :=
  Table.build BranchChip.component (BranchChip.traceInputs [event] 0) data (ProverHint.empty _)

/-- Completeness checks the real local table. It does not assert ensemble channel balance. -/
theorem table_constraints : table.Constraints data :=
  BranchChip.traceTable_constraints [event] 0 data (by simpa using event_valid)

/-- The accepted table contains exactly the generated non-padding row. -/
theorem table_one_real_row : table.table = [row] ∧
    (BranchChip.component.rowInput env).is_real = 1 := by native_decide

/-- Clean's executable constraint checker on the single physical table. It evaluates canonical
data and rejects unchecked legacy lookups; no channel-balance claim is made. -/
def flatCheck : Bool :=
  WitnessGeneration.constraintsHold <| EnsembleWitness.ofTables
    ({ tables := [BranchChip.component], unique_names := by simp, channels := [] } :
      Ensemble (ZMod SP1Prime) unit)
    [table] () rfl

/-- The independent executable whole-row constraint check accepts. -/
theorem flat_check : flatCheck = true := by native_decide

/-- The same decoded instruction executes through the complete official Sail retirement ladder. -/
theorem official_step_exists :
    ∃ target, SailStep source target ∧ RowEffect program rowView source target := by
  refine Advance.advance_of_ctrl (p := SP1Prime)
    (.BTYPE (4092#13, .Regidx 2#5, .Regidx 1#5, .BEQ)) 69628#64 65536#64
    0xe3#8 0x8e#8 0x20#8 0x7e#8 source_loaded.configured source_pc
    (Advance.fetchReady_of_romLoaded program source _ _ source_loaded.romLoaded program_fetch source_pc)
    (fun state cfg => decode_branch state cfg) ?_ row_target rfl
  intro staged frame pc next initialized _
  exact Advance.execute_BTYPE_reaches 4092#13 1#5 2#5 .BEQ 65536#64 69628#64 0#64 0#64
    staged initialized (pc.trans source_pc) next
    ((frame 1#5).trans (source_registers 1#5)) ((frame 2#5).trans (source_registers 2#5))
    (by decide) (by decide) (by decide)

/-- The complete target state of the proved official Sail step. -/
noncomputable def target : SailState := Classical.choose official_step_exists

/-- Normal retirement and complete architectural effects retained from the official step. -/
theorem target_effect : RowEffect program rowView source target :=
  (Classical.choose_spec official_step_exists).2

/-- The full official interpreter step returns this target, including retirement bookkeeping. -/
theorem official_try_step : (try_step 0 false).run source = .ok false target := by
  obtain ⟨_, _, _, _, _, stepped⟩ := target_effect.normal
  exact stepped

/-- The PC observed in the actual retired Sail state agrees with the generated row. -/
theorem target_pc : target.regs.get? Register.PC = some 69628#64 := by
  rw [target_effect.pc, row_target]

/-- The fetched BEQ word selects the ordinary semantic step, not the host-call arm. -/
theorem not_ecall : ¬ SP1Clean.Machine.AboutToExecuteEcall program source := by
  rintro ⟨pc, atPc, fetched⟩
  rw [source_pc] at atPc
  cases Option.some.inj atPc
  rw [program_fetch] at fetched
  exact (by decide : (0x7e208ee3#32 : BitVec 32) ≠ ECALL_ENC) (Option.some.inj fetched)

/-- Complete state/host/clock carrier for this ordinary step; the host policy is irrelevant to BEQ. -/
theorem execution_step (policy : HostPolicy) :
    ExecutionStep policy program ⟨source, {}, 1⟩ .ordinary ⟨target, {}, 9⟩ :=
  ExecutionStep.ordinary rfl not_ecall target_effect.normal

/-- One joined claim: official normal execution, canonical projection, exact compiler output,
the event/physical-row target, and acceptance of the single real local circuit row. -/
theorem joined (policy : HostPolicy) :
    (try_step 0 false).run source = .ok false target ∧
    ExecutionStep policy program ⟨source, {}, 1⟩ .ordinary ⟨target, {}, 9⟩ ∧
    target.regs.get? Register.PC = some 69628#64 ∧
    projectSP1Transition? program ⟨source, ⟨.ordinary, target⟩⟩ = some view ∧
    compileInstructionEvent? view AccessFrontier.initial 1 = some compiled ∧
    compiled.routed = ⟨.branch, event⟩ ∧ event.branchNextPc = 69628 ∧
    sndPcOf (SP1Clean.Soundness.stateAccess rowView) = 69628#64 ∧
    table.Constraints data ∧ table.table = [row] ∧
    (BranchChip.component.rowInput env).is_real = 1 ∧ flatCheck = true :=
  ⟨official_try_step, execution_step policy, target_pc, projected target, compiled_eq,
    compiled_routed, event_target.2.2, row_target, table_constraints, table_one_real_row.1,
    table_one_real_row.2, flat_check⟩

end SP1Clean.Audit.BranchCompilerRoundTrip
