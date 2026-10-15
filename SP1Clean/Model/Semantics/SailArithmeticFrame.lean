import SP1Clean.Model.Semantics.SailArithmeticExecute
import SP1Clean.Model.Semantics.SailExecuteFrame

/-! # Circuit-independent arithmetic retirement and memory frames

Authenticated arithmetic decoding gives an actual normal Sail retirement that preserves the
platform configuration and entire memory map, including x0. The existing official execute-stage
lemmas supply the values; no native chip row or arithmetic constraints enter these statements.
Memory and control-flow instruction families require separate semantic proofs.
-/

namespace SP1Clean.Advance
open SP1Clean Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Defs LeanRV64D.Functions
open SP1Clean.Soundness.Target SP1Clean.TryStepReduction

/-- Arithmetic constructors whose execute stage writes at most one GPR. This is a proof
classification of Sail instructions, not the native supported-program or resource profile. -/
def ArithmeticInstruction : instruction → Prop
  | .RTYPE _ => True
  | .RTYPEW _ => True
  | .ITYPE _ => True
  | .SHIFTIOP _ => True
  | .SHIFTIWOP _ => True
  | .ADDIW _ => True
  | .UTYPE _ => True
  | .DIV _ => True
  | .REM _ => True
  | .DIVW _ => True
  | .REMW _ => True
  | .MUL _ => True
  | .MULW _ => True
  | _ => False

/-- Every arithmetic execute stage preserves the platform configuration and complete memory,
including the x0 and signed/unsigned multiply/divide cases. No chip witness is constructed. -/
theorem arithmetic_execute_frame (state : SailState) (cfg : SailConfigured state)
    (decoded : instruction) (arithmetic : ArithmeticInstruction decoded) : ∃ next,
      (execute decoded).run state = .ok (.Retire_Success ()) next ∧
        SailConfigured next ∧ next.mem = state.mem := by
  unfold ArithmeticInstruction at arithmetic
  split at arithmetic
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, op⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, rtype_execute_reaches rs2 rs1 rd op left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, op⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, rtypew_execute_reaches rs2 rs1 rd op left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨imm, ⟨rs1⟩, ⟨rd⟩, op⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    exact ⟨_, itype_execute_reaches imm rs1 rd op left state leftRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨shamt, ⟨rs1⟩, ⟨rd⟩, op⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    exact ⟨_, shiftitype_execute_reaches shamt rs1 rd op left state leftRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨shamt, ⟨rs1⟩, ⟨rd⟩, op⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    exact ⟨_, shiftiwtype_execute_reaches shamt rs1 rd op left state leftRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨imm, ⟨rs1⟩, ⟨rd⟩⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    exact ⟨_, execute_ADDIW_reaches imm rs1 rd left state leftRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨imm, ⟨rd⟩, op⟩
    exact ⟨_, execute_UTYPE_reaches imm rd op _ state (Std.ExtDHashMap.get?_eq_some_get (cfg.init _)),
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, isU⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, execute_DIV_reaches rs2 rs1 rd isU left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, isU⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, execute_REM_reaches rs2 rs1 rd isU left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, isU⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, execute_DIVW_reaches rs2 rs1 rd isU left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, isU⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, execute_REMW_reaches rs2 rs1 rd isU left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩, op⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, execute_MUL_reaches rs2 rs1 rd op left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next =>
    rename_i operands
    rcases operands with ⟨⟨rs2⟩, ⟨rs1⟩, ⟨rd⟩⟩
    obtain ⟨left, leftRead⟩ := initialized_gpr state cfg.init rs1
    obtain ⟨right, rightRead⟩ := initialized_gpr state cfg.init rs2
    exact ⟨_, execute_MULW_reaches rs2 rs1 rd left right state leftRead rightRead,
      SailConfigured.writeGPR cfg rd _, by split_ifs <;> rfl⟩
  next => contradiction

/-- Authenticated arithmetic instructions actually retire normally, without requiring another
instruction at the outgoing PC. Configuration and the whole byte map are preserved. -/
theorem arithmetic_retire {program : GuestProgram} {source : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (arithmetic : ArithmeticInstruction decoded) :
    ∃ target, SailRetiresNormally source target ∧ SailConfigured target ∧ target.mem = source.mem :=
  retire_frame_of_execute configured loaded atPc fetched decode
    (fun state cfg => arithmetic_execute_frame state cfg decoded arithmetic)

/-- Every actual normal retirement agrees with the constructed arithmetic successor. -/
theorem arithmetic_normal_frame {program : GuestProgram} {source target : SailState}
    {pc : BitVec 64} {word : BitVec 32} {decoded : instruction}
    (configured : SailConfigured source) (loaded : RomLoaded program source)
    (atPc : source.regs.get? Register.PC = some pc)
    (fetched : program.fetchWord pc = some word) (decode : ConfiguredDecode word decoded)
    (arithmetic : ArithmeticInstruction decoded) (normal : SailRetiresNormally source target) :
    SailConfigured target ∧ target.mem = source.mem := by
  obtain ⟨actual, retired, frame⟩ := arithmetic_retire configured loaded atPc fetched decode arithmetic
  obtain ⟨_, _, _, _, _, actualRun⟩ := retired
  obtain ⟨_, _, _, _, _, targetRun⟩ := normal
  rw [actualRun] at targetRun
  cases targetRun
  exact frame

end SP1Clean.Advance
