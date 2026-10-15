import SP1Clean.Alignment.Chips.DecodedProgramProvider.Bridge
import SP1Clean.Model.SP1Field
import Clean.Circuit.WitnessExport

/-! # Executable decoder and fixed Program AIR regressions

Literal instruction encodings cover the entire SP1 opcode projection supported by RV64IM, plus
immediate and reserved-bit edge cases. The uniform parser/Sail agreement theorem is in the main
proof library; these regressions also witness the official hint-extension priority concretely.
-/

namespace SP1CleanTest.Core.InstructionDecode

open Circuit LeanRV64D.Defs SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.Channels

private abbrev Fp := ZMod SP1Clean.SP1Prime

/-- One literal encoding per supported SP1 discriminant, in discriminant order. -/
private def examples : List (BitVec 32 × Opcode) :=
  [(0x003100b3, .ADD), (0x00710093, .ADDI), (0x403100b3, .SUB),
   (0x003140b3, .XOR), (0x003160b3, .OR), (0x003170b3, .AND),
   (0x003110b3, .SLL), (0x003150b3, .SRL), (0x403150b3, .SRA),
   (0x003120b3, .SLT), (0x003130b3, .SLTU),
   (0x023100b3, .MUL), (0x023110b3, .MULH), (0x023130b3, .MULHU),
   (0x023120b3, .MULHSU), (0x023140b3, .DIV), (0x023150b3, .DIVU),
   (0x023160b3, .REM), (0x023170b3, .REMU),
   (0x003100bb, .ADDW), (0x403100bb, .SUBW), (0x003110bb, .SLLW),
   (0x003150bb, .SRLW), (0x403150bb, .SRAW), (0x023100bb, .MULW),
   (0x023140bb, .DIVW), (0x023150bb, .DIVUW), (0x023160bb, .REMW),
   (0x023170bb, .REMUW),
   (0x00010083, .LB), (0x00011083, .LH), (0x00012083, .LW),
   (0x00014083, .LBU), (0x00015083, .LHU), (0x00016083, .LWU), (0x00013083, .LD),
   (0x00110023, .SB), (0x00111023, .SH), (0x00112023, .SW), (0x00113023, .SD),
   (0x00208463, .BEQ), (0x00209463, .BNE), (0x0020c463, .BLT),
   (0x0020d463, .BGE), (0x0020e463, .BLTU), (0x0020f463, .BGEU),
   (0x008000ef, .JAL), (0x004100e7, .JALR), (0x00001097, .AUIPC),
   (0x000010b7, .LUI), (0x00000073, .ECALL)]

/-- No supported SP1 opcode is omitted by the literal-encoding battery. -/
theorem opcodeCoverage : examples.map Prod.snd = Opcode.all.take 51 := by native_decide

/-- Parsing and field projection reach every supported discriminant. -/
theorem literalEncodings : examples.all (fun (word, opcode) =>
    ((ProgramTable.message? (p := SP1Clean.SP1Prime) (65536, word)).map fun msg =>
      msg.opcode == (opcode.toNat : Fp)).getD false) = true := by native_decide

/-- Signed/discontiguous immediates, all shift-width boundaries, and register endpoints. -/
theorem operandEdges :
    InstructionDecode.decode 0xfff00f93 = some (.ITYPE (0xfff, .Regidx 0, .Regidx 31, .ADDI)) ∧
    InstructionDecode.decode 0x03f11093 = some (.SHIFTIOP (63, .Regidx 2, .Regidx 1, .SLLI)) ∧
    InstructionDecode.decode 0x02015093 = some (.SHIFTIOP (32, .Regidx 2, .Regidx 1, .SRLI)) ∧
    InstructionDecode.decode 0x43f15093 = some (.SHIFTIOP (63, .Regidx 2, .Regidx 1, .SRAI)) ∧
    InstructionDecode.decode 0x01f1109b = some (.SHIFTIWOP (31, .Regidx 2, .Regidx 1, .SLLIW)) ∧
    InstructionDecode.decode 0x41f1509b = some (.SHIFTIWOP (31, .Regidx 2, .Regidx 1, .SRAIW)) ∧
    InstructionDecode.decode 0xfff1009b = some (.ADDIW (0xfff, .Regidx 2, .Regidx 1)) ∧
    InstructionDecode.decode 0xfe208ee3 = some (.BTYPE (0x1ffc, .Regidx 2, .Regidx 1, .BEQ)) ∧
    InstructionDecode.decode 0xfffff0ef = some (.JAL (0x1ffffe, .Regidx 1)) ∧
    InstructionDecode.decode 0xfe113c23 = some (.STORE (0xff8, .Regidx 1, .Regidx 2, 8)) := by
  and_intros <;> rfl

/-- Reserved shifts/functions and out-of-profile system, atomic, floating and compressed words fail. -/
theorem rejectedEncodings :
    [0x00000000, 0x00000001, 0x0000000f, 0x0000100f, 0x00100073, 0x30200073,
     0x00111073, 0x00017083, 0x00114023, 0x000120e7, 0x0201109b,
     0x04011093, 0x04015093, 0x0201509b, 0x023110bb, 0x403110b3,
     0x003100af, 0x003100d3, 0xffffffff].all
      (fun word => (InstructionDecode.decode word).isNone) = true := by native_decide

/-- The pinned Sail decoder claims these base-integer no-op encodings for enabled hint
extensions. Neighboring ADD/ORI instructions, including other `rd = x0` cases, remain accepted. -/
theorem hintAliases :
    [0x00200033, 0x00300033, 0x00400033, 0x00500033,
     0x00006013, 0x00116013, 0xfe3fe013].all
      (fun word => (InstructionDecode.decode word).isNone) = true ∧
    [0x00000033, 0x00100033, 0x00600033, 0x00208033, 0x002000b3,
     0x00206013, 0x00406013, 0x00006093, 0x00001017].all
      (fun word => (InstructionDecode.decode word).isSome) = true := by native_decide

open Sail LeanRV64D.Functions in
/-- Official Sail recognizes the overlapping NTL and prefetch encodings as hint constructors.
These kernel-checked witnesses explain why literal ADD/ORI decoding must reject the aliases. -/
theorem sailHintPriority (s : SailState) :
    (ext_decode 0x00200033#32).run s = .ok (.NTL .NTL_P1) s ∧
    (ext_decode 0x00006013#32).run s = .ok (.ZICBOP (.PREFETCH_I, .Regidx 0#5, 0#12)) s := by
  constructor
  · conv_lhs => whnf
    refine (SP1Clean.SailDecode.run_match_step _ (some (instruction.NTL .NTL_P1))
      _ _ s ?_).trans rfl
    conv_lhs => whnf
    rw [show currentlyEnabled extension.Ext_Zihintntl s = .ok true s by
      simp [currentlyEnabled, hartSupports, pure, EStateM.pure]]
    rfl
  · conv_lhs => whnf
    refine (SP1Clean.SailDecode.run_match_step _
      (some (instruction.ZICBOP (.PREFETCH_I, .Regidx 0#5, 0#12))) _ _ s ?_).trans rfl
    conv_lhs => whnf
    rw [show currentlyEnabled extension.Ext_Zicbop s = .ok true s by
      simp [currentlyEnabled, hartSupports, pure, EStateM.pure]]
    rfl

private def image : ProgramImage := ⟨[(65536, 0x003100b3), (65540, 0x73)], 65536, []⟩

/-- Validation checks every ROM word, including unsupported instructions at unused addresses. -/
theorem checkedProgram :
    (image.checkProgram).isSome = true ∧
    (({ image with rom := image.rom ++ [(65544, 0x00100073)] }).checkProgram).isSome = false ∧
    (({ image with rom := image.rom ++ [(65544, 0x00200033)] }).checkProgram).isSome = false ∧
    (({ image with rom := image.rom ++ image.rom }).checkProgram).isSome = false ∧
    (image.programRows (p := SP1Clean.SP1Prime)).length = 2 := by native_decide

private def accepts (input : SP1Clean.ProgramProviderChip.Inputs Fp) : Bool :=
  let program := (SP1Clean.DecodedProgramProvider.circuit image).main
    (varFromOffset SP1Clean.ProgramProviderChip.Inputs 0)
  let env := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  (program.operations (size SP1Clean.ProgramProviderChip.Inputs)).toFlat.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup lookup =>
      if arity : lookup.table.arity = size ProgramMsg then
        lookup.table.name == "sp1.native.program" && image.programRows.any fun msg =>
          toElements msg == arity ▸ lookup.entry.map env
      else false
    | .witness .. | .interact .. => true

/-- Actual constraints and fixed lookups accept honest rows and reject forged full-message fields,
including zero-multiplicity rows. The lookup count is free; bus balance constrains it globally. -/
theorem fixedProgramConstraints :
    ([0, 1, 17] : List Fp).all (fun multiplicity =>
      image.rom.all fun entry =>
        ((SP1Clean.DecodedProgramProvider.populate? image entry multiplicity).map accepts).getD false) = true ∧
    ((SP1Clean.DecodedProgramProvider.populate? image (65536, 0x003100b3) (0 : Fp)).map fun row =>
      !accepts { row with opcode := 2 } &&
      !accepts { row with op_c := #v[4, 0, 0, 0] } &&
      !accepts { row with pc0 := 8 } &&
      !accepts { row with op_a_0 := 1 }).getD false = true := by native_decide

/-- info: exportable ✓ (53 witness cells) -/
#guard_msgs in
#assert_exportable (SP1Clean.DecodedProgramProvider.circuit (p := SP1Clean.SP1Prime) image)

end SP1CleanTest.Core.InstructionDecode
