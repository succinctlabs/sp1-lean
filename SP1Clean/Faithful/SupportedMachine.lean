import SP1Clean.Faithful.AddChip
import SP1Clean.Faithful.AddiChip
import SP1Clean.Faithful.AddwChip
import SP1Clean.Faithful.SubChip
import SP1Clean.Faithful.SubwChip
import SP1Clean.Faithful.BitwiseChip
import SP1Clean.Faithful.LtChip
import SP1Clean.Faithful.ShiftLeftChip
import SP1Clean.Faithful.ShiftRightChip
import SP1Clean.Faithful.JalChip
import SP1Clean.Faithful.JalrChip
import SP1Clean.Faithful.BranchChip
import SP1Clean.Faithful.UTypeChip
import SP1Clean.Faithful.LoadByteChip
import SP1Clean.Faithful.LoadHalfChip
import SP1Clean.Faithful.LoadWordChip
import SP1Clean.Faithful.LoadDoubleChip
import SP1Clean.Faithful.LoadX0Chip
import SP1Clean.Faithful.StoreByteChip
import SP1Clean.Faithful.StoreHalfChip
import SP1Clean.Faithful.StoreWordChip
import SP1Clean.Faithful.StoreDoubleChip
import SP1Clean.Faithful.MulChip
import SP1Clean.Faithful.DivRemChip.Exact
import SP1Clean.Faithful.AluX0Chip
import SP1Clean.FormalModel.CoreProfile
import SP1Clean.Soundness.SupportedMachine

/-! # Whole-chip faithfulness coverage for the supported instruction machine

This is the small audit index for the native instruction slice. Each entry carries the actual
`ChipFaithful` proposition and its kernel-checked proof; the name projection is definitionally equal
to the stable 25-entry `supportedChips` registry. Thus adding, removing, or reordering a supported
instruction table requires updating the faithfulness coverage certificate in the same change.

The certificate covers whole-chip assertions and active interaction multisets. It does not identify
the 28 proof-oriented native provider/system tables row-for-row with upstream's differently shaped
Core AIR tables. Exact upstream table coverage lives in `Faithful/CoreAIR.lean`; the explicit
redistribution and consumer-recount boundary lives in `Composition/`. -/

namespace SP1Clean.Faithful

open SP1Clean.Soundness
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## Extracted column-width guard

The machine manifest records Rust's `mainWidth`, while each generated whole-chip oracle separately
declares the nested column structure consumed by its faithfulness codec.  The following option-valued
index ties those two generated surfaces together for every supported instruction table.  Returning
`none` outside the instruction profile makes omission visible rather than silently reusing the
manifest value. -/

/-- Physical field count of the generated Rust column structure for each supported instruction AIR. -/
def instructionOracleMainWidth : CoreProfile.Table → Option ℕ
  | .add => some (size Extracted.AddOracle.AddCols)
  | .addi => some (size Extracted.AddiOracle.AddiCols)
  | .addw => some (size Extracted.AddwOracle.AddwCols)
  | .sub => some (size Extracted.SubOracle.SubCols)
  | .subw => some (size Extracted.SubwOracle.SubwCols)
  | .bitwise => some (size Extracted.BitwiseOracle.BitwiseCols)
  | .lt => some (size Extracted.LtOracle.LtCols)
  | .shiftLeft => some (size Extracted.ShiftLeftOracle.ShiftLeftCols)
  | .shiftRight => some (size Extracted.ShiftRightOracle.ShiftRightCols)
  | .jal => some (size Extracted.JalOracle.JalColumns)
  | .jalr => some (size Extracted.JalrOracle.JalrColumns)
  | .branch => some (size Extracted.BranchOracle.BranchColumns)
  | .uType => some (size Extracted.UTypeOracle.UTypeColumns)
  | .loadByte => some (size Extracted.LoadByteOracle.LoadByteColumns)
  | .loadHalf => some (size Extracted.LoadHalfOracle.LoadHalfColumns)
  | .loadWord => some (size Extracted.LoadWordOracle.LoadWordColumns)
  | .loadDouble => some (size Extracted.LoadDoubleOracle.LoadDoubleColumns)
  | .loadX0 => some (size Extracted.LoadX0Oracle.LoadX0Columns)
  | .storeByte => some (size Extracted.StoreByteOracle.StoreByteColumns)
  | .storeHalf => some (size Extracted.StoreHalfOracle.StoreHalfColumns)
  | .storeWord => some (size Extracted.StoreWordOracle.StoreWordColumns)
  | .storeDouble => some (size Extracted.StoreDoubleOracle.StoreDoubleColumns)
  | .mul => some (size Extracted.MulOracle.MulCols)
  | .divRem => some (size Extracted.DivRemOracle.DivRemCols)
  | .aluX0 => some (size Extracted.AluX0Oracle.AluX0Cols)
  | _ => none

/-- The width index is defined on exactly the supported instruction profile.  This converse guard
prevents a future system-table arm from being added without an explicit profile decision. -/
theorem instructionOracleMainWidth_isSome_iff (table : CoreProfile.Table) :
    (instructionOracleMainWidth table).isSome ↔ table ∈ CoreProfile.instructionTables := by
  cases table <;> decide

/-- Every table in the exact supported instruction profile has a generated Rust column structure,
and its kernel-computed field count equals the independently extracted `MachineAir::main_width`. -/
theorem supportedInstructionMainWidths :
    ∀ table ∈ CoreProfile.instructionTables,
      instructionOracleMainWidth table = some table.mainWidth := by
  decide

/-- The exact whole-chip faithfulness proposition each supported instruction table must carry.

Binding the proposition to the table by dispatch — instead of letting an anchor infer it from
whatever proof happens to be supplied — makes a mispairing (say, registering `addChip_faithful`
under `.divRem`) a type error rather than a silently passing coverage certificate (external
report, Finding 13). Tables outside the 25-chip instruction slice carry no whole-chip anchor,
so their arm is `False` (unregisterable). -/
def FaithfulPropFor : CoreProfile.Table → Prop
  | .add => ChipFaithful (p := p) AddChip.Inputs AddChip.Columns Extracted.AddOracle.AddCols
      AddChip.circuit addChipRowCodec addChipOracle
  | .addi => ChipFaithful (p := p) AddiChip.Inputs AddiChip.Columns Extracted.AddiOracle.AddiCols
      AddiChip.circuit addiChipRowCodec addiChipOracle
  | .addw => ChipFaithful (p := p) AddwChip.Inputs AddwChip.Columns Extracted.AddwOracle.AddwCols
      AddwChip.circuit addwChipRowCodec addwChipOracle
  | .sub => ChipFaithful (p := p) SubChip.Inputs SubChip.Columns Extracted.SubOracle.SubCols
      SubChip.circuit subChipRowCodec subChipOracle
  | .subw => ChipFaithful (p := p) SubwChip.Inputs SubwChip.Columns Extracted.SubwOracle.SubwCols
      SubwChip.circuit subwChipRowCodec subwChipOracle
  | .bitwise => ChipFaithful (p := p) BitwiseChip.Inputs BitwiseChip.Columns
      Extracted.BitwiseOracle.BitwiseCols BitwiseChip.circuit bitwiseChipRowCodec bitwiseChipOracle
  | .lt => ChipFaithful (p := p) LtChip.Inputs LtChip.Columns Extracted.LtOracle.LtCols
      LtChip.circuit ltChipRowCodec ltChipOracle
  | .shiftLeft => ChipFaithful (p := p) ShiftLeftChip.Inputs ShiftLeftChip.Columns
      Extracted.ShiftLeftOracle.ShiftLeftCols ShiftLeftChip.circuit shiftLeftChipRowCodec
      shiftLeftChipOracle
  | .shiftRight => ChipFaithful (p := p) ShiftRightChip.Inputs ShiftRightChip.Columns
      Extracted.ShiftRightOracle.ShiftRightCols ShiftRightChip.circuit shiftRightChipRowCodec
      shiftRightChipOracle
  | .jal => ChipFaithful (p := p) JalChip.Inputs JalChip.Columns Extracted.JalOracle.JalColumns
      JalChip.circuit jalChipRowCodec jalChipOracle
  | .jalr => ChipFaithful (p := p) JalrChip.Inputs JalrChip.Columns
      Extracted.JalrOracle.JalrColumns JalrChip.circuit jalrChipRowCodec jalrChipOracle
  | .branch => ChipFaithful (p := p) BranchChip.Inputs BranchChip.Columns
      Extracted.BranchOracle.BranchColumns BranchChip.circuit branchChipRowCodec branchChipOracle
  | .uType => ChipFaithful (p := p) UTypeChip.Inputs UTypeChip.Columns
      Extracted.UTypeOracle.UTypeColumns UTypeChip.circuit uTypeChipRowCodec uTypeChipOracle
  | .loadByte => ChipFaithful (p := p) LoadByteChip.Inputs LoadByteChip.Columns
      Extracted.LoadByteOracle.LoadByteColumns LoadByteChip.circuit loadByteChipRowCodec
      loadByteChipOracle
  | .loadHalf => ChipFaithful (p := p) LoadHalfChip.Inputs LoadHalfChip.Columns
      Extracted.LoadHalfOracle.LoadHalfColumns LoadHalfChip.circuit loadHalfChipRowCodec
      loadHalfChipOracle
  | .loadWord => ChipFaithful (p := p) LoadWordChip.Inputs LoadWordChip.Columns
      Extracted.LoadWordOracle.LoadWordColumns LoadWordChip.circuit loadWordChipRowCodec
      loadWordChipOracle
  | .loadDouble => ChipFaithful (p := p) LoadDoubleChip.Inputs LoadDoubleChip.Columns
      Extracted.LoadDoubleOracle.LoadDoubleColumns LoadDoubleChip.circuit loadDoubleChipRowCodec
      loadDoubleChipOracle
  | .loadX0 => ChipFaithful (p := p) LoadX0Chip.Inputs LoadX0Chip.Columns
      Extracted.LoadX0Oracle.LoadX0Columns LoadX0Chip.circuit loadX0ChipRowCodec loadX0ChipOracle
  | .storeByte => ChipFaithful (p := p) StoreByteChip.Inputs StoreByteChip.Columns
      Extracted.StoreByteOracle.StoreByteColumns StoreByteChip.circuit storeByteChipRowCodec
      storeByteChipOracle
  | .storeHalf => ChipFaithful (p := p) StoreHalfChip.Inputs StoreHalfChip.Columns
      Extracted.StoreHalfOracle.StoreHalfColumns StoreHalfChip.circuit storeHalfChipRowCodec
      storeHalfChipOracle
  | .storeWord => ChipFaithful (p := p) StoreWordChip.Inputs StoreWordChip.Columns
      Extracted.StoreWordOracle.StoreWordColumns StoreWordChip.circuit storeWordChipRowCodec
      storeWordChipOracle
  | .storeDouble => ChipFaithful (p := p) StoreDoubleChip.Inputs StoreDoubleChip.Columns
      Extracted.StoreDoubleOracle.StoreDoubleColumns StoreDoubleChip.circuit
      storeDoubleChipRowCodec storeDoubleChipOracle
  | .mul => ChipFaithful (p := p) MulChip.Inputs MulChip.Columns Extracted.MulOracle.MulCols
      MulChip.circuit mulChipRowCodec mulChipOracle
  | .divRem => ChipFaithful (p := p) DivRemChip.Inputs DivRemChip.Columns
      Extracted.DivRemOracle.DivRemCols DivRemChip.circuit divRemChipRowCodec divRemChipOracle
  | .aluX0 => ChipFaithful (p := p) AluX0Chip.Inputs AluX0Chip.Columns
      Extracted.AluX0Oracle.AluX0Cols AluX0Chip.circuit aluX0ChipRowCodec aluX0ChipOracle
  | _ => False

/-- One checked whole-chip proposition, indexed by the exact upstream Core AIR table it covers.
The `proof` field's type is `FaithfulPropFor table`, so the table tag and the theorem are bound
by the kernel, not by reviewer discipline. -/
structure ChipFaithfulnessAnchor where
  table : CoreProfile.Table
  proof : FaithfulPropFor (p := p) table

/-- The 25 whole-chip faithfulness packages, in exactly the physical order of `supportedChips`. -/
def supportedChipFaithfulness : List (ChipFaithfulnessAnchor (p := p)) :=
  [ ⟨.add, addChip_faithful (p := p)⟩,
    ⟨.addi, addiChip_faithful (p := p)⟩,
    ⟨.addw, addwChip_faithful (p := p)⟩,
    ⟨.sub, subChip_faithful (p := p)⟩,
    ⟨.subw, subwChip_faithful (p := p)⟩,
    ⟨.bitwise, bitwiseChip_faithful (p := p)⟩,
    ⟨.lt, ltChip_faithful (p := p)⟩,
    ⟨.shiftLeft, shiftLeftChip_faithful (p := p)⟩,
    ⟨.shiftRight, shiftRightChip_faithful (p := p)⟩,
    ⟨.jal, jalChip_faithful (p := p)⟩,
    ⟨.jalr, jalrChip_faithful (p := p)⟩,
    ⟨.branch, branchChip_faithful (p := p)⟩,
    ⟨.uType, uTypeChip_faithful (p := p)⟩,
    ⟨.loadByte, loadByteChip_faithful (p := p)⟩,
    ⟨.loadHalf, loadHalfChip_faithful (p := p)⟩,
    ⟨.loadWord, loadWordChip_faithful (p := p)⟩,
    ⟨.loadDouble, loadDoubleChip_faithful (p := p)⟩,
    ⟨.loadX0, loadX0Chip_faithful (p := p)⟩,
    ⟨.storeByte, storeByteChip_faithful (p := p)⟩,
    ⟨.storeHalf, storeHalfChip_faithful (p := p)⟩,
    ⟨.storeWord, storeWordChip_faithful (p := p)⟩,
    ⟨.storeDouble, storeDoubleChip_faithful (p := p)⟩,
    ⟨.mul, mulChip_faithful (p := p)⟩,
    ⟨.divRem, divRemChip_faithful (p := p)⟩,
    ⟨.aluX0, aluX0Chip_faithful (p := p)⟩ ]

/-- The coverage index contains one proof package for every supported instruction table. -/
theorem supportedChipFaithfulness_length :
    (supportedChipFaithfulness (p := p)).length = (supportedChips (p := p)).length := rfl

/-- Faithfulness-package names and order are exactly the supported-machine registry names and order. -/
theorem supportedChipFaithfulness_names :
    (supportedChipFaithfulness (p := p)).map (·.table.airName) =
      (supportedChips (p := p)).map (·.kind.name) := rfl

/-- The native coverage certificate contains exactly the 25 instruction AIRs in the pinned upstream
Core profile. Rust and the native witness use different physical orders, so this boundary is a
permutation rather than an equality. -/
theorem supportedChipFaithfulness_upstream :
    ((supportedChipFaithfulness (p := p)).map (·.table)).Perm
      CoreProfile.instructionTables := by
  change
    [ CoreProfile.Table.add, CoreProfile.Table.addi, CoreProfile.Table.addw,
      CoreProfile.Table.sub, CoreProfile.Table.subw, CoreProfile.Table.bitwise,
      CoreProfile.Table.lt, CoreProfile.Table.shiftLeft, CoreProfile.Table.shiftRight,
      CoreProfile.Table.jal, CoreProfile.Table.jalr, CoreProfile.Table.branch,
      CoreProfile.Table.uType, CoreProfile.Table.loadByte, CoreProfile.Table.loadHalf,
      CoreProfile.Table.loadWord, CoreProfile.Table.loadDouble, CoreProfile.Table.loadX0,
      CoreProfile.Table.storeByte, CoreProfile.Table.storeHalf, CoreProfile.Table.storeWord,
      CoreProfile.Table.storeDouble, CoreProfile.Table.mul, CoreProfile.Table.divRem,
      CoreProfile.Table.aluX0 ].Perm
    [ CoreProfile.Table.divRem, CoreProfile.Table.add, CoreProfile.Table.addi,
      CoreProfile.Table.addw, CoreProfile.Table.sub, CoreProfile.Table.subw,
      CoreProfile.Table.bitwise, CoreProfile.Table.mul, CoreProfile.Table.shiftRight,
      CoreProfile.Table.shiftLeft, CoreProfile.Table.lt, CoreProfile.Table.aluX0,
      CoreProfile.Table.loadByte, CoreProfile.Table.loadHalf, CoreProfile.Table.loadWord,
      CoreProfile.Table.loadDouble, CoreProfile.Table.loadX0, CoreProfile.Table.storeByte,
      CoreProfile.Table.storeHalf, CoreProfile.Table.storeWord, CoreProfile.Table.storeDouble,
      CoreProfile.Table.uType, CoreProfile.Table.branch, CoreProfile.Table.jal,
      CoreProfile.Table.jalr ]
  decide

end SP1Clean.Faithful
