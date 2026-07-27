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
import SP1Clean.Faithful.LoadByte
import SP1Clean.Faithful.LoadHalf
import SP1Clean.Faithful.LoadWord
import SP1Clean.Faithful.LoadDouble
import SP1Clean.Faithful.LoadX0
import SP1Clean.Faithful.StoreByte
import SP1Clean.Faithful.StoreHalf
import SP1Clean.Faithful.StoreWord
import SP1Clean.Faithful.StoreDouble
import SP1Clean.Faithful.MulChip
import SP1Clean.Faithful.DivRemChip.Exact
import SP1Clean.Faithful.AluX0
import SP1Clean.FormalModel.CoreProfile
import SP1Clean.Soundness.SupportedMachine

/-! # Whole-chip faithfulness coverage for the supported instruction machine

This is the small audit index for the native instruction slice. Each entry carries the actual
`ChipFaithful` proposition and its kernel-checked proof; the name projection is definitionally equal
to the stable 25-entry `supportedChips` registry. Thus adding, removing, or reordering a supported
instruction table requires updating the faithfulness coverage certificate in the same change.

The certificate covers whole-chip assertions and active interaction multisets. It does not claim that
the 11 native provider tables equal upstream Core AIR tables; exact upstream table coverage lives in
`Faithful/CoreAIR.lean`. -/

namespace SP1Clean.Faithful

open SP1Clean.Soundness

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- One checked whole-chip proposition, indexed by the exact upstream Core AIR table it covers. -/
structure ChipFaithfulnessAnchor where
  table : CoreProfile.Table
  proposition : Prop
  proof : proposition

/-- The 25 whole-chip faithfulness packages, in exactly the physical order of `supportedChips`. -/
def supportedChipFaithfulness : List ChipFaithfulnessAnchor :=
  [ ⟨.add, _, addChip_faithful (p := p)⟩,
    ⟨.addi, _, addiChip_faithful (p := p)⟩,
    ⟨.addw, _, addwChip_faithful (p := p)⟩,
    ⟨.sub, _, subChip_faithful (p := p)⟩,
    ⟨.subw, _, subwChip_faithful (p := p)⟩,
    ⟨.bitwise, _, bitwiseChip_faithful (p := p)⟩,
    ⟨.lt, _, ltChip_faithful (p := p)⟩,
    ⟨.shiftLeft, _, shiftLeftChip_faithful (p := p)⟩,
    ⟨.shiftRight, _, shiftRightChip_faithful (p := p)⟩,
    ⟨.jal, _, jalChip_faithful (p := p)⟩,
    ⟨.jalr, _, jalrChip_faithful (p := p)⟩,
    ⟨.branch, _, branchChip_faithful (p := p)⟩,
    ⟨.uType, _, uTypeChip_faithful (p := p)⟩,
    ⟨.loadByte, _, loadByteChip_faithful (p := p)⟩,
    ⟨.loadHalf, _, loadHalfChip_faithful (p := p)⟩,
    ⟨.loadWord, _, loadWordChip_faithful (p := p)⟩,
    ⟨.loadDouble, _, loadDoubleChip_faithful (p := p)⟩,
    ⟨.loadX0, _, loadX0Chip_faithful (p := p)⟩,
    ⟨.storeByte, _, storeByteChip_faithful (p := p)⟩,
    ⟨.storeHalf, _, storeHalfChip_faithful (p := p)⟩,
    ⟨.storeWord, _, storeWordChip_faithful (p := p)⟩,
    ⟨.storeDouble, _, storeDoubleChip_faithful (p := p)⟩,
    ⟨.mul, _, mulChip_faithful (p := p)⟩,
    ⟨.divRem, _, divRemChip_faithful (p := p)⟩,
    ⟨.aluX0, _, aluX0Chip_faithful (p := p)⟩ ]

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
