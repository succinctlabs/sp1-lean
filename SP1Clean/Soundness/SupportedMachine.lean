import SP1Clean.Model.InstructionRouting
import SP1Clean.Proofs.Chips.AddChip.Bridge
import SP1Clean.Proofs.Chips.AddiChip.Bridge
import SP1Clean.Proofs.Chips.AddwChip.Bridge
import SP1Clean.Proofs.Chips.SubChip.Bridge
import SP1Clean.Proofs.Chips.SubwChip.Bridge
import SP1Clean.Proofs.Chips.BitwiseChip.Bridge
import SP1Clean.Proofs.Chips.LtChip.Bridge
import SP1Clean.Proofs.Chips.ShiftLeftChip.Bridge
import SP1Clean.Proofs.Chips.ShiftRightChip.Bridge
import SP1Clean.Proofs.Chips.JalChip.Bridge
import SP1Clean.Proofs.Chips.JalrChip.Bridge
import SP1Clean.Proofs.Chips.BranchChip.Bridge
import SP1Clean.Proofs.Chips.UTypeChip.Bridge
import SP1Clean.Proofs.Chips.LoadByteChip.Bridge
import SP1Clean.Proofs.Chips.LoadHalfChip.Bridge
import SP1Clean.Proofs.Chips.LoadWordChip.Bridge
import SP1Clean.Proofs.Chips.LoadDoubleChip.Bridge
import SP1Clean.Proofs.Chips.LoadX0Chip.Bridge
import SP1Clean.Proofs.Chips.StoreByteChip.Bridge
import SP1Clean.Proofs.Chips.StoreHalfChip.Bridge
import SP1Clean.Proofs.Chips.StoreWordChip.Bridge
import SP1Clean.Proofs.Chips.StoreDoubleChip.Bridge
import SP1Clean.Proofs.Chips.MulChip.Bridge
import SP1Clean.Proofs.Chips.DivRemChip.Bridge
import SP1Clean.Proofs.Chips.AluX0Chip.Bridge
import Clean.Air.FlatComponent

/-! # The supported native-machine descriptor

This is the circuit-bearing realization of the neutral identity list
`InstructionChipId.all`. `supportedChipFor` binds each low-layer identity to the verified Clean
table and heterogeneous semantic `ChipKind`.  The opcode family and `rd == x0` dispatch guard live
once, in the pure `Model.InstructionRouting` table indexed by that same identity.

Faithfulness to Rust's `RiscvAir` and `tracing.rs` remains a theorem obligation. Provider and
boundary tables remain separate from instruction identities; this module does not turn the
supported subset into a monolithic full-machine descriptor. -/

namespace SP1Clean.Soundness

open Air.Flat

variable {p : ℕ} [Fact p.Prime]

/-- One implemented instruction-table descriptor.  Provider and boundary tables are intentionally
separate: they do not represent decoded instruction rows and therefore have no `ChipKind` or opcode
route. -/
structure SupportedChip (p : ℕ) [Fact p.Prime] [Fact (2 ^ 17 < p)] where
  /-- Stable key for the pure semantic route and physical instruction-table position. -/
  id : InstructionChipId
  kind : ChipKind p
  /-- The verified circuit, retained at its dependent input/output types.  The flat AIR component is
  derived from this field; keeping an independently supplied `Component` here would lose the
  definitional connection needed by the witness decoder. -/
  circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
    kind.provableInputs kind.provableCols
  /-- The circuit contract is exactly the semantic contract registered by `kind`. -/
  spec_eq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
    kind.provableInputs kind.provableCols circuit = kind.chipSpec

section Descriptor

variable [Fact (2 ^ 17 < p)]

/-- The canonical opcode family, projected from the chip's neutral identity. -/
def SupportedChip.opcodes (chip : SupportedChip p) : List Opcode :=
  chip.id.route.opcodes

/-- The canonical `rd == x0` guard, projected from the chip's neutral identity. -/
def SupportedChip.rdGuard (chip : SupportedChip p) : RdGuard :=
  chip.id.route.rdGuard

/-- The untyped Clean table projection used by `Ensemble`. -/
def SupportedChip.table (chip : SupportedChip p) : Component (ZMod p) :=
  letI := chip.kind.provableInputs
  letI := chip.kind.provableCols
  ⟨chip.circuit⟩

/-- Whether this descriptor claims an instruction dispatch key. -/
def SupportedChip.claims (chip : SupportedChip p) (opcode : Opcode) (rdIsX0 : Bool) : Bool :=
  chip.id.route.claims opcode rdIsX0

end Descriptor

section Realization

variable [Fact (2 ^ 24 < p)]

/-- Layer-local realization of a neutral instruction-chip identity. All circuit and Sail imports
stay on this side of the boundary; `Model.InstructionChipId` remains independent of them. -/
def supportedChipFor : InstructionChipId → SupportedChip p
  | .add =>        ⟨.add,        AddChip.kind,        AddChip.circuit,        rfl⟩
  | .addi =>       ⟨.addi,       AddiChip.kind,       AddiChip.circuit,       rfl⟩
  | .addw =>       ⟨.addw,       AddwChip.kind,       AddwChip.circuit,       rfl⟩
  | .sub =>        ⟨.sub,        SubChip.kind,        SubChip.circuit,        rfl⟩
  | .subw =>       ⟨.subw,       SubwChip.kind,       SubwChip.circuit,       rfl⟩
  | .bitwise =>    ⟨.bitwise,    BitwiseChip.kind,    BitwiseChip.circuit,    rfl⟩
  | .lt =>         ⟨.lt,         LtChip.kind,         LtChip.circuit,         rfl⟩
  | .shiftLeft =>  ⟨.shiftLeft,  ShiftLeftChip.kind,  ShiftLeftChip.circuit,  rfl⟩
  | .shiftRight => ⟨.shiftRight, ShiftRightChip.kind, ShiftRightChip.circuit, rfl⟩
  | .jal =>        ⟨.jal,        JalChip.kind,        JalChip.circuit,        rfl⟩
  | .jalr =>       ⟨.jalr,       JalrChip.kind,       JalrChip.circuit,       rfl⟩
  | .branch =>     ⟨.branch,     BranchChip.kind,     BranchChip.circuit,     rfl⟩
  | .uType =>      ⟨.uType,      UTypeChip.kind,      UTypeChip.circuit,      rfl⟩
  | .loadByte =>   ⟨.loadByte,   LoadByteChip.kind,   LoadByteChip.circuit,   rfl⟩
  | .loadHalf =>   ⟨.loadHalf,   LoadHalfChip.kind,   LoadHalfChip.circuit,   rfl⟩
  | .loadWord =>   ⟨.loadWord,   LoadWordChip.kind,   LoadWordChip.circuit,   rfl⟩
  | .loadDouble => ⟨.loadDouble, LoadDoubleChip.kind, LoadDoubleChip.circuit, rfl⟩
  | .loadX0 =>     ⟨.loadX0,     LoadX0Chip.kind,     LoadX0Chip.circuit,     rfl⟩
  | .storeByte =>  ⟨.storeByte,  StoreByteChip.kind,  StoreByteChip.circuit,  rfl⟩
  | .storeHalf =>  ⟨.storeHalf,  StoreHalfChip.kind,  StoreHalfChip.circuit,  rfl⟩
  | .storeWord =>  ⟨.storeWord,  StoreWordChip.kind,  StoreWordChip.circuit,  rfl⟩
  | .storeDouble =>⟨.storeDouble,StoreDoubleChip.kind,StoreDoubleChip.circuit,rfl⟩
  | .mul =>        ⟨.mul,        MulChip.kind,        MulChip.circuit,        rfl⟩
  | .divRem =>     ⟨.divRem,     DivRemChip.kind,     DivRemChip.circuit,     rfl⟩
  | .aluX0 =>      ⟨.aluX0,      AluX0Chip.kind,      AluX0Chip.circuit,      rfl⟩

/-- The supported native instruction machine. The neutral identity enumeration fixes its order;
changing that order is a public witness-format change, not a cosmetic reordering. -/
def supportedChips : List (SupportedChip p) :=
  InstructionChipId.all.map (supportedChipFor (p := p))

/-- Positional coverage: the circuit registry is exactly the pointwise realization of the neutral
identity enumeration. -/
theorem supportedChips_eq_map :
    supportedChips (p := p) = InstructionChipId.all.map (supportedChipFor (p := p)) :=
  rfl

/-- Pointwise form of positional coverage, including out-of-bounds positions. -/
@[simp] theorem supportedChips_getElem? (i : ℕ) :
    (supportedChips (p := p))[i]? =
      (InstructionChipId.all[i]?).map (supportedChipFor (p := p)) := by
  simp [supportedChips]

/-- The supported-chip count is inherited from the neutral identity enumeration. -/
theorem supportedChips_length : (supportedChips (p := p)).length = 25 := by
  simp [supportedChips]

/-- Circuit-bearing realization of the pure semantic route selected by `routeId`. -/
def routeChip (opcode : Opcode) (rdIsX0 : Bool) : Option (SupportedChip p) :=
  (routeId opcode rdIsX0).map (supportedChipFor (p := p))

end Realization

end SP1Clean.Soundness
