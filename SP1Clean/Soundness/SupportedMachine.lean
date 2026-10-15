import SP1Clean.Model.InstructionRouting
import SP1Clean.Alignment.Chips.AddChip.Bridge
import SP1Clean.Alignment.Chips.AddiChip.Bridge
import SP1Clean.Alignment.Chips.AddwChip.Bridge
import SP1Clean.Alignment.Chips.SubChip.Bridge
import SP1Clean.Alignment.Chips.SubwChip.Bridge
import SP1Clean.Alignment.Chips.BitwiseChip.Bridge
import SP1Clean.Alignment.Chips.LtChip.Bridge
import SP1Clean.Alignment.Chips.ShiftLeftChip.Bridge
import SP1Clean.Alignment.Chips.ShiftRightChip.Bridge
import SP1Clean.Alignment.Chips.JalChip.Bridge
import SP1Clean.Alignment.Chips.JalrChip.Bridge
import SP1Clean.Alignment.Chips.BranchChip.Bridge
import SP1Clean.Alignment.Chips.UTypeChip.Bridge
import SP1Clean.Alignment.Chips.LoadByteChip.Bridge
import SP1Clean.Alignment.Chips.LoadHalfChip.Bridge
import SP1Clean.Alignment.Chips.LoadWordChip.Bridge
import SP1Clean.Alignment.Chips.LoadDoubleChip.Bridge
import SP1Clean.Alignment.Chips.LoadX0Chip.Bridge
import SP1Clean.Alignment.Chips.StoreByteChip.Bridge
import SP1Clean.Alignment.Chips.StoreHalfChip.Bridge
import SP1Clean.Alignment.Chips.StoreWordChip.Bridge
import SP1Clean.Alignment.Chips.StoreDoubleChip.Bridge
import SP1Clean.Alignment.Chips.MulChip.Bridge
import SP1Clean.Alignment.Chips.DivRemChip.Bridge
import SP1Clean.Alignment.Chips.AluX0Chip.Bridge
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
  { circuit := chip.circuit }

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

/-- Native instruction rows use channels for cross-table checks and contain no Clean lookups. -/
theorem supportedChipFor_lookups_empty (id : InstructionChipId) :
    (supportedChipFor (p := p) id).table.operations.lookups = [] := by
  cases id with
  | add => exact AddChip.lookups_empty
  | addi => exact AddiChip.lookups_empty
  | addw => exact AddwChip.lookups_empty
  | sub => exact SubChip.lookups_empty
  | subw => exact SubwChip.lookups_empty
  | bitwise => exact BitwiseChip.lookups_empty
  | lt => exact LtChip.lookups_empty
  | shiftLeft => exact ShiftLeftChip.lookups_empty
  | shiftRight => exact ShiftRightChip.lookups_empty
  | jal => exact JalChip.lookups_empty
  | jalr => exact JalrChip.lookups_empty
  | branch => exact BranchChip.lookups_empty
  | uType => exact UTypeChip.lookups_empty
  | loadByte => exact LoadByteChip.lookups_empty
  | loadHalf => exact LoadHalfChip.lookups_empty
  | loadWord => exact LoadWordChip.lookups_empty
  | loadDouble => exact LoadDoubleChip.lookups_empty
  | loadX0 => exact LoadX0Chip.lookups_empty
  | storeByte => exact StoreByteChip.lookups_empty
  | storeHalf => exact StoreHalfChip.lookups_empty
  | storeWord => exact StoreWordChip.lookups_empty
  | storeDouble => exact StoreDoubleChip.lookups_empty
  | mul => exact MulChip.lookups_empty
  | divRem => exact DivRemChip.lookups_empty
  | aluX0 => exact AluX0Chip.lookups_empty

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

/-- The physical instruction components, in the neutral registry's stable order. -/
def sp1Tables : List (Air.Flat.Component (ZMod p)) :=
  (supportedChips (p := p)).map (·.table)

/-- The instruction inventory inherits its lookup metadata from each native circuit. -/
theorem sp1Tables_lookups_empty (component : Component (ZMod p))
    (member : component ∈ sp1Tables) : component.operations.lookups = [] := by
  obtain ⟨chip, chipMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp chipMember
  exact supportedChipFor_lookups_empty id

/-- The table projection retains every registered instruction component. -/
theorem sp1Tables_length : (sp1Tables (p := p)).length = 25 := by
  simpa [sp1Tables] using supportedChips_length (p := p)

/-- Circuit-bearing realization of the pure semantic route selected by `routeId`. -/
def routeChip (opcode : Opcode) (rdIsX0 : Bool) : Option (SupportedChip p) :=
  (routeId opcode rdIsX0).map (supportedChipFor (p := p))

end Realization

end SP1Clean.Soundness
