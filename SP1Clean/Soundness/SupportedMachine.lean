import SP1Clean.Model.Opcode
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

This is the single source of truth for the currently implemented 25-chip machine.  One entry binds
four facts that previously lived in three independent enumerations:

* the verified Clean table included in the ensemble;
* the heterogeneous semantic `ChipKind` used by soundness;
* the upstream opcode family routed to the chip; and
* SP1's `rd == x0` routing guard.

Faithfulness to Rust's `RiscvAir` and `tracing.rs` remains a theorem obligation, but internal wiring can
no longer drift merely because one list was edited without the others.  Full SP1 will extend this
descriptor with syscall, precompile, boundary, and global-interaction tables; it will not silently
reinterpret this supported subset as the full machine. -/

namespace SP1Clean.Soundness

open Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-- The `op_a == 0` dispatch condition used by SP1's trace generator. -/
inductive RdGuard where
  /-- The chip claims the opcode independently of `rd`. -/
  | any
  /-- The chip claims the opcode only when `rd ≠ x0`. -/
  | nonX0
  /-- The chip claims the opcode only when `rd = x0`. -/
  | onlyX0
deriving DecidableEq, Repr

/-- Whether a routing guard accepts the `rd == x0` bit. -/
def RdGuard.holds : RdGuard → Bool → Bool
  | .any, _ => true
  | .nonX0, isX0 => !isX0
  | .onlyX0, isX0 => isX0

/-- One implemented instruction-table descriptor.  Provider and boundary tables are intentionally
separate: they do not represent decoded instruction rows and therefore have no `ChipKind` or opcode
route. -/
structure SupportedChip (p : ℕ) [Fact p.Prime] [Fact (2 ^ 17 < p)] where
  kind : ChipKind p
  /-- The verified circuit, retained at its dependent input/output types.  The flat AIR component is
  derived from this field; keeping an independently supplied `Component` here would lose the
  definitional connection needed by the witness decoder. -/
  circuit : @GeneralFormalCircuit (ZMod p) kind.Inputs kind.Cols inferInstance
    kind.provableInputs kind.provableCols
  /-- The circuit contract is exactly the semantic contract registered by `kind`. -/
  spec_eq : @GeneralFormalCircuit.Spec (ZMod p) kind.Inputs kind.Cols inferInstance
    kind.provableInputs kind.provableCols circuit = kind.chipSpec
  opcodes : List Opcode
  rdGuard : RdGuard

/-- The untyped Clean table projection used by `Ensemble`. -/
def SupportedChip.table (chip : SupportedChip p) : Component (ZMod p) :=
  letI := chip.kind.provableInputs
  letI := chip.kind.provableCols
  ⟨chip.circuit⟩

/-- Whether this descriptor claims an instruction dispatch key. -/
def SupportedChip.claims (chip : SupportedChip p) (opcode : Opcode) (rdIsX0 : Bool) : Bool :=
  chip.opcodes.contains opcode && chip.rdGuard.holds rdIsX0

/-- The supported native instruction machine.  Order is stable and is used by the ensemble witness
layout; changing it is a public witness-format change, not a cosmetic reordering. -/
def supportedChips : List (SupportedChip p) :=
  [ ⟨AddChip.kind,        AddChip.circuit,        rfl, [.ADD],                       .nonX0⟩,
    ⟨AddiChip.kind,       AddiChip.circuit,       rfl, [.ADDI],                      .nonX0⟩,
    ⟨AddwChip.kind,       AddwChip.circuit,       rfl, [.ADDW],                      .nonX0⟩,
    ⟨SubChip.kind,        SubChip.circuit,        rfl, [.SUB],                       .nonX0⟩,
    ⟨SubwChip.kind,       SubwChip.circuit,       rfl, [.SUBW],                      .nonX0⟩,
    ⟨BitwiseChip.kind,    BitwiseChip.circuit,    rfl, [.XOR, .OR, .AND],            .nonX0⟩,
    ⟨LtChip.kind,         LtChip.circuit,         rfl, [.SLT, .SLTU],                .nonX0⟩,
    ⟨ShiftLeftChip.kind,  ShiftLeftChip.circuit,  rfl, [.SLL, .SLLW],                .nonX0⟩,
    ⟨ShiftRightChip.kind, ShiftRightChip.circuit, rfl, [.SRL, .SRA, .SRLW, .SRAW],   .nonX0⟩,
    ⟨JalChip.kind,        JalChip.circuit,        rfl, [.JAL],                       .any⟩,
    ⟨JalrChip.kind,       JalrChip.circuit,       rfl, [.JALR],                      .any⟩,
    ⟨BranchChip.kind,     BranchChip.circuit,     rfl,
      [.BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU], .any⟩,
    ⟨UTypeChip.kind,      UTypeChip.circuit,      rfl, [.AUIPC, .LUI],               .any⟩,
    ⟨LoadByteChip.kind,   LoadByteChip.circuit,   rfl, [.LB, .LBU],                  .nonX0⟩,
    ⟨LoadHalfChip.kind,   LoadHalfChip.circuit,   rfl, [.LH, .LHU],                  .nonX0⟩,
    ⟨LoadWordChip.kind,   LoadWordChip.circuit,   rfl, [.LW, .LWU],                  .nonX0⟩,
    ⟨LoadDoubleChip.kind, LoadDoubleChip.circuit, rfl, [.LD],                       .nonX0⟩,
    ⟨LoadX0Chip.kind,     LoadX0Chip.circuit,     rfl,
      [.LB, .LBU, .LH, .LHU, .LW, .LWU, .LD], .onlyX0⟩,
    ⟨StoreByteChip.kind,  StoreByteChip.circuit,  rfl, [.SB],                       .any⟩,
    ⟨StoreHalfChip.kind,  StoreHalfChip.circuit,  rfl, [.SH],                       .any⟩,
    ⟨StoreWordChip.kind,  StoreWordChip.circuit,  rfl, [.SW],                       .any⟩,
    ⟨StoreDoubleChip.kind,StoreDoubleChip.circuit,rfl, [.SD],                       .any⟩,
    ⟨MulChip.kind,        MulChip.circuit,        rfl,
      [.MUL, .MULH, .MULHU, .MULHSU, .MULW], .nonX0⟩,
    ⟨DivRemChip.kind,     DivRemChip.circuit,     rfl,
      [.DIV, .DIVU, .REM, .REMU, .DIVW, .DIVUW, .REMW, .REMUW], .nonX0⟩,
    ⟨AluX0Chip.kind,      AluX0Chip.circuit,      rfl,
      [.ADD, .ADDI, .ADDW, .SUB, .SUBW, .XOR, .OR, .AND, .SLT, .SLTU,
       .SLL, .SLLW, .SRL, .SRA, .SRLW, .SRAW,
       .MUL, .MULH, .MULHU, .MULHSU, .MULW,
       .DIV, .DIVU, .REM, .REMU, .DIVW, .DIVUW, .REMW, .REMUW], .onlyX0⟩ ]

theorem supportedChips_length : (supportedChips (p := p)).length = 25 := rfl

/-- Descriptor-level instruction routing.  This is definitionally the source of both the semantic
`ChipKind` route and its human-readable name projection. -/
def routeChip (opcode : Opcode) (rdIsX0 : Bool) : Option (SupportedChip p) :=
  (supportedChips (p := p)).find? fun chip => chip.claims opcode rdIsX0

end SP1Clean.Soundness
