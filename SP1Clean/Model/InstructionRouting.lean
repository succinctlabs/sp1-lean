import SP1Clean.Model.InstructionChipId
import SP1Clean.Model.Opcode

/-!
# Pure instruction-chip routing

This module is the semantic routing half of the supported instruction profile.  It assigns each
`InstructionChipId` its opcode family and SP1's `rd == x0` dispatch guard, without importing Clean
circuits, dependent chip rows, Sail proofs, or provider tables.  The circuit-bearing realization in
`Soundness/SupportedMachine.lean` is indexed by the same identity.

Provider and boundary tables intentionally have no entry here: they are not selected by decoded
instruction opcode and must keep a separate identity vocabulary.
-/

namespace SP1Clean

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

/-- Pure dispatch data for one instruction-table family. -/
structure InstructionRoute where
  opcodes : List Soundness.Opcode
  rdGuard : RdGuard
deriving Repr

/-- Whether this route claims an instruction dispatch key. -/
def InstructionRoute.claims (route : InstructionRoute)
    (opcode : Soundness.Opcode) (rdIsX0 : Bool) : Bool :=
  route.opcodes.contains opcode && route.rdGuard.holds rdIsX0

namespace InstructionChipId

/-- The canonical semantic route of each supported instruction-table identity. -/
def route : InstructionChipId → InstructionRoute
  | .add =>        ⟨[.ADD],                     .nonX0⟩
  | .addi =>       ⟨[.ADDI],                    .nonX0⟩
  | .addw =>       ⟨[.ADDW],                    .nonX0⟩
  | .sub =>        ⟨[.SUB],                     .nonX0⟩
  | .subw =>       ⟨[.SUBW],                    .nonX0⟩
  | .bitwise =>    ⟨[.XOR, .OR, .AND],          .nonX0⟩
  | .lt =>         ⟨[.SLT, .SLTU],              .nonX0⟩
  | .shiftLeft =>  ⟨[.SLL, .SLLW],              .nonX0⟩
  | .shiftRight => ⟨[.SRL, .SRA, .SRLW, .SRAW], .nonX0⟩
  | .jal =>        ⟨[.JAL],                     .any⟩
  | .jalr =>       ⟨[.JALR],                    .any⟩
  | .branch =>     ⟨[.BEQ, .BNE, .BLT, .BGE, .BLTU, .BGEU], .any⟩
  | .uType =>      ⟨[.AUIPC, .LUI],             .any⟩
  | .loadByte =>   ⟨[.LB, .LBU],                .nonX0⟩
  | .loadHalf =>   ⟨[.LH, .LHU],                .nonX0⟩
  | .loadWord =>   ⟨[.LW, .LWU],                .nonX0⟩
  | .loadDouble => ⟨[.LD],                      .nonX0⟩
  | .loadX0 =>     ⟨[.LB, .LBU, .LH, .LHU, .LW, .LWU, .LD], .onlyX0⟩
  | .storeByte =>  ⟨[.SB],                      .any⟩
  | .storeHalf =>  ⟨[.SH],                      .any⟩
  | .storeWord =>  ⟨[.SW],                      .any⟩
  | .storeDouble =>⟨[.SD],                      .any⟩
  | .mul =>        ⟨[.MUL, .MULH, .MULHU, .MULHSU, .MULW], .nonX0⟩
  | .divRem =>     ⟨[.DIV, .DIVU, .REM, .REMU, .DIVW, .DIVUW, .REMW, .REMUW], .nonX0⟩
  | .aluX0 =>      ⟨[.ADD, .ADDI, .ADDW, .SUB, .SUBW, .XOR, .OR, .AND, .SLT, .SLTU,
      .SLL, .SLLW, .SRL, .SRA, .SRLW, .SRAW,
      .MUL, .MULH, .MULHU, .MULHSU, .MULW,
      .DIV, .DIVU, .REM, .REMU, .DIVW, .DIVUW, .REMW, .REMUW], .onlyX0⟩

end InstructionChipId

/-- Pure instruction routing.  Canonical identity order supplies the deterministic priority for
the opcode families that split on the `rd == x0` guard. -/
def routeId (opcode : Soundness.Opcode) (rdIsX0 : Bool) : Option InstructionChipId :=
  InstructionChipId.all.find? fun id => id.route.claims opcode rdIsX0

/-- The pure router covers exactly the non-system opcode alphabet, for either value of the `x0`
dispatch bit.  Keeping this theorem below the circuit-bearing coverage layer lets semantic decode
prove route existence without importing a Clean table. -/
theorem routeId_isSome (opcode : Soundness.Opcode) (rdIsX0 : Bool) :
    (routeId opcode rdIsX0).isSome =
      decide (opcode ≠ .ECALL ∧ opcode ≠ .EBREAK ∧ opcode ≠ .UNIMP) := by
  cases opcode <;> cases rdIsX0 <;> decide

/-- Existential form of `routeId_isSome`, convenient at semantic relation boundaries. -/
theorem routeId_exists {opcode : Soundness.Opcode} {rdIsX0 : Bool}
    (covered : opcode ≠ .ECALL ∧ opcode ≠ .EBREAK ∧ opcode ≠ .UNIMP) :
    ∃ chipId, routeId opcode rdIsX0 = some chipId := by
  apply Option.isSome_iff_exists.mp
  rw [routeId_isSome, decide_eq_true_eq]
  exact covered

end SP1Clean
