import SP1Clean.Model.Semantics.TransitionView
import SP1Clean.Model.Semantics.AccessSchedule
import SP1Clean.Proofs.Completeness.EventBuckets

/-!
# One-transition instruction-event compilation

This module is the proof-independent bridge from one decoded, supported Sail transition to the
semantic event consumed by exactly one of the twenty-five native instruction tables.  It does not
build a Clean row and it does not inspect a chip circuit.  Instead it combines three canonical
projections:

* `instructionRouteId` selects the registry identity;
* `instructionAccessPlan?` reads the source/target values in SP1's `RAM,C,B,A` role order; and
* the canonical global access scheduler supplies displaced timestamps after any required
  24-bit-window register refresh.

The resulting `RoutedEvent` is therefore registry-indexed by construction.  `InstructionEventReady`
is intentionally just successful execution of this transparent extractor.  In particular it does
not contain `InstructionChipId.Valid` (or an existential table witness) as a premise.  Address-space,
alignment, and control-flow-target facts needed for full per-chip validity remain semantic facts of
the official Sail step and can be proved at the later execution-fold boundary.
-/

open LeanRV64D.Defs

namespace SP1Clean.TraceGen

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Semantics
open SP1Clean.Soundness.Target

/-! ## Small family-neutral projections -/

/-- Preserve the decoded immediate width: branches use thirteen bits, while I-type and memory
operands use twelve. Narrowing before sign extension changes valid branch targets. -/
private def sextNat {width : ℕ} (immediate : BitVec width) : ℕ :=
  (immediate.signExtend 64).toNat

private def utypeImmediateNat (immediate : BitVec 20) : ℕ :=
  ((immediate.signExtend 64) <<< 12).toNat

/-- The bit-vector projection used by the compiler is exactly the executor-side natural-number
encoding required by `JTypeEvent.UTypeImm`. -/
theorem utypeImmediateNat_eq_luiImmNat (immediate : BitVec 20) :
    utypeImmediateNat immediate = luiImmNat immediate.toNat := by
  have immediateLt : immediate.toNat < 2 ^ 20 := immediate.isLt
  have msb_iff : immediate.msb = true ↔ 2 ^ 19 ≤ immediate.toNat := by
    rw [BitVec.msb_eq_decide, decide_eq_true_eq]
  unfold utypeImmediateNat luiImmNat
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_signExtend, BitVec.toNat_setWidth,
    Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by omega : immediate.toNat < 2 ^ 64)]
  by_cases sign : immediate.msb = true
  · have highGe := msb_iff.mp sign
    have high : ¬ immediate.toNat < 2 ^ 19 := by omega
    rw [if_pos sign, if_neg high]
    have residueLt : immediate.toNat * 4096 + (2 ^ 64 - 2 ^ 32) < 2 ^ 64 := by
      omega
    have rearrange :
        (immediate.toNat + (2 ^ 64 - 2 ^ 20)) * 2 ^ 12 =
          (2 ^ 64) * 4095 + (immediate.toNat * 4096 + (2 ^ 64 - 2 ^ 32)) := by
      omega
    rw [rearrange, Nat.add_mod, Nat.mul_mod]
    simp only [Nat.mod_self, zero_mul, Nat.zero_mod, zero_add,
      Nat.mod_eq_of_lt residueLt]
  · have low : immediate.toNat < 2 ^ 19 := by
      by_contra high
      exact sign (msb_iff.mpr (by omega))
    rw [if_neg sign, if_pos low]
    simp only [Nat.add_zero]
    rw [Nat.mod_eq_of_lt]
    omega

/-! ## Adapter-family event constructors -/

/-- Extract the register indices of a C/B/A-shaped instruction. -/
private def cbaRegisters? : instruction → Option (BitVec 5 × BitVec 5 × BitVec 5)
  | .RTYPE (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .RTYPEW (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .MUL (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .MULW (rs2, rs1, rd) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .DIV (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .DIVW (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .REM (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | .REMW (rs2, rs1, rd, _) => some (regidxBits rs2, regidxBits rs1, regidxBits rd)
  | _ => none

/-- Build an R-type family event from the canonical C/B/A stamped shape. -/
private def rTypeEvent? (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) : Option RTypeEvent := do
  let registers ← cbaRegisters? decoded
  match stamped with
  | [c, b, a] =>
      match c.touch.slot, b.touch.slot, a.touch.slot with
      | .opC, .opB, .opA =>
          pure
            { clk := clk
              pc := pc
              opcode := opcode
              opA := registers.2.2.toNat
              opB := registers.2.1.toNat
              opC := registers.1.toNat
              b := b.touch.pulled.toNat
              c := c.touch.pulled.toNat
              prevA := a.touch.pulled.toNat
              prevTsA := a.previous
              prevTsB := b.previous
              prevTsC := c.previous }
      | _, _, _ => none
  | _ => none

/-- Build the register-register form of the ALU-type family. -/
private def aluRegisterEvent? (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) : Option ALUTypeEvent := do
  let registers ← cbaRegisters? decoded
  match stamped with
  | [c, b, a] =>
      match c.touch.slot, b.touch.slot, a.touch.slot with
      | .opC, .opB, .opA =>
          pure
            { clk := clk
              pc := pc
              opcode := opcode
              opA := registers.2.2.toNat
              opB := registers.2.1.toNat
              opC := registers.1.toNat
              immC := 0
              b := b.touch.pulled.toNat
              c := c.touch.pulled.toNat
              prevA := a.touch.pulled.toNat
              prevTsA := a.previous
              prevTsB := b.previous
              prevTsC := c.previous }
      | _, _, _ => none
  | _ => none

/-- Build the immediate-C form of the ALU-type family. -/
private def aluImmediateEventOf? (stamped : List StampedTouch) (clk pc opcode : ℕ)
    (rs1 rd : regidx) (immediate : BitVec 64) : Option ALUTypeEvent :=
  match stamped with
  | [b, a] =>
      match b.touch.slot, a.touch.slot with
      | .opB, .opA =>
          some
            { clk := clk
              pc := pc
              opcode := opcode
              opA := (regidxBits rd).toNat
              opB := (regidxBits rs1).toNat
              opC := immediate.toNat
              immC := 1
              b := b.touch.pulled.toNat
              c := 0
              prevA := a.touch.pulled.toNat
              prevTsA := a.previous
              prevTsB := b.previous
              prevTsC := 0 }
      | _, _ => none
  | _ => none

/-- Build whichever ALU-type shape the decoded instruction carries. -/
private def aluTypeEvent? (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) : Option ALUTypeEvent :=
  match decoded with
  | .ITYPE (imm, rs1, rd, _) =>
      aluImmediateEventOf? stamped clk pc opcode rs1 rd (imm.signExtend 64)
  | .SHIFTIOP (shamt, rs1, rd, _) =>
      aluImmediateEventOf? stamped clk pc opcode rs1 rd (shamt.setWidth 64)
  | .SHIFTIWOP (shamt, rs1, rd, _) =>
      aluImmediateEventOf? stamped clk pc opcode rs1 rd (shamt.setWidth 64)
  | .ADDIW (imm, rs1, rd) =>
      aluImmediateEventOf? stamped clk pc opcode rs1 rd (imm.signExtend 64)
  | other => aluRegisterEvent? other stamped clk pc opcode

/-- Build the ordinary destination-writing I-type shape. -/
private def iWriteEventOf? (stamped : List StampedTouch) (clk pc opcode : ℕ)
    (rs1 rd : regidx) (immediate : BitVec 12) : Option ITypeEvent :=
  match stamped with
  | [b, a] =>
      match b.touch.slot, a.touch.slot with
      | .opB, .opA =>
          some
            { clk := clk
              pc := pc
              opcode := opcode
              opA := (regidxBits rd).toNat
              opB := (regidxBits rs1).toNat
              imm := sextNat immediate
              b := b.touch.pulled.toNat
              prevA := a.touch.pulled.toNat
              prevTsA := a.previous
              prevTsB := b.previous }
      | _, _ => none
  | _ => none

/-- Build the shared I-type record in its ADDI, JALR, or immutable branch interpretation. -/
private def iTypeEvent? (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) : Option ITypeEvent :=
  match decoded with
  | .ITYPE (imm, rs1, rd, _) => iWriteEventOf? stamped clk pc opcode rs1 rd imm
  | .JALR (imm, rs1, rd) => iWriteEventOf? stamped clk pc opcode rs1 rd imm
  | .BTYPE (imm, rs2, rs1, _) =>
      match stamped with
      | [b, a] =>
          match b.touch.slot, a.touch.slot with
          | .opB, .opA =>
              some
                { clk := clk
                  pc := pc
                  opcode := opcode
                  opA := (regidxBits rs1).toNat
                  opB := (regidxBits rs2).toNat
                  imm := sextNat imm
                  b := b.touch.pulled.toNat
                  prevA := a.touch.pulled.toNat
                  prevTsA := a.previous
                  prevTsB := b.previous }
          | _, _ => none
      | _ => none
  | _ => none

/-- Build the one-register J/U adapter shape. -/
private def jTypeEvent? (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) : Option JTypeEvent :=
  match stamped with
  | [a] =>
      match a.touch.slot with
      | .opA =>
          match decoded with
          | .UTYPE (imm, rd, _) =>
              let value := utypeImmediateNat imm
              some
                { clk := clk
                  pc := pc
                  opcode := opcode
                  opA := (regidxBits rd).toNat
                  immB := value
                  immC := value
                  prevA := a.touch.pulled.toNat
                  prevTsA := a.previous }
          | .JAL (imm, rd) =>
              some
                { clk := clk
                  pc := pc
                  opcode := opcode
                  opA := (regidxBits rd).toNat
                  immB := (imm.signExtend 64).toNat
                  immC := 0
                  prevA := a.touch.pulled.toNat
                  prevTsA := a.previous }
          | _ => none
      | _ => none
  | _ => none

/-- Build the RAM/B/A memory-family record. -/
private def memoryEvent? (decoded : instruction) (stamped : List StampedTouch)
    (clk pc opcode : ℕ) : Option MemoryEvent :=
  match stamped with
  | [ram, b, a] =>
      match ram.touch.slot, b.touch.slot, a.touch.slot with
      | .ram, .opB, .opA =>
          match decoded with
          | .LOAD (imm, rs1, rd, _, _) =>
              some
                { clk := clk
                  pc := pc
                  opcode := opcode
                  opA := (regidxBits rd).toNat
                  opB := (regidxBits rs1).toNat
                  imm := sextNat imm
                  b := b.touch.pulled.toNat
                  prevA := a.touch.pulled.toNat
                  prevTsA := a.previous
                  prevTsB := b.previous
                  prevMem := ram.touch.pulled.toNat
                  prevTsMem := ram.previous }
          | .STORE (imm, rs2, rs1, _) =>
              some
                { clk := clk
                  pc := pc
                  opcode := opcode
                  opA := (regidxBits rs2).toNat
                  opB := (regidxBits rs1).toNat
                  imm := sextNat imm
                  b := b.touch.pulled.toNat
                  prevA := a.touch.pulled.toNat
                  prevTsA := a.previous
                  prevTsB := b.previous
                  prevMem := ram.touch.pulled.toNat
                  prevTsMem := ram.previous }
          | _ => none
      | _, _, _ => none
  | _ => none

/-! ## Registry-indexed compilation -/

/-- Select the event constructor dictated by one registry identity.  This is private because its
public caller first computes the identity with `instructionRouteId`, preventing mismatched
instruction/family pairs. -/
private def instructionEventFor? (id : InstructionChipId) (decoded : instruction)
    (stamped : List StampedTouch) (clk pc opcode : ℕ) : Option id.Event :=
  match id with
  | .add => rTypeEvent? decoded stamped clk pc opcode
  | .addi => iTypeEvent? decoded stamped clk pc opcode
  | .addw => aluTypeEvent? decoded stamped clk pc opcode
  | .sub => rTypeEvent? decoded stamped clk pc opcode
  | .subw => rTypeEvent? decoded stamped clk pc opcode
  | .bitwise => aluTypeEvent? decoded stamped clk pc opcode
  | .lt => aluTypeEvent? decoded stamped clk pc opcode
  | .shiftLeft => aluTypeEvent? decoded stamped clk pc opcode
  | .shiftRight => aluTypeEvent? decoded stamped clk pc opcode
  | .jal => jTypeEvent? decoded stamped clk pc opcode
  | .jalr => iTypeEvent? decoded stamped clk pc opcode
  | .branch => iTypeEvent? decoded stamped clk pc opcode
  | .uType => jTypeEvent? decoded stamped clk pc opcode
  | .loadByte => memoryEvent? decoded stamped clk pc opcode
  | .loadHalf => memoryEvent? decoded stamped clk pc opcode
  | .loadWord => memoryEvent? decoded stamped clk pc opcode
  | .loadDouble => memoryEvent? decoded stamped clk pc opcode
  | .loadX0 => memoryEvent? decoded stamped clk pc opcode
  | .storeByte => memoryEvent? decoded stamped clk pc opcode
  | .storeHalf => memoryEvent? decoded stamped clk pc opcode
  | .storeWord => memoryEvent? decoded stamped clk pc opcode
  | .storeDouble => memoryEvent? decoded stamped clk pc opcode
  | .mul => rTypeEvent? decoded stamped clk pc opcode
  | .divRem => rTypeEvent? decoded stamped clk pc opcode
  | .aluX0 => aluTypeEvent? decoded stamped clk pc opcode

private theorem instructionEventFor?_utype {args : BitVec 20 × regidx × uop}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.UTYPE args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.UTYPE args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.UTYPE args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op
  all_goals
    simp_all only [uopToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, jTypeEvent?]
    rfl

private theorem instructionEventFor?_jal {args : BitVec 21 × regidx}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.JAL args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.JAL args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.JAL args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rd⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  all_goals
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, jTypeEvent?]
    rfl

private theorem instructionEventFor?_jalr {args : BitVec 12 × regidx × regidx}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.JALR args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.JALR args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.JALR args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs1, rd⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  all_goals
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, iTypeEvent?, iWriteEventOf?]
    rfl

private theorem instructionEventFor?_btype {args : BitVec 13 × regidx × regidx × bop}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.BTYPE args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.BTYPE args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.BTYPE args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs2, rs1, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op
  all_goals
    simp_all only [bopToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, iTypeEvent?]
    rfl

private theorem instructionEventFor?_itype {args : BitVec 12 × regidx × regidx × iop}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.ITYPE args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.ITYPE args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.ITYPE args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs1, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op <;> cases flag : regidxIsX0 rd
  all_goals
    simp_all only [iopToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, iTypeEvent?, iWriteEventOf?, aluTypeEvent?, aluImmediateEventOf?]
    rfl

private theorem instructionEventFor?_shiftiop {args : BitVec 6 × regidx × regidx × sop}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.SHIFTIOP args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.SHIFTIOP args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.SHIFTIOP args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs1, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op <;> cases flag : regidxIsX0 rd
  all_goals
    simp_all only [sopToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, aluTypeEvent?, aluImmediateEventOf?]
    rfl

private theorem instructionEventFor?_rtype {args : regidx × regidx × regidx × rop}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.RTYPE args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.RTYPE args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.RTYPE args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op <;> cases flag : regidxIsX0 rd
  all_goals
    simp_all only [ropToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_load {args : BitVec 12 × regidx × regidx × Bool × word_width}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.LOAD args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.LOAD args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.LOAD args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs1, rd, isU, width⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  simp only [loadOpcode] at routed
  split_ifs at routed <;> cases isU <;> cases flag : regidxIsX0 rd
  all_goals
    try simp_all only []
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, memoryEvent?] <;> rfl

private theorem instructionEventFor?_store {args : BitVec 12 × regidx × regidx × word_width}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.STORE args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.STORE args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.STORE args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs2, rs1, width⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  simp only [storeOpcode] at routed
  split_ifs at routed
  all_goals
    try simp_all only [↓reduceIte]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, memoryEvent?]
    rfl

private theorem instructionEventFor?_addiw {args : BitVec 12 × regidx × regidx}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.ADDIW args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.ADDIW args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.ADDIW args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs1, rd⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases flag : regidxIsX0 rd
  all_goals
    try simp_all only []
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, aluTypeEvent?, aluImmediateEventOf?]
    rfl

private theorem instructionEventFor?_rtypew {args : regidx × regidx × regidx × ropw}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.RTYPEW args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.RTYPEW args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.RTYPEW args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op <;> cases flag : regidxIsX0 rd
  all_goals
    simp_all only [ropwToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_shiftiwop {args : BitVec 5 × regidx × regidx × sopw}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.SHIFTIWOP args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.SHIFTIWOP args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.SHIFTIWOP args) stamped clk pc opcode).isSome := by
  rcases args with ⟨imm, rs1, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases op <;> cases flag : regidxIsX0 rd
  all_goals
    simp_all only [sopwToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, aluTypeEvent?, aluImmediateEventOf?]
    rfl

private theorem instructionEventFor?_mul {args : regidx × regidx × regidx × mul_op}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.MUL args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.MUL args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.MUL args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, op⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  rcases op with ⟨part, signed1, signed2⟩
  cases part <;> cases signed1 <;> cases signed2 <;> cases flag : regidxIsX0 rd
  all_goals
    simp_all only [mulOpToOpcode]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_mulw {args : regidx × regidx × regidx}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.MULW args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.MULW args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.MULW args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases flag : regidxIsX0 rd
  all_goals
    try simp_all only []
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_div {args : regidx × regidx × regidx × Bool}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.DIV args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.DIV args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.DIV args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, isU⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases isU <;> cases flag : regidxIsX0 rd
  all_goals
    try simp_all only [↓reduceIte]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_divw {args : regidx × regidx × regidx × Bool}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.DIVW args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.DIVW args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.DIVW args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, isU⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases isU <;> cases flag : regidxIsX0 rd
  all_goals
    try simp_all only [↓reduceIte]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_rem {args : regidx × regidx × regidx × Bool}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.REM args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.REM args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.REM args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, isU⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases isU <;> cases flag : regidxIsX0 rd
  all_goals
    try simp_all only [↓reduceIte]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

private theorem instructionEventFor?_remw {args : regidx × regidx × regidx × Bool}
    {id : InstructionChipId} {stamped : List StampedTouch}
    (routed : instructionRouteId (.REMW args) = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots (.REMW args))
    (clk pc opcode : ℕ) : (instructionEventFor? id (.REMW args) stamped clk pc opcode).isSome := by
  rcases args with ⟨rs2, rs1, rd, isU⟩
  simp only [instructionRouteId, instructionRouteKey, Option.bind_some] at routed
  simp only [instructionAccessSlots, List.map_eq_cons_iff, List.map_eq_nil_iff] at shape
  rcases shape with ⟨first, rest, rfl, firstSlot, shape⟩
  repeat' rcases shape with ⟨next, rest, rfl, nextSlot, shape⟩
  cases isU <;> cases flag : regidxIsX0 rd
  all_goals
    try simp_all only [↓reduceIte]
    simp [routeId, InstructionChipId.all, InstructionRoute.claims,
      InstructionChipId.route, RdGuard.holds] at routed
    cases routed
    simp_all [instructionEventFor?, rTypeEvent?, cbaRegisters?, aluTypeEvent?, aluRegisterEvent?]
    rfl

/-- Canonical roles make every selected family constructor total, including aliases and `x0`. -/
private theorem instructionEventFor?_isSome {id : InstructionChipId} {decoded : instruction}
    {stamped : List StampedTouch} (routed : instructionRouteId decoded = some id)
    (shape : stamped.map (fun touch => touch.touch.slot) = instructionAccessSlots decoded)
    (clk pc opcode : ℕ) : (instructionEventFor? id decoded stamped clk pc opcode).isSome := by
  cases decoded
  case UTYPE => exact instructionEventFor?_utype routed shape clk pc opcode
  case JAL => exact instructionEventFor?_jal routed shape clk pc opcode
  case JALR => exact instructionEventFor?_jalr routed shape clk pc opcode
  case BTYPE => exact instructionEventFor?_btype routed shape clk pc opcode
  case ITYPE => exact instructionEventFor?_itype routed shape clk pc opcode
  case SHIFTIOP => exact instructionEventFor?_shiftiop routed shape clk pc opcode
  case RTYPE => exact instructionEventFor?_rtype routed shape clk pc opcode
  case LOAD => exact instructionEventFor?_load routed shape clk pc opcode
  case STORE => exact instructionEventFor?_store routed shape clk pc opcode
  case ADDIW => exact instructionEventFor?_addiw routed shape clk pc opcode
  case RTYPEW => exact instructionEventFor?_rtypew routed shape clk pc opcode
  case SHIFTIWOP => exact instructionEventFor?_shiftiwop routed shape clk pc opcode
  case MUL => exact instructionEventFor?_mul routed shape clk pc opcode
  case MULW => exact instructionEventFor?_mulw routed shape clk pc opcode
  case DIV => exact instructionEventFor?_div routed shape clk pc opcode
  case DIVW => exact instructionEventFor?_divw routed shape clk pc opcode
  case REM => exact instructionEventFor?_rem routed shape clk pc opcode
  case REMW => exact instructionEventFor?_remw routed shape clk pc opcode
  all_goals simp [instructionRouteId, instructionRouteKey] at routed

/-- The complete proof-independent result for one instruction.  The access schedule retains the
stamped instruction roles, any preceding refresh events, and the outgoing frontier in one carrier;
later compiler stages never reconstruct a parallel access model from event fields. -/
structure CompiledInstructionEvent where
  routed : RoutedEvent
  plan : InstructionAccessPlan
  schedule : AccessSchedule

namespace CompiledInstructionEvent

/-- The role-ordered timestamps copied into the instruction table's semantic event. -/
def stamped (compiled : CompiledInstructionEvent) : List StampedTouch :=
  compiled.schedule.stampedTouches

/-- Register refreshes which must precede this instruction row. -/
def memoryBumps (compiled : CompiledInstructionEvent) : List MemoryBumpEvent :=
  compiled.schedule.memoryBumps

/-- The last-access frontier after every instruction role. -/
def nextFrontier (compiled : CompiledInstructionEvent) : AccessFrontier :=
  compiled.schedule.outgoing

end CompiledInstructionEvent

/-- Compile one decoded supported transition using the canonical refresh-aware access scheduler.

At a 24-bit timestamp-window boundary `scheduleAccessPlan` inserts a register `MemoryBump` before
C/B/A and makes the instruction event cite the refreshed `base + 1` timestamp.  RAM is never
refreshed.  Thus this public compiler does not expose or accidentally substitute the older
refresh-naive `stampPlan` schedule.

Failure means exactly one of: the raw Sail constructor is outside the decoder image, the source
PC/value image is absent, routing is unsupported, or the canonical adapter shape no longer agrees
with the selected registry family. -/
def compileInstructionEvent? (view : SP1TransitionView)
    (frontier : AccessFrontier) (clk : ℕ) : Option CompiledInstructionEvent :=
  match view.accessPlan? with
  | none => none
  | some accesses =>
      let schedule := scheduleAccessPlan frontier clk accesses
      match instructionEventFor? view.chipId view.decoded schedule.stampedTouches clk
          view.pc.toNat view.routeKey.opcode.toNat with
      | none => none
      | some event =>
          some
            { routed := ⟨view.chipId, event⟩
              plan := accesses
              schedule := schedule }

/-- The narrow transparent readiness boundary for one instruction event.  No row-validity theorem
or Clean witness is hidden here. -/
def InstructionEventReady (view : SP1TransitionView)
    (frontier : AccessFrontier) (clk : ℕ) : Prop :=
  (compileInstructionEvent? view frontier clk).isSome

theorem instructionEventReady_iff {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} :
    InstructionEventReady view frontier clk ↔
      ∃ result, compileInstructionEvent? view frontier clk = some result := by
  exact Option.isSome_iff_exists

/-- Canonical access extraction suffices for event compilation, for every frontier and clock.
Readiness is a derived compatibility result; it is not an extra semantic-domain condition. -/
theorem instructionEventReady_of_projection {program : GuestProgram} {located : Machine.LocatedTransition}
    {view : SP1TransitionView} {plan : InstructionAccessPlan}
    (projected : projectSP1Transition? program located = some view)
    (accesses : view.accessPlan? = some plan) (frontier : AccessFrontier) (clk : ℕ) :
    InstructionEventReady view frontier clk := by
  have shape : (scheduleAccessPlan frontier clk plan).stampedTouches.map (fun touch => touch.touch.slot) =
      instructionAccessSlots view.decoded := by
    change List.map (PlannedTouch.slot ∘ StampedTouch.touch) _ = _
    rw [← List.map_map, scheduleAccessPlan_erase]
    exact instructionAccessPlan_slots ((projectSP1Transition?_accesses projected).trans accesses)
  obtain ⟨event, generated⟩ := Option.isSome_iff_exists.mp
    (instructionEventFor?_isSome (projectSP1Transition?_route projected) shape clk
      view.pc.toNat view.routeKey.opcode.toNat)
  simp only [InstructionEventReady, compileInstructionEvent?, accesses, generated, Option.isSome_some]

/-- Successful compilation exposes each proof-independent projection used by the `do` block. -/
private theorem compileInstructionEvent?_components {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result) :
    ∃ accesses event,
      view.accessPlan? = some accesses ∧
      instructionEventFor? view.chipId view.decoded
          (scheduleAccessPlan frontier clk accesses).stampedTouches clk
          view.pc.toNat view.routeKey.opcode.toNat = some event ∧
        result =
          { routed := ⟨view.chipId, event⟩
            plan := accesses
            schedule := scheduleAccessPlan frontier clk accesses } := by
  unfold compileInstructionEvent? at generated
  cases accessEq : view.accessPlan? with
  | none => simp [accessEq] at generated
  | some accesses =>
      simp only [accessEq] at generated
      cases eventEq : instructionEventFor? view.chipId view.decoded
          (scheduleAccessPlan frontier clk accesses).stampedTouches clk
          view.pc.toNat view.routeKey.opcode.toNat with
      | none => simp [eventEq] at generated
      | some event =>
          rw [eventEq] at generated
          simp only [Option.some.injEq] at generated
          exact ⟨accesses, event, rfl, eventEq, generated.symm⟩

/-- Compilation cannot invent or relabel a route: the dependent event carries exactly the identity
selected by the canonical semantic router. -/
theorem compileInstructionEvent?_route {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result) :
    result.routed.id = view.chipId := by
  obtain ⟨accesses, event, accessEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  rfl

/-- The result retains the exact canonical access plan returned by the field-free extractor. -/
theorem compileInstructionEvent?_accessPlan {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result) :
    view.accessPlan? = some result.plan := by
  obtain ⟨accesses, event, accessEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact accessEq

/-- For a retained shared transition projection, the compiler plan is literally the canonical
Model-layer plan of that source/target pair. -/
theorem compileInstructionEvent?_accessPlan_generated
    {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (generated : compileInstructionEvent? view frontier clk = some result) :
    instructionAccessPlan? view.decoded located.source located.transition.target =
      some result.plan := by
  rw [projectSP1Transition?_accesses projected]
  exact compileInstructionEvent?_accessPlan generated

/-- Stamping is not a second access representation: erasing its timestamps returns the retained
canonical plan literally. -/
theorem compileInstructionEvent?_stamped_touches {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result) :
    result.stamped.map StampedTouch.touch = result.plan := by
  obtain ⟨accesses, event, accessEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact scheduleAccessPlan_erase frontier clk accesses

/-- A well-formed extracted plan and a bounded incoming frontier make every timestamp copied into
the event strictly earlier than its own current access.  This discharges the timestamp half of all
four adapter-family `WellFormed` predicates without any instruction-specific semantic premise. -/
theorem compileInstructionEvent?_timestamps {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result)
    (wellFormed : result.plan.WellFormed)
    (bounded : frontier.BoundedAt clk) :
    ∀ stamped ∈ result.stamped, stamped.previous < stamped.current clk := by
  obtain ⟨accesses, event, accessEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact scheduleAccessPlan_previous_lt wellFormed bounded

/-- Every refresh inserted for a compiled row satisfies the MemoryBump event boundary. -/
theorem compileInstructionEvent?_memoryBumps_wellFormed {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result)
    (wellFormed : result.plan.WellFormed)
    (bounded : frontier.BoundedAt clk) (aligned : clk % ordinaryClkInc = 1)
    (currLt : clk + 1 < 2 ^ 48) :
    ∀ event ∈ result.memoryBumps, event.WellFormed := by
  obtain ⟨accesses, event, accessEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact scheduleAccessPlan_memoryBumps_wellFormed
    wellFormed bounded aligned currLt

/-- The scheduler returns a frontier valid at the following ordinary row. -/
theorem compileInstructionEvent?_frontier_bounded_next {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? view frontier clk = some result)
    (bounded : frontier.BoundedAt clk) :
    result.nextFrontier.BoundedAt (clk + ordinaryClkInc) := by
  obtain ⟨accesses, event, accessEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact scheduleAccessPlan_outgoing_bounded_next accesses bounded

private theorem cbaRegisters?_nonzero {decoded : instruction}
    {registers : BitVec 5 × BitVec 5 × BitVec 5} {key : InstructionRouteKey}
    (extracted : cbaRegisters? decoded = some registers)
    (keyEq : instructionRouteKey decoded = some key) (nonzero : key.opAIsX0 = false) :
    registers.2.2.toNat ≠ 0 := by
  cases decoded <;> simp only [cbaRegisters?] at extracted
  all_goals first | contradiction | skip
  all_goals
    cases Option.some.inj extracted
    simp only [instructionRouteKey, Option.some.injEq] at keyEq
    subst key
    simp only [regidxIsX0, regidxBits] at nonzero ⊢
    intro zero
    exact (decide_eq_false_iff_not.mp nonzero) (BitVec.eq_of_toNat_eq zero)

private theorem rTypeEvent?_wellFormed {decoded : instruction}
    {stamped : List StampedTouch} {clk pc : ℕ} {key : InstructionRouteKey} {event : RTypeEvent}
    (keyEq : instructionRouteKey decoded = some key) (nonzero : key.opAIsX0 = false)
    (phase : clk % 8 = 1) (pcBound : pc < 2 ^ 48)
    (ordered : ∀ touch ∈ stamped, touch.previous < touch.current clk)
    (generated : rTypeEvent? decoded stamped clk pc key.opcode.toNat = some event) :
    event.WellFormed ∧ event.opcode = key.opcode.toNat := by
  unfold rTypeEvent? at generated
  cases registersEq : cbaRegisters? decoded with
  | none => simp [registersEq] at generated
  | some registers =>
    simp only [registersEq] at generated
    split at generated
    · rename_i original c b a
      split at generated
      · rename_i cSlot bSlot aSlot
        cases Option.some.inj generated
        have cTime := ordered c (by simp)
        have bTime := ordered b (by simp)
        have aTime := ordered a (by simp)
        simp only [StampedTouch.current, PlannedTouch.recordTime, cSlot, bSlot, aSlot,
          AccessSlot.recordOffset_opC, AccessSlot.recordOffset_opB, AccessSlot.recordOffset_opA] at cTime bTime aTime
        exact ⟨⟨phase, pcBound, registers.2.2.isLt, registers.2.1.isLt, registers.1.isLt,
          cbaRegisters?_nonzero registersEq keyEq nonzero,
          b.touch.pulled.isLt, c.touch.pulled.isLt, a.touch.pulled.isLt,
          aTime, bTime, cTime⟩, rfl⟩
      · contradiction
    · contradiction

/-- The five R-type adapter tables obtain their complete event validity from canonical projection
and the running scheduler invariant. Operand bounds come from the bitvectors themselves; routing
supplies the destination and opcode conditions. This includes all multiply/divide/remainder values,
without any nonzero-divisor or no-overflow restriction. -/
theorem compileInstructionEvent?_rtype_valid
    {program : GuestProgram} {located : Machine.LocatedTransition} {view : SP1TransitionView}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (projected : projectSP1Transition? program located = some view)
    (generated : compileInstructionEvent? view frontier clk = some result)
    (family : view.chipId ∈ [.add, .sub, .subw, .mul, .divRem])
    (phase : clk % 8 = 1) (bounded : frontier.BoundedAt clk) :
    result.routed.id.Valid result.routed.event := by
  have components := projectSP1Transition?_components projected
  have pcBound : view.pc.toNat < 2 ^ 48 := by
    obtain ⟨entry, found, _⟩ := Option.map_eq_some_iff.mp components.2.1
    have same : entry.1 = view.pc := by simpa only [beq_iff_eq] using List.find?_some found
    have window := program.rom_in_window entry (List.mem_of_find?_eq_some found)
    rw [same] at window
    omega
  have keyEq := components.2.2.2.2.1
  have routed := components.2.2.2.2.2.1
  have wellFormed := instructionAccessPlan_wellFormed
    (compileInstructionEvent?_accessPlan_generated projected generated)
  have ordered := compileInstructionEvent?_timestamps generated wellFormed bounded
  have claimed : view.chipId.route.claims view.routeKey.opcode view.routeKey.opAIsX0 = true := by
    rw [instructionRouteId, keyEq, Option.bind_some] at routed
    change (fun id => id.route.claims view.routeKey.opcode view.routeKey.opAIsX0) view.chipId = true
    exact List.find?_some (p := fun id : InstructionChipId =>
      id.route.claims view.routeKey.opcode view.routeKey.opAIsX0) routed
  rcases view with ⟨pc, word, decoded, key, id, plan⟩
  dsimp only at family claimed keyEq pcBound
  simp only [List.mem_cons, List.not_mem_nil, or_false] at family
  rcases family with rfl | rfl | rfl | rfl | rfl
  all_goals
    obtain ⟨accesses, event, _, constructed, rfl⟩ := compileInstructionEvent?_components generated
    have nonzero : key.opAIsX0 = false := by
      simpa only [InstructionChipId.route, RdGuard.holds, Bool.not_eq_true']
        using (Bool.and_eq_true_iff.mp claimed).2
    have valid := rTypeEvent?_wellFormed keyEq nonzero phase pcBound ordered constructed
  · exact valid.1
  · exact valid.1
  · exact valid.1
  · refine ⟨valid.1, ?_⟩
    simp only [InstructionChipId.route, InstructionRoute.claims, RdGuard.holds,
      Bool.and_eq_true, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at claimed
    rcases claimed.1 with h | h | h | h | h <;>
      simp [RTypeEvent.IsMul, valid.2, h, Soundness.Opcode.toNat]
  · refine ⟨valid.1, ?_⟩
    simp only [InstructionChipId.route, InstructionRoute.claims, RdGuard.holds,
      Bool.and_eq_true, List.contains_iff_mem, List.mem_cons, List.not_mem_nil, or_false] at claimed
    rcases claimed.1 with h | h | h | h | h | h | h | h <;>
      simp [RTypeEvent.IsDivRem, valid.2, h, Soundness.Opcode.toNat]

/-- The branch event keeps the entire signed thirteen-bit Sail immediate. In particular the
compiler does not coerce it through the twelve-bit I-type immediate representation. -/
theorem compileInstructionEvent?_branch_immediate
    {view : SP1TransitionView} {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent} {imm : BitVec 13} {rs2 rs1 : regidx} {op : bop}
    (decoded : view.decoded = .BTYPE (imm, rs2, rs1, op))
    (routed : view.chipId = .branch)
    (generated : compileInstructionEvent? view frontier clk = some result) :
    ∃ event : ITypeEvent, result.routed = ⟨.branch, event⟩ ∧
      event.imm = (imm.signExtend 64).toNat := by
  rcases view with ⟨pc, word, instruction, key, id, plan⟩
  dsimp only at decoded routed
  subst instruction id
  obtain ⟨accesses, event, _, constructed, rfl⟩ := compileInstructionEvent?_components generated
  refine ⟨event, rfl, ?_⟩
  simp only [instructionEventFor?, iTypeEvent?] at constructed
  split at constructed
  · split at constructed
    · cases Option.some.inj constructed
      rfl
    · contradiction
  · contradiction

end SP1Clean.TraceGen
