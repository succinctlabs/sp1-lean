import SP1Clean.Model.Semantics.InstructionPlan
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

/-- The numeric PC read from the source Sail state. -/
def sourcePc? (source : SailState) : Option ℕ :=
  (source.regs.get? Register.PC).map BitVec.toNat

/-- The SP1 opcode discriminant of a supported decoded instruction. -/
private def instructionOpcode? (decoded : instruction) : Option ℕ :=
  (instructionRouteKey decoded).map fun key => key.opcode.toNat

/-- The guarded image of the pinned decoder.  These are precisely the three constructor families
whose raw Sail carrier has values outside the actual instruction encoding image. -/
def instructionImageOK : instruction → Bool
  | .MUL (_, _, _, operation) => mulOpCanonical operation
  | .LOAD (_, _, _, isUnsigned, width) => loadWidthOK width isUnsigned
  | .STORE (_, _, _, width) => storeWidthOK width
  | _ => true

private def sext12Nat (immediate : BitVec 12) : ℕ :=
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
              imm := sext12Nat immediate
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
                  imm := sext12Nat imm
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
                  imm := sext12Nat imm
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
                  imm := sext12Nat imm
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
def compileInstructionEvent? (decoded : instruction) (source target : SailState)
    (frontier : AccessFrontier) (clk : ℕ) : Option CompiledInstructionEvent :=
  if instructionImageOK decoded then
    match sourcePc? source with
    | none => none
    | some pc =>
      match instructionOpcode? decoded with
      | none => none
      | some opcode =>
        match instructionAccessPlan? decoded source target with
        | none => none
        | some plan =>
          let schedule := scheduleAccessPlan frontier clk plan
          match instructionRouteId decoded with
          | none => none
          | some id =>
            match instructionEventFor? id decoded schedule.stampedTouches clk pc opcode with
            | none => none
            | some event =>
              some
                { routed := ⟨id, event⟩
                  plan := plan
                  schedule := schedule }
  else none

/-- The narrow transparent readiness boundary for one instruction event.  No row-validity theorem
or Clean witness is hidden here. -/
def InstructionEventReady (decoded : instruction) (source target : SailState)
    (frontier : AccessFrontier) (clk : ℕ) : Prop :=
  (compileInstructionEvent? decoded source target frontier clk).isSome

theorem instructionEventReady_iff {decoded : instruction} {source target : SailState}
    {frontier : AccessFrontier} {clk : ℕ} :
    InstructionEventReady decoded source target frontier clk ↔
      ∃ result, compileInstructionEvent? decoded source target frontier clk = some result := by
  exact Option.isSome_iff_exists

/-- Successful compilation exposes each proof-independent projection used by the `do` block. -/
private theorem compileInstructionEvent?_components {decoded : instruction}
    {source target : SailState} {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? decoded source target frontier clk = some result) :
    ∃ pc opcode plan id event,
      sourcePc? source = some pc ∧
        instructionOpcode? decoded = some opcode ∧
        instructionAccessPlan? decoded source target = some plan ∧
        instructionRouteId decoded = some id ∧
        instructionEventFor? id decoded
            (scheduleAccessPlan frontier clk plan).stampedTouches clk pc opcode =
          some event ∧
        result =
          { routed := ⟨id, event⟩
            plan := plan
            schedule := scheduleAccessPlan frontier clk plan } := by
  unfold compileInstructionEvent? at generated
  by_cases imageOK : instructionImageOK decoded = true
  · simp only [if_pos imageOK] at generated
    cases pcEq : sourcePc? source with
    | none => simp [pcEq] at generated
    | some pc =>
        simp only [pcEq] at generated
        cases opcodeEq : instructionOpcode? decoded with
        | none => simp [opcodeEq] at generated
        | some opcode =>
            simp only [opcodeEq] at generated
            cases planEq : instructionAccessPlan? decoded source target with
            | none => simp [planEq] at generated
            | some plan =>
                simp only [planEq] at generated
                cases routeEq : instructionRouteId decoded with
                | none => simp [routeEq] at generated
                | some id =>
                    simp only [routeEq] at generated
                    cases eventEq : instructionEventFor? id decoded
                        (scheduleAccessPlan frontier clk plan).stampedTouches clk pc opcode with
                    | none =>
                        rw [eventEq] at generated
                        simp at generated
                    | some event =>
                        rw [eventEq] at generated
                        simp only [Option.some.injEq] at generated
                        have resultEq :
                            ({ routed := ⟨id, event⟩
                               plan := plan
                               schedule := scheduleAccessPlan frontier clk plan } :
                              CompiledInstructionEvent) = result := by
                          simpa using generated
                        exact ⟨pc, opcode, plan, id, event, rfl, rfl, rfl, rfl,
                          eventEq, resultEq.symm⟩
  · simp [imageOK] at generated

/-- Compilation cannot invent or relabel a route: the dependent event carries exactly the identity
selected by the canonical semantic router. -/
theorem compileInstructionEvent?_route {decoded : instruction} {source target : SailState}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? decoded source target frontier clk = some result) :
    instructionRouteId decoded = some result.routed.id := by
  obtain ⟨pc, opcode, plan, id, event, pcEq, opcodeEq, planEq, routeEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact routeEq

/-- The result retains the exact canonical access plan returned by the field-free extractor. -/
theorem compileInstructionEvent?_accessPlan {decoded : instruction} {source target : SailState}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? decoded source target frontier clk = some result) :
    instructionAccessPlan? decoded source target = some result.plan := by
  obtain ⟨pc, opcode, plan, id, event, pcEq, opcodeEq, planEq, routeEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact planEq

/-- Stamping is not a second access representation: erasing its timestamps returns the retained
canonical plan literally. -/
theorem compileInstructionEvent?_stamped_touches {decoded : instruction} {source target : SailState}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? decoded source target frontier clk = some result) :
    result.stamped.map StampedTouch.touch = result.plan := by
  obtain ⟨pc, opcode, plan, id, event, pcEq, opcodeEq, planEq, routeEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact scheduleAccessPlan_erase frontier clk plan

/-- A well-formed extracted plan and a bounded incoming frontier make every timestamp copied into
the event strictly earlier than its own current access.  This discharges the timestamp half of all
four adapter-family `WellFormed` predicates without any instruction-specific semantic premise. -/
theorem compileInstructionEvent?_timestamps {decoded : instruction} {source target : SailState}
    {frontier : AccessFrontier} {clk : ℕ} {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? decoded source target frontier clk = some result)
    (bounded : frontier.BoundedAt clk) :
    ∀ stamped ∈ result.stamped, stamped.previous < stamped.current clk := by
  obtain ⟨pc, opcode, plan, id, event, pcEq, opcodeEq, planEq, routeEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact scheduleAccessPlan_previous_lt (instructionAccessPlan_wellFormed planEq) bounded

/-- Every refresh inserted for a compiled row satisfies the MemoryBump event boundary. -/
theorem compileInstructionEvent?_memoryBumps_wellFormed {decoded : instruction}
    {source target : SailState} {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? decoded source target frontier clk = some result)
    (bounded : frontier.BoundedAt clk) (aligned : clk % ordinaryClkInc = 1)
    (currLt : clk + 1 < 2 ^ 48) :
    ∀ event ∈ result.memoryBumps, event.WellFormed := by
  obtain ⟨pc, opcode, plan, id, event, pcEq, opcodeEq, planEq, routeEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact scheduleAccessPlan_memoryBumps_wellFormed
    (instructionAccessPlan_wellFormed planEq) bounded aligned currLt

/-- The scheduler returns a frontier valid at the following ordinary row. -/
theorem compileInstructionEvent?_frontier_bounded_next {decoded : instruction}
    {source target : SailState} {frontier : AccessFrontier} {clk : ℕ}
    {result : CompiledInstructionEvent}
    (generated : compileInstructionEvent? decoded source target frontier clk = some result)
    (bounded : frontier.BoundedAt clk) :
    result.nextFrontier.BoundedAt (clk + ordinaryClkInc) := by
  obtain ⟨pc, opcode, plan, id, event, pcEq, opcodeEq, planEq, routeEq, eventEq, rfl⟩ :=
    compileInstructionEvent?_components generated
  exact scheduleAccessPlan_outgoing_bounded_next plan bounded

end SP1Clean.TraceGen
