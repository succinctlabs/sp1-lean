import SP1Clean.Model.Semantics.AccessPlan
import SP1Clean.Model.Semantics.Decode

/-!
# Semantic instruction access-plan extraction

This module projects one decoded, supported LeanRV64D instruction and its source/target Sail states
onto the field-free `InstructionAccessPlan` shared by trace completeness.  It is deliberately only a
projection:

* register pulls and immutable read-backs come from the source state;
* a genuine destination push comes from the target state (an `x0` destination is an immutable
  read-back of zero);
* a load/store names the aligned eight-byte `RamCell` containing its effective byte address and
  reads the full prior/post cell from the source/target states; and
* unsupported instructions, absent registers, or a RAM cell with any absent byte fail closed.

The emitted roles are in SP1 record-time order: `RAM`, C, B, A, with absent immediate roles omitted.
No clock, timestamp, opcode copy, chip row, event record, or execution relation is introduced here.
Facts connecting the target values to an official Sail step belong to the later compiler proof; the
transparent `InstructionPlanReady` predicate exposes exactly when this pure extractor succeeds.
-/

open LeanRV64D.Defs

namespace SP1Clean.Semantics

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target (instructionRouteId)

/-! ## Field-free operand projections -/

/-- The five-bit architectural index carried by a generated Sail `regidx`. -/
def regidxBits : regidx → BitVec 5
  | .Regidx bits => bits

/-- The wrapped 64-bit effective address used by ordinary loads and stores. -/
def memoryEffectiveAddress (base : BitVec 64) (offset : BitVec 12) : BitVec 64 :=
  base + offset.signExtend 64

/-- The canonical aligned eight-byte cell containing a byte address. -/
def ramCellOfByteAddress (address : BitVec 64) : RamCell :=
  BitVec.ofNat 61 (address.toNat / 8)

/-- The aligned RAM cell touched by a memory instruction with this base and immediate. -/
def memoryRamCell (base : BitVec 64) (offset : BitVec 12) : RamCell :=
  ramCellOfByteAddress (memoryEffectiveAddress base offset)

/-! ## Canonical plan constructors -/

/-- A register role which posts exactly the value it read. -/
private def registerReadback (slot : AccessSlot) (index : BitVec 5)
    (value : BitVec 64) : PlannedTouch where
  slot := slot
  loc := .reg index
  pulled := value
  pushed := value

/-- The A-role prior and post values of a genuine destination (or an `x0` read-back). -/
private def registerDestination (index : BitVec 5) (prior post : BitVec 64) : PlannedTouch where
  slot := .opA
  loc := .reg index
  pulled := prior
  pushed := post

/-- The full prior and post values of one aligned RAM cell. -/
private def ramAccess (cell : RamCell) (prior post : BitVec 64) : PlannedTouch where
  slot := .ram
  loc := .ram cell
  pulled := prior
  pushed := post

/-- A destination at `x0` is the adapter's immutable zero read-back; other destinations are read
from the target state. -/
private def destinationPost? (target : SailState) (index : BitVec 5)
    (prior : BitVec 64) : Option (BitVec 64) :=
  if index = 0 then some prior else target.get_reg? index

private theorem cba_wellFormed (c b a : BitVec 5) (cv bv av post : BitVec 64) :
    InstructionAccessPlan.WellFormed
      [registerReadback .opC c cv, registerReadback .opB b bv,
        registerDestination a av post] := by
  constructor <;> simp [registerReadback, registerDestination, AccessSlot.Accepts]

private theorem ba_wellFormed (b a : BitVec 5) (bv av post : BitVec 64) :
    InstructionAccessPlan.WellFormed
      [registerReadback .opB b bv, registerDestination a av post] := by
  constructor <;> simp [registerReadback, registerDestination, AccessSlot.Accepts]

private theorem a_wellFormed (a : BitVec 5) (av post : BitVec 64) :
    InstructionAccessPlan.WellFormed [registerDestination a av post] := by
  constructor <;> simp [registerDestination, AccessSlot.Accepts]

private theorem baReadback_wellFormed (b a : BitVec 5) (bv av : BitVec 64) :
    InstructionAccessPlan.WellFormed
      [registerReadback .opB b bv, registerReadback .opA a av] := by
  constructor <;> simp [registerReadback, AccessSlot.Accepts]

private theorem ramBa_wellFormed (cell : RamCell) (b a : BitVec 5)
    (oldRam newRam bv av post : BitVec 64) :
    InstructionAccessPlan.WellFormed
      [ramAccess cell oldRam newRam, registerReadback .opB b bv,
        registerDestination a av post] := by
  constructor <;> simp [ramAccess, registerReadback, registerDestination, AccessSlot.Accepts]

private theorem ramBaReadback_wellFormed (cell : RamCell) (b a : BitVec 5)
    (oldRam newRam bv av : BitVec 64) :
    InstructionAccessPlan.WellFormed
      [ramAccess cell oldRam newRam, registerReadback .opB b bv,
        registerReadback .opA a av] := by
  constructor <;> simp [ramAccess, registerReadback, AccessSlot.Accepts]

/-- Internal proof-carrying result.  Erasing the proof below gives the public `Option` API while
making the canonical ordering theorem independent of option-case proof plumbing. -/
private structure CertifiedInstructionPlan where
  plan : InstructionAccessPlan
  wellFormed : plan.WellFormed
  length_le_three : plan.length ≤ 3

private def cbaPlan? (source target : SailState) (rs2 rs1 rd : regidx) :
    Option CertifiedInstructionPlan := do
  let c := regidxBits rs2
  let b := regidxBits rs1
  let a := regidxBits rd
  let cv ← source.get_reg? c
  let bv ← source.get_reg? b
  let av ← source.get_reg? a
  let post ← destinationPost? target a av
  pure ⟨[registerReadback .opC c cv, registerReadback .opB b bv,
    registerDestination a av post], cba_wellFormed c b a cv bv av post, by simp⟩

private def baPlan? (source target : SailState) (rs1 rd : regidx) :
    Option CertifiedInstructionPlan := do
  let b := regidxBits rs1
  let a := regidxBits rd
  let bv ← source.get_reg? b
  let av ← source.get_reg? a
  let post ← destinationPost? target a av
  pure ⟨[registerReadback .opB b bv, registerDestination a av post],
    ba_wellFormed b a bv av post, by simp⟩

private def aPlan? (source target : SailState) (rd : regidx) :
    Option CertifiedInstructionPlan := do
  let a := regidxBits rd
  let av ← source.get_reg? a
  let post ← destinationPost? target a av
  pure ⟨[registerDestination a av post], a_wellFormed a av post, by simp⟩

private def baReadbackPlan? (source : SailState) (rsB rsA : regidx) :
    Option CertifiedInstructionPlan := do
  let b := regidxBits rsB
  let a := regidxBits rsA
  let bv ← source.get_reg? b
  let av ← source.get_reg? a
  pure ⟨[registerReadback .opB b bv, registerReadback .opA a av],
    baReadback_wellFormed b a bv av, by simp⟩

private def loadPlan? (source target : SailState) (offset : BitVec 12)
    (rs1 rd : regidx) : Option CertifiedInstructionPlan := do
  let b := regidxBits rs1
  let a := regidxBits rd
  let bv ← source.get_reg? b
  let av ← source.get_reg? a
  let post ← destinationPost? target a av
  let cell := memoryRamCell bv offset
  let oldRam ← ramWord64? source cell.baseAddr
  let newRam ← ramWord64? target cell.baseAddr
  pure ⟨[ramAccess cell oldRam newRam, registerReadback .opB b bv,
    registerDestination a av post], ramBa_wellFormed cell b a oldRam newRam bv av post, by simp⟩

private def storePlan? (source target : SailState) (offset : BitVec 12)
    (rs2 rs1 : regidx) : Option CertifiedInstructionPlan := do
  let b := regidxBits rs1
  let a := regidxBits rs2
  let bv ← source.get_reg? b
  let av ← source.get_reg? a
  let cell := memoryRamCell bv offset
  let oldRam ← ramWord64? source cell.baseAddr
  let newRam ← ramWord64? target cell.baseAddr
  pure ⟨[ramAccess cell oldRam newRam, registerReadback .opB b bv,
    registerReadback .opA a av], ramBaReadback_wellFormed cell b a oldRam newRam bv av, by simp⟩

/-! ## Instruction extraction -/

/-- The five adapter shapes selected by every instruction constructor covered by
`instructionRouteId`.  This function assumes only that routing has already succeeded. -/
private def instructionPlanByShape? (source target : SailState) :
    instruction → Option CertifiedInstructionPlan
  | .RTYPE (rs2, rs1, rd, _) => cbaPlan? source target rs2 rs1 rd
  | .ITYPE (_, rs1, rd, _) => baPlan? source target rs1 rd
  | .UTYPE (_, rd, _) => aPlan? source target rd
  | .JAL (_, rd) => aPlan? source target rd
  | .JALR (_, rs1, rd) => baPlan? source target rs1 rd
  | .BTYPE (_, rs2, rs1, _) => baReadbackPlan? source rs2 rs1
  | .LOAD (offset, rs1, rd, _, _) => loadPlan? source target offset rs1 rd
  | .STORE (offset, rs2, rs1, _) => storePlan? source target offset rs2 rs1
  | .SHIFTIOP (_, rs1, rd, _) => baPlan? source target rs1 rd
  | .SHIFTIWOP (_, rs1, rd, _) => baPlan? source target rs1 rd
  | .ADDIW (_, rs1, rd) => baPlan? source target rs1 rd
  | .RTYPEW (rs2, rs1, rd, _) => cbaPlan? source target rs2 rs1 rd
  | .MUL (rs2, rs1, rd, _) => cbaPlan? source target rs2 rs1 rd
  | .MULW (rs2, rs1, rd) => cbaPlan? source target rs2 rs1 rd
  | .DIV (rs2, rs1, rd, _) => cbaPlan? source target rs2 rs1 rd
  | .DIVW (rs2, rs1, rd, _) => cbaPlan? source target rs2 rs1 rd
  | .REM (rs2, rs1, rd, _) => cbaPlan? source target rs2 rs1 rd
  | .REMW (rs2, rs1, rd, _) => cbaPlan? source target rs2 rs1 rd
  | _ => none

/-- Proof-carrying implementation behind the public extractor.  The route guard is intentional:
the shape match cannot accidentally make an instruction available outside the canonical supported
profile if decode/routing changes later. -/
private def certifiedInstructionPlan? (decoded : instruction) (source target : SailState) :
    Option CertifiedInstructionPlan :=
  match instructionRouteId decoded with
  | none => none
  | some _ => instructionPlanByShape? source target decoded

/-- Extract the exact field-free offline-memory roles of one supported decoded instruction.

The result contains at most three roles for the current supported profile: `C,B,A` for register
ALU operations, `B,A` for immediate/control-source operations, `A` for J/U operations, and
`RAM,B,A` for loads/stores.  An `x0` destination and the A slot of branch/store are immutable
read-backs rather than architectural writes. -/
def instructionAccessPlan? (decoded : instruction) (source target : SailState) :
    Option InstructionAccessPlan :=
  (certifiedInstructionPlan? decoded source target).map CertifiedInstructionPlan.plan

/-- The narrow, transparent representability boundary for the semantic access projection. -/
def InstructionPlanReady (decoded : instruction) (source target : SailState) : Prop :=
  ∃ plan, instructionAccessPlan? decoded source target = some plan

/-- A produced plan is routed by one of the twenty-five canonical instruction-table identities. -/
theorem instructionRouteId_exists_of_accessPlan {decoded : instruction} {source target : SailState}
    {plan : InstructionAccessPlan}
    (generated : instructionAccessPlan? decoded source target = some plan) :
    ∃ id, instructionRouteId decoded = some id := by
  unfold instructionAccessPlan? certifiedInstructionPlan? at generated
  cases routeEq : instructionRouteId decoded with
  | none => simp [routeEq] at generated
  | some id => exact ⟨id, rfl⟩

/-- Every extracted plan has the canonical role ordering, location kinds, and C/B read-backs. -/
theorem instructionAccessPlan_wellFormed {decoded : instruction} {source target : SailState}
    {plan : InstructionAccessPlan}
    (generated : instructionAccessPlan? decoded source target = some plan) :
    plan.WellFormed := by
  unfold instructionAccessPlan? at generated
  cases certifiedEq : certifiedInstructionPlan? decoded source target with
  | none => simp [certifiedEq] at generated
  | some certified =>
      simp only [certifiedEq, Option.map_some, Option.some.injEq] at generated
      subst plan
      exact certified.wellFormed

/-- The supported instruction profile emits at most three actual Memory-bus locations per row. -/
theorem instructionAccessPlan_length_le_three {decoded : instruction} {source target : SailState}
    {plan : InstructionAccessPlan}
    (generated : instructionAccessPlan? decoded source target = some plan) :
    plan.length ≤ 3 := by
  unfold instructionAccessPlan? at generated
  cases certifiedEq : certifiedInstructionPlan? decoded source target with
  | none => simp [certifiedEq] at generated
  | some certified =>
      simp only [certifiedEq, Option.map_some, Option.some.injEq] at generated
      subst plan
      exact certified.length_le_three

/-- Constructor form of readiness, useful when the compiler retains the extracted plan. -/
theorem InstructionPlanReady.of_generated {decoded : instruction} {source target : SailState}
    {plan : InstructionAccessPlan}
    (generated : instructionAccessPlan? decoded source target = some plan) :
    InstructionPlanReady decoded source target :=
  ⟨plan, generated⟩

end SP1Clean.Semantics
