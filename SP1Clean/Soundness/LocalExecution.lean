import SP1Clean.Soundness.ChipRegistry
import SP1Clean.FormalModel.Execution
import SP1Clean.Model.Semantics.MicroTime

/-! # Ordered grounded rows produce a local Sail execution

This is the semantic engine above channel/timing grounding and below the AIR capstone.  Its premises
contain row-local facts—registered chip, `Spec`, committed decode, current operands, and
`advanceReady`—but no next state or execution witness.  Each next state is constructed by the chip's
verified `advance` theorem.
-/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open Sail LeanRV64D
open SP1Clean.Execution
open SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

universe u

/-- The pc projection of an ordered State-bus trail.  `Row` deliberately remains generic: the
production path retains each `DecodedInstructionRow` (and therefore its physical circuit row) until
local soundness has fired, while this engine observes only its semantic `ChipRow` projection. -/
def PcWalk {Row : Type u} (rowOf : Row → ChipRow p) : BitVec 64 → BitVec 64 → List Row → Prop
  | initial, final, [] => initial = final
  | initial, final, row :: rest =>
      rcvPcOf (stateAccess (rowOf row).view) = initial ∧
        PcWalk rowOf (sndPcOf (stateAccess (rowOf row).view)) final rest

/-- State-independent facts about one active decoded row.  These come from deterministic witness
decoding, the chip registry, and Program-channel grounding; they do not belong to the evolving-state
induction. -/
structure StaticGroundedRow (program : GuestProgram) (row : ChipRow p) : Prop where
  real : row.is_real = 1
  registered : row.kind ∈ allChipKinds (p := p)
  decoded : decodedInROM program (programAccess row.view).toRow

/-- Facts about one row that depend on the current official-Sail state.  In particular, the proof of
the row's `chipSpec` is dynamic even though the proposition itself does not mention `state`: many chip
soundness assumptions are discharged from register/Memory values that are current only at this
execution position.  The timed Memory engine and per-chip readiness contracts supply these facts. -/
structure DynamicGroundedRow (data : ProverData (ZMod p)) (program : GuestProgram)
    (row : ChipRow p) (state : SailState) : Prop where
  spec : row.chipSpec data
  ready : row.kind.advanceReady row.inputs row.cols program state
  operands : ValueOperandsBound row.view state

/-- Everything needed to fire one registered chip row in the current semantic state. -/
structure GroundedRow (data : ProverData (ZMod p)) (program : GuestProgram)
    (row : ChipRow p) (state : SailState) extends
    StaticGroundedRow program row, DynamicGroundedRow data program row state

/-- Position-indexed grounding for an ordered list of row labels.  The labels stay generic so a
caller can retain a physical decoded circuit row while this semantic engine reads only `rowOf`.
Static facts are stated once per member; only operand currency and readiness are indexed by an
already-constructed Sail prefix. -/
structure RowsGrounded {Row : Type u} (rowOf : Row → ChipRow p)
    (data : ProverData (ZMod p)) (program : GuestProgram)
    (initial : SailState) (rows : List Row) : Prop where
  static : ∀ row ∈ rows, StaticGroundedRow program (rowOf row)
  dynamic : ∀ done row suffix, rows = done ++ row :: suffix →
    ∀ state, SailChain done.length initial state → DynamicGroundedRow data program (rowOf row) state

/-- Recombine the static and position-dependent layers at one execution position. -/
theorem RowsGrounded.at {Row : Type u} {rowOf : Row → ChipRow p}
    {data : ProverData (ZMod p)} {program : GuestProgram}
    {initial : SailState} {rows : List Row}
    (grounded : RowsGrounded rowOf data program initial rows)
    (done : List Row) (row : Row) (suffix : List Row)
    (rowsEq : rows = done ++ row :: suffix) (state : SailState)
    (chain : SailChain done.length initial state) :
    GroundedRow data program (rowOf row) state := by
  refine { toStaticGroundedRow := grounded.static row ?_
           toDynamicGroundedRow := grounded.dynamic done row suffix rowsEq state chain }
  rw [rowsEq]
  simp

/-- Fire one grounded row through its registered `ChipKind.advance`. -/
theorem GroundedRow.advance {data : ProverData (ZMod p)} {program : GuestProgram}
    {row : ChipRow p} {state : SailState} (grounded : GroundedRow data program row state)
    (configured : SailConfigured state) (romLoaded : RomLoaded program state)
    (pc : state.regs.get? Register.PC = some (rcvPcOf (stateAccess row.view))) :
    ∃ next, SailStep state next ∧ RowEffect program row.view state next := by
  have migrated : row.kind.advance.isSome = true :=
    allChipKinds_migrated row.kind grounded.registered
  obtain ⟨advance, -⟩ := Option.isSome_iff_exists.mp migrated
  exact advance.down row.inputs row.cols data program state grounded.real grounded.spec
    configured romLoaded pc grounded.operands grounded.decoded grounded.ready

/-- Execute the unprocessed suffix of a pc walk, retaining the already-executed prefix only as an
index into `RowsGrounded`. -/
private theorem executePcWalkAux {Row : Type u}
    (rowOf : Row → ChipRow p)
    (data : ProverData (ZMod p)) (program : GuestProgram) (initial : SailState)
    (rows : List Row) (grounded : RowsGrounded rowOf data program initial rows)
    (codeMemoryCompatible : SailCodeMemoryCompatible program initial) :
    ∀ (done suffix : List Row) (current final : BitVec 64) (state : SailState),
      rows = done ++ suffix →
      PcWalk rowOf current final suffix →
      SailChain done.length initial state →
      state.regs.get? Register.PC = some current →
      RomLoaded program state → SailConfigured state →
      ∃ finalState,
        SailChain rows.length initial finalState ∧
        finalState.regs.get? Register.PC = some final := by
  intro done suffix
  induction suffix generalizing done with
  | nil =>
      intro current final state rows_eq walk chain pc _ _
      have current_eq : current = final := walk
      refine ⟨state, ?_, by simpa [current_eq] using pc⟩
      simpa [rows_eq] using chain
  | cons row suffix ih =>
      intro current final state rows_eq walk chain pc rom cfg
      obtain ⟨rowSource, tailWalk⟩ := walk
      have pcRow : state.regs.get? Register.PC =
          some (rcvPcOf (stateAccess (rowOf row).view)) := by
        rw [rowSource]
        exact pc
      have rowGrounded := grounded.at done row suffix rows_eq state chain
      obtain ⟨next, step, effect⟩ := rowGrounded.advance cfg rom pcRow
      have rows_eq' : rows = (done ++ [row]) ++ suffix := by
        simpa [List.append_assoc] using rows_eq
      have chain' : SailChain (done ++ [row]).length initial next := by
        simpa using chain.snoc step
      have nextRom : RomLoaded program next :=
        codeMemoryCompatible chain step rom
      exact ih (done ++ [row]) (sndPcOf (stateAccess (rowOf row).view)) final next rows_eq'
        tailWalk chain' effect.pc nextRom (effect.cfg cfg)

/-- A fully grounded, ordered row list constructs a genuine local official-Sail chain. -/
theorem sailChain_of_groundedRows {Row : Type u} (rowOf : Row → ChipRow p)
    (data : ProverData (ZMod p)) (program : GuestProgram) (initial : SailState)
    (rows : List Row) (initialPc finalPc : BitVec 64)
    (walk : PcWalk rowOf initialPc finalPc rows)
    (grounded : RowsGrounded rowOf data program initial rows)
    (codeMemoryCompatible : SailCodeMemoryCompatible program initial)
    (pc : initial.regs.get? Register.PC = some initialPc)
    (rom : RomLoaded program initial) (cfg : SailConfigured initial) :
    ∃ finalState,
      SailChain rows.length initial finalState ∧
      finalState.regs.get? Register.PC = some finalPc := by
  simpa using executePcWalkAux rowOf data program initial rows grounded codeMemoryCompatible
    [] rows initialPc finalPc initial (by simp) walk (.refl initial) pc rom cfg

/-- Package the grounded-row engine as the honest local execution relation.  Schedule/clock equality
is kept as a structural grounding premise because it comes from decoded State rows, not Sail steps. -/
theorem groundedRows_localExecution {Row : Type u}
    (model : Machine.SP1MachineModel)
    (statement : ProgramStatement (SupportedCorePrefixPublicValues (ZMod p)))
    (data : ProverData (ZMod p)) (initial : SailState)
    (rowOf : Row → ChipRow p) (rows : List Row)
    (wellFormed : statement.program.WellFormed)
    (pc : initial.regs.get? Register.PC = some
      (supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
        statement.publicValues.init_pc2))
    (rom : RomLoaded statement.program initial) (cfg : SailConfigured initial)
    (codeMemoryCompatible : SailCodeMemoryCompatible statement.program initial)
    (walk : PcWalk rowOf
      (supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
        statement.publicValues.init_pc2)
      (supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
        statement.publicValues.final_pc2) rows)
    (grounded : RowsGrounded rowOf data statement.program initial rows)
    (clockMatches : Machine.localExecutionClock
      ({ program := statement.program, wellFormed, initial, romLoaded := rom, configured := cfg } :
        Machine.LocalExecutionCtx model)
      (Semantics.clkNat statement.publicValues.init_clk_high statement.publicValues.init_clk_low)
      rows.length =
        Semantics.clkNat statement.publicValues.final_clk_high statement.publicValues.final_clk_low) :
    ∃ witness, SupportedCoreLocalExecutionRelation model statement witness := by
  obtain ⟨finalState, chain, finalPc⟩ :=
    sailChain_of_groundedRows rowOf data statement.program initial rows _ _ walk grounded
      codeMemoryCompatible pc rom cfg
  let context : Machine.LocalExecutionCtx model :=
    { program := statement.program, wellFormed, initial, romLoaded := rom, configured := cfg }
  let execution : Machine.LocalExecutionSegmentWitness context :=
    { steps := rows.length
      finalState := finalState
      reached := Semantics.chainState_of_sailChain chain }
  refine ⟨⟨context, execution⟩, wellFormed, rfl, pc, finalPc, ?_⟩
  exact clockMatches

end SP1Clean.Soundness
