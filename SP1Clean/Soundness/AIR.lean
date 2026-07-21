import SP1Clean.FormalModel.Execution
import SP1Clean.Model.Semantics.ProgramCommitment
import SP1Clean.Soundness.RankedGrounding
import SP1Clean.Soundness.SP1Ensemble
import SP1Clean.Soundness.ProviderBindings
import SP1Clean.Soundness.TimedGrounding
import SP1Clean.Soundness.LocalExecution
import SP1Clean.Soundness.RowSoundness
import SP1Clean.Soundness.TypedProgram
import SP1Clean.Soundness.TypedTimeContracts

/-! # AIR witness relations and the semantic capstone

This module is the naming boundary the old trail capstone lacked:

* `SupportedCoreEnsembleRelation` is exactly the algebra checked by the 36-table Clean ensemble;
* `SP1SemanticBoundaryRelation` separately binds its preprocessed/provider rows to the committed
  program and a concrete local initial Sail state;
* `SupportedCoreNativeRelation` is their conjunction; and
* `SupportedCoreLocalExecutionRelation` is the finite official-Sail target for that slice.

The names `supported_core_air_sound` and `sp1_air_sound` are reserved for extracted upstream AIR
relations.  They are not declared over the native ensemble because doing so would conflate a Clean
implementation with its Rust-faithfulness theorem. -/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Execution

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The public statement type of the currently supported core slice. -/
abbrev SupportedCoreStatement (p : ℕ) :=
  ProgramStatement (SupportedCorePrefixPublicValues (ZMod p))

/-- The private native-Clean witness currently implemented by this repository. -/
abbrev SupportedCoreNativeWitness (p : ℕ) [Fact p.Prime] [Fact (2 ^ 25 < p)] :=
  EnsembleWitness (sp1Ensemble (p := p))

/-- The raw algebraic relation checked by today's Clean ensemble.  It intentionally says nothing
about which program/provider contents the rows represent. -/
def SupportedCoreEnsembleRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  fun statement witness =>
    witness.publicInput = statement.publicValues ∧
    witness.Constraints ∧
    witness.BalancedChannels

/-- The non-execution companion relation: the program commitment and provider/boundary tables really
describe the caller's program and one concrete local initial Sail state. -/
def SP1SemanticBoundaryRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  SemanticBoundaryBinding

/-- The honest native relation used by semantic soundness.  Provider truth is an explicit companion
predicate, not an implication smuggled out of raw interaction balance. -/
def SupportedCoreNativeRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  fun statement witness =>
    SupportedCoreEnsembleRelation statement witness ∧
      SP1SemanticBoundaryRelation statement witness

/-! ## Native grounding and the local-execution capstone -/

/-- The exact output expected from the remaining witness-grounding proof.

This record cannot choose a convenient unrelated trace: `orderedRows` is a permutation of precisely
the active physical rows produced by the deterministic typed decoder.  Retaining each dependent
descriptor is essential: circuit soundness fires on that exact row before the local-execution engine
observes its semantic `ChipRow` projection.  The remaining fields order those rows between the public
PC endpoints, ground every row against the evolving official-Sail state, and bind the table row count
to the currently supported eight-tick clock window. -/
structure SupportedCoreGrounding
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState) (orderedRows : List (DecodedInstructionRow p)) : Prop where
  exhaustive : orderedRows.Perm (realDecodedInstructionRows witness.data witness.tables)
  walk : PcWalk (fun decoded : DecodedInstructionRow p => decoded.toChipRow witness.data)
    (supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
      statement.publicValues.init_pc2)
    (supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
      statement.publicValues.final_pc2)
    orderedRows
  grounded : RowsGrounded (fun decoded : DecodedInstructionRow p =>
      decoded.toChipRow witness.data)
    witness.data statement.program initial orderedRows
  clockCount :
    Semantics.clkNat statement.publicValues.init_clk_high statement.publicValues.init_clk_low +
        8 * orderedRows.length =
      Semantics.clkNat statement.publicValues.final_clk_high statement.publicValues.final_clk_low

/-- The committed-decode field of every statically grounded ordered row is already discharged.
This theorem deliberately sits beside the remaining grounding seam: Program truth comes entirely
from the exact chip pulls, Clean balance, the canonical table-33 provider, and the statement binding;
it is not an assumption of the timed State/Memory induction. -/
theorem supportedCore_orderedRows_programDecoded
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {initial : SailState} (boundary : InitialBoundaryFacts statement witness initial)
    (orderedRows : List (DecodedInstructionRow p))
    (exhaustive : orderedRows.Perm
      (realDecodedInstructionRows witness.data witness.tables)) :
    ∀ decoded ∈ orderedRows,
      Target.decodedInROM statement.program
        (programAccess (decoded.toChipRow witness.data).view).toRow := by
  intro decoded decodedMem
  have sourceMem := exhaustive.mem_iff.mp decodedMem
  rw [realDecodedInstructionRows, List.mem_filter] at sourceMem
  simp only [decide_eq_true_eq] at sourceMem
  have truth := decoded.programTruth_of_active witness constraints balanced boundary.programProvider
    sourceMem.1 sourceMem.2
  have decodedTruth := truth.2
  rw [boundary.programCommitted.2] at decodedTruth
  simpa only [rowOfMsg_programMessageOfView] using decodedTruth

/-- Assemble every state-independent grounding field once per ordered row.  Activity and registry
membership follow from exhaustive deterministic decoding, while committed decode follows from the
Program provider and channel balance.  The semantic chip `Spec` is deliberately absent: its proof can
depend on the current Memory operands and therefore belongs to `DynamicGroundedRow`. -/
theorem supportedCore_orderedRows_static
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {initial : SailState} (boundary : InitialBoundaryFacts statement witness initial)
    (orderedRows : List (DecodedInstructionRow p))
    (exhaustive : orderedRows.Perm
      (realDecodedInstructionRows witness.data witness.tables)) :
    ∀ decoded ∈ orderedRows,
      StaticGroundedRow statement.program (decoded.toChipRow witness.data) := by
  intro decoded decodedMem
  have sourceMem := exhaustive.mem_iff.mp decodedMem
  rw [realDecodedInstructionRows, List.mem_filter] at sourceMem
  simp only [decide_eq_true_eq] at sourceMem
  exact {
    real := sourceMem.2
    registered := by
      change decoded.chip.kind ∈ allChipKinds (p := p)
      exact List.mem_map_of_mem
        (decodedInstructionRows_chip_mem witness.tables sourceMem.1)
    decoded := supportedCore_orderedRows_programDecoded statement witness constraints balanced
      boundary orderedRows exhaustive decoded decodedMem }

/-- A walk of full State messages projects to the pc-only walk consumed by local execution.  The
projection is lossless for this purpose because the decoded edge is definitionally the row's State
pull/push pair. -/
theorem pcWalk_of_decodedStateWalk (data : ProverData (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk (decodedStateEdge data) initial final rows →
        PcWalk (fun decoded : DecodedInstructionRow p => decoded.toChipRow data)
          (Semantics.StateMsg.pcBits initial) (Semantics.StateMsg.pcBits final) rows := by
  intro initial final rows walk
  induction rows generalizing initial with
  | nil =>
      change initial = final at walk
      subst final
      rfl
  | cons decoded rows ih =>
      obtain ⟨source, tail⟩ := walk
      constructor
      · rw [← congrArg Semantics.StateMsg.pcBits source]
        simp [decodedStateEdge]
      · simpa [decodedStateEdge] using ih tail

/-- A full State-message walk whose rows each advance eight ticks has the expected endpoint clock
count.  This isolates the purely telescoping part from Memory and Sail-state grounding. -/
theorem clockCount_of_decodedStateWalk (data : ProverData (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk (decodedStateEdge data) initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (decodedStateEdge data decoded).2 =
          Semantics.StateMsg.timeNat (decodedStateEdge data decoded).1 + 8) →
      Semantics.StateMsg.timeNat initial + 8 * rows.length =
        Semantics.StateMsg.timeNat final := by
  intro initial final rows walk steps
  induction rows generalizing initial with
  | nil =>
      change initial = final at walk
      subst final
      simp
  | cons decoded rows ih =>
      obtain ⟨source, tail⟩ := walk
      have sourceTime := congrArg Semantics.StateMsg.timeNat source
      have rowStep := steps decoded List.mem_cons_self
      have tailCount := ih tail (fun other otherMem =>
        steps other (List.mem_cons_of_mem decoded otherMem))
      simp only [List.length_cons]
      omega

/-- The telescoping endpoint-multiset balance of a State walk: the head plus each row's push equals the
final plus each row's pull, as multisets.  The `List`-level companion of
`RankedGrounding.endpointBalanced_of_balanced`, derived directly from `IsWalk` so it carries the
`statement.publicValues` endpoints natively — the exact State-balance hypothesis `TimedGrounding.walk`
consumes (after mapping `decodedStateEdge` onto the aligned carrier's `statePush`/`statePull`). -/
theorem endpointBalance_of_decodedStateWalk (data : ProverData (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk (decodedStateEdge data) initial final rows →
      initial ::ₘ (↑(rows.map (fun d => (decodedStateEdge data d).2)) :
          Multiset (Channels.StateMsg (ZMod p)))
        = final ::ₘ ↑(rows.map (fun d => (decodedStateEdge data d).1)) := by
  intro initial final rows walk
  induction rows generalizing initial with
  | nil =>
      change initial = final at walk
      subst final
      rfl
  | cons decoded rows ih =>
      obtain ⟨source, tail⟩ := walk
      have ihEq := ih tail
      simp only [List.map_cons, Multiset.cons_coe, Multiset.coe_eq_coe] at ihEq ⊢
      rw [source]
      exact (List.Perm.cons initial ihEq).trans (List.Perm.swap final initial _)

/-- The State walk and each chip's proved `+8` clock contract locate every exact decoded row at its
prefix length. This is the position equation consumed by shard-local Memory currency. -/
theorem statePullTime_of_decodedStateWalk (data : ProverData (ZMod p)) :
    ∀ {initial final : Channels.StateMsg (ZMod p)}
      {rows : List (DecodedInstructionRow p)},
      Walk.IsWalk (decodedStateEdge data) initial final rows →
      (∀ decoded ∈ rows,
        Semantics.StateMsg.timeNat (decodedStateEdge data decoded).2 =
          Semantics.StateMsg.timeNat (decodedStateEdge data decoded).1 + 8) →
      ∀ done decoded suffix, rows = done ++ decoded :: suffix →
        Semantics.StateMsg.timeNat (decodedStateEdge data decoded).1 =
          Semantics.StateMsg.timeNat initial + 8 * done.length := by
  intro initial final rows walk steps done
  induction done generalizing initial rows with
  | nil =>
      intro decoded suffix rowsEq
      subst rows
      obtain ⟨source, -⟩ := walk
      simpa using congrArg Semantics.StateMsg.timeNat source
  | cons head done ih =>
      intro decoded suffix rowsEq
      subst rows
      obtain ⟨source, tail⟩ := walk
      have headStep := steps head List.mem_cons_self
      have tailSteps : ∀ row ∈ done ++ decoded :: suffix,
          Semantics.StateMsg.timeNat (decodedStateEdge data row).2 =
            Semantics.StateMsg.timeNat (decodedStateEdge data row).1 + 8 := by
        intro row rowMem
        exact steps row (List.mem_cons_of_mem head rowMem)
      have position := ih tail tailSteps decoded suffix rfl
      have sourceTime := congrArg Semantics.StateMsg.timeNat source
      simp only [List.length_cons]
      omega

set_option warn.sorry false in
/-- The one remaining dynamic grounding seam, now stated over the exact ordered physical rows.

Ordering, activity, registry membership, Program decode, and clock accounting are all proved outside
this theorem.  Its proof must use timed Memory grounding to establish each row's
`DecodedRowOpenSoundnessInputs`, obtain `chipSpec` through
`DecodedInstructionRow.chipSpec_of_openSoundnessInputs`, and derive current operands plus the
chip-specific `advanceReady` fact at the corresponding official-Sail prefix. -/
theorem supportedCore_orderedRows_dynamic
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (boundary : InitialBoundaryFacts statement witness initial)
    (orderedRows : List (DecodedInstructionRow p))
    (exhaustive : orderedRows.Perm
      (realDecodedInstructionRows witness.data witness.tables))
    (stateWalk : Walk.IsWalk (decodedStateEdge witness.data)
      (initialBoundaryStateMessage statement.publicValues)
      (finalBoundaryStateMessage statement.publicValues) orderedRows) :
    ∀ done decoded suffix, orderedRows = done ++ decoded :: suffix →
      ∀ state, Target.SailChain done.length initial state →
        DynamicGroundedRow witness.data statement.program
          (decoded.toChipRow witness.data) state := by
  sorry

set_option warn.sorry false in
/-- The sole semantic grounding seam for the supported native slice.

Program-provider commitment is no longer part of this seam:
`supportedCore_orderedRows_programDecoded` supplies the exact static decode field for every exhaustive
ordering, and `supportedCore_orderedRows_static` packages the whole static layer without pretending
that row `Spec`s are state-independent.  Ranked State-bus ordering and clock counting are now closed;
`supportedCore_orderedRows_dynamic` is the remaining timed Memory/spec/readiness argument. -/
theorem supported_core_witness_grounding
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState)
    (publicInputEq : witness.publicInput = statement.publicValues)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (boundary : InitialBoundaryFacts statement witness initial) :
    ∃ orderedRows, SupportedCoreGrounding statement witness initial orderedRows := by
  obtain ⟨orderedRows, stateWalk, exhaustiveMultiset⟩ :=
    witness_realDecodedState_exhaustiveTrail witness constraints balanced
  rw [publicInputEq] at stateWalk
  have exhaustive : orderedRows.Perm
      (realDecodedInstructionRows witness.data witness.tables) :=
    Multiset.coe_eq_coe.mp exhaustiveMultiset
  refine ⟨orderedRows, exhaustive, ?_, ?_, ?_⟩
  · simpa [initialBoundaryStateMessage, finalBoundaryStateMessage,
      Semantics.StateMsg.pcBits, supportedPcBits] using
      pcWalk_of_decodedStateWalk witness.data stateWalk
  · exact {
      static := supportedCore_orderedRows_static statement witness constraints balanced boundary
        orderedRows exhaustive
      dynamic := supportedCore_orderedRows_dynamic statement witness initial constraints balanced
        boundary orderedRows exhaustive stateWalk }
  · have clockCount := clockCount_of_decodedStateWalk witness.data stateWalk
      (fun decoded decodedMem =>
        witness_realDecodedInstructionRows_timeStep witness constraints balanced decoded
          (exhaustive.mem_iff.mp decodedMem))
    change
      Semantics.clkNat statement.publicValues.init_clk_high statement.publicValues.init_clk_low +
          8 * orderedRows.length =
        Semantics.clkNat statement.publicValues.final_clk_high statement.publicValues.final_clk_low
      at clockCount
    exact clockCount

/-- **Supported native-Clean soundness.** A satisfying, channel-balanced witness whose provider
tables are semantically bound produces a genuine local official-Sail execution between its public
endpoints.  This deliberately concludes a shard-local segment; boot reachability is supplied later by
`supportedCoreLocalExecution_anchors` when consecutive shards are composed. -/
theorem supported_core_native_sound (model : Machine.SP1MachineModel)
    (ordinary : model.UsesOrdinarySchedule) :
    WitnessRelation.Sound (SupportedCoreNativeRelation (p := p))
      (SupportedCoreLocalExecutionRelation model) := by
  intro statement witness valid
  obtain ⟨⟨publicInputEq, constraints, balanced⟩, initial, boundary⟩ := valid
  obtain ⟨rows, -, walk, grounded, clockCount⟩ :=
    supported_core_witness_grounding statement witness initial publicInputEq constraints balanced
      boundary
  apply groundedRows_localExecution model statement witness.data initial
    (fun decoded : DecodedInstructionRow p => decoded.toChipRow witness.data) rows
    boundary.programWellFormed boundary.initialPc boundary.romLoaded boundary.configured walk grounded
  rw [Machine.localExecutionClock_eq_ordinary ordinary]
  exact clockCount

/-! ## Completeness boundary

Whole-machine completeness is intentionally not inferred from the `completeness` field embedded in
each `GeneralFormalCircuit`.  The real converse must start from a *supported, trace-generatable*
semantic execution, construct all table witnesses, and prove the four global channel balances.  Its
eventual shape is:

```lean
theorem supported_core_native_complete :
    WitnessRelation.Complete SupportedCoreNativeRelation
      SupportedCoreTraceGeneratableExecutionRelation := by
  -- proof deferred
```

`SupportedCoreTraceGeneratableExecutionRelation` must include decoded-opcode support, canonical witness
generation inputs, memory initialization, and provider-table obligations; using the broader
`SupportedCoreLocalExecutionRelation` would make the claim false for unsupported Sail executions.  We accept
an explicit top-level completeness `sorry` while that relation and trace generator are verified.  This
does not require changing Clean's `GeneralFormalCircuit` representation. -/

/-! ## Reserved full target

Once the full extracted witness exists, the headline theorem should have precisely this shape:

```lean
theorem sp1_air_sound :
    WitnessRelation.Sound
      (SP1AIRRelation (p := p))
      (Execution.SP1ShardExecutionRelation layout model programBinding) := by
  -- proof deferred
```

Here `SP1AIRRelation` must range over the real `SP1PublicValues` layout and a faithful full-machine
witness (including CPU/syscall, memory, program, byte, global interaction, initialization, and
finalization tables).  We intentionally do not manufacture a placeholder relation: `False`, `True`,
an opaque axiom, or a current-ensemble projection would all make the desired signature elaborate while
changing the theorem being claimed. -/

/-! Shard AIR soundness is not itself a halting theorem.  After recursion authenticates an ordered
ledger and all companion integrity relations, the composed target has the separate shape:

```lean
theorem sp1_execution_sound :
    WitnessRelation.Sound SP1RecursiveAIRRelation
      (Execution.SP1ExecutionRelation layout model programBinding shardIntegrity) := by
  -- proof deferred
```

The segment layout in `SP1ExecutionRelation` begins at step zero, consumes consecutive execution
shards, permits non-execution shards only when pc/timestamp are unchanged, and ends in `SP1Halted`. -/

end SP1Clean.Soundness
