import SP1Clean.Soundness.GroundingInternal

/-! # AIR witness relations and the semantic capstone

This module is the "read this one file" audit boundary: the public relations and the capstone
theorems, with the timed-grounding interior factored into
`Soundness/GroundingInternal.lean`:

* `SupportedCoreEnsembleRelation` is exactly the algebra checked by the 53-table Clean ensemble;
* `SP1SemanticBoundaryRelation` separately binds its preprocessed/provider rows to the committed
  program and a concrete local initial Sail state;
* `SupportedCoreNativeRelation` is their conjunction; and
* `SupportedCoreSailRelation` is the plain official-Sail target for that slice
  (`supported_core_native_sound`), with the model-scheduled and capacity-bounded shard forms as
  corollaries.

The names `supported_core_air_sound` and `sp1_air_sound` are reserved for extracted upstream AIR
relations.  They are not declared over the native ensemble because doing so would conflate a Clean
implementation with its Rust-faithfulness theorem. -/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Execution

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

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

/-- The honest native relation used by semantic soundness. Provider truth is an explicit companion
predicate, not an implication smuggled out of raw interaction balance.

There is deliberately **no** third conjunct. The physical range premise SP1's generic RAM
access-timestamp comparison needs — a genuine 24-bit high limb on every pulled Memory record — used
to travel here as `SupportedCoreMemoryTimestampRangeRelation`, because the per-chip aligned-carrier
contract demanded it before producing the touch lists that the capstone's per-location memory
balance is built from. Moving that demand into the per-touch antecedent of the contract's slot
conjunct broke the cycle: `supportedCore_orderedRows_dynamic_of_obligations` now *derives* both
timestamp facts for every pulled record from the produced side of the widened balance
(`pushGood`/`pullGood`), so the capstone's remaining premises are exactly the ensemble algebra and
the semantic boundary binding. -/
def SupportedCoreNativeRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  fun statement witness =>
    SupportedCoreEnsembleRelation statement witness ∧
      SP1SemanticBoundaryRelation statement witness

/-- The capacity-bounded native shard relation.

This is the ordinary native relation restricted in place; it does not introduce another native
witness or copy any constraint/boundary field.  It projects the physical active-row count into the
same `CoreProfile.WithinOrdinaryRowLimit` predicate used by the semantic relation. -/
def SupportedCoreNativeShardRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) (SupportedCoreNativeWitness p) :=
  SupportedCoreNativeRelation.restrict fun _ witness =>
    CoreProfile.WithinOrdinaryRowLimit
      (realDecodedInstructionRows witness.data witness.tables).length


/-- Export the complete semantic grounding certificate from the honest native relation.

Unlike the local-execution soundness projection below, this theorem retains the initial boundary
facts together with the grounding record's final-State and memory-finalize truths.  It is therefore
the reusable native endpoint for shard composition and for later exact-Core/ArkLib transport: callers
do not have to reopen the relation or reconstruct facts that the timed grounding walk already proved. -/
theorem supported_core_native_grounding
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (valid : SupportedCoreNativeRelation statement witness) :
    ∃ initial orderedRows, InitialBoundaryFacts statement witness initial ∧
      SupportedCoreGrounding statement witness initial orderedRows := by
  obtain ⟨⟨publicInputEq, constraints, balanced⟩, binding⟩ := valid
  obtain ⟨initial, boundary⟩ := binding.boundaryFacts
  obtain ⟨orderedRows, grounding⟩ :=
    supported_core_witness_grounding statement witness initial publicInputEq constraints balanced
      boundary
  exact ⟨initial, orderedRows, boundary, grounding⟩

/-- **Supported native-Clean soundness.** A satisfying, channel-balanced witness whose provider
tables are semantically bound produces a genuine shard-local official-Sail execution: a
normally-retiring interpreter run between the committed public pc endpoints, taking exactly the
committed number of eight-tick instructions.  Those two conjuncts are the *whole* premise: the
RAM access-timestamp range fact the generic underflow argument needs is derived inside the
capstone from the per-location Memory balance, not assumed here.  No machine-model parameter and
no schedule hypothesis appear; the model-scheduled form is
`supported_core_native_sound_scheduled` below.  This deliberately concludes a shard-local
segment; boot reachability is supplied later by `supportedCoreLocalExecution_anchors` when
consecutive shards are composed. -/
theorem supported_core_native_sound :
    WitnessRelation.Sound (SupportedCoreNativeRelation (p := p))
      (SupportedCoreSailRelation (p := p)) := by
  intro statement witness valid
  obtain ⟨initial, rows, boundary, grounding⟩ :=
    supported_core_native_grounding statement witness valid
  obtain ⟨memBoundary, memWF, memContent⟩ :=
    exists_populated_memoryBoundary witness initial
      (Semantics.StateMsg.timeNat (finalBoundaryStateMessage statement.publicValues))
      boundary.memoryFinalizeProviderUnique boundary.memoryProvider grounding.memoryFinalizeTruth
  have timeEq : Semantics.StateMsg.timeNat (finalBoundaryStateMessage statement.publicValues) =
      Commit.initClkNat witness.data + 8 * rows.length := by
    have h1 := grounding.clockCount
    have h2 := boundary.initialClock
    change Semantics.clkNat statement.publicValues.final_clk_high
      statement.publicValues.final_clk_low = _
    omega
  refine groundedRows_sailRelation statement witness.data initial
    (fun decoded : DecodedInstructionRow p => decoded.toChipRow witness.data) rows memBoundary
    boundary.programWellFormed boundary.initialPc boundary.romLoaded boundary.configured
    boundary.codeMemoryCompatible grounding.walk grounding.grounded grounding.clockCount
    memWF ?_
  intro final chainEq cell member
  obtain ⟨initContent, finalMicro⟩ := memContent cell member
  refine ⟨initContent, ?_⟩
  rw [timeEq] at finalMicro
  exact locContent_final_of_microValue chainEq finalMicro

/-- The model-scheduled corollary of `supported_core_native_sound`: any machine model
implementing SP1's ordinary eight-tick schedule recovers the local-execution-witness form.  This
is the composition seam consumed by `supportedCoreLocalExecution_anchors` when shards are
composed along a model-selected boot trajectory. -/
theorem supported_core_native_sound_scheduled (model : Machine.SP1MachineModel)
    (ordinary : model.UsesOrdinarySchedule) :
    WitnessRelation.Sound (SupportedCoreNativeRelation (p := p))
      (SupportedCoreLocalExecutionRelation model) := by
  intro statement witness valid
  obtain ⟨w, sailValid⟩ := supported_core_native_sound statement witness valid
  exact supportedCoreLocalExecution_of_sailRelation model ordinary sailValid

/-- Construct the common semantic witness while retaining its exact active-row count.

The witness stores the grounded initial state, the ordinary event transcript, and the **populated
Memory boundary**: one cell per canonically-addressed, genesis-backed committed finalize record,
agreeing with the selected initial state and the evaluated final state
(`exists_populated_memoryBoundary` + `locContent_final_of_microValue`).  Transition targets are
recovered by the shared evaluator, so native soundness does not publish a second trace-shaped
semantic relation. -/
theorem supported_core_native_shard_execution
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (valid : SupportedCoreNativeShardRelation statement witness) :
    ∃ semanticWitness : Machine.CoreShardSemanticWitness,
      SupportedCoreShardExecutionRelation statement semanticWitness ∧
        (semanticWitness.evaluatedTrace (supportedCoreShardModel (p := p))).steps =
          (realDecodedInstructionRows witness.data witness.tables).length := by
  obtain ⟨nativeValid, rowLimit⟩ := valid
  obtain ⟨⟨publicInputEq, constraints, balanced⟩, binding⟩ := nativeValid
  obtain ⟨initial, boundary⟩ := binding.boundaryFacts
  obtain ⟨rows, grounding⟩ :=
    supported_core_witness_grounding statement witness initial publicInputEq constraints balanced
      boundary
  obtain ⟨execution, initialEq, stepsEq, finalPc, executionValid, clocked, finalClock,
      ordinary, supported⟩ :=
    eventExecution_of_groundedRows Machine.ExecutableSyscallHandler.none.relation
      (fun decoded : DecodedInstructionRow p => decoded.toChipRow witness.data)
      witness.data statement.program initial rows
      (supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
        statement.publicValues.init_pc2)
      (supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
        statement.publicValues.final_pc2)
      grounding.walk grounding.grounded boundary.codeMemoryCompatible boundary.initialPc
      boundary.romLoaded boundary.configured
      (Semantics.clkNat statement.publicValues.init_clk_high
        statement.publicValues.init_clk_low)
  -- The populated Memory boundary: real per-location init/final content instead of `⟨[]⟩`.
  obtain ⟨memBoundary, memWF, memContent⟩ :=
    exists_populated_memoryBoundary witness initial
      (Semantics.StateMsg.timeNat (finalBoundaryStateMessage statement.publicValues))
      boundary.memoryFinalizeProviderUnique boundary.memoryProvider grounding.memoryFinalizeTruth
  let semanticWitness := Machine.CoreShardSemanticWitness.ofOrdinaryTrace
    statement.program memBoundary execution
  have publicValuesWellFormed : statement.publicValues.LimbBounds := by
    rw [← publicInputEq]
    exact witness_publicInput_limbBounds witness constraints balanced
  have evaluated := Machine.CoreShardSemanticWitness.trace?_ofOrdinaryTrace
    (supportedCoreShardModel (p := p)) statement.program memBoundary execution executionValid
    ordinary
  have timeEq : Semantics.StateMsg.timeNat (finalBoundaryStateMessage statement.publicValues) =
      Commit.initClkNat witness.data + 8 * execution.steps := by
    have h1 := grounding.clockCount
    have h2 := boundary.initialClock
    rw [stepsEq]
    change Semantics.clkNat statement.publicValues.final_clk_high
      statement.publicValues.final_clk_low = _
    omega
  have chain := Semantics.chainState_of_sailChain
    (execution.sailChain executionValid ordinary)
  rw [initialEq] at chain
  refine ⟨semanticWitness, {
    statementValid := publicValuesWellFormed
    programWellFormed := boundary.programWellFormed
    programBound := rfl
    programValid := boundary.programCommitted.encodable
    contractValid := trivial
    romLoaded := ?_
    configured := ?_
    codeMemoryCompatible := ?_
    memoryWellFormed := ?_
    memoryAgrees := ?_
    shardCase := ?_ }, ?_⟩
  · change Target.RomLoaded statement.program execution.initialState
    rw [initialEq]
    exact boundary.romLoaded
  · change Target.SailConfigured execution.initialState
    rw [initialEq]
    exact boundary.configured
  · change Target.SailCodeMemoryCompatible statement.program execution.initialState
    rw [initialEq]
    exact boundary.codeMemoryCompatible
  · -- memoryWellFormed: the populated boundary's hygiene at the committed final clock.
    change memBoundary.WellFormed (Semantics.clkNat statement.publicValues.final_clk_high
      statement.publicValues.final_clk_low)
    exact memWF
  · -- memoryAgrees: genesis content at the initial state, walk value-currency at the final state.
    intro cell member
    obtain ⟨initContent, finalMicro⟩ := memContent cell member
    refine ⟨?_, ?_⟩
    · change Semantics.locContent execution.initialState cell.loc = some cell.initialValue
      rw [initialEq]
      exact initContent
    · rw [Machine.CoreShardSemanticWitness.evaluatedTrace_eq_of_trace? evaluated]
      rw [timeEq] at finalMicro
      exact locContent_final_of_microValue chain finalMicro
  · refine .execution execution.events execution rfl rfl evaluated executionValid clocked
      (finalClock.trans grounding.clockCount) ?_ finalPc ?_
    · simpa only [initialEq, supportedCoreShardModel, supportedCoreShardBoundary] using
        boundary.initialPc
    · refine ⟨ordinary, supported, ?_⟩
      rw [stepsEq, grounding.exhaustive.length_eq]
      exact rowLimit
  · rw [Machine.CoreShardSemanticWitness.evaluatedTrace_eq_of_trace? evaluated]
    exact stepsEq.trans grounding.exhaustive.length_eq

/-- **Capacity-aligned native soundness into the one canonical shard relation.**

The intermediate `EventExecutionTrace` is immediately embedded by its initial state and event
transcript; its target states are then recovered by the shared evaluator.  The canonical witness's
Memory boundary is populated from the committed finalize records — real initial/final content per
canonically-addressed, genesis-backed location; exact Core fills the same field from the paired
six-table cluster. -/
theorem supported_core_native_shard_sound :
    WitnessRelation.Sound (SupportedCoreNativeShardRelation (p := p))
      (SupportedCoreShardExecutionRelation (p := p)) := by
  intro statement witness valid
  obtain ⟨semanticWitness, semantic, -⟩ :=
    supported_core_native_shard_execution statement witness valid
  exact ⟨semanticWitness, semantic⟩

/-! ## Completeness boundary

Whole-machine completeness is intentionally not inferred from the `completeness` field embedded in
each `GeneralFormalCircuit`. `Soundness/AIRCompleteness.lean` proves
`supported_core_generated_trace_complete` for `SupportedCoreGeneratedTraceRelation`: a canonical
trace record whose per-table routing facts, canonical nonnegative provider-count encodings, four
exact centered-integer channel balances, public equality, and semantic boundary binding are
supplied. It constructs every physical table row with the circuits' own witness generators. This is
generator-relative AIR assembly completeness, not yet the stronger theorem that every supported
Sail execution produces such a trace; the latter still requires a verified Sail-execution-to-trace
generator. Using the broader `SupportedCoreLocalExecutionRelation` directly would be false for
unsupported Sail executions. -/

/-! ## Full extracted target

`Soundness/CoreAIR.lean` owns the conditional
`sp1_air_refinement_of_obligations`/`sp1_air_sound_of_obligations` combinators.  Their source is the
concrete paired 34+6-table Rust relation in `Faithful/CoreAIR.lean`, not this smaller native ensemble.
The required field-by-field proof bundle is not yet instantiated, so the unqualified
`sp1_air_refinement`/`sp1_air_sound` names remain reserved for that closed result.  Its COMMIT
conclusion is deliberately limited to correctness of rows that exist.  The base composed execution
relation preserves that distinction; complete eight-row coverage appears only in the optional
`SP1CommitCoveredExecutionRelation`, derived from the explicit program contract
`UsesStandardHaltWrapper`.  This file continues to own only the 25-chip proof-oriented Clean slice. -/

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
