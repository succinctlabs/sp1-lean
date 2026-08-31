import SP1Clean.Proofs.Completeness.ExecutionCompiler
import SP1Clean.Proofs.Completeness.MemoryHistory
import SP1Clean.Proofs.Completeness.StateHistory
import SP1Clean.Proofs.Completeness.CanonicalClosureWellFormed
import SP1Clean.Proofs.Completeness.ConsumerClosure
import SP1Clean.Proofs.Completeness.Footprint
import SP1Clean.Soundness.AIR

/-!
# Deterministic native ensemble trace compiler

This is the low-level functional seam between the common shard witness's evaluated
`Machine.EventExecutionTrace` and the ordinary 53-table Clean ensemble. The compiler has no proof
argument and makes no row choices:

* `Execution.compileExecution` selects the chronological instruction events and Memory refreshes;
* `CompiledExecution.memoryHistory` determines one Memory-init/final row per touched location;
* `stateBumpEvents` determines the State refresh table;
* `SupportedCoreTraceWitness.canonicalClosure` recounts Byte, Range, and Program demand from the
  literal Clean consumer ledger; and
* the statement's public boundary is stored directly, without a second endpoint encoding.

`Soundness.NativeTraceReady` is deliberately an audit bundle over that one result.  It names the
remaining compiler-to-built-row representation facts and the two field-free chronologies.  It
does not contain channel balance, table constraints, or an existential AIR witness: those are
derived below.
-/

namespace SP1Clean.TraceGen

open SP1Clean.LookupAccessList

namespace MemoryHistoryAccess

/-- The two active Memory accesses represented by one chronological history transition. -/
def ledger {p : ℕ} [NeZero p] (access : MemoryHistoryAccess) : LookupAccessList :=
  linkAccesses (access.pulledKey (p := p)) (access.pushedKey (p := p))

end MemoryHistoryAccess

namespace CompiledExecution

/-- The chronological dependent instruction stream retained by the global compiler. -/
def routedEvents (compiled : CompiledExecution) : List RoutedEvent :=
  compiled.rows.map fun row => row.instruction.routed

/-- The single chronological Memory-record stream.  Each scheduled role expands its optional
refresh before the instruction access which consumes it. -/
def memoryHistory (compiled : CompiledExecution) : List MemoryHistoryAccess :=
  compiled.rows.flatMap fun row =>
    MemoryHistoryAccess.ofAccessSchedule row.clock row.instruction.schedule

/-- Instruction-owned history transitions, still in chronological row/role order. -/
def instructionMemoryHistory (compiled : CompiledExecution) : List MemoryHistoryAccess :=
  compiled.rows.flatMap fun row =>
    row.instruction.stamped.map (MemoryHistoryAccess.ofStamped row.clock)

/-- Refresh-owned history transitions, in chronological row/role order. -/
def bumpMemoryHistory (compiled : CompiledExecution) : List MemoryHistoryAccess :=
  compiled.memoryBumps.map MemoryHistoryAccess.ofMemoryBump

@[simp] theorem instructionEvents_eq_ofChronological (compiled : CompiledExecution) :
    compiled.instructionEvents = EventBuckets.ofChronological compiled.routedEvents := rfl

@[simp] theorem memoryHistory_nil :
    (emptyCompiledExecution 0).memoryHistory = [] := rfl

end CompiledExecution

end SP1Clean.TraceGen

namespace SP1Clean.Soundness

open Sail LeanRV64D LeanRV64D.Defs LeanRV64D.Functions
open SP1Clean.Execution
open SP1Clean.LookupAccessList
open SP1Clean.Soundness.Target
open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance nativeTraceCompilerFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-! ## The proof-independent trace map -/

/-- Decode the public initial clock once, at the same boundary used by execution semantics and
the committed prover-data encoder. -/
def nativeInitialClock (statement : SupportedCoreStatement p) : ℕ :=
  SP1Clean.Semantics.clkNat statement.publicValues.init_clk_high
    statement.publicValues.init_clk_low

/-- Decode the public final clock. -/
def nativeFinalClock (statement : SupportedCoreStatement p) : ℕ :=
  SP1Clean.Semantics.clkNat statement.publicValues.final_clk_high
    statement.publicValues.final_clk_low

/-- Decode the public initial program counter into the field-free State-history representation. -/
def nativeInitialPc (statement : SupportedCoreStatement p) : ℕ :=
  (supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
    statement.publicValues.init_pc2).toNat

/-- Decode the public final program counter. -/
def nativeFinalPc (statement : SupportedCoreStatement p) : ℕ :=
  (supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
    statement.publicValues.final_pc2).toNat

/-- The canonical field-free endpoints used by the State hand-off proof. -/
def nativeStateBoundary (statement : SupportedCoreStatement p) : StateBoundary :=
  StateBoundary.canonical (nativeInitialClock statement) (nativeInitialPc statement)
    (nativeFinalClock statement) (nativeFinalPc statement)

/-- Provider/boundary occurrences determined before preprocessed closure. -/
def nativeBaseProviderOccurrences (compiled : CompiledExecution) :
    (id : ProviderTableId) → List id.Occurrence
  | .byte _ => []
  | .range _ => []
  | .program => []
  | .memoryInit => memoryInitialEntries compiled.memoryHistory
  | .memoryFinalize => memoryFinalEntries compiled.memoryHistory
  | .memoryBump => compiled.memoryBumps
  | .stateBump => stateBumpEvents compiled.routedEvents
  | .halt => []

/-- Assemble the unique unclosed native trace from one chronological compiler result.  The three
preprocessed provider families are empty here; `canonicalClosure` below reconstructs them from
this trace's own evaluated consumer interactions. -/
noncomputable def nativeBaseTraceOfCompiled (statement : SupportedCoreStatement p)
    (compiled : CompiledExecution) : SupportedCoreTraceWitness p where
  instructionEvents := compiled.instructionEvents
  providerOccurrences := nativeBaseProviderOccurrences compiled
  data := Commit.dataOfAt statement.program (nativeInitialClock statement)
  hint := ProverHint.empty (ZMod p)
  boundary := statement.publicValues

/-- Total base trace.  Outside the supported compiler image this uses `compileExecution`'s empty
fallback; admissibility proves that branch unreachable. -/
noncomputable def nativeBaseTrace (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace) : SupportedCoreTraceWitness p :=
  nativeBaseTraceOfCompiled statement
    (TraceGen.compileExecution statement.program execution (nativeInitialClock statement))

/-- The one final native trace: deterministic semantic compilation followed by deterministic
provider recounting. -/
noncomputable def nativeTrace (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace) : SupportedCoreTraceWitness p :=
  (nativeBaseTrace statement execution).canonicalClosure

/-- The sole remaining representation seam for State compilation: physical instruction rows,
decoded in chip-table order, project to the field-free links of the same bucketed events.  Bump
rows, public endpoints, closure transport, and chronological permutation are all derived. -/
noncomputable def NativeStateRowProjection (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace) : Prop :=
  stateInstrLinks (nativeBaseTrace statement execution) =
    physicalInstructionStateLinks (p := p)
      (TraceGen.compileExecution statement.program execution
        (nativeInitialClock statement)).routedEvents

/-- The physical instruction-table part of the native Memory ledger. -/
noncomputable def physicalInstructionMemoryLedger
    (trace : SupportedCoreTraceWitness p) : LookupAccessList :=
  (decodedInstructionRows (p := p) trace.witness.tables).flatMap fun decoded =>
    (decoded.interactionsWith trace.witness.data Channels.memoryChannel).map fun interaction =>
      Interaction.toAccess interaction.raw

/-- The physical MemoryBump-table part of the native Memory ledger. -/
noncomputable def physicalMemoryBumpLedger
    (trace : SupportedCoreTraceWitness p) : LookupAccessList :=
  (typedTableInteractionsWith (memoryBumpTable trace.witness) Channels.memoryChannel).map
    fun interaction => Interaction.toAccess interaction.raw

/-- The residual representation seam for native Memory generation: active instruction and refresh
rows project to the two chronological streams retained by the compiler.  Boundary tables and
per-location regrouping are derived downstream. -/
structure NativeMemoryRowProjection (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace) : Prop where
  instruction : (active (physicalInstructionMemoryLedger
      (nativeTrace statement execution))).Perm
    ((TraceGen.compileExecution statement.program execution
      (nativeInitialClock statement)).instructionMemoryHistory.flatMap
        (MemoryHistoryAccess.ledger (p := p)))
  bumps : (active (physicalMemoryBumpLedger
      (nativeTrace statement execution))).Perm
    ((TraceGen.compileExecution statement.program execution
      (nativeInitialClock statement)).bumpMemoryHistory.flatMap
        (MemoryHistoryAccess.ledger (p := p)))

/-- Field-free semantic genesis of the canonical Memory history.

Each touched location's first pulled word is the selected initial Sail content.  The boundary
table's typed messages are deliberately absent: their exact projection from these histories is a
compiler theorem in `NativeMemoryAgreement`; the canonical init clock is definitionally zero. -/
def NativeMemoryGenesis (initial : SailState) (stream : List MemoryHistoryAccess) : Prop :=
  ∀ history ∈ memoryLocationHistories stream,
    SP1Clean.Semantics.locContent initial history.loc = some history.first.pulled

/-- Exact representation agreement still owed by the deterministic Program-row compiler.

For every literal Program key selected from the generated consumer ledger, one retained compiler
row names the same source PC and guarded Program-row projection.  The successful decode equation is
kept in this contract because it is the compiler's proof-independent computation, not a semantic
AIR fact.  No provider row, multiplicity, or second instruction list appears here. -/
def NativeProgramRowProjection (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace) : Prop :=
  ∀ key ∈ (nativeBaseTrace statement execution).closingKeyList,
    key.1 = InteractionKind.Program →
      ∃ compiledRow ∈
          (TraceGen.compileExecution statement.program execution
            (nativeInitialClock statement)).rows,
        ∃ row : ProgramChip.ProgramRow (ZMod p),
          SP1Clean.Semantics.projectSP1Transition? statement.program compiledRow.located =
              some compiledRow.view ∧
            compiledRow.located.source.regs.get? Register.PC =
              some (pcBitsOfRow row) ∧
            instrToProgramRow' (rowPcVec row) compiledRow.view.decoded = some row ∧
            key = ProgramChip.programRowKey row

@[simp] theorem nativeBaseTraceOfCompiled_publicValues
    (statement : SupportedCoreStatement p) (compiled : CompiledExecution) :
    (nativeBaseTraceOfCompiled statement compiled).publicValues = statement.publicValues := rfl

@[simp] theorem nativeBaseTrace_publicValues
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace) :
    (nativeBaseTrace statement execution).publicValues = statement.publicValues := rfl

@[simp] theorem nativeTrace_publicValues
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace) :
    (nativeTrace statement execution).publicValues = statement.publicValues := rfl

@[simp] theorem nativeTrace_witness_publicInput
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace) :
    (nativeTrace statement execution).witness.publicInput = statement.publicValues := rfl

/-! ## Local trace well-formedness -/

/-- The base trace's table-local side conditions are exactly the compiler's indexed event facts,
the two refresh schedulers' facts, and the public limb bounds.  Boundary inventories are valid by
construction. -/
theorem nativeBaseTraceOfCompiled_wellFormed
    (statement : SupportedCoreStatement p) (compiled : CompiledExecution)
    (publicWellFormed : statement.publicValues.LimbBounds)
    (compiledWellFormed : compiled.WellFormed)
    (stateBumpsReady : StateBumpReady compiled.routedEvents) :
    (nativeBaseTraceOfCompiled statement compiled).WellFormed := by
  constructor
  · intro id event member
    exact compiledWellFormed.instruction id event member
  · intro id event member
    cases id with
    | byte provider => cases provider <;> simp [nativeBaseTraceOfCompiled,
        nativeBaseProviderOccurrences] at member
    | range width => simp [nativeBaseTraceOfCompiled, nativeBaseProviderOccurrences] at member
    | program => simp [nativeBaseTraceOfCompiled, nativeBaseProviderOccurrences] at member
    | memoryInit =>
        exact memoryInitialEntries_wellFormed compiled.memoryHistory event member
    | memoryFinalize => trivial
    | memoryBump => exact compiledWellFormed.memoryBumps event member
    | stateBump => exact stateBumpEvents_wellFormed stateBumpsReady event member
    | halt => exact event.elim
  · exact publicWellFormed

/-! ## Explicit readiness of the one compiled trace -/

/-- Concrete residual obligations of deterministic native trace generation.

Every field refers to a named value computed above.  The State and Memory agreement fields are
representation bridges from circuit-built rows to that value; the chronology fields are
field-free semantic invariants.  Byte polarity and provider servability are local facts about the
literal Clean skeleton.  Program and Memory semantic-boundary facts are derived in the agreement
layer rather than stored here. -/
structure NativeTraceReady (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace) : Prop where
  /-- The compiler's syscall-free domain restriction: the deterministic instruction-event
  compiler emits only ordinary rows, so halting shards (whose terminal transition is the
  canonical HALT syscall) are outside this readiness bundle by construction.  Extending the
  compiler with the terminal halt row lifts this field. -/
  syscallFree : execution.AllOrdinary
  /-- The Exit hand-off's ordinary-shard consequence: with no active halt row the state-boundary
  verifier's ungated `⟨exit_code⟩` pull can only balance against the padding row's zero code.
  Native soundness *derives* this from the same balance
  (`Soundness/ExitAccounting.lean`); the compiler direction consumes it. -/
  exitZero : statement.publicValues.exit_code = 0
  compiler : NativeCompilerReady statement.program execution (nativeInitialClock statement)
  stateBumps : StateBumpReady
    (TraceGen.compileExecution statement.program execution
      (nativeInitialClock statement)).routedEvents
  stateChronology : StateChronology (nativeStateBoundary statement).initial
    (TraceGen.compileExecution statement.program execution
      (nativeInitialClock statement)).routedEvents
    (nativeStateBoundary statement).final
  stateProjection : NativeStateRowProjection statement execution
  memoryAddresses : MemoryAddressesCanonical
    (TraceGen.compileExecution statement.program execution
      (nativeInitialClock statement)).memoryHistory
  memoryChronology : MemoryRecordChronology
    (TraceGen.compileExecution statement.program execution
      (nativeInitialClock statement)).memoryHistory
  memoryProjection : NativeMemoryRowProjection statement execution
  byteConsumers : (nativeBaseTrace statement execution).ByteConsumersOnlyPull
  demandServable : (nativeBaseTrace statement execution).DemandServable
  programProjection : NativeProgramRowProjection statement execution
  memoryGenesis : NativeMemoryGenesis execution.initialState
    (TraceGen.compileExecution statement.program execution
      (nativeInitialClock statement)).memoryHistory

/-- Compiler readiness supplies well-formedness of the total compiler result; the `getD` fallback
is eliminated using the recorded successful optional compilation. -/
theorem NativeTraceReady.compiledWellFormed
    {statement : SupportedCoreStatement p} {execution : Machine.EventExecutionTrace}
    (ready : NativeTraceReady statement execution) :
    (TraceGen.compileExecution statement.program execution
      (nativeInitialClock statement)).WellFormed := by
  obtain ⟨compiled, generated, wellFormed⟩ := ready.compiler
  rw [TraceGen.compileExecution_eq_of_some generated]
  exact wellFormed

/-- Every base occurrence routed by the deterministic compiler meets its native table contract. -/
theorem NativeTraceReady.baseWellFormed
    {statement : SupportedCoreStatement p} {execution : Machine.EventExecutionTrace}
    (ready : NativeTraceReady statement execution)
    (publicWellFormed : statement.publicValues.LimbBounds) :
    (nativeBaseTrace statement execution).WellFormed :=
  nativeBaseTraceOfCompiled_wellFormed statement _ publicWellFormed
    ready.compiledWellFormed ready.stateBumps

/-- Provider recounting preserves well-formedness because every demanded key is servable. -/
theorem NativeTraceReady.wellFormed
    {statement : SupportedCoreStatement p} {execution : Machine.EventExecutionTrace}
    (ready : NativeTraceReady statement execution)
    (publicWellFormed : statement.publicValues.LimbBounds) :
    (nativeTrace statement execution).WellFormed := by
  exact (nativeBaseTrace statement execution).canonicalClosure_wellFormed
    (ready.baseWellFormed publicWellFormed) ready.demandServable

/-- The exact assertion system of all 53 native tables plus the verifier row. -/
theorem NativeTraceReady.constraints
    {statement : SupportedCoreStatement p} {execution : Machine.EventExecutionTrace}
    (ready : NativeTraceReady statement execution)
    (publicWellFormed : statement.publicValues.LimbBounds) :
    (nativeTrace statement execution).witness.Constraints :=
  (nativeTrace statement execution).witness_constraints
    (ready.wellFormed publicWellFormed)

/-- Registry-wide Program emission shape supplies the Program half of consumer polarity.  Native
readiness therefore stores only the residual Byte-channel fact. -/
theorem NativeTraceReady.consumers
    {statement : SupportedCoreStatement p} {execution : Machine.EventExecutionTrace}
    (ready : NativeTraceReady statement execution)
    (publicWellFormed : statement.publicValues.LimbBounds) :
    ConsumersOnlyPull (nativeBaseTrace statement execution) :=
  (nativeBaseTrace statement execution).consumersOnlyPull_of_byte
    (ready.baseWellFormed publicWellFormed) ready.byteConsumers

/-- Consumer polarity makes the provider-free skeleton nonpositive at every demanded key.  The
separate `ConsumerClosure` adapter derives the Program half registry-wide, leaving callers only a
Byte-specific fact when that heavier theorem is desired. -/
theorem NativeTraceReady.skeletonNonpositive
    {statement : SupportedCoreStatement p} {execution : Machine.EventExecutionTrace}
    (ready : NativeTraceReady statement execution)
    (publicWellFormed : statement.publicValues.LimbBounds) :
  ∀ key ∈ (nativeBaseTrace statement execution).closingKeyList,
      multiplicitySum (nativeBaseTrace statement execution).skeletonLedger key ≤ 0 := by
  apply hnonpos_of_consumersOnlyPull
  exact ready.consumers publicWellFormed

/-- Convert the four-component footprint carrier into the channel-indexed length premise used by
Clean's balance theorem. -/
theorem NativeTraceFootprint.interactionLengths
    {trace : SupportedCoreTraceWitness p}
    (fits : (NativeTraceFootprint.ofTrace trace).Fits p) :
    ∀ channel ∈ (sp1Ensemble (p := p)).channels,
      (trace.witness.interactionsWith channel).length < p := by
  intro channel channelMem
  simp only [sp1Ensemble_channels, List.mem_cons, List.not_mem_nil, or_false] at channelMem
  rcases channelMem with rfl | rfl | rfl | rfl | rfl
  · simpa only [NativeTraceFootprint.ofTrace,
      Air.Flat.EnsembleWitness.interactionsWith_allTablesWitness] using fits.1
  · simpa only [NativeTraceFootprint.ofTrace,
      Air.Flat.EnsembleWitness.interactionsWith_allTablesWitness] using fits.2.1
  · simpa only [NativeTraceFootprint.ofTrace,
      Air.Flat.EnsembleWitness.interactionsWith_allTablesWitness] using fits.2.2.1
  · simpa only [NativeTraceFootprint.ofTrace,
      Air.Flat.EnsembleWitness.interactionsWith_allTablesWitness] using fits.2.2.2.1
  · simpa only [NativeTraceFootprint.ofTrace,
      Air.Flat.EnsembleWitness.interactionsWith_allTablesWitness] using fits.2.2.2.2

/-- Public limb well-formedness makes the arbitrary-shard prover-data clock representable. -/
theorem nativeInitialClock_encodable (statement : SupportedCoreStatement p)
    (publicWellFormed : statement.publicValues.LimbBounds) :
    Commit.InitialClockEncodable (nativeInitialClock statement) := by
  obtain ⟨high, low, -⟩ :=
    initialBoundaryStateMessage_bounds statement.publicValues publicWellFormed
  exact clkNat_lt_of_limbs high low

/-- Residual admissibility of the deterministic native compiler on one shared semantic witness.

This predicate contains only facts about the total `nativeTrace` projection.  It deliberately does
not repeat semantic execution validity or the Core row budget, which belong to the shared relation
in `FormalModel.SupportedShard`. -/
def NativeTraceAdmissible (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace) : Prop :=
  NativeTraceReady statement execution ∧
    (NativeTraceFootprint.ofTrace (nativeTrace statement execution)).Fits p

/-! ## Canonical shard source

The low-level compiler consumes the common witness's evaluated `EventExecutionTrace`; its public
completeness relation therefore has the same witness type and semantic validity as soundness. -/

/-- Compiler admissibility of the deterministic trace represented by a canonical shard witness. -/
noncomputable def NativeShardTraceAdmissible (statement : SupportedCoreStatement p)
    (witness : Machine.CoreShardSemanticWitness) : Prop :=
  NativeTraceAdmissible statement
    (witness.evaluatedTrace (supportedCoreShardModel (p := p)))

/-- The canonical semantic language restricted only by the still-visible compiler facts. -/
noncomputable def SupportedCoreNativeAdmissibleShardRelation :
    WitnessRelation.Relation (SupportedCoreStatement p) Machine.CoreShardSemanticWitness :=
  (SupportedCoreShardExecutionRelation (p := p)).restrict NativeShardTraceAdmissible

/-- Exact remaining domain-closure statement on the one public semantic relation, **restricted to
syscall-free shards**: the semantic language now also contains halting shards (the shared
`.halted` case), whose terminal transition is the canonical HALT syscall — outside the
deterministic compiler's domain until it emits the terminal halt row
(`NativeTraceReady.syscallFree`).  Quantifying over halting witnesses here would make the
condition false by construction rather than open. -/
noncomputable def NativeShardTraceTotal : Prop :=
  ∀ (statement : SupportedCoreStatement p) (witness : Machine.CoreShardSemanticWitness),
    SupportedCoreShardExecutionRelation statement witness →
      (witness.evaluatedTrace (supportedCoreShardModel (p := p))).AllOrdinary →
      NativeShardTraceAdmissible statement witness

end SP1Clean.Soundness
