import SP1Clean.Proofs.Completeness.NativeTraceCompiler

/-!
# Native compiler agreement with the built State tables

This module closes the representation-only part of deterministic State completeness.  The
chronological compiler remains field-free; the lemmas here identify its records with the rows
actually produced by `SupportedCoreTraceWitness` and show that canonical Byte/Range/Program
closure does not disturb either instruction rows or the StateBump suffix.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels
open SP1Clean.Execution
open SP1Clean.LookupAccessList
open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance nativeStateAgreementFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-! ## Stable physical tables -/

/-- The stable final provider position of an assembled witness is its generated StateBump table. -/
theorem SupportedCoreTraceWitness.stateBumpTable_witness
    (trace : SupportedCoreTraceWitness p) :
    stateBumpTable trace.witness = trace.providerTableFor .stateBump := by
  unfold stateBumpTable SupportedCoreTraceWitness.witness
  simp [SupportedCoreTraceWitness.tables, SupportedCoreTraceWitness.instructionTables,
    SupportedCoreTraceWitness.providerTables, stateBumpIndex, instructionTableCount,
    stateSilentProviderTableCount, InstructionChipId.all, ProviderTableId.all,
    ByteProviderId.all]

/-- Canonical closure keeps the exact physical StateBump table, not merely its occurrence list. -/
@[simp] theorem SupportedCoreTraceWitness.canonicalClosure_stateBumpTable
    (trace : SupportedCoreTraceWitness p) :
    stateBumpTable trace.canonicalClosure.witness = stateBumpTable trace.witness := by
  rw [trace.canonicalClosure.stateBumpTable_witness, trace.stateBumpTable_witness]
  rfl

/-- Canonical closure keeps the exact decoded instruction-row stream. -/
@[simp] theorem SupportedCoreTraceWitness.canonicalClosure_decodedInstructionRows
    (trace : SupportedCoreTraceWitness p) :
    decodedInstructionRows (p := p) trace.canonicalClosure.tables =
      decodedInstructionRows (p := p) trace.tables := by
  unfold decodedInstructionRows
  change decodeInstructionTables supportedChips
      (trace.canonicalClosure.tables.take instructionTableCount) =
    decodeInstructionTables supportedChips (trace.tables.take instructionTableCount)
  rw [trace.canonicalClosure.tables_take_instructionTables,
    trace.tables_take_instructionTables, trace.canonicalClosure_instructionTables]

/-- Therefore canonical closure preserves the instruction half of the State ledger verbatim. -/
@[simp] theorem SupportedCoreTraceWitness.canonicalClosure_stateInstrLinks
    (trace : SupportedCoreTraceWitness p) :
    stateInstrLinks trace.canonicalClosure = stateInstrLinks trace := by
  unfold stateInstrLinks
  simp only [SupportedCoreTraceWitness.witness_data,
    SupportedCoreTraceWitness.witness_tables,
    SupportedCoreTraceWitness.canonicalClosure_data]
  exact congrArg (fun rows =>
    (rows.filter fun d => signedVal (d.toChipRow trace.data).is_real = 1).map fun d =>
      (msgToken stateChannel (statePullMessage (d.toChipRow trace.data)),
        msgToken stateChannel (statePushMessage (d.toChipRow trace.data))))
    trace.canonicalClosure_decodedInstructionRows

/-- Canonical closure also preserves the StateBump half verbatim. -/
@[simp] theorem SupportedCoreTraceWitness.canonicalClosure_stateBumpLinks
    (trace : SupportedCoreTraceWitness p) :
    stateBumpLinks trace.canonicalClosure = stateBumpLinks trace := by
  simp [stateBumpLinks]

/-- Both public State tokens survive canonical closure. -/
@[simp] theorem SupportedCoreTraceWitness.canonicalClosure_stateInitToken
    (trace : SupportedCoreTraceWitness p) :
    stateInitToken trace.canonicalClosure = stateInitToken trace := by
  rfl

@[simp] theorem SupportedCoreTraceWitness.canonicalClosure_stateFinalToken
    (trace : SupportedCoreTraceWitness p) :
    stateFinalToken trace.canonicalClosure = stateFinalToken trace := by
  rfl

/-- Any base-trace agreement transports through the closure operation without a new premise. -/
theorem StateTraceAgreement.canonicalClosure
    {trace : SupportedCoreTraceWitness p} {events : List RoutedEvent}
    {initial final : StateRecord} (agreement : StateTraceAgreement trace events initial final) :
    StateTraceAgreement trace.canonicalClosure events initial final where
  instruction := by simpa using agreement.instruction
  bumps := by simpa using agreement.bumps
  initial := by simpa using agreement.initial
  final := by simpa using agreement.final

/-! ## Public endpoint records -/

omit [Fact (2 ^ 25 < p)] in
/-- Canonically splitting the semantic values of an already-canonical State message recovers the
message itself.  This is the field-free/field-valued endpoint bridge used below. -/
theorem StateRecord.canonical_toMessage_eq
    (message : StateMsg (ZMod p))
    (clkLowBound : message.clk_low.val < 2 ^ 24)
    (pc0Bound : message.pc0.val < 2 ^ 16)
    (pc1Bound : message.pc1.val < 2 ^ 16)
    (pc2Bound : message.pc2.val < 2 ^ 16) :
    (StateRecord.canonical (Semantics.StateMsg.timeNat message)
        (Semantics.StateMsg.pcBits message).toNat).toMessage (p := p) = message := by
  have pcNat : (Semantics.StateMsg.pcBits message).toNat =
      message.pc0.val + message.pc1.val * 2 ^ 16 + message.pc2.val * 2 ^ 32 := by
    simp only [Semantics.StateMsg.pcBits, Semantics.pcBits, BitVec.toNat_ofNat]
    rw [Nat.mod_eq_of_lt]
    omega
  unfold StateRecord.canonical StateRecord.toMessage Semantics.StateMsg.timeNat Semantics.clkNat
  congr 1
  · rw [show (message.clk_high.val * 2 ^ 24 + message.clk_low.val) / 2 ^ 24 =
        message.clk_high.val by omega,
      ZMod.natCast_zmod_val]
  · rw [show (message.clk_high.val * 2 ^ 24 + message.clk_low.val) % 2 ^ 24 =
        message.clk_low.val by omega,
      ZMod.natCast_zmod_val]
  · rw [pcNat, show
        (message.pc0.val + message.pc1.val * 2 ^ 16 + message.pc2.val * 2 ^ 32) %
            2 ^ 16 = message.pc0.val by omega,
      ZMod.natCast_zmod_val]
  · rw [pcNat, show
        (message.pc0.val + message.pc1.val * 2 ^ 16 + message.pc2.val * 2 ^ 32) /
              2 ^ 16 % 2 ^ 16 = message.pc1.val by omega,
      ZMod.natCast_zmod_val]
  · rw [pcNat, show
        (message.pc0.val + message.pc1.val * 2 ^ 16 + message.pc2.val * 2 ^ 32) /
              2 ^ 32 % 2 ^ 16 = message.pc2.val by omega,
      ZMod.natCast_zmod_val]

/-- The decoded public initial endpoint is exactly the verifier's initial State message. -/
theorem nativeStateBoundary_initial_toMessage
    (statement : SupportedCoreStatement p) (wellFormed : statement.publicValues.LimbBounds) :
    (nativeStateBoundary statement).initial.toMessage (p := p) =
      initialBoundaryStateMessage statement.publicValues := by
  have bounds := initialBoundaryStateMessage_bounds statement.publicValues wellFormed
  simpa only [nativeStateBoundary, StateBoundary.canonical, nativeInitialClock, nativeInitialPc,
    supportedPcBits, initialBoundaryStateMessage, Semantics.StateMsg.timeNat,
    Semantics.StateMsg.pcBits] using
      StateRecord.canonical_toMessage_eq
        (initialBoundaryStateMessage statement.publicValues) bounds.2.1 bounds.2.2.1
          bounds.2.2.2.1 bounds.2.2.2.2

/-- The final endpoint has the identical round trip. -/
theorem nativeStateBoundary_final_toMessage
    (statement : SupportedCoreStatement p) (wellFormed : statement.publicValues.LimbBounds) :
    (nativeStateBoundary statement).final.toMessage (p := p) =
      finalBoundaryStateMessage statement.publicValues := by
  have bounds := finalBoundaryStateMessage_bounds statement.publicValues wellFormed
  simpa only [nativeStateBoundary, StateBoundary.canonical, nativeFinalClock, nativeFinalPc,
    supportedPcBits, finalBoundaryStateMessage, Semantics.StateMsg.timeNat,
    Semantics.StateMsg.pcBits] using
      StateRecord.canonical_toMessage_eq
        (finalBoundaryStateMessage statement.publicValues) bounds.2.1 bounds.2.2.1
          bounds.2.2.2.1 bounds.2.2.2.2

/-- The two boundary-token fields of base State agreement are consequences of public limb
well-formedness, not trace-assembly assumptions. -/
theorem nativeBaseTraceOfCompiled_stateInitToken
    (statement : SupportedCoreStatement p) (compiled : CompiledExecution)
    (wellFormed : statement.publicValues.LimbBounds) :
    stateInitToken (nativeBaseTraceOfCompiled statement compiled) =
      (nativeStateBoundary statement).initial.key (p := p) := by
  unfold stateInitToken StateRecord.key
  change msgToken stateChannel (initialBoundaryStateMessage statement.publicValues) = _
  rw [nativeStateBoundary_initial_toMessage statement wellFormed]

theorem nativeBaseTraceOfCompiled_stateFinalToken
    (statement : SupportedCoreStatement p) (compiled : CompiledExecution)
    (wellFormed : statement.publicValues.LimbBounds) :
    stateFinalToken (nativeBaseTraceOfCompiled statement compiled) =
      (nativeStateBoundary statement).final.key (p := p) := by
  unfold stateFinalToken StateRecord.key
  change msgToken stateChannel (finalBoundaryStateMessage statement.publicValues) = _
  rw [nativeStateBoundary_final_toMessage statement wellFormed]

/-! ## Common generated CPU-state messages -/

private theorem clockLow_split (clock : ℕ) :
    clock % 2 ^ 16 + (clock / 2 ^ 16 % 256) * 2 ^ 16 = clock % 2 ^ 24 := by
  calc
    _ = (clock % (2 ^ 16 * 256)) % 2 ^ 16 +
          (clock % (2 ^ 16 * 256)) / 2 ^ 16 * 2 ^ 16 := by
      rw [Nat.mod_mul_right_div_self]
      rw [Nat.mod_mod_of_dvd clock (by exact dvd_mul_right (2 ^ 16) 256)]
    _ = clock % (2 ^ 16 * 256) := Nat.mod_add_div' _ _
    _ = clock % 2 ^ 24 := by norm_num

omit [Fact (2 ^ 25 < p)] in
/-- The shared CPU-state input builder pulls the canonical field-free clock/PC record. -/
theorem cpuStatePullMessage_cpuStateCols (clock pc : ℕ) :
    cpuStatePullMessage (cpuStateCols (p := p) clock pc) =
      (StateRecord.canonical clock pc).toMessage (p := p) := by
  unfold cpuStatePullMessage cpuStateCols StateRecord.canonical StateRecord.toMessage
  simp only [Nat.shiftRight_eq_div_pow, Vector.getElem_mk, List.getElem_toArray]
  congr 1
  have split := congrArg (fun n : ℕ => (n : ZMod p)) (clockLow_split clock)
  norm_num [Nat.cast_add, Nat.cast_mul] at split
  exact split

omit [Fact (2 ^ 25 < p)] in
/-- The ordinary generated push deliberately leaves both low-limb carries raw. -/
theorem cpuStatePushMessage_cpuStateCols (clock pc : ℕ) :
    cpuStatePushMessage (cpuStateCols (p := p) clock pc) =
      ({ clkHigh := clock / 2 ^ 24
         clkLow := clock % 2 ^ 24 + 8
         pc0 := pc % 2 ^ 16 + 4
         pc1 := pc / 2 ^ 16 % 2 ^ 16
         pc2 := pc / 2 ^ 32 % 2 ^ 16 } : StateRecord).toMessage (p := p) := by
  unfold cpuStatePushMessage cpuStateCols StateRecord.toMessage
  simp only [Nat.shiftRight_eq_div_pow, Vector.getElem_mk, List.getElem_toArray]
  congr 1
  have split := congrArg (fun n : ℕ => (n : ZMod p)) (clockLow_split clock)
  norm_num [Nat.cast_add, Nat.cast_mul] at split ⊢
  rw [split]
  all_goals norm_num [Nat.cast_add]

/-! ## Physical instruction-row decomposition -/

/-- The decoder zips a registry realization with its correspondingly built tables pointwise. -/
private theorem decodeInstructionTables_map_registry
    (trace : SupportedCoreTraceWitness p) (ids : List InstructionChipId) :
    decodeInstructionTables
        (ids.map (supportedChipFor (p := p)))
        (ids.map trace.instructionTableFor) =
      ids.flatMap fun id =>
        (trace.instructionTableFor id).table.map fun physical =>
          (DecodedInstructionRow.mk (supportedChipFor (p := p) id) physical) := by
  induction ids with
  | nil => rfl
  | cons id ids ih =>
      simp only [List.map_cons, decodeInstructionTables, List.flatMap_cons]
      rw [ih]

/-- The canonical decoder of an assembled trace is exactly a table-ordered flattening of the
twenty-five generated instruction tables. -/
theorem SupportedCoreTraceWitness.decodedInstructionRows_witness
    (trace : SupportedCoreTraceWitness p) :
    decodedInstructionRows (p := p) trace.witness.tables =
      InstructionChipId.all.flatMap fun id =>
        (trace.instructionTableFor id).table.map fun physical =>
          (DecodedInstructionRow.mk (supportedChipFor (p := p) id) physical) := by
  unfold decodedInstructionRows
  rw [trace.witness_tables]
  change decodeInstructionTables supportedChips
      (trace.tables.take instructionTableCount) = _
  rw [trace.tables_take_instructionTables]
  unfold SupportedCoreTraceWitness.instructionTables supportedChips
  exact decodeInstructionTables_map_registry trace InstructionChipId.all

/-- State links projected from one physical generated instruction table. -/
noncomputable def SupportedCoreTraceWitness.instructionStateLinksFor
    (trace : SupportedCoreTraceWitness p) (id : InstructionChipId) :
    List (LookupKey × LookupKey) :=
  (((trace.instructionTableFor id).table.map fun physical =>
      DecodedInstructionRow.mk (supportedChipFor (p := p) id) physical).filter fun decoded =>
        signedVal (decoded.toChipRow trace.data).is_real = 1).map fun decoded =>
    (msgToken stateChannel (statePullMessage (decoded.toChipRow trace.data)),
      msgToken stateChannel (statePushMessage (decoded.toChipRow trace.data)))

/-- The instruction half of the State ledger is grouped by the physical registry order. -/
theorem SupportedCoreTraceWitness.stateInstrLinks_eq_flatMap
    (trace : SupportedCoreTraceWitness p) :
    stateInstrLinks trace =
      InstructionChipId.all.flatMap trace.instructionStateLinksFor := by
  rw [stateInstrLinks, trace.decodedInstructionRows_witness]
  simp only [List.filter_flatMap, List.map_flatMap]
  rfl

/-! ## Generated StateBump rows -/

/-- Reading the input prefix of an honestly built StateBump row returns the exact supplied row. -/
@[simp] theorem stateBumpRow_buildRow
    (inputs : List (StateBumpChip.Inputs (ZMod p)))
    (input : StateBumpChip.Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) :
    stateBumpRow (Table.build StateBumpChip.component inputs data hint)
        (StateBumpChip.component.buildRow input data hint) = input := by
  unfold stateBumpRow
  change StateBumpChip.component.rowInput
      (Environment.fromArray (StateBumpChip.component.buildRow input data hint) data) = input
  exact StateBumpChip.component.rowInput_buildRow input data data hint

private theorem signedVal_one_nativeState : signedVal (1 : ZMod p) = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
  rw [signedVal_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod,
    Nat.mod_eq_of_lt (by omega)]
  rfl

/-- Every generated StateBump row has the literal selector `1`.  This is independent of table
constraints and hence does not need a well-formedness premise. -/
theorem SupportedCoreTraceWitness.stateBumpSelectorBinary
    (trace : SupportedCoreTraceWitness p) :
    ∀ row ∈ (stateBumpTable trace.witness).table,
      (stateBumpRow (stateBumpTable trace.witness) row).is_real = 0 ∨
        (stateBumpRow (stateBumpTable trace.witness) row).is_real = 1 := by
  intro row rowMem
  rw [trace.stateBumpTable_witness] at rowMem ⊢
  simp only [SupportedCoreTraceWitness.providerTableFor, Table.build_table,
    List.mem_map] at rowMem
  obtain ⟨input, inputMem, rfl⟩ := rowMem
  change
    (stateBumpRow
      (Table.build StateBumpChip.component
        (stateBumpTraceInputs (trace.providerOccurrences .stateBump)) trace.data trace.hint)
      (StateBumpChip.component.buildRow input trace.data trace.hint)).is_real = 0 ∨
    (stateBumpRow
      (Table.build StateBumpChip.component
        (stateBumpTraceInputs (trace.providerOccurrences .stateBump)) trace.data trace.hint)
      (StateBumpChip.component.buildRow input trace.data trace.hint)).is_real = 1
  rw [stateBumpRow_buildRow]
  right
  rw [stateBumpTraceInputs] at inputMem
  obtain ⟨event, -, rfl⟩ := List.mem_map.mp inputMem
  rfl

private theorem stateBumpBuiltLinks_aux
    (tableInputs inputs : List (StateBumpChip.Inputs (ZMod p)))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (active : ∀ input ∈ inputs, signedVal input.is_real = 1) :
    (((inputs.map fun input => StateBumpChip.component.buildRow input data hint).filter fun row =>
        signedVal (stateBumpRow
          (Table.build StateBumpChip.component tableInputs data hint)
          row).is_real = 1).map fun row =>
      (msgToken stateChannel (StateBumpChip.pulledMessage (stateBumpRow
        (Table.build StateBumpChip.component tableInputs data hint) row)),
       msgToken stateChannel (StateBumpChip.pushedMessage (stateBumpRow
        (Table.build StateBumpChip.component tableInputs data hint) row)))) =
      inputs.map fun input =>
        (msgToken stateChannel (StateBumpChip.pulledMessage input),
          msgToken stateChannel (StateBumpChip.pushedMessage input)) := by
  let table := Table.build StateBumpChip.component tableInputs data hint
  have decoded (input : StateBumpChip.Inputs (ZMod p)) :
      stateBumpRow table (StateBumpChip.component.buildRow input data hint) = input := by
    exact stateBumpRow_buildRow tableInputs input data hint
  have filtered :
      (inputs.map fun input => StateBumpChip.component.buildRow input data hint).filter
          (fun row => decide (signedVal (stateBumpRow table row).is_real = 1)) =
        inputs.map fun input => StateBumpChip.component.buildRow input data hint := by
    apply List.filter_eq_self.mpr
    intro row rowMem
    obtain ⟨input, inputMem, rfl⟩ := List.mem_map.mp rowMem
    exact Bool.decide_true (by rw [decoded]; exact active input inputMem)
  change
    (((inputs.map fun input => StateBumpChip.component.buildRow input data hint).filter fun row =>
      signedVal (stateBumpRow table row).is_real = 1).map fun row =>
        (msgToken stateChannel (StateBumpChip.pulledMessage (stateBumpRow table row)),
          msgToken stateChannel (StateBumpChip.pushedMessage (stateBumpRow table row)))) = _
  rw [filtered, List.map_map]
  exact List.map_congr_left fun input _ => by
    cases input
    simp only [Function.comp_apply]
    rw [decoded]

/-- Closed form of the built StateBump link list for an arbitrary generated trace. -/
theorem SupportedCoreTraceWitness.stateBumpLinks_eq_occurrences
    (trace : SupportedCoreTraceWitness p) :
    stateBumpLinks trace =
      (trace.providerOccurrences .stateBump).map fun event =>
        (msgToken stateChannel (StateBumpChip.pulledMessage (stateBumpCols (p := p) event)),
          msgToken stateChannel
            (StateBumpChip.pushedMessage (stateBumpCols (p := p) event))) := by
  rw [stateBumpLinks, trace.stateBumpTable_witness]
  simp only [SupportedCoreTraceWitness.providerTableFor, Table.build_table]
  have active : ∀ input ∈ stateBumpTraceInputs (p := p)
      (trace.providerOccurrences .stateBump), signedVal input.is_real = 1 := by
    intro input inputMem
    rw [stateBumpTraceInputs] at inputMem
    obtain ⟨event, -, rfl⟩ := List.mem_map.mp inputMem
    exact signedVal_one_nativeState
  have rowsEq :
      (stateBumpTraceInputs (p := p) (trace.providerOccurrences .stateBump)).map
          (fun input : StateBumpChip.component.Input (ZMod p) =>
            StateBumpChip.component.buildRow input trace.data trace.hint) =
        (stateBumpTraceInputs (p := p) (trace.providerOccurrences .stateBump)).map
          (fun input : StateBumpChip.Inputs (ZMod p) =>
            StateBumpChip.component.buildRow input trace.data trace.hint) := by
    exact List.map_congr_left fun input _ => by cases input; rfl
  rw [rowsEq]
  have result := stateBumpBuiltLinks_aux (p := p)
      (stateBumpTraceInputs (p := p) (trace.providerOccurrences .stateBump))
      (stateBumpTraceInputs (p := p) (trace.providerOccurrences .stateBump))
      trace.data trace.hint active
  have rhsEq :
      (stateBumpTraceInputs (p := p) (trace.providerOccurrences .stateBump)).map
          (fun input : StateBumpChip.Inputs (ZMod p) =>
            (msgToken stateChannel (StateBumpChip.pulledMessage input),
              msgToken stateChannel (StateBumpChip.pushedMessage input))) =
        (trace.providerOccurrences .stateBump).map fun event =>
          (msgToken stateChannel (StateBumpChip.pulledMessage (stateBumpCols (p := p) event)),
            msgToken stateChannel
              (StateBumpChip.pushedMessage (stateBumpCols (p := p) event))) := by
    rw [stateBumpTraceInputs, List.map_map]
    exact List.map_congr_left fun event _ => rfl
  rw [rhsEq] at result
  exact result

/-- The base compiler's built StateBump links are exactly the separately stored physical bump
links derived from the chronological instruction stream. -/
theorem nativeBaseTraceOfCompiled_stateBumpLinks
    (statement : SupportedCoreStatement p) (compiled : CompiledExecution) :
    stateBumpLinks (nativeBaseTraceOfCompiled statement compiled) =
      physicalStateBumpLinks (p := p) compiled.routedEvents := by
  rw [(nativeBaseTraceOfCompiled statement compiled).stateBumpLinks_eq_occurrences]
  simp only [nativeBaseTraceOfCompiled, nativeBaseProviderOccurrences]
  induction compiled.routedEvents with
  | nil => rfl
  | cons routed rest ih =>
      have head :
          (routed.stateBumpEvents.map fun event =>
            (msgToken stateChannel (StateBumpChip.pulledMessage (stateBumpCols (p := p) event)),
              msgToken stateChannel
                (StateBumpChip.pushedMessage (stateBumpCols (p := p) event)))) =
          if routed.rawPushState = routed.nextState then []
          else [(routed.rawPushState.key (p := p), routed.nextState.key (p := p))] := by
        by_cases canonical : routed.rawPushState = routed.nextState
        · simp [RoutedEvent.stateBumpEvents, canonical]
        · simp only [RoutedEvent.stateBumpEvents, if_neg canonical, List.map_cons,
            List.map_nil]
          rw [StateRecord.pulledMessage_stateBumpCols,
            StateRecord.pushedMessage_stateBumpCols]
          rfl
      simp only [stateBumpEvents, List.flatMap_cons, List.map_append,
        physicalStateBumpLinks, List.flatMap_cons]
      have ih' := ih
      simp only [stateBumpEvents, physicalStateBumpLinks] at ih'
      rw [ih', head]

/-- Once the one instruction-row projection is known, every other field of base State agreement
is generated data. -/
theorem nativeBaseTraceOfCompiled_stateAgreement
    (statement : SupportedCoreStatement p) (compiled : CompiledExecution)
    (publicWellFormed : statement.publicValues.LimbBounds)
    (instruction : stateInstrLinks (nativeBaseTraceOfCompiled statement compiled) =
      physicalInstructionStateLinks (p := p) compiled.routedEvents) :
    StateTraceAgreement (nativeBaseTraceOfCompiled statement compiled) compiled.routedEvents
      (nativeStateBoundary statement).initial (nativeStateBoundary statement).final where
  instruction := instruction
  bumps := nativeBaseTraceOfCompiled_stateBumpLinks statement compiled
  initial := nativeBaseTraceOfCompiled_stateInitToken statement compiled publicWellFormed
  final := nativeBaseTraceOfCompiled_stateFinalToken statement compiled publicWellFormed

/-- Canonical provider closure upgrades the narrow row projection to full final-trace agreement. -/
theorem nativeTrace_stateAgreement
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace)
    (publicWellFormed : statement.publicValues.LimbBounds)
    (projection : NativeStateRowProjection statement execution) :
    StateTraceAgreement (nativeTrace statement execution)
      (TraceGen.compileExecution statement.program execution
        (nativeInitialClock statement)).routedEvents
      (nativeStateBoundary statement).initial (nativeStateBoundary statement).final := by
  apply StateTraceAgreement.canonicalClosure
  apply nativeBaseTraceOfCompiled_stateAgreement statement _ publicWellFormed
  exact projection

/-- StateBump selector binarity is generated data, not a readiness premise. -/
theorem nativeTrace_stateBumpSelectorBinary
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace) :
    ∀ row ∈ (stateBumpTable (nativeTrace statement execution).witness).table,
      (stateBumpRow (stateBumpTable (nativeTrace statement execution).witness) row).is_real = 0 ∨
      (stateBumpRow (stateBumpTable (nativeTrace statement execution).witness) row).is_real = 1 :=
  (nativeTrace statement execution).stateBumpSelectorBinary

/-- The compiler's State chronology supplies the full active State ledger hand-off.  StateBump
selector binarity is a theorem of the generated table, so readiness need not carry it. -/
theorem NativeTraceReady.stateLedgerPerm
    {statement : SupportedCoreStatement p} {execution : Machine.EventExecutionTrace}
    (ready : NativeTraceReady statement execution)
    (publicWellFormed : statement.publicValues.LimbBounds) :
    (active (nativeTrace statement execution).stateLedger).Perm
      (handoff (chainTokens
        (stateInitToken (nativeTrace statement execution),
          chronologicalStateLinks (p := p)
            (TraceGen.compileExecution statement.program execution
              (nativeInitialClock statement)).routedEvents,
          stateFinalToken (nativeTrace statement execution)))) := by
  exact (nativeTrace_stateAgreement statement execution publicWellFormed
      ready.stateProjection).ledger_perm_handoff
    (witness_decodedInstructionRows_selectorBinary _
      (ready.constraints publicWellFormed))
    (nativeTrace_stateBumpSelectorBinary statement execution) ready.stateChronology

end SP1Clean.Soundness
