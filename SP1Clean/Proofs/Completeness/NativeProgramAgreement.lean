import SP1Clean.Proofs.Completeness.ConsumerClosure
import SP1Clean.Proofs.Completeness.NativeTraceCompiler

/-!
# Native compiler agreement with the canonical Program provider

The deterministic compiler builds instruction rows first and then reconstructs the Program
provider from the literal keys those rows pull.  This module connects that canonical provider back
to the semantic program named by the ordinary-execution relation.

There is one representation seam: `NativeProgramRowProjection` says that an actual generated
instruction Program pull is the projection of the retained located decode.  The shared semantic
relation's `SupportedSP1Transition` already owns the same shared transition view for every
configured Sail state, so the `decodedInROM` hoist is projected from semantic validity rather than
stored again in `NativeTraceReady`.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open Sail LeanRV64D LeanRV64D.Defs LeanRV64D.Functions
open SP1Clean.Channels
open SP1Clean.Execution
open SP1Clean.LookupAccessList
open SP1Clean.Semantics
open SP1Clean.Soundness.Target
open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance nativeProgramAgreementFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-! ## Stable physical Program table and key projection -/

/-- The stable Program-provider position of an assembled witness is its generated Program table. -/
theorem SupportedCoreTraceWitness.programProviderTable_witness
    (trace : SupportedCoreTraceWitness p) :
    programProviderTable trace.witness = trace.providerTableFor .program := by
  unfold programProviderTable SupportedCoreTraceWitness.witness
  simp [SupportedCoreTraceWitness.tables, SupportedCoreTraceWitness.instructionTables,
    SupportedCoreTraceWitness.providerTables, programProviderIndex, instructionTableCount,
    byteProviderTableCount, rangeProviderTableCount, InstructionChipId.all, ProviderTableId.all,
    ByteProviderId.all]

/-- The typed Program token is exactly the canonical `ProgramRow` key of its recovered message. -/
private theorem word_toList {R : Type} (word : Vector R 4) :
    word.toList = [word[0], word[1], word[2], word[3]] := by
  apply List.ext_getElem (by simp)
  intro i _ rightBound
  simp only [List.length_cons, List.length_nil] at rightBound
  interval_cases i <;> simp

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
private theorem programMsg_toList (message : ProgramMsg (ZMod p)) :
    (toElements message).toList =
      [message.pc0, message.pc1, message.pc2, message.opcode, message.op_a,
       message.op_b[0], message.op_b[1], message.op_b[2], message.op_b[3],
       message.op_c[0], message.op_c[1], message.op_c[2], message.op_c[3],
       message.op_a_0, message.imm_b, message.imm_c] := by
  change (#v[message.pc0] ++ (#v[message.pc1] ++ (#v[message.pc2] ++
    (#v[message.opcode] ++ (#v[message.op_a] ++ (message.op_b ++ (message.op_c ++
      (#v[message.op_a_0] ++ (#v[message.imm_b] ++ (#v[message.imm_c] ++
        (#v[] : Vector (ZMod p) 0))))))))))).toList = _
  simp only [Vector.toList_append, Vector.toList_mk, word_toList,
    List.append_nil, List.cons_append, List.nil_append]

omit [Fact (2 ^ 25 < p)] in
theorem msgToken_program_eq_programRowKey (message : ProgramMsg (ZMod p)) :
    msgToken (programChannel (p := p)) message =
      ProgramChip.programRowKey (rowOfMsg message) := by
  unfold msgToken ProgramChip.programRowKey rowOfMsg
  rw [programMsg_toList]
  simp only [List.map_cons, List.map_nil, programChannel, kindOf, if_true]
  rw [if_neg (by decide)]

omit [Fact (2 ^ 25 < p)] in
/-- Recovering a typed Program message from a raw Clean interaction preserves its literal ledger
key. -/
theorem keyOf_toAccess_typedProgram
    (interaction : TypedInteraction (programChannel (p := p))) :
    keyOf (Interaction.toAccess interaction.raw) =
      ProgramChip.programRowKey (rowOfMsg interaction.message) := by
  have messageEq : interaction.raw.msg = (toElements interaction.message).toArray :=
    (TypedInteraction.message_eq_iff interaction interaction.message).mp rfl
  change (kindOf interaction.raw.channel.name, interaction.raw.channel.name,
      interaction.raw.msg.toList.map ZMod.val) = _
  rw [interaction.channel_eq, messageEq]
  exact msgToken_program_eq_programRowKey interaction.message

/-! ## Semantic grounding of one demanded key -/

omit [Fact (2 ^ 25 < p)] in
/-- Compiler success identifies every retained compiler row with a transition of the one semantic
execution carrier. -/
private theorem compiledRow_located_mem
    {statement : SupportedCoreStatement p} {execution : Machine.EventExecutionTrace}
    (compiler : NativeCompilerReady statement.program execution (nativeInitialClock statement))
    {compiledRow : TraceGen.CompiledLocatedInstruction}
    (rowMem : compiledRow ∈
      (TraceGen.compileExecution statement.program execution
        (nativeInitialClock statement)).rows) :
    compiledRow.located ∈ execution.locatedTransitions := by
  obtain ⟨compiled, generated, -⟩ := compiler
  rw [TraceGen.compileExecution_eq_of_some generated] at rowMem
  rw [← TraceGen.compileExecution?_located generated]
  exact List.mem_map_of_mem rowMem

/-- A demanded Program key satisfying the compiler-row projection is a genuine decode of the
semantic statement's ROM.  This is the only place the exact relation's fetch/decode evidence and
the configured-state decoder hoist meet. -/
theorem nativeProgramKey_decodedInROM
    {statement : SupportedCoreStatement p} {semanticWitness : Machine.CoreShardSemanticWitness}
    {execution : Machine.EventExecutionTrace}
    (semantic : SupportedCoreShardExecutionRelation statement semanticWitness)
    (executionEq : execution =
      semanticWitness.evaluatedTrace (supportedCoreShardModel (p := p)))
    (ordinary : execution.AllOrdinary)
    (compiler : NativeCompilerReady statement.program execution (nativeInitialClock statement))
    (projection : NativeProgramRowProjection statement execution)
    {key : LookupKey}
    (keyMem : key ∈ (nativeBaseTrace statement execution).closingKeyList)
    (keyKind : key.1 = InteractionKind.Program) :
    ∃ row : ProgramChip.ProgramRow (ZMod p),
      key = ProgramChip.programRowKey row ∧ decodedInROM statement.program row := by
  subst execution
  obtain ⟨-, -, -, -, -, -, supported, -⟩ :=
    Execution.SupportedCoreShardExecutionValid.evaluatedTrace_facts semantic ordinary
  have semanticSupported : AllTransitionsSupported statement.program
      (semanticWitness.evaluatedTrace (supportedCoreShardModel (p := p))) := by
    simpa only [Execution.SupportedCoreShardExecutionValid.program_eq semantic] using supported
  obtain ⟨compiledRow, compiledRowMem, row, generatedView, sourcePc, projected, keyEq⟩ :=
    projection key keyMem keyKind
  have locatedMem : compiledRow.located ∈
      (semanticWitness.evaluatedTrace
        (supportedCoreShardModel (p := p))).locatedTransitions :=
    compiledRow_located_mem compiler compiledRowMem
  obtain ⟨semanticView, semanticViewEq, stableDecode⟩ :=
    (semanticSupported compiledRow.located locatedMem).view
  have viewEq : semanticView = compiledRow.view :=
    Option.some.inj (semanticViewEq.symm.trans generatedView)
  subst semanticView
  obtain ⟨viewPc, viewFetch, -, -, -, -, -⟩ :=
    SP1Clean.Semantics.projectSP1Transition?_components generatedView
  have pcValueEq : compiledRow.view.pc = pcBitsOfRow row :=
    Option.some.inj (viewPc.symm.trans sourcePc)
  refine ⟨row, keyEq, compiledRow.view.word, compiledRow.view.decoded, ?_, stableDecode,
    projected⟩
  simpa only [pcValueEq] using viewFetch

/-! ## Canonical provider grounding -/

/-- Program servability supplies the structural `RowSpec` of the typed message at that same
literal key. -/
private theorem rowSpec_of_programServableRow
    (message : ProgramMsg (ZMod p))
    (servable : ProgramServable
      (ProgramChip.programRowKey (rowOfMsg message))) :
    ProgramMsg.RowSpec message := by
  unfold ProgramServable at servable
  simp only [cell, ProgramChip.programRowKey, rowOfMsg, List.getD_cons_zero,
    List.getD_cons_succ] at servable
  have flag : message.op_a_0 = 0 ∨ message.op_a_0 = 1 := by
    rcases servable.1.2 with zero | one
    · exact Or.inl ((ZMod.val_eq_zero message.op_a_0).mp zero)
    · exact Or.inr (ZMod.val_injective p (one.trans (ZMod.val_one p).symm))
  exact ⟨servable.1.1, servable.2.1.1, servable.2.1.2.1,
    servable.2.1.2.2.1, flag⟩

private theorem rowSpec_of_programServable
    {key : LookupKey} (servable : ProgramServable key)
    (interaction : TypedInteraction (programChannel (p := p)))
    (keyEq : keyOf (Interaction.toAccess interaction.raw) = key) :
    ProgramMsg.RowSpec interaction.message := by
  have rowKeyEq := keyOf_toAccess_typedProgram interaction
  have keyToRow : key = ProgramChip.programRowKey (rowOfMsg interaction.message) :=
    keyEq.symm.trans rowKeyEq
  exact rowSpec_of_programServableRow interaction.message (keyToRow ▸ servable)

/-- The canonical Program table rebuilt from actual generated pulls is grounded in the exact
semantic statement.  The only non-derived source facts are the two named seams above; in
particular this theorem assumes neither `ProgramProviderBound` nor an AIR-witness existential. -/
theorem nativeTrace_programProviderBound
    {statement : SupportedCoreStatement p} {semanticWitness : Machine.CoreShardSemanticWitness}
    {execution : Machine.EventExecutionTrace}
    (semantic : SupportedCoreShardExecutionRelation statement semanticWitness)
    (executionEq : execution =
      semanticWitness.evaluatedTrace (supportedCoreShardModel (p := p)))
    (ordinary : execution.AllOrdinary)
    (compiler : NativeCompilerReady statement.program execution (nativeInitialClock statement))
    (servable : (nativeBaseTrace statement execution).DemandServable)
    (projection : NativeProgramRowProjection statement execution) :
    ProgramProviderBound (nativeTrace statement execution).witness := by
  subst execution
  let execution := semanticWitness.evaluatedTrace (supportedCoreShardModel (p := p))
  intro raw member _
  let typed : TypedInteraction (programChannel (p := p)) :=
    { raw := raw
      channel_eq := (programProviderTable (nativeTrace statement execution).witness).channel_eq_of_mem_interactionsWith member }
  have rawMem : raw ∈
      (programProviderTable (nativeTrace statement execution).witness).interactions := by
    rw [Air.Flat.Table.interactionsWith_eq_filter] at member
    exact (List.mem_filter.mp member).1
  have accessMem : Interaction.toAccess raw ∈
      tableCleanAccesses
        (programProviderTable (nativeTrace statement execution).witness) :=
    List.mem_map_of_mem rawMem
  rw [(nativeTrace statement execution).programProviderTable_witness] at accessMem
  change Interaction.toAccess raw ∈ tableCleanAccesses
    (Table.build (ProgramProviderChip.component (p := p))
      (ProgramProviderChip.traceInputs
        (nativeBaseTrace statement execution).closureRomEntries)
      (nativeBaseTrace statement execution).data
      (nativeBaseTrace statement execution).hint) at accessMem
  rw [program_traceTable_actualAccesses _ _ _
    ((nativeBaseTrace statement execution).closureRomEntries_romKeyFits servable)] at accessMem
  obtain ⟨entry, entryMem, accessEq⟩ := List.mem_map.mp accessMem
  obtain ⟨key, filteredKeyMem, entryEq⟩ := List.mem_map.mp entryMem
  subst entry
  have keyMem : key ∈ (nativeBaseTrace statement execution).closingKeyList :=
    (List.mem_filter.mp filteredKeyMem).1
  have selected : IsProgramKey key = true :=
    (List.mem_filter.mp filteredKeyMem).2
  have keyKind : key.1 = InteractionKind.Program := programKey_kind selected
  have keyServable : ProgramServable key :=
    (servable.program key keyMem keyKind).2
  have rawKeyEq : keyOf (Interaction.toAccess raw) = key := by
    rw [← accessEq]
    simp only [actualProviderAccess, keyOf_withFieldMultiplicity]
    rw [program_round key _ selected keyServable]
    rfl
  obtain ⟨semanticRow, semanticKey, decoded⟩ :=
    nativeProgramKey_decodedInROM semantic rfl ordinary compiler projection keyMem keyKind
  have typedKey :
      ProgramChip.programRowKey (rowOfMsg typed.message) = key :=
    (keyOf_toAccess_typedProgram typed).symm.trans rawKeyEq
  have rowEq : rowOfMsg typed.message = semanticRow :=
    ProgramChip.programRow_eq_of_key (typedKey.trans semanticKey)
  have clockEncodable := nativeInitialClock_encodable statement
    (Execution.SupportedCoreShardExecutionValid.publicValuesWellFormed semantic)
  have committed := Commit.dataOfAt_statementFor (p := p) statement.program
    (nativeInitialClock statement)
    (by simpa only [Execution.SupportedCoreShardExecutionValid.program_eq semantic] using
      semantic.programWellFormed)
    (by simpa only [Execution.SupportedCoreShardExecutionValid.program_eq semantic] using
      Execution.SupportedCoreShardExecutionValid.programEncodable semantic)
    clockEncodable
  change Semantics.CommittedProgTruth typed.message (nativeTrace statement execution).witness.data
  refine ⟨rowSpec_of_programServable keyServable typed rawKeyEq, Or.inl ?_⟩
  have programEq :
      Commit.progOf (nativeTrace statement execution).witness.data = statement.program := by
    change Commit.progOf
      (Commit.dataOfAt statement.program (nativeInitialClock statement)) = statement.program
    exact committed.2
  rw [programEq, rowEq]
  exact decoded

end SP1Clean.Soundness
