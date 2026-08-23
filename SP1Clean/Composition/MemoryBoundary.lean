import SP1Clean.Faithful.CoreAIR
import SP1Clean.Composition.Table
import SP1Clean.Proofs.Completeness.Providers

/-! # Exact memory-boundary rows to native boundary providers

SP1's memory boundary is proved in a separate six-table cluster.  `MemoryGlobalInit` and
`MemoryGlobalFinalize` publish a compact eight-field global-memory message: clock, three address
limbs, and a packed representation of the four value limbs.  The native Clean ensemble deliberately
uses the unpacked Memory-channel form instead.  This module is the constructive row redistribution:
it reads the exact columns, rebuilds the native init/finalize inputs, drops multiplicity-zero padding,
and proves the two native tables' constraints under one explicit boundary-decoding contract.

The contract is not disguised as an AIR consequence.  Word and timestamp ranges are established
upstream through Byte/Global interaction balance rather than solely by the two rows' local assertion
lists.  Closing it therefore requires the exact Byte/Range provider transport and the Global-table
argument.  Naming those facts here prevents a local-assertion proof from silently assuming what only
cross-table balance can provide.
-/

set_option autoImplicit false

namespace SP1Clean.Composition

-- The faithfulness vocabulary (`ChipOracle`, `ChipFaithful`, `ChipRowCodec`,
-- `nativeAccesses`) is at the stratum below; this namespace no longer encloses it since the
-- 2026-08 move out of `Faithful/Transport/`.
open SP1Clean.Faithful

open Circuit
open Air.Flat (Component Table)
open SP1Clean.Channels (MemoryMsg)
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance memoryBoundaryFieldBound : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The active exact MemoryGlobalInit rows.  Inactive rows have no observable interaction key and
are omitted instead of forcing their unconstrained padding cells through native range checks. -/
def activeMemoryGlobalInitRows
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) :
    List (CoreAIR.Current.Row p .memoryGlobalInit) :=
  (witness.trace.rows .memoryGlobalInit).filter fun row =>
    decide (row.main.values[23] ≠ 0)

/-- The active exact MemoryGlobalFinalize rows. -/
def activeMemoryGlobalFinalizeRows
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) :
    List (CoreAIR.Current.Row p .memoryGlobalFinalize) :=
  (witness.trace.rows .memoryGlobalFinalize).filter fun row =>
    decide (row.main.values[23] ≠ 0)

/-- Decode the exact init row's address/value into the native zero-clock Memory push.

Column order is `MemoryInitCols` at the v6.4.0 pin: `addr = 6..8`, `value = 17..20`,
`is_real = 23`.  The native row keeps the original four u16 value limbs; upstream's Global message
packs the low two limbs together with the two bytes of limb 2 only for its hash input. -/
def memoryGlobalInitInput (row : CoreAIR.Current.Row p .memoryGlobalInit) :
    MemoryProviderChip.Inputs (ZMod p) where
  clk_high := 0
  clk_low := 0
  addr0 := row.main.values[6]
  addr1 := row.main.values[7]
  addr2 := row.main.values[8]
  value := #v[row.main.values[17], row.main.values[18], row.main.values[19], row.main.values[20]]
  multiplicity := row.main.values[23]

/-- Decode the exact finalize row into the native final Memory pull.  Unlike init, the exact row's
clock columns `0,1` are retained. -/
def memoryGlobalFinalizeInput (row : CoreAIR.Current.Row p .memoryGlobalFinalize) :
    MemoryFinalizeChip.Inputs (ZMod p) where
  clk_high := row.main.values[0]
  clk_low := row.main.values[1]
  addr0 := row.main.values[6]
  addr1 := row.main.values[7]
  addr2 := row.main.values[8]
  value := #v[row.main.values[17], row.main.values[18], row.main.values[19], row.main.values[20]]
  multiplicity := row.main.values[23]

/-- Cross-table facts needed to decode the exact memory-boundary cluster into native provider rows.
These are precisely the consequences expected from Byte/Range/Global balance: active words are u64,
the finalize low clock is 24-bit, and the exact selector is boolean. -/
structure MemoryBoundaryProviderContract
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) : Prop where
  init : ∀ row ∈ activeMemoryGlobalInitRows witness,
    Word.isU64 (memoryGlobalInitInput row).value ∧
      ((memoryGlobalInitInput row).multiplicity = 0 ∨
        (memoryGlobalInitInput row).multiplicity = 1)
  finalize : ∀ row ∈ activeMemoryGlobalFinalizeRows witness,
    Word.isU64 (memoryGlobalFinalizeInput row).value ∧
      (memoryGlobalFinalizeInput row).clk_low.val < 2 ^ 24 ∧
      ((memoryGlobalFinalizeInput row).multiplicity = 0 ∨
        (memoryGlobalFinalizeInput row).multiplicity = 1)

/-- The genuinely cross-table part of memory-boundary decoding.  Selector binarity is omitted:
unlike these range facts, it is a local assertion of both exact MemoryGlobal tables and is derived
below from `CoreAIR.Current.Relation`. -/
structure MemoryBoundarySemanticContract
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) : Prop where
  initWord : ∀ row ∈ activeMemoryGlobalInitRows witness,
    Word.isU64 (memoryGlobalInitInput row).value
  finalizeWord : ∀ row ∈ activeMemoryGlobalFinalizeRows witness,
    Word.isU64 (memoryGlobalFinalizeInput row).value
  finalizeClock : ∀ row ∈ activeMemoryGlobalFinalizeRows witness,
    (memoryGlobalFinalizeInput row).clk_low.val < 2 ^ 24

omit [Fact (2 ^ 24 < p)] in
/-- The exact MemoryGlobalInit selector gate implies native multiplicity binarity. -/
theorem memoryGlobalInitMultiplicity_bool
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .memoryGlobalInit)
    (valid : List.Forall (· = 0)
      (CoreAIR.Current.assertions publicValues .memoryGlobalInit row)) :
    (memoryGlobalInitInput row).multiplicity = 0 ∨
      (memoryGlobalInitInput row).multiplicity = 1 := by
  apply bool_of_mul_pred
  apply (List.forall_iff_forall_mem.mp valid)
  change row.main.values[23] * (row.main.values[23] - 1) ∈
    Extracted.MemoryGlobalInitCols.asserts row.main row.preprocessed publicValues.toBaseVector
  rw [Extracted.MemoryGlobalInitCols.asserts]
  simp

omit [Fact (2 ^ 24 < p)] in
/-- The exact MemoryGlobalFinalize selector gate implies native multiplicity binarity. -/
theorem memoryGlobalFinalizeMultiplicity_bool
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .memoryGlobalFinalize)
    (valid : List.Forall (· = 0)
      (CoreAIR.Current.assertions publicValues .memoryGlobalFinalize row)) :
    (memoryGlobalFinalizeInput row).multiplicity = 0 ∨
      (memoryGlobalFinalizeInput row).multiplicity = 1 := by
  apply bool_of_mul_pred
  apply (List.forall_iff_forall_mem.mp valid)
  change row.main.values[23] * (row.main.values[23] - 1) ∈
    Extracted.MemoryGlobalFinalizeCols.asserts row.main row.preprocessed publicValues.toBaseVector
  rw [Extracted.MemoryGlobalFinalizeCols.asserts]
  simp

omit [Fact (2 ^ 24 < p)] in
/-- Exact boundary-cluster validity supplies both local selector gates; only the explicitly named
word/timestamp consequences of cross-table balance remain as a semantic premise. -/
theorem memoryBoundaryProviderContract_of_relation {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (valid : CoreAIR.Current.Relation binds .memoryBoundary statement witness)
    (semantic : MemoryBoundarySemanticContract witness) :
    MemoryBoundaryProviderContract witness := by
  have rowValid : ∀ table row, row ∈ witness.trace.rows table →
      List.Forall (· = 0) (CoreAIR.Current.assertions statement.publicValues table row) :=
    valid.2.2.1
  exact {
    init := fun row hrow => ⟨semantic.initWord row hrow,
      memoryGlobalInitMultiplicity_bool statement.publicValues row
        (rowValid .memoryGlobalInit row (List.mem_filter.mp hrow).1)⟩
    finalize := fun row hrow => ⟨semantic.finalizeWord row hrow,
      semantic.finalizeClock row hrow,
      memoryGlobalFinalizeMultiplicity_bool statement.publicValues row
        (rowValid .memoryGlobalFinalize row (List.mem_filter.mp hrow).1)⟩ }

namespace MemoryBoundaryProviderContract

variable {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}

omit [Fact (2 ^ 24 < p)] in
/-- Every retained init row has native multiplicity exactly one.  This is why filtering the exact
padding rows preserves the active interaction multiset. -/
theorem initMultiplicity_one (contract : MemoryBoundaryProviderContract witness)
    {row : CoreAIR.Current.Row p .memoryGlobalInit}
    (hrow : row ∈ activeMemoryGlobalInitRows witness) :
    (memoryGlobalInitInput row).multiplicity = 1 := by
  have active : row.main.values[23] ≠ 0 := by
    obtain ⟨-, active⟩ := List.mem_filter.mp hrow
    simpa only [decide_eq_true_eq] using active
  rcases (contract.init row hrow).2 with zero | one
  · exact absurd zero active
  · exact one

omit [Fact (2 ^ 24 < p)] in
/-- Every retained finalize row has native multiplicity exactly one. -/
theorem finalizeMultiplicity_one (contract : MemoryBoundaryProviderContract witness)
    {row : CoreAIR.Current.Row p .memoryGlobalFinalize}
    (hrow : row ∈ activeMemoryGlobalFinalizeRows witness) :
    (memoryGlobalFinalizeInput row).multiplicity = 1 := by
  have active : row.main.values[23] ≠ 0 := by
    obtain ⟨-, active⟩ := List.mem_filter.mp hrow
    simpa only [decide_eq_true_eq] using active
  rcases (contract.finalize row hrow).2.2 with zero | one
  · exact absurd zero active
  · exact one

end MemoryBoundaryProviderContract

/-- The native Memory-init provider table constructed from the active exact init rows. -/
def transportMemoryInitTable
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Table (ZMod p) :=
  Table.build MemoryProviderChip.component
    ((activeMemoryGlobalInitRows witness).map memoryGlobalInitInput) data hint

/-- The native Memory-finalize provider table constructed from the active exact finalize rows. -/
def transportMemoryFinalizeTable
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Table (ZMod p) :=
  Table.build MemoryFinalizeChip.component
    ((activeMemoryGlobalFinalizeRows witness).map memoryGlobalFinalizeInput) data hint

variable {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}

theorem transportMemoryInitTable_constraints
    (contract : MemoryBoundaryProviderContract witness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (transportMemoryInitTable witness data hint).Constraints := by
  apply Table.build_constraints _ _ _ _ MemoryProviderChip.computableWitnesses
  intro input hinput
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hinput
  have decoded := contract.init row hrow
  exact ⟨decoded.1, rfl, rfl, decoded.2⟩

omit [Fact (2 ^ 24 < p)] in
theorem transportMemoryFinalizeTable_constraints
    (contract : MemoryBoundaryProviderContract witness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (transportMemoryFinalizeTable witness data hint).Constraints := by
  apply Table.build_constraints _ _ _ _ MemoryFinalizeChip.computableWitnesses
  intro input hinput
  obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hinput
  have decoded := contract.finalize row hrow
  exact ⟨decoded.1, decoded.2.1, decoded.2.2⟩

/-- The two memory-boundary tables in native provider order. -/
def extractedMemoryBoundaryTables
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : List (Table (ZMod p)) :=
  [transportMemoryInitTable witness data hint,
   transportMemoryFinalizeTable witness data hint]

/-- The constructed tables follow the complete twenty-four-table preprocessing prefix. -/
theorem extractedMemoryBoundaryTables_components
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (extractedMemoryBoundaryTables witness data hint).map (·.component) =
      ((Soundness.sp1ProviderTables (p := p)).drop
        Soundness.preprocessedProviderTableCount).take 2 := rfl

/-- Both constructed boundary tables use the same committed data. -/
theorem extractedMemoryBoundaryTables_data
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ table ∈ extractedMemoryBoundaryTables witness data hint, table.data = data := by
  intro table hmem
  simp only [extractedMemoryBoundaryTables, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl <;> rfl

/-- Both constructed native boundary tables satisfy their complete constraints. -/
theorem extractedMemoryBoundaryTables_constraints
    (contract : MemoryBoundaryProviderContract witness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ table ∈ extractedMemoryBoundaryTables witness data hint, table.Constraints := by
  intro table hmem
  simp only [extractedMemoryBoundaryTables, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl
  · exact transportMemoryInitTable_constraints contract data hint
  · exact transportMemoryFinalizeTable_constraints contract data hint

omit [Fact (2 ^ 24 < p)] in
/-- The decoded native init payload, exposed as a stable contract equation for the later
Global-balance proof. -/
theorem memoryGlobalInitInput_message
    (row : CoreAIR.Current.Row p .memoryGlobalInit) :
    (memoryGlobalInitInput row).toMessage =
      ({ clk_high := 0, clk_low := 0,
         addr0 := row.main.values[6], addr1 := row.main.values[7], addr2 := row.main.values[8],
         value := #v[row.main.values[17], row.main.values[18],
           row.main.values[19], row.main.values[20]] } : MemoryMsg (ZMod p)) := rfl

omit [Fact (2 ^ 24 < p)] in
/-- The decoded native finalize payload, exposed for the later Global-balance proof. -/
theorem memoryGlobalFinalizeInput_message
    (row : CoreAIR.Current.Row p .memoryGlobalFinalize) :
    (memoryGlobalFinalizeInput row).toMessage =
      ({ clk_high := row.main.values[0], clk_low := row.main.values[1],
         addr0 := row.main.values[6], addr1 := row.main.values[7], addr2 := row.main.values[8],
         value := #v[row.main.values[17], row.main.values[18],
           row.main.values[19], row.main.values[20]] } : MemoryMsg (ZMod p)) := rfl

/-! ## Access lowering

The exact Global payload is deliberately not identified with the native Memory payload.  The
former packs two value limbs with byte-decomposition witnesses and lives on `.raw .global`; the
latter keeps all four u16 limbs and lives on `SP1Memory`.  We expose both endpoints and name the
row-wise lowering between them.  This is the precise non-permutation seam consumed by the later
Global-table proof. -/

/-- The actual generated `.raw .global` access of one exact init row. -/
def exactMemoryGlobalInitRawAccess
    (row : CoreAIR.Current.Row p .memoryGlobalInit) : LookupAccess :=
  (Extracted.Interaction.toAccess
    ⟨.send,
      .raw .global
        [0, 0, row.main.values[6], row.main.values[7], row.main.values[8],
         row.main.values[17] + row.main.values[21] * 65536,
         row.main.values[18] + row.main.values[22] * 65536,
         row.main.values[20], 1, 0, 1],
      row.main.values[23]⟩)

/-- The actual generated `.raw .global` access of one exact finalize row. -/
def exactMemoryGlobalFinalizeRawAccess
    (row : CoreAIR.Current.Row p .memoryGlobalFinalize) : LookupAccess :=
  (Extracted.Interaction.toAccess
    ⟨.send,
      .raw .global
        [row.main.values[0], row.main.values[1], row.main.values[6], row.main.values[7],
         row.main.values[8], row.main.values[17] + row.main.values[21] * 65536,
         row.main.values[18] + row.main.values[22] * 65536,
         row.main.values[20], 0, 1, 1],
      row.main.values[23]⟩)

/-- Native init-side projection of the exact row.  The `.receive` direction is intentional: after
the native compatibility projection dualizes Memory, the init provider's push has this sign. -/
def projectedMemoryGlobalInitAccess
    (row : CoreAIR.Current.Row p .memoryGlobalInit) : LookupAccess :=
  (Extracted.Interaction.toAccess
    ⟨.receive,
      .memory 0 0 row.main.values[6] row.main.values[7] row.main.values[8]
        row.main.values[17] row.main.values[18] row.main.values[19] row.main.values[20],
      row.main.values[23]⟩)

/-- Native finalize-side projection of the exact row.  Finalize is already send-oriented after the
native pull is dualized, so its projected direction is `.send`. -/
def projectedMemoryGlobalFinalizeAccess
    (row : CoreAIR.Current.Row p .memoryGlobalFinalize) : LookupAccess :=
  (Extracted.Interaction.toAccess
    ⟨.send,
      .memory row.main.values[0] row.main.values[1]
        row.main.values[6] row.main.values[7] row.main.values[8]
        row.main.values[17] row.main.values[18] row.main.values[19] row.main.values[20],
      row.main.values[23]⟩)

omit [Fact (2 ^ 24 < p)] in
/-- The exact generated init interaction list really contains the raw source named above. -/
theorem exactMemoryGlobalInitRawAccess_mem
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .memoryGlobalInit) :
    exactMemoryGlobalInitRawAccess row ∈
      (CoreAIR.Current.interactions publicValues .memoryGlobalInit row).map
        Extracted.Interaction.toAccess := by
  rw [CoreAIR.Current.interactions, Extracted.MemoryGlobalInitCols.interactions]
  simp [exactMemoryGlobalInitRawAccess]

omit [Fact (2 ^ 24 < p)] in
/-- The exact generated finalize interaction list really contains the raw source named above. -/
theorem exactMemoryGlobalFinalizeRawAccess_mem
    (publicValues : SP1PublicValues (ZMod p))
    (row : CoreAIR.Current.Row p .memoryGlobalFinalize) :
    exactMemoryGlobalFinalizeRawAccess row ∈
      (CoreAIR.Current.interactions publicValues .memoryGlobalFinalize row).map
        Extracted.Interaction.toAccess := by
  rw [CoreAIR.Current.interactions, Extracted.MemoryGlobalFinalizeCols.interactions]
  simp [exactMemoryGlobalFinalizeRawAccess]

/-- The exact raw Global rows paired with their native typed-Memory lowerings.  The pair makes the
non-lossless representation change auditable: no theorem silently rewrites one key as the other. -/
def memoryBoundaryAccessLowerings
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) :
    List (LookupAccess × LookupAccess) :=
  ((witness.trace.rows .memoryGlobalInit).map fun row =>
      (exactMemoryGlobalInitRawAccess row, projectedMemoryGlobalInitAccess row)) ++
    ((witness.trace.rows .memoryGlobalFinalize).map fun row =>
      (exactMemoryGlobalFinalizeRawAccess row, projectedMemoryGlobalFinalizeAccess row))

/-- The exact raw-Global source side of `memoryBoundaryAccessLowerings`. -/
def exactMemoryBoundaryRawGlobalAccesses
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) : LookupAccessList :=
  (memoryBoundaryAccessLowerings witness).map Prod.fst

/-- The typed-Memory target side of `memoryBoundaryAccessLowerings`. -/
def projectedMemoryBoundaryProviderAccesses
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) : LookupAccessList :=
  (memoryBoundaryAccessLowerings witness).map Prod.snd

omit [Fact (2 ^ 24 < p)] in
@[simp] theorem exactMemoryBoundaryRawGlobalAccesses_eq
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) :
    exactMemoryBoundaryRawGlobalAccesses witness =
      (witness.trace.rows .memoryGlobalInit).map exactMemoryGlobalInitRawAccess ++
      (witness.trace.rows .memoryGlobalFinalize).map exactMemoryGlobalFinalizeRawAccess := by
  simp only [exactMemoryBoundaryRawGlobalAccesses, memoryBoundaryAccessLowerings,
    List.map_append, List.map_map, Function.comp_def]

omit [Fact (2 ^ 24 < p)] in
@[simp] theorem projectedMemoryBoundaryProviderAccesses_eq
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) :
    projectedMemoryBoundaryProviderAccesses witness =
      (witness.trace.rows .memoryGlobalInit).map projectedMemoryGlobalInitAccess ++
      (witness.trace.rows .memoryGlobalFinalize).map projectedMemoryGlobalFinalizeAccess := by
  simp only [projectedMemoryBoundaryProviderAccesses, memoryBoundaryAccessLowerings,
    List.map_append, List.map_map, Function.comp_def]

private theorem memoryInitProvider_memoryInteractions
    (input : Var MemoryProviderChip.Inputs (ZMod p)) (offset : ℕ) :
    ((MemoryProviderChip.main input).operations offset).interactionsWith
        Channels.memoryChannel.toRaw =
      [(pushedIf (channel := Channels.memoryChannel)
        input.multiplicity input.toMessage).toRaw] := by
  classical
  simp only [MemoryProviderChip.main, circuit_norm]
  rw [show List.filter (fun interaction =>
      decide (interaction.channel = Channels.memoryChannel.toRaw))
      (FlatOperation.interactions
        (WordRangeCheck.circuit.toSubcircuit offset input.value).ops.toFlat) = [] from by
    have noMemory := InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
      WordRangeCheck.circuit Channels.memoryChannel.toRaw (n := offset) input.value
      ([] : Operations (ZMod p)) List.not_mem_nil List.not_mem_nil
    simpa [Operations.interactionsWith_subcircuit,
      Operations.interactionsWith_nil] using noMemory]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem memoryFinalizeProvider_memoryInteractions
    (input : Var MemoryFinalizeChip.Inputs (ZMod p)) (offset : ℕ) :
    ((MemoryFinalizeChip.main input).operations offset).interactionsWith
        Channels.memoryChannel.toRaw =
      [(pulledIf (channel := Channels.memoryChannel)
        input.multiplicity input.toMessage).toRaw] := by
  simp only [MemoryFinalizeChip.main, circuit_norm]

private def memoryInitInputAccess
    (input : MemoryProviderChip.Inputs (ZMod p)) : LookupAccess :=
  (InteractionKind.Memory, "SP1Memory",
    [input.clk_high.val, input.clk_low.val, input.addr0.val, input.addr1.val,
      input.addr2.val, input.value[0].val, input.value[1].val, input.value[2].val,
      input.value[3].val],
    signedVal (- input.multiplicity))

private def memoryFinalizeInputAccess
    (input : MemoryFinalizeChip.Inputs (ZMod p)) : LookupAccess :=
  (InteractionKind.Memory, "SP1Memory",
    [input.clk_high.val, input.clk_low.val, input.addr0.val, input.addr1.val,
      input.addr2.val, input.value[0].val, input.value[1].val, input.value[2].val,
      input.value[3].val],
    signedVal input.multiplicity)

omit [Fact (2 ^ 24 < p)] in
private theorem memoryProvider_eval_toMessage
    (env : Environment (ZMod p))
    (input : Var MemoryProviderChip.Inputs (ZMod p)) :
    ProvableStruct.eval env
        (input.toMessage : MemoryMsg (Expression (ZMod p))) =
      (Eval.eval env input).toMessage := by
  rw [← ProvableStruct.eval_field_var_eq_eval]
  cases input
  simp only [MemoryProviderChip.Inputs.toMessage, circuit_norm]

omit [Fact (2 ^ 24 < p)] in
private theorem memoryFinalize_eval_toMessage
    (env : Environment (ZMod p))
    (input : Var MemoryFinalizeChip.Inputs (ZMod p)) :
    ProvableStruct.eval env
        (input.toMessage : MemoryMsg (Expression (ZMod p))) =
      (Eval.eval env input).toMessage := by
  rw [← ProvableStruct.eval_field_var_eq_eval]
  cases input
  simp only [MemoryFinalizeChip.Inputs.toMessage, circuit_norm]

private theorem memoryProvider_toAccess_eq_inputAccess
    (env : Environment (ZMod p))
    (input : Var MemoryProviderChip.Inputs (ZMod p)) :
    LookupAccessList.negMult
        (AbstractInteraction.toAccess env
          (pushedIf (channel := Channels.memoryChannel)
            input.multiplicity input.toMessage).toRaw) =
      memoryInitInputAccess (Eval.eval env input) := by
  rw [toAccess_pushIf_memory]
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  simp only [memoryInitInputAccess, LookupAccessList.negMult, circuit_norm]
  rw [memoryProvider_eval_toMessage, signedVal_neg hp]
  have evaluated := ProvableStruct.eval_var_eq_eval env input
  simp only [MemoryProviderChip.Inputs.toMessage]
  rw [congrArg MemoryProviderChip.Inputs.clk_high evaluated,
    congrArg MemoryProviderChip.Inputs.clk_low evaluated,
    congrArg MemoryProviderChip.Inputs.addr0 evaluated,
    congrArg MemoryProviderChip.Inputs.addr1 evaluated,
    congrArg MemoryProviderChip.Inputs.addr2 evaluated,
    congrArg (fun x : MemoryProviderChip.Inputs (ZMod p) => x.value[0]) evaluated,
    congrArg (fun x : MemoryProviderChip.Inputs (ZMod p) => x.value[1]) evaluated,
    congrArg (fun x : MemoryProviderChip.Inputs (ZMod p) => x.value[2]) evaluated,
    congrArg (fun x : MemoryProviderChip.Inputs (ZMod p) => x.value[3]) evaluated]

private theorem memoryFinalize_toAccess_eq_inputAccess
    (env : Environment (ZMod p))
    (input : Var MemoryFinalizeChip.Inputs (ZMod p)) :
    LookupAccessList.negMult
        (AbstractInteraction.toAccess env
          (pulledIf (channel := Channels.memoryChannel)
            input.multiplicity input.toMessage).toRaw) =
      memoryFinalizeInputAccess (Eval.eval env input) := by
  rw [toAccess_pullIf_memory]
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  simp only [memoryFinalizeInputAccess, LookupAccessList.negMult, circuit_norm,
    signedVal_neg hp, neg_neg]
  rw [memoryFinalize_eval_toMessage]
  have evaluated := ProvableStruct.eval_var_eq_eval env input
  simp only [MemoryFinalizeChip.Inputs.toMessage]
  rw [congrArg MemoryFinalizeChip.Inputs.clk_high evaluated,
    congrArg MemoryFinalizeChip.Inputs.clk_low evaluated,
    congrArg MemoryFinalizeChip.Inputs.addr0 evaluated,
    congrArg MemoryFinalizeChip.Inputs.addr1 evaluated,
    congrArg MemoryFinalizeChip.Inputs.addr2 evaluated,
    congrArg (fun x : MemoryFinalizeChip.Inputs (ZMod p) => x.value[0]) evaluated,
    congrArg (fun x : MemoryFinalizeChip.Inputs (ZMod p) => x.value[1]) evaluated,
    congrArg (fun x : MemoryFinalizeChip.Inputs (ZMod p) => x.value[2]) evaluated,
    congrArg (fun x : MemoryFinalizeChip.Inputs (ZMod p) => x.value[3]) evaluated]

private theorem memoryProvider_nativeAccesses_symbolic
    (env : Environment (ZMod p)) :
    Faithful.nativeAccesses env
        (⟨MemoryProviderChip.circuit⟩ : Component (ZMod p)).operations =
      [LookupAccessList.negMult
        (AbstractInteraction.toAccess env
          (pushedIf (channel := Channels.memoryChannel)
            (varFromOffset MemoryProviderChip.Inputs 0 :
              Var MemoryProviderChip.Inputs (ZMod p)).multiplicity
            (varFromOffset MemoryProviderChip.Inputs 0 :
              Var MemoryProviderChip.Inputs (ZMod p)).toMessage).toRaw)] := by
  rw [Faithful.nativeAccesses_component_eq_rowOperations MemoryProviderChip.circuit]
  have only : ∀ channel ∈ (MemoryProviderChip.circuit (p := p)).channels,
      channel = Channels.memoryChannel.toRaw := by
    intro channel channelMem
    have channelMem' : channel ∈ (MemoryProviderChip.circuit (p := p)).channels := channelMem
    simp only [GeneralFormalCircuit.channels] at channelMem'
    unfold MemoryProviderChip.circuit at channelMem'
    simpa [circuit_norm] using channelMem'
  rw [nativeAccesses_memoryOnly MemoryProviderChip.circuit only]
  rw [Component.rowOperations_mk]
  rw [show (MemoryProviderChip.circuit (p := p)).main =
      MemoryProviderChip.main from rfl]
  rw [memoryInitProvider_memoryInteractions]
  simp only [List.map_cons, List.map_nil]

omit [Fact (2 ^ 24 < p)] in
private theorem memoryFinalize_nativeAccesses_symbolic
    (env : Environment (ZMod p)) :
    Faithful.nativeAccesses env
        (⟨MemoryFinalizeChip.circuit⟩ : Component (ZMod p)).operations =
      [LookupAccessList.negMult
        (AbstractInteraction.toAccess env
          (pulledIf (channel := Channels.memoryChannel)
            (varFromOffset MemoryFinalizeChip.Inputs 0 :
              Var MemoryFinalizeChip.Inputs (ZMod p)).multiplicity
            (varFromOffset MemoryFinalizeChip.Inputs 0 :
              Var MemoryFinalizeChip.Inputs (ZMod p)).toMessage).toRaw)] := by
  rw [Faithful.nativeAccesses_component_eq_rowOperations MemoryFinalizeChip.circuit]
  have only : ∀ channel ∈ (MemoryFinalizeChip.circuit (p := p)).channels,
      channel = Channels.memoryChannel.toRaw := by
    intro channel channelMem
    have channelMem' : channel ∈ (MemoryFinalizeChip.circuit (p := p)).channels := channelMem
    simp only [GeneralFormalCircuit.channels] at channelMem'
    unfold MemoryFinalizeChip.circuit at channelMem'
    simpa [circuit_norm] using channelMem'
  rw [nativeAccesses_memoryOnly MemoryFinalizeChip.circuit only]
  rw [Component.rowOperations_mk]
  rw [show (MemoryFinalizeChip.circuit (p := p)).main =
      MemoryFinalizeChip.main from rfl]
  rw [memoryFinalizeProvider_memoryInteractions]
  simp only [List.map_cons, List.map_nil]

omit [Fact (2 ^ 24 < p)] in
private theorem memoryGlobalInitInput_access
    (row : CoreAIR.Current.Row p .memoryGlobalInit) :
    memoryInitInputAccess (memoryGlobalInitInput row) =
      projectedMemoryGlobalInitAccess row := by
  simp only [memoryInitInputAccess, memoryGlobalInitInput,
    projectedMemoryGlobalInitAccess, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  rfl

omit [Fact (2 ^ 24 < p)] in
private theorem memoryGlobalFinalizeInput_access
    (row : CoreAIR.Current.Row p .memoryGlobalFinalize) :
    memoryFinalizeInputAccess (memoryGlobalFinalizeInput row) =
      projectedMemoryGlobalFinalizeAccess row := by
  simp only [memoryFinalizeInputAccess, memoryGlobalFinalizeInput,
    projectedMemoryGlobalFinalizeAccess, Extracted.Interaction.toAccess,
    Extracted.Dir.sign]
  rfl

private theorem memoryGlobalInitRow_nativeAccesses
    (row : CoreAIR.Current.Row p .memoryGlobalInit)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Faithful.nativeAccesses
        (Environment.fromArray
          ((⟨MemoryProviderChip.circuit⟩ : Component (ZMod p)).buildRow
            (memoryGlobalInitInput row) data hint) data)
        (⟨MemoryProviderChip.circuit⟩ : Component (ZMod p)).operations =
      [projectedMemoryGlobalInitAccess row] := by
  rw [memoryProvider_nativeAccesses_symbolic,
    memoryProvider_toAccess_eq_inputAccess]
  let component := (⟨MemoryProviderChip.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray
    (component.buildRow (memoryGlobalInitInput row) data hint) data
  have inputEq : Eval.eval env
      (varFromOffset MemoryProviderChip.Inputs 0 :
        Var MemoryProviderChip.Inputs (ZMod p)) = memoryGlobalInitInput row := by
    rw [eval_varFromOffset_valueFromOffset]
    exact component.rowInput_buildRow (memoryGlobalInitInput row) data data hint
  rw [inputEq, memoryGlobalInitInput_access]

private theorem memoryGlobalFinalizeRow_nativeAccesses
    (row : CoreAIR.Current.Row p .memoryGlobalFinalize)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    Faithful.nativeAccesses
        (Environment.fromArray
          ((⟨MemoryFinalizeChip.circuit⟩ : Component (ZMod p)).buildRow
            (memoryGlobalFinalizeInput row) data hint) data)
        (⟨MemoryFinalizeChip.circuit⟩ : Component (ZMod p)).operations =
      [projectedMemoryGlobalFinalizeAccess row] := by
  rw [memoryFinalize_nativeAccesses_symbolic,
    memoryFinalize_toAccess_eq_inputAccess]
  let component := (⟨MemoryFinalizeChip.circuit⟩ : Component (ZMod p))
  let env := Environment.fromArray
    (component.buildRow (memoryGlobalFinalizeInput row) data hint) data
  have inputEq : Eval.eval env
      (varFromOffset MemoryFinalizeChip.Inputs 0 :
        Var MemoryFinalizeChip.Inputs (ZMod p)) = memoryGlobalFinalizeInput row := by
    rw [eval_varFromOffset_valueFromOffset]
    exact component.rowInput_buildRow (memoryGlobalFinalizeInput row) data data hint
  rw [inputEq, memoryGlobalFinalizeInput_access]

private theorem transportMemoryInitTable_accesses
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    tableNativeAccesses (transportMemoryInitTable witness data hint) =
      (activeMemoryGlobalInitRows witness).map projectedMemoryGlobalInitAccess := by
  simpa only [transportMemoryInitTable, MemoryProviderChip.component] using
    tableNativeAccesses_build_map_singleton
      (⟨MemoryProviderChip.circuit⟩ : Component (ZMod p))
      (activeMemoryGlobalInitRows witness) memoryGlobalInitInput projectedMemoryGlobalInitAccess
      data hint (fun row _ => memoryGlobalInitRow_nativeAccesses row data hint)

private theorem transportMemoryFinalizeTable_accesses
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    tableNativeAccesses (transportMemoryFinalizeTable witness data hint) =
      (activeMemoryGlobalFinalizeRows witness).map projectedMemoryGlobalFinalizeAccess := by
  simpa only [transportMemoryFinalizeTable, MemoryFinalizeChip.component] using
    tableNativeAccesses_build_map_singleton
      (⟨MemoryFinalizeChip.circuit⟩ : Component (ZMod p))
      (activeMemoryGlobalFinalizeRows witness) memoryGlobalFinalizeInput
      projectedMemoryGlobalFinalizeAccess data hint
      (fun row _ => memoryGlobalFinalizeRow_nativeAccesses row data hint)

private theorem active_projectedMemoryGlobalInitAccess_map
    (rows : List (CoreAIR.Current.Row p .memoryGlobalInit)) :
    LookupAccessList.active (rows.map projectedMemoryGlobalInitAccess) =
      (rows.filter fun row => decide (row.main.values[23] ≠ 0)).map
        projectedMemoryGlobalInitAccess := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons, LookupAccessList.active_cons, ih,
      projectedMemoryGlobalInitAccess, Extracted.Interaction.toAccess,
      Extracted.Dir.sign, LookupAccessList.multOf]
    have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
    rw [signedVal_neg hp]
    by_cases h : row.main.values[23] = 0
    · simp [h, signedVal_eq_zero_iff]
    · simp [h, signedVal_eq_zero_iff]
      unfold projectedMemoryGlobalInitAccess
      simp only [Extracted.Interaction.toAccess, Extracted.Dir.sign]
      rw [signedVal_neg hp]
      simp only [ZMod.val_zero]

omit [Fact (2 ^ 24 < p)] in
private theorem active_projectedMemoryGlobalFinalizeAccess_map
    (rows : List (CoreAIR.Current.Row p .memoryGlobalFinalize)) :
    LookupAccessList.active (rows.map projectedMemoryGlobalFinalizeAccess) =
      (rows.filter fun row => decide (row.main.values[23] ≠ 0)).map
        projectedMemoryGlobalFinalizeAccess := by
  induction rows with
  | nil => rfl
  | cons row rest ih =>
    simp only [List.map_cons, LookupAccessList.active_cons, ih,
      projectedMemoryGlobalFinalizeAccess, Extracted.Interaction.toAccess,
      Extracted.Dir.sign, LookupAccessList.multOf]
    by_cases h : row.main.values[23] = 0
    · simp [h, signedVal_eq_zero_iff]
    · simp [h, signedVal_eq_zero_iff]
      rfl

/-- **Exact memory-boundary access transport after the explicit Global→Memory lowering.**  The two
native tables emit precisely the active target side of `memoryBoundaryAccessLowerings`.  Padding
rows are erased by `signedVal_eq_zero_iff`; no balance or final-state premise is assumed. -/
theorem extractedMemoryBoundaryTables_activeAccesses
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    LookupAccessList.active
        ((extractedMemoryBoundaryTables witness data hint).flatMap tableNativeAccesses) =
      LookupAccessList.active (projectedMemoryBoundaryProviderAccesses witness) := by
  simp only [extractedMemoryBoundaryTables, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, transportMemoryInitTable_accesses,
    transportMemoryFinalizeTable_accesses, projectedMemoryBoundaryProviderAccesses_eq,
    LookupAccessList.active, List.filter_append]
  change
    LookupAccessList.active
        ((activeMemoryGlobalInitRows witness).map projectedMemoryGlobalInitAccess) ++
      LookupAccessList.active
        ((activeMemoryGlobalFinalizeRows witness).map projectedMemoryGlobalFinalizeAccess) =
    LookupAccessList.active
        ((witness.trace.rows .memoryGlobalInit).map projectedMemoryGlobalInitAccess) ++
      LookupAccessList.active
        ((witness.trace.rows .memoryGlobalFinalize).map projectedMemoryGlobalFinalizeAccess)
  rw [active_projectedMemoryGlobalInitAccess_map,
    active_projectedMemoryGlobalFinalizeAccess_map,
    active_projectedMemoryGlobalInitAccess_map,
    active_projectedMemoryGlobalFinalizeAccess_map]
  simp only [activeMemoryGlobalInitRows, activeMemoryGlobalFinalizeRows,
    List.filter_filter, Bool.and_self]

end SP1Clean.Composition
