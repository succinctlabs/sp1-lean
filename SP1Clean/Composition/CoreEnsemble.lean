import SP1Clean.Composition.Extracted
import SP1Clean.Composition.ProviderSegment
import ToClean.Air.EnsembleBuild
import SP1Clean.Soundness.EnsembleLookups

/-! # Exact Core rows assembled as a canonical native witness

Whole-chip faithfulness transports 25 instruction tables; the exact memory-boundary witness and
preprocessing inventory supply 30 provider/system tables. The canonical Clean witness derives
its data from those 55 physical tables and evaluates the public verifier separately. Generation
data supplies row builders only. Provider demand is recounted from the actual verifier and
physical consumer ledgers, preserving repeated and zero-multiplicity occurrences.

`exactNativeBoundary` reverses upstream W3 timestamp limbs into native low-to-high order and
retains PC and terminal cells. `ExactNativeBoundaryContract` supplies the source range facts for
the verifier's semantic specification. Native U8 operand order matches the source; native
Range16 requests differ from the source's Range13 requests for `(limb - 1) / 8`.

This module proves physical constraints and Byte/Program recount balance under the existing
transport contracts. Full channel balance, authenticated program/boundary binding and exact
source-to-native range redistribution remain separate integration obligations.
-/

set_option autoImplicit false

namespace SP1Clean.Composition

open SP1Clean.Faithful

open Circuit
open Air.Flat (EnsembleWitness Table)
open SP1Clean.LookupAccessList (LookupKey)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance coreEnsembleFieldBound : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-! ## Public-boundary projection -/

/-- Project the exact shard public values onto the native boundary carrier: the fourteen
State-endpoint limbs consumed by the boundary verifier plus the three terminal-cell mirrors
(`exit_code`, `is_execution_shard`, the flattened digest).

The timestamp reversal is load-bearing: upstream W3 is `(bits 32..48, 24..32, 16..24, 0..16)`,
whereas `SP1StateBoundary` names `(0..16, 16..24, 24..32, 32..48)`.  The pc vectors already use
the native low-to-high limb order; the terminal cells are copied verbatim. -/
def exactNativeBoundary (publicValues : SP1PublicValues (ZMod p)) : SP1PublicIO (ZMod p) where
  init_clk_0_16 := publicValues.initial_timestamp[3]
  init_clk_16_24 := publicValues.initial_timestamp[2]
  init_clk_24_32 := publicValues.initial_timestamp[1]
  init_clk_32_48 := publicValues.initial_timestamp[0]
  init_pc0 := publicValues.pc_start[0]
  init_pc1 := publicValues.pc_start[1]
  init_pc2 := publicValues.pc_start[2]
  final_clk_0_16 := publicValues.last_timestamp[3]
  final_clk_16_24 := publicValues.last_timestamp[2]
  final_clk_24_32 := publicValues.last_timestamp[1]
  final_clk_32_48 := publicValues.last_timestamp[0]
  final_pc0 := publicValues.next_pc[0]
  final_pc1 := publicValues.next_pc[1]
  final_pc2 := publicValues.next_pc[2]
  exit_code := publicValues.exit_code
  is_execution_shard := publicValues.is_execution_shard
  committed_value_digest := publicValues.committed_value_digest.flatten

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The native verifier's initial U8 pair has the exact public-value interaction's operand order.
This regression prevents the two individually range-valid timestamp bytes from being silently
reversed at the balance boundary. -/
@[simp] theorem exactNativeBoundary_init_u8Pair
    (publicValues : SP1PublicValues (ZMod p)) :
    ((exactNativeBoundary publicValues).init_clk_24_32,
      (exactNativeBoundary publicValues).init_clk_16_24) =
      (publicValues.initial_timestamp[1], publicValues.initial_timestamp[2]) := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- Final-boundary counterpart of `exactNativeBoundary_init_u8Pair`. -/
@[simp] theorem exactNativeBoundary_final_u8Pair
    (publicValues : SP1PublicValues (ZMod p)) :
    ((exactNativeBoundary publicValues).final_clk_24_32,
      (exactNativeBoundary publicValues).final_clk_16_24) =
      (publicValues.last_timestamp[1], publicValues.last_timestamp[2]) := rfl

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
/-- The three terminal cells are copied verbatim from the exact record — the anchor a re-pin's
layout change would trip. -/
@[simp] theorem exactNativeBoundary_terminalCells
    (publicValues : SP1PublicValues (ZMod p)) :
    ((exactNativeBoundary publicValues).exit_code,
      (exactNativeBoundary publicValues).is_execution_shard,
      (exactNativeBoundary publicValues).committed_value_digest) =
      (publicValues.exit_code, publicValues.is_execution_shard,
        publicValues.committed_value_digest.flatten) := rfl

omit [Fact (2 ^ 24 < p)] in
/-- Recombination after the W3 reversal is the exact high-clock expression emitted by the
upstream public-value State interaction. -/
@[simp] theorem exactNativeBoundary_init_clk_high
    (publicValues : SP1PublicValues (ZMod p)) :
    (exactNativeBoundary publicValues).init_clk_high =
      publicValues.initial_timestamp[1] + publicValues.initial_timestamp[0] * 256 := rfl

omit [Fact (2 ^ 24 < p)] in
/-- Recombination after the W3 reversal is the exact low-clock expression emitted by the
upstream public-value State interaction. -/
@[simp] theorem exactNativeBoundary_init_clk_low
    (publicValues : SP1PublicValues (ZMod p)) :
    (exactNativeBoundary publicValues).init_clk_low =
      publicValues.initial_timestamp[3] + publicValues.initial_timestamp[2] * 65536 := rfl

omit [Fact (2 ^ 24 < p)] in
/-- Final-boundary high-clock counterpart of `exactNativeBoundary_init_clk_high`. -/
@[simp] theorem exactNativeBoundary_final_clk_high
    (publicValues : SP1PublicValues (ZMod p)) :
    (exactNativeBoundary publicValues).final_clk_high =
      publicValues.last_timestamp[1] + publicValues.last_timestamp[0] * 256 := rfl

omit [Fact (2 ^ 24 < p)] in
/-- Final-boundary low-clock counterpart of `exactNativeBoundary_init_clk_low`. -/
@[simp] theorem exactNativeBoundary_final_clk_low
    (publicValues : SP1PublicValues (ZMod p)) :
    (exactNativeBoundary publicValues).final_clk_low =
      publicValues.last_timestamp[3] + publicValues.last_timestamp[2] * 65536 := rfl

/-- The exact source-side range facts needed by the native boundary verifier, and no unrelated
public-value condition.  The exact public-value block justifies these through its Byte/Range
interactions (and, for the low timestamp limbs, the accompanying `8 * range13 + 1` equations);
deriving them from exact balance and PCS-authenticated preprocessing is a later global transport
theorem. -/
structure ExactNativeBoundaryContract (publicValues : SP1PublicValues (ZMod p)) : Prop where
  /-- Canonical upstream W3 encoding of the initial timestamp. -/
  initialTimestamp : publicValues.initial_timestamp.WellFormed
  /-- Canonical three-limb encoding of the initial pc. -/
  pcStart : publicValues.pc_start.WellFormed
  /-- Canonical upstream W3 encoding of the final timestamp. -/
  lastTimestamp : publicValues.last_timestamp.WellFormed
  /-- Canonical three-limb encoding of the final pc. -/
  nextPc : publicValues.next_pc.WellFormed

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem word48_getElem_bound (word : SP1Word48 (ZMod p))
    (wellFormed : word.WellFormed) (i : ℕ) (hi : i < 3) :
    word[i].val < 2 ^ 16 := by
  apply wellFormed word[i]
  change word.toList[i]'(by simpa) ∈ word.toList
  exact List.getElem_mem (by simpa using hi)

omit [Fact (2 ^ 24 < p)] in
/-- The source-native range contract is exactly sufficient for the native verifier's
`SP1StateBoundary.LimbBounds` contract. -/
theorem exactNativeBoundary_limbBounds (publicValues : SP1PublicValues (ZMod p))
    (contract : ExactNativeBoundaryContract publicValues) :
    (exactNativeBoundary publicValues).LimbBounds := by
  exact ⟨contract.initialTimestamp.2.2.2,
    contract.initialTimestamp.2.2.1,
    contract.initialTimestamp.2.1,
    contract.initialTimestamp.1,
    word48_getElem_bound publicValues.pc_start contract.pcStart 0 (by omega),
    word48_getElem_bound publicValues.pc_start contract.pcStart 1 (by omega),
    word48_getElem_bound publicValues.pc_start contract.pcStart 2 (by omega),
    contract.lastTimestamp.2.2.2,
    contract.lastTimestamp.2.2.1,
    contract.lastTimestamp.2.1,
    contract.lastTimestamp.1,
    word48_getElem_bound publicValues.next_pc contract.nextPc 0 (by omega),
    word48_getElem_bound publicValues.next_pc contract.nextPc 1 (by omega),
    word48_getElem_bound publicValues.next_pc contract.nextPc 2 (by omega)⟩

/-! ## Acyclic native-consumer skeleton -/

/-- The actual public verifier's complete ordered access ledger at an explicit data environment. -/
def exactNativeVerifierLedger {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest) (data : ProverData (ZMod p)) : LookupAccessList :=
  ((Soundness.sp1Ensemble (p := p)).verifierOperations.interactionValues
    (Environment.fromInput (exactNativeBoundary statement.publicValues) data)).map Interaction.toAccess

/-- Public verifier interactions depend on public cells, not row-generation metadata. -/
theorem exactNativeVerifierLedger_setData {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest) (data data' : ProverData (ZMod p)) :
    exactNativeVerifierLedger statement data = exactNativeVerifierLedger statement data' := by
  apply congrArg (List.map Interaction.toAccess)
  exact Operations.interactionValues_congr
    (env := Environment.fromInput (exactNativeBoundary statement.publicValues) data)
    (env' := Environment.fromInput (exactNativeBoundary statement.publicValues) data') rfl

/-- Public verifier and physical consumer demand, including the transported instructions,
memory boundaries, both bumps, Halt padding and the empty syscall table. Preprocessed providers
are absent, so their recounted multiplicities do not depend on themselves. -/
def exactNativeSkeletonLedger {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : LookupAccessList :=
  exactNativeVerifierLedger statement data ++
    tablesCleanAccesses ((extractedInstructionRows executionWitness).transported data) data ++
    tablesCleanAccesses (extractedMemoryBoundaryTables memoryBoundaryWitness data hint) data ++
    tablesCleanAccesses (extractedBumpTables executionWitness data) data

/-! ## 55-table assembly -/

/-- The transported instruction segment followed by thirty reconstructed provider/system
tables whose preprocessing multiplicities recount the literal non-preprocessed skeleton. -/
def exactNativeTables {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : List (Table (ZMod p)) :=
  (extractedInstructionRows executionWitness).transported data ++
    exactProviderTables executionWitness memoryBoundaryWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint)
      data hint

/-- The assembled exact/native tables align component-for-component with the complete native
55-table ensemble. -/
theorem exactNativeTables_components {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (exactNativeTables statement executionWitness memoryBoundaryWitness inventory data hint).map
        (fun table => table.component) =
      (Soundness.sp1Ensemble (p := p)).tables := by
  simp only [exactNativeTables, List.map_append,
    ExtractedInstructionRows.transported_map_component,
    exactProviderTables_components, Soundness.sp1Ensemble_tables]

/-- Exact relations and the explicit native transport contract yield all 55
constraint-satisfying native ensemble tables (the public verifier is evaluated separately). -/
theorem exactNativeTables_constraints {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (contract : ExactProviderTransportContract binds statement
      executionWitness memoryBoundaryWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint)) :
    ∀ table ∈ exactNativeTables statement executionWitness memoryBoundaryWitness inventory data hint,
      table.Constraints data := by
  intro table tableMem
  simp only [exactNativeTables, List.mem_append] at tableMem
  rcases tableMem with tableMem | tableMem
  · exact extracted_instructionTables_constraints statement executionWitness
      contract.executionRelation data table tableMem
  · exact exactProviderTables_constraints statement executionWitness memoryBoundaryWitness
      inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint)
      data hint contract table tableMem

/-! ## Native ensemble witness and constraints -/

/-- The structural native `EnsembleWitness` assembled from the exact rows and projected boundary. -/
def exactNativeEnsembleWitness {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    EnsembleWitness (Soundness.sp1Ensemble (p := p)) :=
  EnsembleWitness.ofTables _
    (exactNativeTables statement executionWitness memoryBoundaryWitness inventory data hint)
    (exactNativeBoundary statement.publicValues)
    (exactNativeTables_components statement executionWitness memoryBoundaryWitness inventory data hint)

@[simp] theorem exactNativeEnsembleWitness_tables {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint).tables =
      exactNativeTables statement executionWitness memoryBoundaryWitness inventory data hint := rfl

@[simp] theorem exactNativeEnsembleWitness_publicInput {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint).publicInput =
      exactNativeBoundary statement.publicValues := rfl

/-- The source endpoint range contract proves the public verifier's semantic specification. -/
theorem exactNativeEnsembleWitness_verifierSpec {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (boundary : ExactNativeBoundaryContract statement.publicValues) :
    (Soundness.sp1Ensemble (p := p)).VerifierSpec
      (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint).publicInput
      (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint).data :=
  exactNativeBoundary_limbBounds statement.publicValues boundary

/-- **Given the explicit transport contracts, the selected exact rows satisfy the native ensemble's
physical constraints at canonical data.** The public verifier contributes channel obligations
separately. -/
theorem exactNativeEnsembleWitness_constraints {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (transport : ExactProviderTransportContract binds statement
      executionWitness memoryBoundaryWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint)) :
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
      ).Constraints := by
  intro table member row rowMem
  apply Soundness.sp1Table_constraints_setData table.component
    (EnsembleWitness.mem_component_of_mem (witness :=
      exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint) member)
    (data := data)
  exact exactNativeTables_constraints statement executionWitness memoryBoundaryWitness
    inventory data hint transport table member row rowMem

/-! ## Literal Clean ledger and recount payoff -/

/-- The actual verifier and physical-table ledger of the constructed canonical witness. -/
def exactNativeAllCleanAccesses {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : LookupAccessList :=
  (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
    ).interactions.map Interaction.toAccess

/-- The literal full access ledger is exactly the `Interaction.toAccess` image of the constructed
ensemble witness's evaluated interactions.  This structural equation is the bridge used to turn
the Byte/Program recount theorem into per-channel Clean balance; it performs no Rust-facing sign
dualization. -/
theorem exactNativeAllCleanAccesses_eq_interactions {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    exactNativeAllCleanAccesses statement executionWitness memoryBoundaryWitness inventory data hint =
      (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
        ).interactions.map Interaction.toAccess := rfl

/-- The actual full native ledger permutes to the acyclic skeleton followed by its recounted
preprocessed provider ledger. -/
theorem exactNativeAllCleanAccesses_perm {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (recount : PreprocessedProviderRecountContract executionWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint)) :
    List.Perm
      (exactNativeAllCleanAccesses statement executionWitness memoryBoundaryWitness inventory data hint)
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint ++
        recountedPreprocessedProviderAccesses inventory
          (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint)) := by
  let witness := exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
  rw [exactNativeAllCleanAccesses, EnsembleWitness.interactions, List.map_append,
    List.map_flatMap]
  change (exactNativeVerifierLedger statement witness.data ++
    tablesCleanAccesses (exactNativeTables statement executionWitness memoryBoundaryWitness inventory data hint)
      witness.data).Perm _
  rw [exactNativeVerifierLedger_setData statement witness.data data,
    tablesCleanAccesses_setData _ witness.data data]
  rw [exactNativeTables, tablesCleanAccesses_append,
    exactProviderTables_cleanAccesses executionWitness memoryBoundaryWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint)
      data hint recount]
  simp only [tablesCleanAccesses]
  let consumerHead : LookupAccessList :=
    exactNativeVerifierLedger statement data ++
    ((extractedInstructionRows executionWitness).transported data).flatMap (fun table => tableCleanAccesses table data)
  let providerLedger : LookupAccessList := recountedPreprocessedProviderAccesses inventory
    (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint)
  let systemTail : LookupAccessList :=
    (extractedMemoryBoundaryTables memoryBoundaryWitness data hint).flatMap (fun table => tableCleanAccesses table data) ++
      (extractedBumpTables executionWitness data).flatMap (fun table => tableCleanAccesses table data)
  refine List.Perm.trans (l₂ := consumerHead ++ (providerLedger ++ systemTail))
    (List.Perm.of_eq ?_) ?_
  · simp only [consumerHead, providerLedger, systemTail, List.append_assoc]
  refine List.Perm.trans (l₂ := consumerHead ++ (systemTail ++ providerLedger))
    ((List.perm_append_comm (l₁ := providerLedger) (l₂ := systemTail)).append_left
      consumerHead) (List.Perm.of_eq ?_)
  simp only [consumerHead, providerLedger, systemTail, exactNativeSkeletonLedger,
    tablesCleanAccesses, List.append_assoc]

/-- Recounting closes the integer balance equation for every Byte/Program-kind key of the actual
constructed native ledger.  State and Memory are intentionally outside this theorem. -/
theorem exactNativeAllCleanAccesses_preprocessedBalance {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (recount : PreprocessedProviderRecountContract executionWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint))
    (key : LookupKey) (keyKind : IsPreprocessedProviderKey key) :
    LookupAccessList.multiplicitySum
        (exactNativeAllCleanAccesses statement executionWitness memoryBoundaryWitness inventory data hint)
        key = 0 := by
  rw [LookupAccessList.multiplicitySum_perm _ _
    (exactNativeAllCleanAccesses_perm statement executionWitness memoryBoundaryWitness inventory
      data hint recount) key]
  exact skeleton_append_recountedPreprocessedProviderAccesses_balanced recount key keyKind

end SP1Clean.Composition
