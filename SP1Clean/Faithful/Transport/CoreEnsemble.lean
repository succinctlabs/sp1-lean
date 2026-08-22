import SP1Clean.Faithful.Transport.Extracted
import SP1Clean.Faithful.Transport.ProviderSegment
import ToClean.Air.EnsembleBuild

/-! # Exact Core rows assembled as the native fifty-three-table ensemble

This module closes the structural and local-constraint half of the exact-AIR-to-native boundary.
An exact execution-cluster witness supplies the twenty-five instruction tables through the
whole-chip faithfulness transport; that execution witness together with the separate exact
memory-boundary witness supplies the twenty-eight provider/system tables through
`ExactProviderTransportContract` and a caller-supplied, demand-oriented
`CanonicalPreprocessedInventory`.  Appending the two segments produces exactly the fifty-three
components of `Soundness.sp1Ensemble`, all carrying one `ProverData` object.  The inventory is the
explicit efficient-selection endpoint; this module does not run quadratic raw-row deduplication.

The exact public-value timestamp is stored in upstream W3 order (most-significant 16-bit limb
first), while `SP1StateBoundary` names its limbs in ascending order.  `exactNativeBoundary`
performs that reversal explicitly and copies the three pc limbs without reordering.  The exact
AIR exposes range interactions for these fourteen cells, but the derivation of their canonicity
from global balance is not part of the local table transport.  The minimal missing fact is named
by `ExactNativeBoundaryContract`; given it, the native verifier table also satisfies its complete
constraint system. The native verifier emits its U8 pair as `(24..32, 16..24)`, matching the exact
public-value interaction's operand order; the pair's range semantics remain symmetric. The
remaining range seam is not an interaction permutation: for each low timestamp limb the exact
public-value block looks up `(limb - 1) / 8` in Range13, whereas the native verifier looks up the
limb itself in Range16.  A later balance bridge must account for that explicit redistribution.

The resulting `exactNativeEnsembleWitness_constraints` theorem deliberately proves only
`EnsembleWitness.Constraints`.  It does not claim `BalancedChannels`, a semantic boundary
binding, `Ensemble.Statement`, or `SupportedCoreNativeRelation`; those are the remaining global
transport/refinement seams.
-/

set_option autoImplicit false

namespace SP1Clean.Faithful.Transport

open Circuit
open Air.Flat (EnsembleWitness Table)
open SP1Clean.LookupAccessList (LookupKey)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance coreEnsembleFieldBound : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-! ## Public-boundary projection -/

/-- Project the exact shard public values onto the fourteen cells consumed by the native
boundary verifier.

The timestamp reversal is load-bearing: upstream W3 is `(bits 32..48, 24..32, 16..24, 0..16)`,
whereas `SP1StateBoundary` names `(0..16, 16..24, 24..32, 32..48)`.  The pc vectors already use
the native low-to-high limb order. -/
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

/-- The verifier table used both by the native witness and by the recount skeleton. -/
def exactNativeVerifierTable {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Table (ZMod p) :=
  Table.build (Soundness.verifierComponent (p := p))
    [exactNativeBoundary statement.publicValues] data hint

/-- Literal Clean ledger of every non-preprocessed native consumer: verifier, twenty-five
transported instruction tables, memory init/finalize, and both bumps.  Preprocessed providers are
absent, so their recounted multiplicities do not recursively depend on themselves. -/
def exactNativeSkeletonLedger {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : LookupAccessList :=
  tableCleanAccesses (exactNativeVerifierTable statement data hint) ++
    tablesCleanAccesses ((extractedInstructionRows executionWitness).transported data) ++
    tablesCleanAccesses (extractedMemoryBoundaryTables memoryBoundaryWitness data hint) ++
    tablesCleanAccesses (extractedBumpTables executionWitness data)

/-! ## Fifty-three-table assembly -/

/-- The transported instruction segment followed by twenty-eight reconstructed provider/system
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
fifty-three-table ensemble. -/
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

/-- Every assembled table carries the one committed prover-data object. -/
theorem exactNativeTables_data {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ table ∈ exactNativeTables statement executionWitness memoryBoundaryWitness inventory data hint,
      table.data = data := by
  intro table tableMem
  simp only [exactNativeTables, List.mem_append] at tableMem
  rcases tableMem with tableMem | tableMem
  · exact ExtractedInstructionRows.transported_data
      (extractedInstructionRows executionWitness) data table tableMem
  · exact exactProviderTables_data executionWitness memoryBoundaryWitness
      inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint)
      data hint table tableMem

/-- The full fifty-three-table list as Clean's shared-data `Tables` package. -/
def exactNativeTableBundle {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Air.Flat.Tables (ZMod p) where
  tables := exactNativeTables statement executionWitness memoryBoundaryWitness inventory data hint
  data := data
  same_data := exactNativeTables_data statement executionWitness memoryBoundaryWitness inventory data hint

/-- The shared-data bundle carries exactly the complete native ensemble component list. -/
theorem exactNativeTableBundle_components {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (exactNativeTableBundle statement executionWitness memoryBoundaryWitness inventory data hint).components =
      (Soundness.sp1Ensemble (p := p)).tables :=
  exactNativeTables_components statement executionWitness memoryBoundaryWitness inventory data hint

/-- Exact relations and the explicit native transport contract yield all fifty-three
constraint-satisfying native ensemble tables (excluding the separately built verifier row). -/
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
      table.Constraints := by
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
    (exactNativeTables statement executionWitness memoryBoundaryWitness inventory data hint) data
    (exactNativeBoundary statement.publicValues)
    (exactNativeTables_components statement executionWitness memoryBoundaryWitness inventory data hint)
    (exactNativeTables_data statement executionWitness memoryBoundaryWitness inventory data hint)

@[simp] theorem exactNativeEnsembleWitness_tables {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint).tables =
      exactNativeTables statement executionWitness memoryBoundaryWitness inventory data hint := rfl

@[simp] theorem exactNativeEnsembleWitness_data {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint).data =
      data := rfl

@[simp] theorem exactNativeEnsembleWitness_publicInput {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint).publicInput =
      exactNativeBoundary statement.publicValues := rfl

/-- The assembled witness's verifier row is exactly the table used in the skeleton recount. -/
theorem exactNativeEnsembleWitness_verifierTable {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
      ).verifierTable = exactNativeVerifierTable statement data hint :=
  Air.Flat.verifierTable_eq_build _ _

/-- **Given the explicit transport contracts, the selected exact rows satisfy the native ensemble's
complete local constraint system.**  This includes the twenty-five transported instructions, all
twenty-eight providers, and the verifier row. -/
theorem exactNativeEnsembleWitness_constraints {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (transport : ExactProviderTransportContract binds statement
      executionWitness memoryBoundaryWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint))
    (boundary : ExactNativeBoundaryContract statement.publicValues) :
    (exactNativeEnsembleWitness statement executionWitness memoryBoundaryWitness inventory data hint
      ).Constraints := by
  rw [EnsembleWitness.Constraints]
  intro table tableMem
  simp only [EnsembleWitness.allTables, List.mem_cons] at tableMem
  rcases tableMem with rfl | tableMem
  · rw [exactNativeEnsembleWitness_verifierTable]
    exact Soundness.verifierTable_constraints _ _ _ fun publicInput publicInputMem => by
      rw [List.mem_singleton.mp publicInputMem]
      exact exactNativeBoundary_limbBounds statement.publicValues boundary
  · exact exactNativeTables_constraints statement executionWitness memoryBoundaryWitness
      inventory data hint transport table tableMem

/-! ## Literal Clean ledger and recount payoff -/

/-- Literal access ledger of every table in the constructed witness, verifier included. -/
def exactNativeAllCleanAccesses {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : LookupAccessList :=
  tableCleanAccesses (exactNativeVerifierTable statement data hint) ++
    tablesCleanAccesses
      (exactNativeTables statement executionWitness memoryBoundaryWitness inventory data hint)

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
        ).interactions.map Interaction.toAccess := by
  simp only [exactNativeAllCleanAccesses, EnsembleWitness.interactions,
    EnsembleWitness.allTables, List.flatMap_cons, List.map_append, List.map_flatMap,
    tableCleanAccesses, tablesCleanAccesses,
    exactNativeEnsembleWitness_tables]
  rw [exactNativeEnsembleWitness_verifierTable]
  apply congrArg (fun tail : LookupAccessList =>
    (exactNativeVerifierTable statement data hint).interactions.map Interaction.toAccess ++ tail)
  apply List.flatMap_congr
  intro table tableMem
  rfl

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
  rw [exactNativeAllCleanAccesses, exactNativeTables, tablesCleanAccesses_append,
    exactProviderTables_cleanAccesses executionWitness memoryBoundaryWitness inventory
      (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint)
      data hint recount]
  simp only [tablesCleanAccesses]
  let consumerHead : LookupAccessList :=
    tableCleanAccesses (exactNativeVerifierTable statement data hint) ++
    ((extractedInstructionRows executionWitness).transported data).flatMap tableCleanAccesses
  let providerLedger : LookupAccessList := recountedPreprocessedProviderAccesses inventory
    (exactNativeSkeletonLedger statement executionWitness memoryBoundaryWitness data hint)
  let systemTail : LookupAccessList :=
    (extractedMemoryBoundaryTables memoryBoundaryWitness data hint).flatMap tableCleanAccesses ++
      (extractedBumpTables executionWitness data).flatMap tableCleanAccesses
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

end SP1Clean.Faithful.Transport
