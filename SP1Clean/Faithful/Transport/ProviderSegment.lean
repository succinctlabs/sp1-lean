import SP1Clean.Faithful.Transport.MemoryBoundary
import SP1Clean.Faithful.Transport.PreprocessedProviders
import SP1Clean.Faithful.Transport.SystemTables

/-! # Exact Core rows as the native twenty-eight-table provider segment

The native Core ensemble has twenty-eight non-instruction tables: six Byte providers, all
seventeen fixed-width Range providers, Program, memory init/finalize, and the Memory/State bump
tables.  Caller-supplied exact Core execution and memory-boundary relations constrain the source
rows under an explicit preprocessing-opening predicate, but
the exact Byte/Range/Program main multiplicities are not the multiplicities of this reduced native
ensemble: exact system consumers omitted from the native slice would otherwise leave it unbalanced.

`ExactProviderTransportContract` therefore receives the literal Clean ledger of an acyclic
non-preprocessed skeleton.  Its preprocessing field proves the provider keys' local meaning and
records the recount obligations.  A separate Type-valued inventory supplies source-backed,
projected-key-unique
representatives for nonzero demand without materializing the raw preprocessing universe; the proof
contract explicitly states demand coverage, sign, and centered-count facts.  The constructed
provider rows use
`Int.toNat (-multiplicitySum skeleton key)`; no theorem below equates them with exact source main
columns.

Memory boundary semantics remain a separate explicit lowering contract.  The execution and
memory-boundary relations discharge the local constraints of the bump and boundary tables,
respectively.  This module constructs and validates all twenty-eight provider tables, and states
their literal Clean ledger as recounted preprocessing followed by the actual boundary/bump ledgers.
-/

set_option autoImplicit false

namespace SP1Clean.Faithful.Transport

open Circuit
open Air.Flat (Table)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance providerSegmentFieldBound : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Exact/local premises for constructing the complete native provider segment at one explicitly
chosen non-preprocessed Clean skeleton.  The recount fields are global AIR/ArkLib translation
obligations, not consequences of local provider assertions. -/
structure ExactProviderTransportContract {Digest : Type}
    (binds : CoreAIR.Current.PreprocessedBinding p Digest)
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (skeleton : LookupAccessList) : Prop where
  /-- Exact validity of the 34-table execution cluster. -/
  executionRelation :
    CoreAIR.Current.Relation binds .execution statement executionWitness
  /-- Exact validity of the separate six-table memory-boundary cluster. -/
  memoryBoundaryRelation :
    CoreAIR.Current.Relation binds .memoryBoundary statement memoryBoundaryWitness
  /-- Source-row local semantics plus the explicit native recount obligations. -/
  preprocessing : PreprocessedProviderRecountContract executionWitness inventory skeleton
  /-- Cross-table word/timestamp facts for active MemoryGlobalInit/Finalize rows. -/
  boundarySemantics : MemoryBoundarySemanticContract memoryBoundaryWitness

/-- All twenty-eight reconstructed provider/system tables in `sp1ProviderTables` order. -/
def exactProviderTables
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : List (Table (ZMod p)) :=
  extractedPreprocessedProviderTables executionWitness inventory skeleton data hint ++
    extractedMemoryBoundaryTables memoryBoundaryWitness data hint ++
      extractedBumpTables executionWitness data

/-- The construction lands component-for-component on the native ensemble's provider segment. -/
theorem exactProviderTables_components
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (exactProviderTables executionWitness memoryBoundaryWitness inventory skeleton data hint).map
        (fun table => table.component) =
      Soundness.sp1ProviderTables := by
  simp only [exactProviderTables, List.map_append,
    extractedPreprocessedProviderTables_components,
    extractedMemoryBoundaryTables_components, extractedBumpTables_components]
  rfl

/-- Every reconstructed provider table carries the same committed prover data. -/
theorem exactProviderTables_data
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    ∀ table ∈ exactProviderTables executionWitness memoryBoundaryWitness inventory skeleton data hint,
      table.data = data := by
  intro table tableMem
  simp only [exactProviderTables, List.mem_append] at tableMem
  rcases tableMem with (tableMem | tableMem) | tableMem
  · exact extractedPreprocessedProviderTables_data executionWitness inventory skeleton data hint
      table tableMem
  · exact extractedMemoryBoundaryTables_data memoryBoundaryWitness data hint table tableMem
  · exact extractedBumpTables_data executionWitness data table tableMem

/-- Shared-data bundle for the native provider segment. -/
def exactProviderTableBundle
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) : Air.Flat.Tables (ZMod p) where
  tables := exactProviderTables executionWitness memoryBoundaryWitness inventory skeleton data hint
  data := data
  same_data := exactProviderTables_data executionWitness memoryBoundaryWitness inventory skeleton data hint

/-- The shared-data bundle has exactly the native provider components. -/
theorem exactProviderTableBundle_components
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (exactProviderTableBundle executionWitness memoryBoundaryWitness inventory skeleton data hint).components =
      Soundness.sp1ProviderTables :=
  exactProviderTables_components executionWitness memoryBoundaryWitness inventory skeleton data hint

/-- **Constructive exact-provider transport.**  The two exact relations plus the explicit native
recount and memory-boundary contracts produce all constraint-satisfying provider/system tables. -/
theorem exactProviderTables_constraints {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (contract : ExactProviderTransportContract binds statement
      executionWitness memoryBoundaryWitness inventory skeleton) :
    ∀ table ∈ exactProviderTables executionWitness memoryBoundaryWitness inventory skeleton data hint,
      table.Constraints := by
  intro table tableMem
  simp only [exactProviderTables, List.mem_append] at tableMem
  rcases tableMem with (tableMem | tableMem) | tableMem
  · exact extractedPreprocessedProviderTables_constraints
      contract.preprocessing.localSemantics inventory skeleton data hint table tableMem
  · exact extractedMemoryBoundaryTables_constraints
      (memoryBoundaryProviderContract_of_relation statement memoryBoundaryWitness
        contract.memoryBoundaryRelation contract.boundarySemantics) data hint table tableMem
  · exact extractedBumpTables_constraints statement executionWitness data
      contract.executionRelation table tableMem

/-- Bundle form of `exactProviderTables_constraints`. -/
theorem exactProviderTableBundle_constraints {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (contract : ExactProviderTransportContract binds statement
      executionWitness memoryBoundaryWitness inventory skeleton) :
    (exactProviderTableBundle executionWitness memoryBoundaryWitness inventory skeleton data hint
      ).Constraints :=
  exactProviderTables_constraints statement executionWitness memoryBoundaryWitness inventory skeleton
    data hint contract

/-- Literal Clean ledger decomposition of the complete provider segment.  The boundary and bump
terms are deliberately left as their actual constructed-table ledgers, with no Rust-facing sign
dualization. -/
theorem exactProviderTables_cleanAccesses
    (executionWitness memoryBoundaryWitness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (inventory : CanonicalPreprocessedInventory executionWitness)
    (skeleton : LookupAccessList)
    (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (recount : PreprocessedProviderRecountContract executionWitness inventory skeleton) :
    tablesCleanAccesses
        (exactProviderTables executionWitness memoryBoundaryWitness inventory skeleton data hint) =
      recountedPreprocessedProviderAccesses inventory skeleton ++
        tablesCleanAccesses (extractedMemoryBoundaryTables memoryBoundaryWitness data hint) ++
        tablesCleanAccesses (extractedBumpTables executionWitness data) := by
  simp only [exactProviderTables, tablesCleanAccesses, List.flatMap_append]
  have preprocessing :=
    extractedPreprocessedProviderTables_cleanAccesses recount data hint
  unfold tablesCleanAccesses at preprocessing
  rw [preprocessing]

end SP1Clean.Faithful.Transport
