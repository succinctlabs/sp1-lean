import SP1Clean.FormalModel.CoreProfile
import SP1Clean.FormalModel.Relations
import SP1Clean.Model.Machine.Syscall

/-! # Exact-table Core AIR relation

This is the relation-level adapter between generated table oracles and semantic refinement.  It does
not invent another constraint language: each table adapter supplies its extracted row predicate, and
one global predicate supplies precisely the transition, public-value, and interaction-balance checks
of the upstream AIR instance.

The active table list is witness data but must equal one of the two pinned Rust clusters.  This makes
omitting a hard table, or quietly adding a helper table, a failed equality rather than an informal
coverage claim. -/

namespace SP1Clean.CoreAIR

open SP1Clean.CoreProfile

/-- The two baseline trusted clusters proved by the Core workstream. -/
inductive Cluster
  | execution
  | memoryBoundary
deriving DecidableEq, Repr

/-- Exact active-table set for a cluster at the current Rust pin. -/
def Cluster.tables : Cluster → List Table
  | .execution => coreCluster
  | .memoryBoundary => memoryBoundaryCluster

theorem Cluster.tables_nodup (cluster : Cluster) : cluster.tables.Nodup := by
  cases cluster <;> simp only [Cluster.tables, coreCluster_nodup,
    memoryBoundaryCluster_nodup]

/-- Heterogeneous trace matrices indexed by the audited table enum. -/
structure TableTrace (Row : Table → Type) where
  rows : (table : Table) → List (Row table)

/-- AIR witness for exactly one upstream cluster.  Inactive tables have no hidden rows. -/
structure Witness (Row : Table → Type) where
  cluster : Cluster
  activeTables : List Table
  trace : TableTrace Row

/-- Shape validity is independent of algebraic validity and can be audited before opening any row
proof.  Every active upstream table has a nonempty padded evaluation domain; permitting an empty
active trace here would make all of its row constraints and interactions vacuous.  Exact domain
sizes remain proof-system data, while inactive tables are required to contain no hidden rows. -/
def Witness.WellShaped {Row : Table → Type} (witness : Witness Row) : Prop :=
  witness.activeTables = witness.cluster.tables ∧
    (∀ table ∈ witness.activeTables, witness.trace.rows table ≠ []) ∧
    ∀ table, table ∉ witness.activeTables → witness.trace.rows table = []

/-- Adapter supplied by faithful extraction of every table in the profile.

`localValid` is the conjunction of the table's complete extracted `assertZero` system on a row.
`globalValid` contains only facts that intrinsically mention several rows/tables: transition
constraints, public-value checks, and local/global interaction balance. -/
structure System (Public : Type) where
  profile : Profile
  Row : Table → Type
  localValid : (table : Table) → Public → Row table → Prop
  globalValid : Public → Witness Row → Prop

/-- Total decoder for raw syscall events.  Like a functional refinement map, it reads only the
statement and witness; AIR validity is used later to prove facts about the decoded events. -/
structure EventDecoder {Public : Type} (system : System Public) where
  syscallEvents : Public → Witness system.Row → List Machine.CoreSyscallEvent

/-- The honest AIR witness relation induced by a table system. -/
def System.relation {Public : Type} (system : System Public) :
    WitnessRelation.Relation Public (Witness system.Row) :=
  fun statement witness =>
    witness.WellShaped ∧
      (∀ table row, row ∈ witness.trace.rows table →
        system.localValid table statement row) ∧
      system.globalValid statement witness

/-- Restrict a system relation to one exact upstream cluster.

This guard is semantically necessary: the execution and memory-boundary clusters share a row
universe, but a valid memory-boundary proof is not an execution-shard witness.  A refinement theorem
must name which cluster it consumes rather than recover that choice from proof data. -/
def System.relationFor {Public : Type} (system : System Public) (cluster : Cluster) :
    WitnessRelation.Relation Public (Witness system.Row) :=
  fun statement witness => witness.cluster = cluster ∧ system.relation statement witness

/-- The extraction adapter is for the exact current semantic source/profile. -/
def System.IsCurrent {Public : Type} (system : System Public) : Prop :=
  system.profile = CoreProfile.current

/-- Constructive, profile-checked refinement from exact extracted tables to a semantic relation.
This is the object the ArkLib AIR extractor should post-compose with. -/
structure TableRefinement {Public ExecutionWitness : Type} (system : System Public)
    (cluster : Cluster)
    (execution : WitnessRelation.Relation Public ExecutionWitness) where
  currentProfile : system.IsCurrent
  refinement : WitnessRelation.FunctionalRefinement (system.relationFor cluster) execution

/-- Forget table/profile metadata and recover ordinary witness-producing soundness. -/
theorem TableRefinement.sound {Public ExecutionWitness : Type} {system : System Public}
    {cluster : Cluster}
    {execution : WitnessRelation.Relation Public ExecutionWitness}
    (refinement : TableRefinement system cluster execution) :
    WitnessRelation.Sound (system.relationFor cluster) execution :=
  refinement.refinement.sound

end SP1Clean.CoreAIR
