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
coverage claim.

`Cluster.tables_nodup` and the paired `System.shardRelation` are part of the reserved
exact-AIR/ArkLib composition API: declared ahead of the `CoreAIRRefinementObligations` closure that
consumes them. -/

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
  cases cluster <;> simp only [Cluster.tables, coreCluster_nodup, memoryBoundaryCluster_nodup]

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

/-- The exact proof-free witness of one Core shard consists of both upstream clusters.  Keeping the
pair in one carrier prevents an AIR refinement or ArkLib extractor from authenticating execution
rows while silently omitting the six memory-boundary tables. -/
structure ShardWitness {Public : Type} (system : System Public) where
  execution : Witness system.Row
  memoryBoundary : Witness system.Row

/-- Exact paired 34+6-table relation for a Core shard. -/
def System.shardRelation {Public : Type} (system : System Public) :
    WitnessRelation.Relation Public (ShardWitness system) :=
  fun statement witness =>
    system.relationFor .execution statement witness.execution ∧
      system.relationFor .memoryBoundary statement witness.memoryBoundary

theorem System.execution_of_shardRelation {Public : Type} {system : System Public}
    {statement : Public} {witness : ShardWitness system}
    (valid : system.shardRelation statement witness) :
    system.relationFor .execution statement witness.execution :=
  valid.1

theorem System.memoryBoundary_of_shardRelation {Public : Type} {system : System Public}
    {statement : Public} {witness : ShardWitness system}
    (valid : system.shardRelation statement witness) :
    system.relationFor .memoryBoundary statement witness.memoryBoundary :=
  valid.2

/-- Recover one table row's complete local validity directly from a cluster-restricted relation.
This is the shared elimination rule for exact-row consumers: they should not depend on the nested
conjunction layout of `System.relation`/`relationFor`. -/
theorem System.localValid_of_relationFor {Public : Type} {system : System Public}
    {cluster : Cluster} {statement : Public} {witness : Witness system.Row}
    {table : Table} {row : system.Row table}
    (valid : system.relationFor cluster statement witness)
    (rowMem : row ∈ witness.trace.rows table) :
    system.localValid table statement row :=
  valid.2.2.1 table row rowMem

/-- The extraction adapter is for the exact current semantic source/profile. -/
def System.IsCurrent {Public : Type} (system : System Public) : Prop :=
  system.profile = CoreProfile.current

end SP1Clean.CoreAIR
