import SP1Clean.FormalModel.Contracts.PublicValues
import SP1Clean.FormalModel.CoreAIRRelation

/-! # Explicit semantic premises for the Core AIR

Most semantic facts must be consequences of extracted constraints.  This file isolates the one
temporary upstream fact currently needed by the full public-value theorem: a public commit flag must
have the complete family of introducing syscall rows.  The instruction AIR proves that each such row's
operand equals the corresponding public digest word; the premise below supplies only row provenance
and does not assume those operand equalities.

This is an ordinary theorem parameter, never an axiom, instance, channel guarantee, or per-chip
assumption.  A stronger public-value refinement may take it explicitly; instruction execution
soundness must not. -/

namespace SP1Clean.CoreAIR

open SP1Clean.Machine

/-- Every one of the eight digest indices occurs in a syscall row carrying the exact canonical Rust
code.  Requiring the complete `x5` value is intentional: the instruction AIR recognizes these
operations by byte zero alone, whereas Rust decodes and writes back a concrete `SyscallCode` value.
Duplicate rows are permitted; their values remain constrained by the AIR. -/
def DigestRowsCover (syscallCode : ℕ) (events : List CoreSyscallEvent) : Prop :=
  ∀ index : Fin 8, ∃ event ∈ events,
    event.IsCanonicalCode syscallCode ∧ event.arg1.toNat = index

/-- The shard changes the rolling public-output commit flag from false to true. -/
def PublicCommitIntroduced {p : ℕ} (publicValues : SP1PublicValues (ZMod p)) : Prop :=
  publicValues.prev_commit_syscall = 0 ∧ publicValues.commit_syscall = 1

/-- The shard changes the rolling deferred-digest commit flag from false to true. -/
def DeferredCommitIntroduced {p : ℕ} (publicValues : SP1PublicValues (ZMod p)) : Prop :=
  publicValues.prev_commit_deferred_syscall = 0 ∧
    publicValues.commit_deferred_syscall = 1

/-- The eight canonical COMMIT rows expose exactly the eight public digest words. -/
def PublicDigestRowsMatch {p : ℕ} (publicValues : SP1PublicValues (ZMod p))
    (events : List CoreSyscallEvent) : Prop :=
  ∀ index : Fin 8, ∃ event ∈ events,
    event.IsCanonicalCode commitSyscallId ∧
      event.arg1.toNat = index ∧
      event.arg2 = BitVec.ofNat 64 (publicValues.committed_value_digest[index].toNat)

/-- The eight canonical COMMIT_DEFERRED rows expose exactly the eight field elements of the rolling
deferred-proof digest.  The cast is the `Word.reduce` equation enforced by the row AIR. -/
def DeferredDigestRowsMatch {p : ℕ} (publicValues : SP1PublicValues (ZMod p))
    (events : List CoreSyscallEvent) : Prop :=
  ∀ index : Fin 8, ∃ event ∈ events,
    event.IsCanonicalCode commitDeferredSyscallId ∧
      event.arg1.toNat = index ∧
      (event.arg2.toNat : ZMod p) = publicValues.deferred_proofs_digest[index]

/-- Public-digest meaning contributed by a shard's decoded syscall rows.  A flag already carried in
from an earlier shard imposes no duplicate-row requirement here. -/
def CommitRowsMatch {p : ℕ} (publicValues : SP1PublicValues (ZMod p))
    (events : List CoreSyscallEvent) : Prop :=
  (PublicCommitIntroduced publicValues → PublicDigestRowsMatch publicValues events) ∧
    (DeferredCommitIntroduced publicValues → DeferredDigestRowsMatch publicValues events)

/-- The narrowly scoped temporary premise for a concrete AIR relation and its audited event decoder.
The two predicates mean that the corresponding rolling flag is *introduced in this shard*
(`prev = 0 ∧ current = 1`), not merely that an earlier shard already set it. -/
structure CoreAIRSemanticAssumptions {Statement AIRWitness : Type}
    (air : WitnessRelation.Relation Statement AIRWitness)
    (eventsOf : Statement → AIRWitness → List CoreSyscallEvent)
    (publicCommitFlag deferredCommitFlag : Statement → Prop) : Prop where
  publicCommitRows : ∀ statement witness,
    air statement witness → publicCommitFlag statement →
      DigestRowsCover commitSyscallId (eventsOf statement witness)
  deferredCommitRows : ∀ statement witness,
    air statement witness → deferredCommitFlag statement →
      DigestRowsCover commitDeferredSyscallId (eventsOf statement witness)

/-- Specialize the premise to an exact-table system and its total syscall decoder. -/
abbrev SystemSemanticAssumptions {Statement : Type} (system : System Statement)
    (cluster : Cluster) (decoder : EventDecoder system)
    (publicCommitFlag deferredCommitFlag : Statement → Prop) :=
  CoreAIRSemanticAssumptions (system.relationFor cluster) decoder.syscallEvents
    publicCommitFlag deferredCommitFlag

end SP1Clean.CoreAIR
