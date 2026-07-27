import SP1Clean.FormalModel.Contracts.PublicValues
import SP1Clean.FormalModel.CoreAIRRelation

/-! # Commit-row contracts for the Core AIR

The syscall AIR constrains every COMMIT row that exists, but intentionally does not prove the converse
`commit_syscall = 1 → a COMMIT row exists`.  Row existence is a program-level property of SP1's
standard halt wrapper and belongs at the composed-execution boundary, across all shards.  This file
therefore separates two predicates:

* `CommitRowsMatch`: per-shard correctness of every existing COMMIT/COMMIT_DEFERRED row, proved from AIR;
* `CompleteCommitCoverage`: all eight public COMMIT indices occur in a whole-execution transcript,
  supplied by an explicit standard-wrapper contract.

No rolling-flag transition is used as provenance. -/

namespace SP1Clean.CoreAIR

open SP1Clean.Machine

/-- Every one of the eight digest indices occurs in a syscall row carrying the exact canonical Rust
code.  Requiring the complete `x5` value is intentional: the instruction AIR recognizes these
operations by byte zero alone, whereas Rust decodes and writes back a concrete `SyscallCode` value.
Duplicate rows are permitted; their values remain constrained by the AIR. -/
def DigestRowsCover (syscallCode : ℕ) (events : List CoreSyscallEvent) : Prop :=
  ∀ index : Fin 8, ∃ event ∈ events,
    event.IsCanonicalCode syscallCode ∧ event.arg1.toNat = index

/-- Whole-execution coverage promised by the standard `syscall_halt` wrapper. -/
def CompleteCommitCoverage (events : List CoreSyscallEvent) : Prop :=
  DigestRowsCover commitSyscallId events

/-- Deferred-commit coverage, intentionally separate because not every target theorem needs it. -/
def CompleteDeferredCommitCoverage (events : List CoreSyscallEvent) : Prop :=
  DigestRowsCover commitDeferredSyscallId events

/-- Every existing canonical COMMIT row has the public digest operand required by its index.  This
predicate asserts no row existence. -/
def PublicCommitRowsMatch {p : ℕ} (publicValues : SP1PublicValues (ZMod p))
    (events : List CoreSyscallEvent) : Prop :=
  ∀ event ∈ events, ∀ index : Fin 8,
    event.IsCanonicalCode commitSyscallId → event.arg1.toNat = index →
      event.arg2 = BitVec.ofNat 64 (publicValues.committed_value_digest[index].toNat)

/-- Existing COMMIT_DEFERRED rows obey the corresponding rolling-digest operand equation.  Like the
public form, this is per-row soundness and carries no converse/existence claim. -/
def DeferredCommitRowsMatch {p : ℕ} (publicValues : SP1PublicValues (ZMod p))
    (events : List CoreSyscallEvent) : Prop :=
  ∀ event ∈ events, ∀ index : Fin 8,
    event.IsCanonicalCode commitDeferredSyscallId → event.arg1.toNat = index →
      (event.arg2.toNat : ZMod p) = publicValues.deferred_proofs_digest[index]

/-- Per-shard AIR conclusion for commit syscalls: every existing row is correct.  Coverage is the
separate whole-execution `CompleteCommitCoverage` contract. -/
def CommitRowsMatch {p : ℕ} (publicValues : SP1PublicValues (ZMod p))
    (events : List CoreSyscallEvent) : Prop :=
  PublicCommitRowsMatch publicValues events ∧
    DeferredCommitRowsMatch publicValues events

end SP1Clean.CoreAIR
