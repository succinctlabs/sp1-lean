import SP1Clean.Soundness.CoreAIR

set_option autoImplicit false

/-! # The syscall-free restriction, and the obligations it discharges

`CoreAIRRefinementObligations` (`Soundness/CoreAIR.lean`) is the fourteen-field proof bundle the
conditional `sp1_air_refinement_of_obligations` / `sp1_air_sound_of_obligations` combinators
consume. Five fields mention SP1's syscall table: four quantify over decoded syscall events, while
`syscallTranscript` compares the supplied decoder's transcript with the extracted one. On a shard
that performs no syscalls the four event fields are vacuous and the transcript field reduces under
an explicit decoder-preservation premise — which is
worth stating, because the drift-stable AIR scope this workstream verifies deliberately excludes
the Global/Syscall cluster, so a syscall-free restriction is the regime the rest of the bundle will
first be closed in.

## What this file is, and is not

It closes four fields outright and conditionally reduces a fifth, leaving ten conceptually open
obligations. It does **not** close `executionCase` — the field that carries the actual refinement, turning a valid extracted
Core AIR witness into a Sail event-execution trace matching the shard's public endpoints. That one
needs the whole-ensemble transport (`Faithful/Transport/` covers the twenty-five instruction
tables' constraints; the provider, memory-boundary and system-table segments and the four channel
balances are not built), and is the substance of the remaining work in `docs/roadmap.md`.

Nor does it claim the restriction is harmless: a syscall-free shard cannot commit public values, so
`commitTransition` and the two commit flags are trivially consistent for reasons that say nothing
about a shard that does commit. That is precisely why the restriction is a named hypothesis here
rather than a silent scoping decision.
-/

namespace SP1Clean.Soundness

open SP1Clean.Execution

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **A shard performs no syscalls**: its syscall table decodes to no events. Stated on the
extracted witness, so it is checkable on the Rust side rather than being a property of some
decoding we chose. -/
def SyscallFree (witness : CoreAIR.Witness (CoreAIR.Current.Row p)) : Prop :=
  CoreAIR.Current.syscallEvents witness = []

/-- The relation-indexed form the obligation fields are stated against: every witness the extracted
Core AIR accepts for this statement is syscall-free. -/
def RelationSyscallFree {Digest : Type} (binds : CoreAIR.Current.PreprocessedBinding p Digest) :
    Prop :=
  ∀ statement witness, CoreAIR.Current.Relation binds .execution statement witness →
    SyscallFree witness

namespace RelationSyscallFree

variable {Digest : Type} {binds : CoreAIR.Current.PreprocessedBinding p Digest}

omit [Fact (2 ^ 17 < p)] in
/-- Under the restriction, no syscall event exists to quantify over — the shape all four
event-quantified obligation fields reduce to. -/
theorem elim (free : RelationSyscallFree binds)
    {statement : SP1ShardStatement (ZMod p) Digest}
    {witness : CoreAIR.Witness (CoreAIR.Current.Row p)}
    (valid : CoreAIR.Current.Relation binds .execution statement witness)
    {event : Machine.CoreSyscallEvent}
    (mem : event ∈ CoreAIR.Current.syscallEvents witness) : False := by
  rw [free statement witness valid] at mem
  exact absurd mem List.not_mem_nil

omit [Fact (2 ^ 17 < p)] in
/-- `publicCommitOperand`, discharged. -/
theorem publicCommitOperand (free : RelationSyscallFree binds) :
    ∀ statement witness,
      CoreAIR.Current.Relation binds .execution statement witness →
      ∀ event ∈ CoreAIR.Current.syscallEvents witness, ∀ index : Fin 8,
        event.IsCanonicalCode Machine.commitSyscallId →
        event.arg1.toNat = index →
        event.arg2 =
          BitVec.ofNat 64 (statement.publicValues.committed_value_digest[index].toNat) :=
  fun _ _ valid _ mem _ _ _ => absurd (free.elim valid mem) not_false

omit [Fact (2 ^ 17 < p)] in
/-- `deferredCommitOperand`, discharged. -/
theorem deferredCommitOperand (free : RelationSyscallFree binds) :
    ∀ statement witness,
      CoreAIR.Current.Relation binds .execution statement witness →
      ∀ event ∈ CoreAIR.Current.syscallEvents witness, ∀ index : Fin 8,
        event.IsCanonicalCode Machine.commitDeferredSyscallId →
        event.arg1.toNat = index →
        (event.arg2.toNat : ZMod p) = statement.publicValues.deferred_proofs_digest[index] :=
  fun _ _ valid _ mem _ _ _ => absurd (free.elim valid mem) not_false

omit [Fact (2 ^ 17 < p)] in
/-- `publicCommitSetsFlag`, discharged. -/
theorem publicCommitSetsFlag (free : RelationSyscallFree binds) :
    ∀ statement witness,
      CoreAIR.Current.Relation binds .execution statement witness →
      ∀ event ∈ CoreAIR.Current.syscallEvents witness,
        event.IsCanonicalCode Machine.commitSyscallId →
          statement.publicValues.commit_syscall = 1 :=
  fun _ _ valid _ mem _ => absurd (free.elim valid mem) not_false

omit [Fact (2 ^ 17 < p)] in
/-- `deferredCommitSetsFlag`, discharged. -/
theorem deferredCommitSetsFlag (free : RelationSyscallFree binds) :
    ∀ statement witness,
      CoreAIR.Current.Relation binds .execution statement witness →
      ∀ event ∈ CoreAIR.Current.syscallEvents witness,
        event.IsCanonicalCode Machine.commitDeferredSyscallId →
          statement.publicValues.commit_deferred_syscall = 1 :=
  fun _ _ valid _ mem _ => absurd (free.elim valid mem) not_false

omit [Fact (2 ^ 17 < p)] in
/-- `syscallTranscript`, discharged for any decoder that emits no syscall events on a syscall-free
shard. The premise is a property of the *decoder* the eventual bundle supplies, not of the AIR, so
it is kept explicit rather than assumed away. -/
theorem syscallTranscript (free : RelationSyscallFree binds)
    (decode : SP1ShardStatement (ZMod p) Digest →
      CoreAIR.Witness (CoreAIR.Current.Row p) → SP1EventfulShardExecutionWitness)
    (decodeFree : ∀ statement witness, SyscallFree witness →
      (decode statement witness).syscallEvents = []) :
    ∀ statement witness,
      CoreAIR.Current.Relation binds .execution statement witness →
        (decode statement witness).syscallEvents = CoreAIR.Current.syscallEvents witness :=
  fun statement witness valid =>
    (decodeFree statement witness (free statement witness valid)).trans
      (free statement witness valid).symm

end RelationSyscallFree

end SP1Clean.Soundness
