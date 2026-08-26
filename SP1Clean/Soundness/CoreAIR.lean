import SP1Clean.Faithful.CoreAIR
import SP1Clean.FormalModel.Execution
import SP1Clean.Model.SP1Field

/-! # Auditable Core AIR capstone

This is the public deterministic refinement boundary for the pinned baseline Core AIR.  Its source
is the exact Rust row/assertion/interaction relation in `Faithful/CoreAIR.lean`; its target is the
eventful SP1/Sail shard relation in `FormalModel/Execution.lean`.

The still-open table proofs are intentionally collected as named fields below.  This makes the
remaining semantic work auditable, but the bundle is not currently instantiated: in particular,
`executionCase` is the system-table grounding theorem that must connect the exact upstream rows to an
eventful Sail segment.  Accordingly the proved combinators are named `_of_obligations`; the unqualified
`sp1_air_refinement` and `sp1_air_sound` names remain reserved for a closed construction of this bundle.
The decoder is a total function of the statement and AIR witness, so the eventual construction can be
used directly as ArkLib's post-extraction map.  AIR validity authenticates already-decoded data; it
does not choose it.

This bundle is a composition record, not evidence that every field is an AIR consequence. A future
closed constructor must keep application-level loader/platform/handler contracts as explicit public
parameters or source restrictions; only the system-table facts should be advertised as derived from
`CoreAIR.Current.Relation`.

The shard theorem proves only forward AIR facts: every COMMIT row that exists has the correct
digest operand and sets the corresponding rolling flag.  Exact public-value transition laws record
how a set flag freezes the digest in later shards.  Complete eight-row coverage is still a separate
whole-execution contract of the pinned program's standard halt wrapper; the rolling flag is never
used as a converse claim that rows exist. -/

namespace SP1Clean.Soundness

open SP1Clean.Execution
open SP1Clean.Soundness.Target
open LeanRV64D.Defs

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Narrow external semantics that are not consequences of the algebraic tables.

The decoder is total proof-free data.  The remaining fields are exactly program authentication and
platform/loader facts; system-table chronology, public-value laws, syscall alignment, and Memory
boundary agreement are deliberately absent and remain obligations below. -/
structure CoreAIRExternalContext {Digest : Type}
    (binds : CoreAIR.Current.PreprocessedBinding p Digest)
    (handler : Machine.ExecutableSyscallHandler)
    (programBinding : ProgramBinding p Digest) where
  decode : SP1ShardStatement (ZMod p) Digest →
    CoreAIR.ShardWitness (CoreAIR.Current.system binds) → Machine.CoreShardSemanticWitness
  programWellFormed : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      (decode statement witness).program.WellFormed
  programBound : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      programBinding statement.verifyingKey (decode statement witness).program
  entryPoint : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      BitVec.ofNat 64 statement.verifyingKey.pc_start.toNat =
        (decode statement witness).program.pc_start
  romLoaded : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      RomLoaded (decode statement witness).program (decode statement witness).initialState
  configured : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      SailConfigured (decode statement witness).initialState
  codeMemoryCompatible : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      SailCodeMemoryCompatible (decode statement witness).program
        (decode statement witness).initialState

/-- Proof modules needed to refine the exact Rust AIR witness into one semantic shard witness.

Each field has one owner in the implementation:

* public-value AIR proofs establish canonical public encodings;
* preprocessing/program proofs recover the committed `GuestProgram`;
* ordered State/Memory grounding proves the explicit boundary and execution cases;
* the syscall instruction-table proof establishes transcript alignment and digest operands.

The verifying-key and configuration fields are absent because they are already literal conjuncts of
`CoreAIR.Current.GlobalValid` and are projected directly by the capstone. -/
structure CoreAIRRefinementObligations {Digest : Type}
    (binds : CoreAIR.Current.PreprocessedBinding p Digest)
    (handler : Machine.ExecutableSyscallHandler)
    (programBinding : ProgramBinding p Digest)
    (external : CoreAIRExternalContext binds handler programBinding) where
  publicValuesWellFormed : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      statement.publicValues.WellFormed .base
  firstExecutionShard : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      statement.publicValues.is_first_execution_shard = 1 →
        statement.publicValues.pcStartBits = (external.decode statement witness).program.pc_start ∧
          statement.publicValues.initial_timestamp.toNat = 1 ∧
          statement.publicValues.is_execution_shard = 1
  syscallTranscript : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      (external.decode statement witness).syscallEvents =
        CoreAIR.Current.syscallEvents witness.execution
  publicCommitOperand : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      ∀ event ∈ CoreAIR.Current.syscallEvents witness.execution, ∀ index : Fin 8,
        event.IsCanonicalCode Machine.commitSyscallId →
        event.arg1.toNat = index →
        event.arg2 =
          BitVec.ofNat 64 (statement.publicValues.committed_value_digest[index].toNat)
  deferredCommitOperand : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      ∀ event ∈ CoreAIR.Current.syscallEvents witness.execution, ∀ index : Fin 8,
        event.IsCanonicalCode Machine.commitDeferredSyscallId →
        event.arg1.toNat = index →
        (event.arg2.toNat : ZMod p) = statement.publicValues.deferred_proofs_digest[index]
  publicCommitSetsFlag : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      ∀ event ∈ CoreAIR.Current.syscallEvents witness.execution,
        event.IsCanonicalCode Machine.commitSyscallId →
          statement.publicValues.commit_syscall = 1
  deferredCommitSetsFlag : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      ∀ event ∈ CoreAIR.Current.syscallEvents witness.execution,
        event.IsCanonicalCode Machine.commitDeferredSyscallId →
          statement.publicValues.commit_deferred_syscall = 1
  commitTransition : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      statement.publicValues.CommitTransitionValid
  memoryWellFormed : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      (external.decode statement witness).memoryBoundary.WellFormed
        (sp1CoreShardBoundary statement).finalClock
  memoryAgrees : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      (external.decode statement witness).memoryBoundary.AgreesWith
        (external.decode statement witness).initialState
        ((external.decode statement witness).evaluatedTrace
          (sp1CoreShardModel handler programBinding)).finalState
  boundaryCase : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      (sp1CoreShardBoundary statement).isExecution = false →
        (external.decode statement witness).events = none ∧
          (sp1CoreShardBoundary statement).initialPc =
            (sp1CoreShardBoundary statement).finalPc ∧
          (sp1CoreShardBoundary statement).initialClock =
            (sp1CoreShardBoundary statement).finalClock
  executionCase : ∀ statement witness,
    CoreAIR.Current.ShardRelation binds statement witness →
      (sp1CoreShardBoundary statement).isExecution = true →
        ∃ events trace,
          (external.decode statement witness).events = some events ∧
            (external.decode statement witness).trace?
              (sp1CoreShardModel handler programBinding) = some trace ∧
            trace.Valid handler.relation (external.decode statement witness).program ∧
            trace.Clocked (sp1CoreShardBoundary statement).initialClock ∧
            trace.finalClock (sp1CoreShardBoundary statement).initialClock =
              (sp1CoreShardBoundary statement).finalClock ∧
            trace.initialState.regs.get? Register.PC =
              some (sp1CoreShardBoundary statement).initialPc ∧
            trace.finalState.regs.get? Register.PC =
              some (sp1CoreShardBoundary statement).finalPc

namespace CoreAIRRefinementObligations

omit [Fact (2 ^ 17 < p)] in
/-- Package the two proved per-existing-row operand equations.  This theorem deliberately has no
coverage premise and draws no converse from either rolling commit flag. -/
theorem commitRowsMatch {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    {handler : Machine.ExecutableSyscallHandler} {programBinding : ProgramBinding p Digest}
    {external : CoreAIRExternalContext binds handler programBinding}
    (proofs : CoreAIRRefinementObligations binds handler programBinding external)
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.ShardWitness (CoreAIR.Current.system binds))
    (valid : CoreAIR.Current.ShardRelation binds statement witness) :
    CoreAIR.CommitRowsMatch statement.publicValues
      (external.decode statement witness).syscallEvents := by
  have transcript := proofs.syscallTranscript statement witness valid
  constructor
  · intro event eventMem index canonical indexEq
    rw [transcript] at eventMem
    exact proofs.publicCommitOperand statement witness valid event eventMem index canonical indexEq
  · intro event eventMem index canonical indexEq
    rw [transcript] at eventMem
    exact proofs.deferredCommitOperand statement witness valid event eventMem index canonical indexEq

omit [Fact (2 ^ 17 < p)] in
/-- Package the two AIR-forced row-to-flag implications.  These are deliberately one-way: a set
rolling flag does not imply that this shard contains any COMMIT row. -/
theorem commitRowsSetFlags {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    {handler : Machine.ExecutableSyscallHandler} {programBinding : ProgramBinding p Digest}
    {external : CoreAIRExternalContext binds handler programBinding}
    (proofs : CoreAIRRefinementObligations binds handler programBinding external)
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.ShardWitness (CoreAIR.Current.system binds))
    (valid : CoreAIR.Current.ShardRelation binds statement witness) :
    CoreAIR.CommitRowsSetFlags statement.publicValues
      (external.decode statement witness).syscallEvents := by
  have transcript := proofs.syscallTranscript statement witness valid
  constructor
  · intro event eventMem canonical
    rw [transcript] at eventMem
    exact proofs.publicCommitSetsFlag statement witness valid event eventMem canonical
  · intro event eventMem canonical
    rw [transcript] at eventMem
    exact proofs.deferredCommitSetsFlag statement witness valid event eventMem canonical

omit [Fact (2 ^ 17 < p)] in
/-- Assemble the explicit boundary/execution proof fields into the public shard-case proposition. -/
theorem shardCase {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    {handler : Machine.ExecutableSyscallHandler} {programBinding : ProgramBinding p Digest}
    {external : CoreAIRExternalContext binds handler programBinding}
    (proofs : CoreAIRRefinementObligations binds handler programBinding external)
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.ShardWitness (CoreAIR.Current.system binds))
    (valid : CoreAIR.Current.ShardRelation binds statement witness) :
    CoreShardCase (sp1CoreShardModel handler programBinding)
      (sp1CoreShardContract .base) statement (external.decode statement witness) := by
  cases execution : (sp1CoreShardBoundary statement).isExecution with
  | false =>
      obtain ⟨noEvents, pc, clock⟩ :=
        proofs.boundaryCase statement witness valid execution
      exact .boundary execution noEvents pc clock trivial
  | true =>
      obtain ⟨events, trace, hasEvents, evaluated, traceValid, clocked, finalClock,
          initialPc, finalPc⟩ := proofs.executionCase statement witness valid execution
      exact .execution events trace execution hasEvents evaluated traceValid clocked finalClock
        initialPc finalPc trivial

end CoreAIRRefinementObligations

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **Conditional constructive baseline Core AIR refinement.**

The returned map is the exact postprocessor an ArkLib knowledge extractor should compose with.  This
theorem is deterministic and has no cryptographic claim: ArkLib must separately establish extraction
of a witness satisfying the paired `CoreAIR.Current.ShardRelation binds`, including interaction
balance and both clusters' committed preprocessed traces. It is conditional on the explicit, currently uninstantiated
`CoreAIRRefinementObligations` bundle. -/
def sp1_air_refinement_of_obligations {Digest : Type}
    (binds : CoreAIR.Current.PreprocessedBinding SP1Prime Digest)
    (handler : Machine.ExecutableSyscallHandler)
    (programBinding : ProgramBinding SP1Prime Digest)
    (external : CoreAIRExternalContext (p := SP1Prime) binds handler programBinding)
    (proofs : CoreAIRRefinementObligations (p := SP1Prime)
      binds handler programBinding external) :
    WitnessRelation.FunctionalRefinement (CoreAIR.Current.ShardRelation binds)
      (SP1CoreShardSemanticRelation .base handler programBinding) where
  map := external.decode
  map_valid statement witness valid := by
    have global := valid.1.2.2.2
    exact {
      statementValid := ⟨global.1,
        proofs.publicValuesWellFormed statement witness valid, global.2.1⟩
      programWellFormed := external.programWellFormed statement witness valid
      programBound := external.programBound statement witness valid
      programValid := ⟨external.entryPoint statement witness valid,
        proofs.firstExecutionShard statement witness valid⟩
      contractValid := ⟨proofs.commitRowsMatch statement witness valid,
        proofs.commitRowsSetFlags statement witness valid,
        proofs.commitTransition statement witness valid⟩
      romLoaded := external.romLoaded statement witness valid
      configured := external.configured statement witness valid
      codeMemoryCompatible := external.codeMemoryCompatible statement witness valid
      memoryWellFormed := proofs.memoryWellFormed statement witness valid
      memoryAgrees := proofs.memoryAgrees statement witness valid
      shardCase := proofs.shardCase statement witness valid }

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- **Conditional pinned baseline Core AIR soundness.**

This is the existential corollary used by relation-level clients.  Proof-system integrations should
prefer `sp1_air_refinement_of_obligations`, which retains the explicit deterministic witness decoder.
The unqualified `sp1_air_sound` name is deliberately not declared until the obligations have a closed
construction from the exact AIR relation and disclosed external contracts. -/
theorem sp1_air_sound_of_obligations {Digest : Type}
    (binds : CoreAIR.Current.PreprocessedBinding SP1Prime Digest)
    (handler : Machine.ExecutableSyscallHandler)
    (programBinding : ProgramBinding SP1Prime Digest)
    (external : CoreAIRExternalContext (p := SP1Prime) binds handler programBinding)
    (proofs : CoreAIRRefinementObligations (p := SP1Prime)
      binds handler programBinding external) :
    WitnessRelation.Sound (CoreAIR.Current.ShardRelation binds)
      (SP1CoreShardSemanticRelation .base handler programBinding) :=
  (sp1_air_refinement_of_obligations binds handler programBinding external proofs).sound

end SP1Clean.Soundness
