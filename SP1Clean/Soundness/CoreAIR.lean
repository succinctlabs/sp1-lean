import SP1Clean.Faithful.CoreAIR
import SP1Clean.FormalModel.Execution

/-! # Auditable Core AIR capstone

This is the public deterministic soundness layer for the pinned baseline Core AIR.  Its source is
the exact Rust row/assertion/interaction relation in `Faithful/CoreAIR.lean`; its target is the
eventful SP1/Sail shard relation in `FormalModel/Execution.lean`.

The table proofs are intentionally collected as named fields below.  This keeps the headline theorem
small without hiding its hard work in an opaque `airValid → executionValid` field.  The decoder is a
total function of the statement and AIR witness, so this bundle can be used directly as ArkLib's
post-extraction map.  AIR validity authenticates that already-decoded data; it does not choose it.

`commitRowProvenance` is the one temporary upstream premise.  It says that introducing either rolling
commit flag is accompanied by all eight corresponding syscall rows.  The ordinary proof obligations
still have to derive each row's digest operand from the extracted constraints. -/

namespace SP1Clean.Soundness

open SP1Clean.Execution
open SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

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
    (handler : Machine.SyscallHandler) (programBinding : ProgramBinding p Digest) where
  decode : SP1ShardStatement (ZMod p) Digest →
    CoreAIR.Witness (CoreAIR.Current.Row p) → SP1EventfulShardExecutionWitness
  publicValuesWellFormed : ∀ statement witness,
    CoreAIR.Current.Relation binds .execution statement witness →
      statement.publicValues.WellFormed .base
  programWellFormed : ∀ statement witness,
    CoreAIR.Current.Relation binds .execution statement witness →
      (decode statement witness).program.WellFormed
  programBound : ∀ statement witness,
    CoreAIR.Current.Relation binds .execution statement witness →
      programBinding statement.verifyingKey (decode statement witness).program
  entryPoint : ∀ statement witness,
    CoreAIR.Current.Relation binds .execution statement witness →
      BitVec.ofNat 64 statement.verifyingKey.pc_start.toNat =
        (decode statement witness).program.pc_start
  firstExecutionShard : ∀ statement witness,
    CoreAIR.Current.Relation binds .execution statement witness →
      statement.publicValues.is_first_execution_shard = 1 →
        statement.publicValues.pcStartBits = (decode statement witness).program.pc_start ∧
          statement.publicValues.initial_timestamp.toNat = 1 ∧
          statement.publicValues.is_execution_shard = 1
  syscallTranscript : ∀ statement witness,
    CoreAIR.Current.Relation binds .execution statement witness →
      (decode statement witness).syscallEvents = CoreAIR.Current.syscallEvents witness
  publicCommitOperand : ∀ statement witness,
    CoreAIR.Current.Relation binds .execution statement witness →
      ∀ event ∈ CoreAIR.Current.syscallEvents witness, ∀ index : Fin 8,
        event.IsCanonicalCode Machine.commitSyscallId →
        event.arg1.toNat = index →
        event.arg2 =
          BitVec.ofNat 64 (statement.publicValues.committed_value_digest[index].toNat)
  deferredCommitOperand : ∀ statement witness,
    CoreAIR.Current.Relation binds .execution statement witness →
      ∀ event ∈ CoreAIR.Current.syscallEvents witness, ∀ index : Fin 8,
        event.IsCanonicalCode Machine.commitDeferredSyscallId →
        event.arg1.toNat = index →
        (event.arg2.toNat : ZMod p) = statement.publicValues.deferred_proofs_digest[index]
  boundaryCase : ∀ statement witness,
    CoreAIR.Current.Relation binds .execution statement witness →
      statement.publicValues.is_execution_shard = 0 →
        (decode statement witness).execution = none ∧
          statement.publicValues.pc_start = statement.publicValues.next_pc ∧
          statement.publicValues.initial_timestamp = statement.publicValues.last_timestamp
  executionCase : ∀ statement witness,
    CoreAIR.Current.Relation binds .execution statement witness →
      statement.publicValues.is_execution_shard = 1 →
        ∃ trace : Machine.EventExecutionTrace,
          (decode statement witness).execution = some trace ∧
            RomLoaded (decode statement witness).program trace.initialState ∧
            SailConfigured trace.initialState ∧
            EventSegmentMatches (handler := handler)
              statement.publicValues.initial_timestamp.toNat
              statement.publicValues.pcStartBits statement.publicValues.last_timestamp.toNat
              statement.publicValues.nextPcBits (decode statement witness).program trace

namespace CoreAIRRefinementObligations

omit [Fact (2 ^ 17 < p)] in
/-- Combine the temporary row-existence premise with the proved per-row operand equations.

The distinction is load-bearing: provenance contributes only the existence of each canonical row;
`publicCommitOperand` and `deferredCommitOperand` must still come from the exact SyscallInstrs AIR. -/
theorem commitRowsMatch {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    {handler : Machine.SyscallHandler} {programBinding : ProgramBinding p Digest}
    (proofs : CoreAIRRefinementObligations binds handler programBinding)
    (commitRowProvenance : CoreAIR.SystemSemanticAssumptions
      (CoreAIR.Current.system binds) .execution (CoreAIR.Current.eventDecoder binds)
      (fun statement => CoreAIR.PublicCommitIntroduced statement.publicValues)
      (fun statement => CoreAIR.DeferredCommitIntroduced statement.publicValues))
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (valid : CoreAIR.Current.Relation binds .execution statement witness) :
    CoreAIR.CommitRowsMatch statement.publicValues
      (proofs.decode statement witness).syscallEvents := by
  constructor
  · intro introduced index
    obtain ⟨event, eventMem, canonical, indexEq⟩ :=
      commitRowProvenance.publicCommitRows statement witness valid introduced index
    refine ⟨event, ?_, canonical, indexEq, ?_⟩
    · rw [proofs.syscallTranscript statement witness valid]
      exact eventMem
    · exact proofs.publicCommitOperand statement witness valid event eventMem index canonical indexEq
  · intro introduced index
    obtain ⟨event, eventMem, canonical, indexEq⟩ :=
      commitRowProvenance.deferredCommitRows statement witness valid introduced index
    refine ⟨event, ?_, canonical, indexEq, ?_⟩
    · rw [proofs.syscallTranscript statement witness valid]
      exact eventMem
    · exact proofs.deferredCommitOperand statement witness valid event eventMem index canonical indexEq

omit [Fact (2 ^ 17 < p)] in
/-- Assemble the explicit boundary/execution proof fields into the public shard-case proposition. -/
theorem shardCase {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    {handler : Machine.SyscallHandler} {programBinding : ProgramBinding p Digest}
    (proofs : CoreAIRRefinementObligations binds handler programBinding)
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (valid : CoreAIR.Current.Relation binds .execution statement witness) :
    SP1CoreShardCase handler statement (proofs.decode statement witness) := by
  rcases SP1PublicValues.executionShard_bool
    (proofs.publicValuesWellFormed statement witness valid) with boundary | execution
  · obtain ⟨noTrace, pc, timestamp⟩ := proofs.boundaryCase statement witness valid boundary
    exact .boundary boundary noTrace pc timestamp
  · obtain ⟨trace, hasTrace, rom, configured, segment⟩ :=
      proofs.executionCase statement witness valid execution
    exact .execution trace execution hasTrace rom configured segment

end CoreAIRRefinementObligations

/-- **Constructive baseline Core AIR refinement.**

The returned map is the exact postprocessor an ArkLib knowledge extractor should compose with.  This
theorem is deterministic and has no cryptographic claim: ArkLib must separately establish extraction
of a witness satisfying `CoreAIR.Current.Relation binds .execution`, including interaction balance
and the committed preprocessed trace. -/
def sp1_air_refinement {Digest : Type}
    (binds : CoreAIR.Current.PreprocessedBinding p Digest)
    (handler : Machine.SyscallHandler) (programBinding : ProgramBinding p Digest)
    (commitRowProvenance : CoreAIR.SystemSemanticAssumptions
      (CoreAIR.Current.system binds) .execution (CoreAIR.Current.eventDecoder binds)
      (fun statement => CoreAIR.PublicCommitIntroduced statement.publicValues)
      (fun statement => CoreAIR.DeferredCommitIntroduced statement.publicValues))
    (proofs : CoreAIRRefinementObligations binds handler programBinding) :
    WitnessRelation.FunctionalRefinement (CoreAIR.Current.Relation binds .execution)
      (SP1CoreShardExecutionRelation .base handler programBinding) where
  map := proofs.decode
  map_valid statement witness valid := by
    have global := valid.2.2.2
    exact {
      verifyingKeyWellFormed := global.1
      publicValuesWellFormed := proofs.publicValuesWellFormed statement witness valid
      configurationMatches := global.2.1
      programWellFormed := proofs.programWellFormed statement witness valid
      programBound := proofs.programBound statement witness valid
      entryPoint := proofs.entryPoint statement witness valid
      firstExecutionShard := proofs.firstExecutionShard statement witness valid
      commitRows := proofs.commitRowsMatch commitRowProvenance statement witness valid
      shardCase := proofs.shardCase statement witness valid }

omit [Fact (2 ^ 17 < p)] in
/-- **Pinned baseline Core AIR soundness.**

This is the existential corollary used by relation-level clients.  Proof-system integrations should
prefer `sp1_air_refinement`, which retains the explicit deterministic witness decoder. -/
theorem sp1_air_sound {Digest : Type}
    (binds : CoreAIR.Current.PreprocessedBinding p Digest)
    (handler : Machine.SyscallHandler) (programBinding : ProgramBinding p Digest)
    (commitRowProvenance : CoreAIR.SystemSemanticAssumptions
      (CoreAIR.Current.system binds) .execution (CoreAIR.Current.eventDecoder binds)
      (fun statement => CoreAIR.PublicCommitIntroduced statement.publicValues)
      (fun statement => CoreAIR.DeferredCommitIntroduced statement.publicValues))
    (proofs : CoreAIRRefinementObligations binds handler programBinding) :
    WitnessRelation.Sound (CoreAIR.Current.Relation binds .execution)
      (SP1CoreShardExecutionRelation .base handler programBinding) :=
  (sp1_air_refinement binds handler programBinding commitRowProvenance proofs).sound

end SP1Clean.Soundness
