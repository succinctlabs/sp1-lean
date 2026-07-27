import SP1Clean.FormalModel.Contracts.CoreAIR
import SP1Clean.FormalModel.Contracts.PublicValues
import SP1Clean.FormalModel.Relations
import SP1Clean.Model.Machine.EventExecution
import SP1Clean.Model.Machine.Execution
import SP1Clean.Model.Semantics.MicroTime

/-! # Program-execution relations

The semantic side of AIR soundness is a witness relation, not a Boolean verifier result.  The current
Clean ensemble uses an internal statement that fixes both the guest program and its State boundary;
its private witness is one finite segment of the canonical Sail run.  An upstream shard verifier has a
different public statement: a machine verifying key plus the full shard public-values record.  The
program is then private data bound by the verifying key's preprocessed commitment.

Neither relation equates a shard endpoint with halting.  Halting is a property of the composed
execution theorem, after shard continuity and the recursion completion checks have been proved. -/

open LeanRV64D.Defs

namespace SP1Clean.Execution

open Sail LeanRV64D
open SP1Clean.Soundness.Target

/-- A public AIR statement binds a program as well as its public-values record. -/
structure ProgramStatement (PublicValues : Type) where
  program : GuestProgram
  publicValues : PublicValues

/-- Recombine the current supported-core pc limbs. -/
def supportedPcBits {p : ℕ} (pc0 pc1 pc2 : ZMod p) : BitVec 64 :=
  SP1Clean.Semantics.pcBits pc0 pc1 pc2

/-- One execution segment agrees with decoded clock and pc endpoints. -/
noncomputable def SegmentMatches {model : Machine.SP1MachineModel}
    {ctx : Machine.ExecutionCtx model} (initialClock : ℕ) (initialPc : BitVec 64)
    (finalClock : ℕ) (finalPc : BitVec 64)
    (execution : Machine.ExecutionSegmentWitness ctx) : Prop :=
  execution.initialState.regs.get? Register.PC =
      some initialPc ∧
    execution.finalState.regs.get? Register.PC = some finalPc ∧
    Machine.ExecutionSegmentWitness.clockAt execution initialClock execution.steps = finalClock

/-- Specialize `SegmentMatches` to the State-bus boundary used by the supported Clean ensemble. -/
noncomputable def SegmentMatchesBoundary {p : ℕ} {model : Machine.SP1MachineModel}
    {ctx : Machine.ExecutionCtx model} (boundary : SP1StateBoundary (ZMod p))
    (execution : Machine.ExecutionSegmentWitness ctx) : Prop :=
  SegmentMatches
    (SP1Clean.Semantics.clkNat boundary.init_clk_high boundary.init_clk_low)
    (supportedPcBits boundary.init_pc0 boundary.init_pc1 boundary.init_pc2)
    (SP1Clean.Semantics.clkNat boundary.final_clk_high boundary.final_clk_low)
    (supportedPcBits boundary.final_pc0 boundary.final_pc1 boundary.final_pc2)
    execution

/-- A shard-local execution agrees with its decoded clock and pc endpoints.  Unlike
`SegmentMatches`, this starts from the state carried by the local context and makes no boot
reachability claim. -/
noncomputable def LocalSegmentMatches {model : Machine.SP1MachineModel}
    {ctx : Machine.LocalExecutionCtx model} (initialClock : ℕ) (initialPc : BitVec 64)
    (finalClock : ℕ) (finalPc : BitVec 64)
    (execution : Machine.LocalExecutionSegmentWitness ctx) : Prop :=
  ctx.initial.regs.get? Register.PC = some initialPc ∧
    execution.finalState.regs.get? Register.PC = some finalPc ∧
    execution.clockAt initialClock execution.steps = finalClock

/-- Specialize `LocalSegmentMatches` to the State boundary consumed by the supported ensemble. -/
noncomputable def LocalSegmentMatchesBoundary {p : ℕ} {model : Machine.SP1MachineModel}
    {ctx : Machine.LocalExecutionCtx model} (boundary : SP1StateBoundary (ZMod p))
    (execution : Machine.LocalExecutionSegmentWitness ctx) : Prop :=
  LocalSegmentMatches
    (SP1Clean.Semantics.clkNat boundary.init_clk_high boundary.init_clk_low)
    (supportedPcBits boundary.init_pc0 boundary.init_pc1 boundary.init_pc2)
    (SP1Clean.Semantics.clkNat boundary.final_clk_high boundary.final_clk_low)
    (supportedPcBits boundary.final_pc0 boundary.final_pc1 boundary.final_pc2)
    execution

/-- Honest semantic target of one supported-core AIR shard: a successful official-Sail trajectory
from the public initial state to the public final state.  Reachability of the initial state from the
model-selected boot state is intentionally absent and is supplied only when shards are composed. -/
noncomputable def SupportedCoreLocalExecutionRelation {p : ℕ} (model : Machine.SP1MachineModel) :
    WitnessRelation.Relation
      (ProgramStatement (SupportedCorePrefixPublicValues (ZMod p)))
      (Machine.ClosedLocalExecutionSegmentWitness model) :=
  fun statement witness =>
    statement.program.WellFormed ∧
    witness.context.program = statement.program ∧
    LocalSegmentMatchesBoundary statement.publicValues witness.execution

/-- Semantic execution for the currently wired 25-chip slice.

The ensemble exposes only State endpoints, so the honest result is a finite segment of the one
model-selected Sail run.  It does not assert that the segment begins at program entry or ends in a
halt.  `supported_core_air_sound` separately assumes the ordinary eight-tick schedule implemented by
these 25 chips. -/
noncomputable def SupportedCoreExecutionRelation {p : ℕ} (model : Machine.SP1MachineModel) :
    WitnessRelation.Relation
      (ProgramStatement (SupportedCorePrefixPublicValues (ZMod p)))
      (Machine.ClosedExecutionSegmentWitness model) :=
  fun statement witness =>
    statement.program.WellFormed ∧
    witness.context.program = statement.program ∧
    SegmentMatchesBoundary statement.publicValues witness.execution

/-- A local shard result lifts to the canonical execution relation once its initial state is known
to occur in the model-selected boot trajectory.  This is the intended shard-composition seam. -/
theorem supportedCoreLocalExecution_anchors {p : ℕ} {model : Machine.SP1MachineModel}
    {statement : ProgramStatement (SupportedCorePrefixPublicValues (ZMod p))}
    {localWitness : Machine.ClosedLocalExecutionSegmentWitness model}
    (localValid : SupportedCoreLocalExecutionRelation model statement localWitness)
    (global : Machine.ExecutionCtx model) (globalProgram : global.program = statement.program)
    (startStep : ℕ)
    (initialReached : Machine.trajectory global.initial startStep =
      some localWitness.context.initial) :
    ∃ witness, SupportedCoreExecutionRelation model statement witness := by
  obtain ⟨wellFormed, localProgram, boundary⟩ := localValid
  have programEq : localWitness.context.program = global.program :=
    localProgram.trans globalProgram.symm
  let execution := localWitness.execution.anchor startStep programEq initialReached
  refine ⟨⟨global, execution⟩, wellFormed, globalProgram, ?_⟩
  obtain ⟨initialPc, finalPc, finalClock⟩ := boundary
  exact ⟨initialPc, finalPc, by
    rw [Machine.LocalExecutionSegmentWitness.clockAt_anchor]
    exact finalClock⟩

/-! ## Full upstream shard statement -/

/-- The cryptographic setup seam: the machine verifying key opens to this guest program.  For SP1,
this combines the preprocessed Program table commitment, entry pc, initial global-memory sum, and
untrusted-program configuration.  The concrete relation belongs to the extracted AIR/PCS adapter;
`ProverData` by itself is not a verifying-key commitment. -/
abbrev ProgramBinding (p : ℕ) (Digest : Type) :=
  SP1MachineVerifyingKey (ZMod p) Digest → GuestProgram → Prop

/-! ## Eventful Core shard target -/

/-- Private, proof-free semantic witness for one Core shard.  An execution shard carries raw event
trace data checked by the relation below; a non-execution shard carries `none`. -/
structure SP1EventfulShardExecutionWitness where
  program : GuestProgram
  execution : Option Machine.EventExecutionTrace

/-- Syscall transcript exposed by a shard witness; boundary-only shards expose the empty list. -/
def SP1EventfulShardExecutionWitness.syscallEvents
    (witness : SP1EventfulShardExecutionWitness) : List Machine.CoreSyscallEvent :=
  witness.execution.map Machine.EventExecutionTrace.syscallEvents |>.getD []

/-- An eventful execution segment agrees with the public pc and timestamp endpoints. -/
def EventSegmentMatches {handler : Machine.SyscallHandler} (initialClock : ℕ)
    (initialPc : BitVec 64) (finalClock : ℕ) (finalPc : BitVec 64)
    (program : GuestProgram) (execution : Machine.EventExecutionTrace) : Prop :=
  execution.Valid handler program ∧
    execution.Clocked initialClock ∧
    execution.initialState.regs.get? Register.PC = some initialPc ∧
    execution.finalState.regs.get? Register.PC = some finalPc ∧
    execution.finalClock initialClock = finalClock

/-- The two honest semantic cases of a baseline Core shard.

Making the branch a named inductive keeps the top-level audit surface readable and prevents a proof
from satisfying an opaque disjunction with an unrelated existential.  A boundary shard consumes no
machine step; an execution shard exposes the exact trace that was decoded from the AIR witness. -/
inductive SP1CoreShardCase {p : ℕ} {Digest : Type} (handler : Machine.SyscallHandler)
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : SP1EventfulShardExecutionWitness) : Prop
  | boundary :
      statement.publicValues.is_execution_shard = 0 →
      witness.execution = none →
      statement.publicValues.pc_start = statement.publicValues.next_pc →
      statement.publicValues.initial_timestamp = statement.publicValues.last_timestamp →
      SP1CoreShardCase handler statement witness
  | execution (trace : Machine.EventExecutionTrace) :
      statement.publicValues.is_execution_shard = 1 →
      witness.execution = some trace →
      RomLoaded witness.program trace.initialState →
      SailConfigured trace.initialState →
      EventSegmentMatches (handler := handler)
        statement.publicValues.initial_timestamp.toNat
        statement.publicValues.pcStartBits statement.publicValues.last_timestamp.toNat
        statement.publicValues.nextPcBits witness.program trace →
      SP1CoreShardCase handler statement witness

/-- Named validity record for the semantic result of one baseline Core shard.

The fields are intentionally the complete public audit surface.  Table-specific proofs may be split
however is convenient internally, but the AIR refinement must fill these fields explicitly. -/
structure SP1CoreShardExecutionValid {p : ℕ} {Digest : Type}
    (layout : SP1PublicValuesLayout) (handler : Machine.SyscallHandler)
    (programBinding : ProgramBinding p Digest)
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : SP1EventfulShardExecutionWitness) : Prop where
  verifyingKeyWellFormed : statement.verifyingKey.WellFormed layout
  publicValuesWellFormed : statement.publicValues.WellFormed layout
  configurationMatches : statement.ConfigurationMatches
  programWellFormed : witness.program.WellFormed
  programBound : programBinding statement.verifyingKey witness.program
  entryPoint :
    BitVec.ofNat 64 statement.verifyingKey.pc_start.toNat = witness.program.pc_start
  firstExecutionShard : statement.publicValues.is_first_execution_shard = 1 →
    statement.publicValues.pcStartBits = witness.program.pc_start ∧
      statement.publicValues.initial_timestamp.toNat = 1 ∧
      statement.publicValues.is_execution_shard = 1
  commitRows : CoreAIR.CommitRowsMatch statement.publicValues witness.syscallEvents
  shardCase : SP1CoreShardCase handler statement witness

/-- Full semantic target for a baseline Core AIR shard.

Ordinary rows are official Sail steps; syscall rows are raw, auditable events interpreted by the
explicit `handler` relation.  This avoids both failure modes of the older projection: treating every
row as an ordinary Sail step, or hiding syscall behavior in an existential machine model.  The
relation remains shard-local; boot reachability and cross-shard state continuity belong to the
authenticated ledger theorem. -/
def SP1CoreShardExecutionRelation {p : ℕ} {Digest : Type}
    (layout : SP1PublicValuesLayout) (handler : Machine.SyscallHandler)
    (programBinding : ProgramBinding p Digest) :
    WitnessRelation.Relation (SP1ShardStatement (ZMod p) Digest)
      SP1EventfulShardExecutionWitness :=
  SP1CoreShardExecutionValid layout handler programBinding

/-! ## Authenticated shard composition and the halted execution relation -/

/-- The narrow algebraic check recursion performs on the verifying key's initial global digest and
the per-shard global cumulative sums.  The ArkLib/recursion adapter instantiates this with SP1's
septic-curve group law; the relation cannot inspect unrelated public-value fields. -/
abbrev GlobalCumulativeBalance (p : ℕ) :=
  SP1SepticDigest (ZMod p) → List (SP1SepticDigest (ZMod p)) → Prop

/-- Authentication of the final rolling deferred-proof digest.  Its private proof list belongs to
the recursion witness, not to `SP1PublicValues`, so this boundary exposes only the exact digest it
must authenticate. -/
abbrev DeferredDigestAuthenticated (p : ℕ) := Vector (ZMod p) 8 → Prop

/-- Extract the execution traces from a ledger-aligned optional segment list. -/
def executionTraces (segments : List (Option Machine.EventExecutionTrace)) :
    List Machine.EventExecutionTrace :=
  segments.filterMap id

/-- The syscall transcript of the entire execution, in authenticated shard order. -/
def executionSyscallEvents (segments : List (Option Machine.EventExecutionTrace)) :
    List Machine.CoreSyscallEvent :=
  (executionTraces segments).flatMap Machine.EventExecutionTrace.syscallEvents

/-- Trace-level form of the standard halt wrapper's eight-call COMMIT coverage. -/
def CompleteCommitCoverage (segments : List (Option Machine.EventExecutionTrace)) : Prop :=
  CoreAIR.CompleteCommitCoverage (executionSyscallEvents segments)

/-- Optional deferred-commit twin.  It is named separately because the current public-output claim
authenticates the deferred digest cryptographically and does not yet claim wrapper-derived row coverage. -/
def CompleteDeferredCommitCoverage
    (segments : List (Option Machine.EventExecutionTrace)) : Prop :=
  CoreAIR.CompleteDeferredCommitCoverage (executionSyscallEvents segments)

/-- Full-state alignment of consecutive shard segments.

Public values authenticate PC and clock continuity, but those two fields alone do not authenticate
registers or RAM.  This relation therefore carries the stronger fact the AIR grounding proof must
establish: every next execution trace begins at the complete state produced by the preceding trace.
Non-execution shards consume no semantic step and leave that complete state unchanged. -/
def EventShardLayout {p : ℕ} (handler : Machine.SyscallHandler) (program : GuestProgram) :
    List (SP1PublicValues (ZMod p)) → List (Option Machine.EventExecutionTrace) →
      SailState → SailState → Prop
  | [], [], source, target => target = source
  | publicValues :: publicRest, none :: segmentRest, source, target =>
      publicValues.is_execution_shard = 0 ∧
        publicValues.pc_start = publicValues.next_pc ∧
        publicValues.initial_timestamp = publicValues.last_timestamp ∧
        CoreAIR.CommitRowsMatch publicValues [] ∧
        EventShardLayout handler program publicRest segmentRest source target
  | publicValues :: publicRest, some execution :: segmentRest, source, target =>
      publicValues.is_execution_shard = 1 ∧
        execution.initialState = source ∧
        RomLoaded program source ∧
        SailConfigured source ∧
        EventSegmentMatches (handler := handler)
          publicValues.initial_timestamp.toNat publicValues.pcStartBits
          publicValues.last_timestamp.toNat publicValues.nextPcBits program execution ∧
        CoreAIR.CommitRowsMatch publicValues execution.syscallEvents ∧
        EventShardLayout handler program publicRest segmentRest execution.finalState target
  | _, _, _, _ => False

/-- The last execution shard, ignoring any trailing boundary-only shards, ends in the canonical Rust
HALT syscall and exposes its pre-HALT state. -/
def LastExecutionHalts (program : GuestProgram) (exitCode : BitVec 64)
    (segments : List (Option Machine.EventExecutionTrace)) : Prop :=
  ∃ execution,
    (executionTraces segments).getLast? = some execution ∧
      execution.HaltsWith program exitCode

/-- Explicit program-level contract for SP1's standard `syscall_halt` wrapper.  It connects a valid,
fully stitched execution that ends in the raw HALT syscall to eight canonical COMMIT events somewhere
in the complete cross-shard transcript.  This is not an AIR theorem: callers justify it from the
verification-key-bound guest program. -/
def UsesStandardHaltWrapper {p : ℕ} (handler : Machine.SyscallHandler)
    (program : GuestProgram) : Prop :=
  ∀ {publicValues : List (SP1PublicValues (ZMod p))}
    {segments : List (Option Machine.EventExecutionTrace)} {initial final : SailState}
    {exitCode : BitVec 64},
    EventShardLayout handler program publicValues segments initial final →
      LastExecutionHalts program exitCode segments →
        CompleteCommitCoverage segments

/-- Proof-free semantic witness recovered from a complete recursive Core proof. -/
structure SP1ExecutionWitness where
  program : GuestProgram
  initialState : SailState
  finalState : SailState
  exitCode : BitVec 64
  segments : List (Option Machine.EventExecutionTrace)

/-- The honest eventful target of recursion/shard composition.

The public ledger is concrete (`AuthenticatedLedger`), including every equality checked by SP1's
compression loop and its complete-proof endpoints.  Only two cryptographic/algebraic facts remain as
narrow parameters: septic global-sum balance and authentication of the deferred-proof digest.  The
semantic layout separately requires complete-state stitching, avoiding the unsound inference that
PC/timestamp continuity alone identifies a machine state.  Every COMMIT row that occurs is tied to the
corresponding shard digest by `EventShardLayout`, but this base relation intentionally does not require
all eight rows to occur.  Complete coverage belongs to the optional program-level strengthening below;
it is not inferred from an AIR flag or from the occurrence of a raw HALT ECALL. -/
def SP1ExecutionRelation {p : ℕ} {Digest : Type}
    (layout : SP1PublicValuesLayout) (model : Machine.SP1MachineModel)
    (handler : Machine.SyscallHandler) (programBinding : ProgramBinding p Digest)
    (globalBalance : GlobalCumulativeBalance p)
    (deferredAuthenticated : DeferredDigestAuthenticated p) :
    WitnessRelation.Relation (SP1ExecutionStatement (ZMod p) Digest) SP1ExecutionWitness :=
  fun statement witness =>
    statement.verifyingKey.WellFormed layout ∧
    (∀ publicValues ∈ statement.shards,
      publicValues.WellFormed layout ∧
        (SP1ShardStatement.mk statement.verifyingKey publicValues).ConfigurationMatches ∧
        (publicValues.is_first_execution_shard = 1 →
          publicValues.is_execution_shard = 1 ∧
            publicValues.initial_timestamp.toNat = 1 ∧
            publicValues.pcStartBits = witness.program.pc_start)) ∧
    witness.program.WellFormed ∧
    programBinding statement.verifyingKey witness.program ∧
    BitVec.ofNat 64 statement.verifyingKey.pc_start.toNat = witness.program.pc_start ∧
    (∃ wellFormed : witness.program.WellFormed,
      witness.initialState = model.boot witness.program wellFormed) ∧
    SP1PublicValues.AuthenticatedLedger 1 statement.shards ∧
    globalBalance statement.verifyingKey.initial_global_cumulative_sum
      (statement.shards.map SP1PublicValues.global_cumulative_sum) ∧
    EventShardLayout handler witness.program statement.shards witness.segments
      witness.initialState witness.finalState ∧
    LastExecutionHalts witness.program witness.exitCode witness.segments ∧
    ∃ finalPublicValues,
      statement.shards.getLast? = some finalPublicValues ∧
        deferredAuthenticated finalPublicValues.deferred_proofs_digest ∧
        finalPublicValues.exitCodeBits = witness.exitCode

/-- Optional strengthening for claims that need every committed-digest word to occur in the syscall
transcript.  This is only COMMIT-event coverage: output bytes and the wrapper's hashing behavior are not
yet modeled, so it must not be described as full guest-public-output authentication. -/
def SP1CommitCoveredExecutionRelation {p : ℕ} {Digest : Type}
    (layout : SP1PublicValuesLayout) (model : Machine.SP1MachineModel)
    (handler : Machine.SyscallHandler) (programBinding : ProgramBinding p Digest)
    (globalBalance : GlobalCumulativeBalance p)
    (deferredAuthenticated : DeferredDigestAuthenticated p) :
    WitnessRelation.Relation (SP1ExecutionStatement (ZMod p) Digest) SP1ExecutionWitness :=
  fun statement witness =>
    SP1ExecutionRelation layout model handler programBinding globalBalance
        deferredAuthenticated statement witness ∧
      CompleteCommitCoverage witness.segments

/-- A verifying-key-specific contract asserting that every program admitted by the binding relation
uses the standard halt wrapper.  It can be proved from the exact committed ROM, or retained as an
explicit application-level hypothesis until program correctness is formalized. -/
def OutputSafeVerifyingKey {p : ℕ} {Digest : Type} (handler : Machine.SyscallHandler)
    (programBinding : ProgramBinding p Digest)
    (verifyingKey : SP1MachineVerifyingKey (ZMod p) Digest) : Prop :=
  ∀ program, programBinding verifyingKey program →
    UsesStandardHaltWrapper (p := p) handler program

/-- A base execution plus correctness of its selected program's halt wrapper has complete COMMIT
coverage.  AIR supplies correctness of every row that exists; `wrapper` supplies existence. -/
theorem commitCovered_of_standardWrapper {p : ℕ} {Digest : Type}
    {layout : SP1PublicValuesLayout} {model : Machine.SP1MachineModel}
    {handler : Machine.SyscallHandler} {programBinding : ProgramBinding p Digest}
    {globalBalance : GlobalCumulativeBalance p}
    {deferredAuthenticated : DeferredDigestAuthenticated p}
    {statement : SP1ExecutionStatement (ZMod p) Digest} {witness : SP1ExecutionWitness}
    (valid : SP1ExecutionRelation layout model handler programBinding globalBalance
      deferredAuthenticated statement witness)
    (wrapper : UsesStandardHaltWrapper (p := p) handler witness.program) :
    SP1CommitCoveredExecutionRelation layout model handler programBinding globalBalance
      deferredAuthenticated statement witness := by
  refine ⟨valid, ?_⟩
  rcases valid with ⟨_, _, _, _, _, _, _, _, shardLayout, halts, _⟩
  exact wrapper shardLayout halts

/-- A verification key satisfying the application-level output-safety contract supplies the wrapper
hypothesis for whichever bound program appears in the recovered execution. -/
theorem commitCovered_of_outputSafeVerifyingKey {p : ℕ} {Digest : Type}
    {layout : SP1PublicValuesLayout} {model : Machine.SP1MachineModel}
    {handler : Machine.SyscallHandler} {programBinding : ProgramBinding p Digest}
    {globalBalance : GlobalCumulativeBalance p}
    {deferredAuthenticated : DeferredDigestAuthenticated p}
    {statement : SP1ExecutionStatement (ZMod p) Digest} {witness : SP1ExecutionWitness}
    (valid : SP1ExecutionRelation layout model handler programBinding globalBalance
      deferredAuthenticated statement witness)
    (outputSafe : OutputSafeVerifyingKey handler programBinding statement.verifyingKey) :
    SP1CommitCoveredExecutionRelation layout model handler programBinding globalBalance
      deferredAuthenticated statement witness :=
  commitCovered_of_standardWrapper valid
    (outputSafe witness.program valid.2.2.2.1)

end SP1Clean.Execution
