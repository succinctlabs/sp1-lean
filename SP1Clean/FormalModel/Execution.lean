import SP1Clean.FormalModel.Contracts.CoreAIR
import SP1Clean.FormalModel.Contracts.PublicValues
import SP1Clean.FormalModel.CoreShard
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
execution theorem, after shard continuity and the recursion completion checks have been proved.

Like its `Relations`/`CoreProfile`/`CoreAIRRelation`/`Verifier` siblings, part of this module is
reserved relation-level API for the exact-AIR/ArkLib composition — declared ahead of the consumer
that will instantiate it, so some declarations are expected to be unreferenced in-tree today. -/

open LeanRV64D.Defs

namespace SP1Clean.Execution

open Sail LeanRV64D
open SP1Clean.Soundness.Target

/-- A public AIR statement binds a program as well as its public-values record. -/
structure ProgramStatement (PublicValues : Type) where
  program : GuestProgram
  publicValues : PublicValues

/-- The one public statement shared by the native Core AIR relation and its ordinary-shard
semantic relation.  This belongs at the relation-model layer: soundness and completeness must not
introduce direction-specific aliases for the same program and boundary pair. -/
abbrev SupportedCoreStatement (p : ℕ) :=
  ProgramStatement (SupportedCorePrefixPublicValues (ZMod p))

/-- Recombine the current supported-core pc limbs. -/
def supportedPcBits {p : ℕ} (pc0 pc1 pc2 : ZMod p) : BitVec 64 :=
  SP1Clean.Semantics.pcBits pc0 pc1 pc2

/-! ### Named statement projections

Later relations read the four State-boundary endpoints only through these projections, so the
public-values record can widen (exit code, shard flags, digests) without touching any statement
that speaks only about pc and clock endpoints. -/

/-- The committed initial pc of a supported-core statement. -/
abbrev ProgramStatement.initPcBits {p : ℕ} (statement : SupportedCoreStatement p) : BitVec 64 :=
  supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
    statement.publicValues.init_pc2

/-- The committed final pc of a supported-core statement. -/
abbrev ProgramStatement.finalPcBits {p : ℕ} (statement : SupportedCoreStatement p) : BitVec 64 :=
  supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
    statement.publicValues.final_pc2

/-- The committed initial bus clock of a supported-core statement. -/
abbrev ProgramStatement.initClkNat {p : ℕ} (statement : SupportedCoreStatement p) : ℕ :=
  SP1Clean.Semantics.clkNat statement.publicValues.init_clk_high
    statement.publicValues.init_clk_low

/-- The committed final bus clock of a supported-core statement. -/
abbrev ProgramStatement.finalClkNat {p : ℕ} (statement : SupportedCoreStatement p) : ℕ :=
  SP1Clean.Semantics.clkNat statement.publicValues.final_clk_high
    statement.publicValues.final_clk_low

/-- The committed exit code of a supported-core statement, decoded to the Sail width. -/
abbrev ProgramStatement.exitCodeBits {p : ℕ} (statement : SupportedCoreStatement p) : BitVec 64 :=
  statement.publicValues.exitCodeBits

/-! ### The plain-Sail conclusion -/

/-- Proof-free carrier of the plain-Sail conclusion: one finite segment of the official Sail run
plus the finite Memory boundary it certifies. -/
structure SailSegmentWitness where
  initial : SailState
  steps : ℕ
  final : SailState
  memory : Machine.CoreMemoryBoundary

/-- The committed start state of one shard: the public initial pc, the committed ROM loaded, and
the platform configuration pinned.  For a first shard whose public initial pc is the program entry
point, a booted `IsInitialState` refines this via `ShardStartState.of_isInitialState`. -/
structure ShardStartState {p : ℕ} (statement : SupportedCoreStatement p) (s : SailState) :
    Prop where
  pc : s.regs.get? Register.PC = some statement.initPcBits
  romLoaded : RomLoaded statement.program s
  configured : SailConfigured s

/-- A booted initial state is a valid shard start whenever the statement's public initial pc is
the program entry point. -/
theorem ShardStartState.of_isInitialState {p : ℕ} {statement : SupportedCoreStatement p}
    {s : SailState} (boot : IsInitialState statement.program s)
    (entry : statement.initPcBits = statement.program.pc_start) :
    ShardStartState statement s :=
  { pc := by rw [entry]; exact boot.pc
    romLoaded := boot.romLoaded
    configured := boot.configured }

/-- The ordinary (all-retire) run shape of one plain-Sail shard segment: a normally-retiring
official-interpreter run between the committed public pc endpoints, taking exactly the committed
number of eight-tick instructions, with the committed exit code zero (the Exit hand-off's
ordinary-shard consequence). -/
def SailSegmentWitness.OrdinaryRun {p : ℕ} (statement : SupportedCoreStatement p)
    (w : SailSegmentWitness) : Prop :=
  SailRetireChain w.steps w.initial w.final ∧
  w.final.regs.get? Register.PC = some statement.finalPcBits ∧
  statement.finalClkNat = statement.initClkNat + 8 * w.steps ∧
  statement.publicValues.exit_code = 0

/-- The halting run shape of one plain-Sail shard segment: a normally-retiring prefix reaches a
genuine `SP1Halted` state — the pc at a committed `ECALL` word, `t0` holding the canonical `HALT`
code, `a0` the committed exit code — and the final state is that state parked at SP1's terminal
`haltPc`, one 264-tick syscall window after the prefix. -/
def SailSegmentWitness.HaltedRun {p : ℕ} (statement : SupportedCoreStatement p)
    (w : SailSegmentWitness) : Prop :=
  ∃ preHalt : SailState,
    1 ≤ w.steps ∧
    SailRetireChain (w.steps - 1) w.initial preHalt ∧
    SP1Halted statement.program statement.exitCodeBits preHalt ∧
    w.final = { preHalt with regs := preHalt.regs.insert Register.PC Machine.haltPc } ∧
    statement.finalPcBits = Machine.haltPc ∧
    statement.finalClkNat = statement.initClkNat + 8 * (w.steps - 1) + 264

/-- **The plain-Sail relation.**  What the native ensemble certifies about the official Sail
machine, with no machine-model parameter: from the committed shard start, either an ordinary
normally-retiring run between the committed public pc endpoints (`OrdinaryRun`), or a
normally-retiring prefix reaching a genuine `SP1Halted` state, terminally parked at `haltPc`
(`HaltedRun`); in both shapes the Memory boundary is well formed at the committed final clock and
agrees with real location content at both ends of the run. -/
def SupportedCoreSailRelation {p : ℕ} :
    WitnessRelation.Relation (SupportedCoreStatement p) SailSegmentWitness :=
  fun statement w =>
    statement.program.WellFormed ∧
    ShardStartState statement w.initial ∧
    w.memory.WellFormed statement.finalClkNat ∧
    w.memory.AgreesWith w.initial w.final ∧
    (SailSegmentWitness.OrdinaryRun statement w ∨
      SailSegmentWitness.HaltedRun statement w)

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

/-- Every plain-Sail conclusion yields the model-scheduled local-execution form, for any machine
model implementing the ordinary eight-tick schedule.  This is the no-strength-lost adapter: the
model parameter and schedule hypothesis of the older statement are recoverable from the
model-free `SupportedCoreSailRelation`. -/
theorem supportedCoreLocalExecution_of_sailRelation {p : ℕ}
    (model : Machine.SP1MachineModel) (ordinary : model.UsesOrdinarySchedule)
    {statement : SupportedCoreStatement p} {w : SailSegmentWitness}
    (valid : SupportedCoreSailRelation statement w)
    (run : SailSegmentWitness.OrdinaryRun statement w) :
    ∃ witness, SupportedCoreLocalExecutionRelation model statement witness := by
  obtain ⟨wellFormed, start, -, -, -⟩ := valid
  obtain ⟨chain, finalPc, clock, -⟩ := run
  let context : Machine.LocalExecutionCtx model :=
    { program := statement.program, wellFormed, initial := w.initial
      romLoaded := start.romLoaded, configured := start.configured }
  let execution : Machine.LocalExecutionSegmentWitness context :=
    { steps := w.steps
      finalState := w.final
      reached := SP1Clean.Semantics.chainState_of_sailChain chain.toSailChain }
  refine ⟨⟨context, execution⟩, wellFormed, rfl, start.pc, finalPc, ?_⟩
  show Machine.localExecutionClock context _ _ = _
  rw [Machine.localExecutionClock_eq_ordinary ordinary]
  exact clock.symm

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
  obtain ⟨wellFormed, localProgram, initialPc, finalPc, finalClock⟩ := localValid
  refine ⟨⟨global, localWitness.execution.anchor startStep
    (localProgram.trans globalProgram.symm) initialReached⟩,
    wellFormed, globalProgram, initialPc, finalPc, ?_⟩
  rwa [Machine.LocalExecutionSegmentWitness.clockAt_anchor]

/-! ## Full upstream shard statement -/

/-- The cryptographic setup seam: the machine verifying key opens to this guest program.  For SP1,
this combines the preprocessed Program table commitment, entry pc, initial global-memory sum, and
untrusted-program configuration.  The concrete relation belongs to the extracted AIR/PCS adapter;
`ProverData` by itself is not a verifying-key commitment. -/
abbrev ProgramBinding (p : ℕ) (Digest : Type) :=
  SP1MachineVerifyingKey (ZMod p) Digest → GuestProgram → Prop

/-! ## Eventful Core shard target -/

/-- An eventful execution segment agrees with the public pc and timestamp endpoints. -/
def EventSegmentMatches {handler : Machine.SyscallHandler} (initialClock : ℕ)
    (initialPc : BitVec 64) (finalClock : ℕ) (finalPc : BitVec 64)
    (program : GuestProgram) (execution : Machine.EventExecutionTrace) : Prop :=
  execution.Valid handler program ∧
    execution.Clocked initialClock ∧
    execution.initialState.regs.get? Register.PC = some initialPc ∧
    execution.finalState.regs.get? Register.PC = some finalPc ∧
    execution.finalClock initialClock = finalClock

/-! ### Canonical specialization -/

/-- Project full SP1 shard public values into the shared execution coordinates. -/
def sp1CoreShardBoundary {p : ℕ} {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest) : Machine.CoreShardBoundary where
  isExecution := decide (statement.publicValues.is_execution_shard = 1)
  initialClock := statement.publicValues.initial_timestamp.toNat
  initialPc := statement.publicValues.pcStartBits
  finalClock := statement.publicValues.last_timestamp.toNat
  finalPc := statement.publicValues.nextPcBits
  exit := statement.publicValues.exitCodeBits

/-- Exact Core operational model.  The executable host handler supplies both evaluation and the
relational graph checked by the shared semantics. -/
def sp1CoreShardModel {p : ℕ} {Digest : Type}
    (handler : Machine.ExecutableSyscallHandler)
    (programBinding : ProgramBinding p Digest) :
    Machine.CoreShardModel (SP1ShardStatement (ZMod p) Digest) where
  boundary := sp1CoreShardBoundary
  programBound := fun statement program => programBinding statement.verifyingKey program
  syscalls := handler

/-- Exact-profile laws around the fixed shared execution semantics.  COMMIT behavior is stated once
on the common syscall transcript and therefore applies uniformly to both shard branches. -/
def sp1CoreShardContract {p : ℕ} {Digest : Type}
    (layout : SP1PublicValuesLayout) :
    CoreShardContract (SP1ShardStatement (ZMod p) Digest) where
  statementValid := fun statement =>
    statement.verifyingKey.WellFormed layout ∧
      statement.publicValues.WellFormed layout ∧
      statement.ConfigurationMatches
  programValid := fun statement program =>
    BitVec.ofNat 64 statement.verifyingKey.pc_start.toNat = program.pc_start ∧
      (statement.publicValues.is_first_execution_shard = 1 →
        statement.publicValues.pcStartBits = program.pc_start ∧
          statement.publicValues.initial_timestamp.toNat = 1 ∧
          statement.publicValues.is_execution_shard = 1)
  witnessValid := fun statement witness =>
    CoreAIR.CommitRowsMatch statement.publicValues witness.syscallEvents ∧
      CoreAIR.CommitRowsSetFlags statement.publicValues witness.syscallEvents ∧
      statement.publicValues.CommitTransitionValid
  -- Deliberately trivial: the exact routing/instruction profile of an execution shard is not yet
  -- formalized at this layer; the execution branch's laws live in the refinement obligations.
  executionValid := fun _ _ _ => True
  -- Deliberately trivial: likewise for the exact halting discipline — the terminal transition's
  -- own laws (canonical code, exit binding, endpoints) travel in the shared `.halted`
  -- constructor via `HaltsWith` and trace validity.
  haltValid := fun _ _ _ => True

/-- Exact Core validity is a specialization of the one canonical shard validity record. -/
abbrev SP1CoreShardSemanticValid {p : ℕ} {Digest : Type}
    (layout : SP1PublicValuesLayout) (handler : Machine.ExecutableSyscallHandler)
    (programBinding : ProgramBinding p Digest) :=
  CoreShardExecutionValid (sp1CoreShardModel handler programBinding)
    (sp1CoreShardContract layout)

/-- Exact Core semantic target used by the paired AIR refinement and ArkLib composition seam. -/
def SP1CoreShardSemanticRelation {p : ℕ} {Digest : Type}
    (layout : SP1PublicValuesLayout) (handler : Machine.ExecutableSyscallHandler)
    (programBinding : ProgramBinding p Digest) :
    WitnessRelation.Relation (SP1ShardStatement (ZMod p) Digest)
      Machine.CoreShardSemanticWitness :=
  CoreShardExecutionRelation (sp1CoreShardModel handler programBinding)
    (sp1CoreShardContract layout)

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

/-- Every canonical COMMIT row in the composed transcript carries the terminal public digest word
for its index.  Unlike coverage, this predicate constrains rows that exist but creates none. -/
def FinalCommitRowsMatch {p : ℕ} (finalPublicValues : SP1PublicValues (ZMod p))
    (segments : List (Option Machine.EventExecutionTrace)) : Prop :=
  ∀ event ∈ executionSyscallEvents segments, ∀ index : Fin 8,
    event.IsCanonicalCode Machine.commitSyscallId → event.arg1.toNat = index →
      event.arg2 = BitVec.ofNat 64
        (finalPublicValues.committed_value_digest[index].toNat)

/-- All eight terminal public-digest words occur as canonical COMMIT rows with the exact value.
This is the honest composed claim obtained by combining program-level coverage with AIR row
correctness and authenticated rolling-digest continuity. -/
def CompleteCommitDigestMatches {p : ℕ} (finalPublicValues : SP1PublicValues (ZMod p))
    (segments : List (Option Machine.EventExecutionTrace)) : Prop :=
  ∀ index : Fin 8, ∃ event ∈ executionSyscallEvents segments,
    event.IsCanonicalCode Machine.commitSyscallId ∧ event.arg1.toNat = index ∧
      event.arg2 = BitVec.ofNat 64
        (finalPublicValues.committed_value_digest[index].toNat)

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
        CoreAIR.CommitRowsSetFlags publicValues [] ∧
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
        CoreAIR.CommitRowsSetFlags publicValues execution.syscallEvents ∧
        EventShardLayout handler program publicRest segmentRest execution.finalState target
  | _, _, _, _ => False

@[simp]
theorem executionSyscallEvents_cons_none
    (segments : List (Option Machine.EventExecutionTrace)) :
    executionSyscallEvents (none :: segments) = executionSyscallEvents segments := by
  simp [executionSyscallEvents, executionTraces]

@[simp]
theorem executionSyscallEvents_cons_some (execution : Machine.EventExecutionTrace)
    (segments : List (Option Machine.EventExecutionTrace)) :
    executionSyscallEvents (some execution :: segments) =
      execution.syscallEvents ++ executionSyscallEvents segments := by
  simp [executionSyscallEvents, executionTraces]

/-- Per-shard COMMIT operand facts lift to the terminal digest.  A row first sets its own shard's
rolling flag; the authenticated ledger and exact public-values transition laws then preserve that
digest through every later shard. -/
theorem finalCommitRowsMatch_of_layout {p : ℕ}
    {handler : Machine.SyscallHandler} {program : GuestProgram}
    {publicValues : List (SP1PublicValues (ZMod p))}
    {segments : List (Option Machine.EventExecutionTrace)}
    {initial finalState : SailState} {finalPublicValues : SP1PublicValues (ZMod p)}
    (layout : EventShardLayout handler program publicValues segments initial finalState)
    (last : publicValues.getLast? = some finalPublicValues)
    (continuous : SP1PublicValues.LedgerContinuous publicValues)
    (transitions : ∀ values ∈ publicValues, values.CommitTransitionValid) :
    FinalCommitRowsMatch finalPublicValues segments := by
  induction publicValues generalizing segments initial with
  | nil => simp at last
  | cons values rest ih =>
      cases segments with
      | nil => simp [EventShardLayout] at layout
      | cons segment segmentRest =>
          cases segment with
          | none =>
              obtain ⟨_, _, _, _, _, tailLayout⟩ := layout
              have tailMatches : FinalCommitRowsMatch finalPublicValues segmentRest := by
                cases rest with
                | nil =>
                    cases segmentRest with
                    | nil => simp [FinalCommitRowsMatch, executionSyscallEvents, executionTraces]
                    | cons next tail => simp [EventShardLayout] at tailLayout
                | cons next tail =>
                    apply ih tailLayout
                    · simpa using last
                    · exact continuous.2
                    · intro later member
                      exact transitions later (by simp [member])
              simpa [FinalCommitRowsMatch] using tailMatches
          | some execution =>
              obtain ⟨_, _, _, _, _, rowsMatch, rowsSetFlags, tailLayout⟩ := layout
              have tailMatches : FinalCommitRowsMatch finalPublicValues segmentRest := by
                cases rest with
                | nil =>
                    cases segmentRest with
                    | nil => simp [FinalCommitRowsMatch, executionSyscallEvents, executionTraces]
                    | cons next tail => simp [EventShardLayout] at tailLayout
                | cons next tail =>
                    apply ih tailLayout
                    · simpa using last
                    · exact continuous.2
                    · intro later member
                      exact transitions later (by simp [member])
              intro event member index canonical indexEq
              rw [executionSyscallEvents_cons_some] at member
              rcases List.mem_append.mp member with current | later
              · have committed := rowsSetFlags.publicCommit event current canonical
                have digestEq := SP1PublicValues.committedDigest_eq_last_of_flag
                  last continuous transitions committed
                have wordEq := congrArg (fun digest => digest[index]) digestEq
                calc
                  event.arg2 = BitVec.ofNat 64
                      (values.committed_value_digest[index].toNat) :=
                    rowsMatch.1 event current index canonical indexEq
                  _ = BitVec.ofNat 64
                      (finalPublicValues.committed_value_digest[index].toNat) := by
                    rw [wordEq]
              · exact tailMatches event later index canonical indexEq

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
        publicValues.CommitTransitionValid ∧
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

/-- Every canonical COMMIT row recovered from a valid composed execution is tied to the terminal
public digest.  This is the cross-shard provenance theorem: row-to-flag comes from the syscall AIR,
while flag/digest persistence comes from the public-values AIR and authenticated ledger. -/
theorem finalCommitRowsMatch_of_execution {p : ℕ} {Digest : Type}
    {layout : SP1PublicValuesLayout} {model : Machine.SP1MachineModel}
    {handler : Machine.SyscallHandler} {programBinding : ProgramBinding p Digest}
    {globalBalance : GlobalCumulativeBalance p}
    {deferredAuthenticated : DeferredDigestAuthenticated p}
    {statement : SP1ExecutionStatement (ZMod p) Digest} {witness : SP1ExecutionWitness}
    (valid : SP1ExecutionRelation layout model handler programBinding globalBalance
      deferredAuthenticated statement witness) :
    ∃ finalPublicValues,
      statement.shards.getLast? = some finalPublicValues ∧
        FinalCommitRowsMatch finalPublicValues witness.segments := by
  obtain ⟨_, perShard, _, _, _, _, authenticatedLedger, _, shardLayout, _,
    finalPublicValues, last, _, _⟩ := valid
  obtain ⟨_, _, _, _, _, _, _, continuous, _⟩ := authenticatedLedger
  refine ⟨finalPublicValues, last,
    finalCommitRowsMatch_of_layout shardLayout last continuous ?_⟩
  intro values member
  exact (perShard values member).2.1

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

/-- Complete wrapper coverage plus the base execution theorem supplies all eight canonical COMMIT
rows, each carrying the corresponding word of the terminal committed-value digest. -/
theorem completeCommitDigestMatches_of_coveredExecution {p : ℕ} {Digest : Type}
    {layout : SP1PublicValuesLayout} {model : Machine.SP1MachineModel}
    {handler : Machine.SyscallHandler} {programBinding : ProgramBinding p Digest}
    {globalBalance : GlobalCumulativeBalance p}
    {deferredAuthenticated : DeferredDigestAuthenticated p}
    {statement : SP1ExecutionStatement (ZMod p) Digest} {witness : SP1ExecutionWitness}
    (valid : SP1CommitCoveredExecutionRelation layout model handler programBinding globalBalance
      deferredAuthenticated statement witness) :
    ∃ finalPublicValues,
      statement.shards.getLast? = some finalPublicValues ∧
        CompleteCommitDigestMatches finalPublicValues witness.segments := by
  obtain ⟨finalPublicValues, last, rowsMatch⟩ :=
    finalCommitRowsMatch_of_execution valid.1
  refine ⟨finalPublicValues, last, ?_⟩
  intro index
  obtain ⟨event, member, canonical, indexEq⟩ := valid.2 index
  exact ⟨event, member, canonical, indexEq,
    rowsMatch event member index canonical indexEq⟩

/-- A verifying-key-specific coverage contract asserting that every program admitted by the binding
relation uses the standard halt wrapper.  It can be proved from the exact committed ROM, or retained
as an explicit application-level hypothesis until program correctness is formalized. -/
def CommitCoveringVerifyingKey {p : ℕ} {Digest : Type} (handler : Machine.SyscallHandler)
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
  have ⟨_, _, _, _, _, _, _, _, shardLayout, halts, _⟩ := valid
  exact ⟨valid, wrapper shardLayout halts⟩

/-- A verification key satisfying the application-level coverage contract supplies the wrapper
hypothesis for whichever bound program appears in the recovered execution. -/
theorem commitCovered_of_commitCoveringVerifyingKey {p : ℕ} {Digest : Type}
    {layout : SP1PublicValuesLayout} {model : Machine.SP1MachineModel}
    {handler : Machine.SyscallHandler} {programBinding : ProgramBinding p Digest}
    {globalBalance : GlobalCumulativeBalance p}
    {deferredAuthenticated : DeferredDigestAuthenticated p}
    {statement : SP1ExecutionStatement (ZMod p) Digest} {witness : SP1ExecutionWitness}
    (valid : SP1ExecutionRelation layout model handler programBinding globalBalance
      deferredAuthenticated statement witness)
    (commitCovering : CommitCoveringVerifyingKey
      handler programBinding statement.verifyingKey) :
    SP1CommitCoveredExecutionRelation layout model handler programBinding globalBalance
      deferredAuthenticated statement witness :=
  commitCovered_of_standardWrapper valid
    (commitCovering witness.program valid.2.2.2.1)

end SP1Clean.Execution
