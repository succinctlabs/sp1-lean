import SP1Clean.FormalModel.Contracts.PublicValues
import SP1Clean.FormalModel.Relations
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

/-- One shard is either an execution segment or a non-execution shard.  The context always carries
the program opened from the verifying key; `none` is permitted only by the non-execution branch of
`SP1ShardExecutionRelation`. -/
structure SP1ShardExecutionWitness (model : Machine.SP1MachineModel) where
  context : Machine.ExecutionCtx model
  execution : Option (Machine.ExecutionSegmentWitness context)

/-- The pc/timestamp execution projection of the real upstream shard relation.

Execution shards expose a genuine segment of the canonical Sail run.  Non-execution shards preserve
pc and timestamp exactly, as Rust's `ExecutionRecord.eval_state` requires.  Companion relations must
still cover digests, global-memory ranges and cumulative sums, deferred proofs, syscalls, and proof
nonce integrity before this projection can serve as the complete `sp1_air_sound` target. -/
noncomputable def SP1ShardExecutionRelation {p : ℕ} {Digest : Type}
    (layout : SP1PublicValuesLayout) (model : Machine.SP1MachineModel)
    (programBinding : ProgramBinding p Digest) :
    WitnessRelation.Relation (SP1ShardStatement (ZMod p) Digest)
      (SP1ShardExecutionWitness model) :=
  fun statement witness =>
    statement.verifyingKey.WellFormed layout ∧
    statement.publicValues.WellFormed layout ∧
    statement.ConfigurationMatches ∧
    programBinding statement.verifyingKey witness.context.program ∧
    BitVec.ofNat 64 statement.verifyingKey.pc_start.toNat = witness.context.program.pc_start ∧
    (statement.publicValues.is_first_execution_shard = 1 →
      statement.publicValues.pcStartBits = witness.context.program.pc_start) ∧
    ((statement.publicValues.is_execution_shard = 0 ∧
        witness.execution = none ∧
        statement.publicValues.pc_start = statement.publicValues.next_pc ∧
        statement.publicValues.initial_timestamp = statement.publicValues.last_timestamp) ∨
      (statement.publicValues.is_execution_shard = 1 ∧
        ∃ execution, witness.execution = some execution ∧
          SegmentMatches statement.publicValues.initial_timestamp.toNat
            statement.publicValues.pcStartBits statement.publicValues.last_timestamp.toNat
            statement.publicValues.nextPcBits execution))

/-! ## Shard composition and the halted execution relation -/

/-- The non-execution fields that recursion must authenticate across a shard ledger.  A concrete
instantiation covers the committed-value and deferred-proof digests, global-memory address/page
ranges and cumulative sums, syscall flags, proof nonce, and empty-shard rules.  Keeping this as a
named parameter is preferable to either omitting those fields or pretending they are Sail semantics. -/
abbrev ShardIntegrity (p : ℕ) (Digest : Type) :=
  SP1MachineVerifyingKey (ZMod p) Digest → List (SP1PublicValues (ZMod p)) → Prop

/-- Alignment of public shard records with consecutive slices of one canonical Sail run.

`cursor` is the next unclaimed semantic step.  Non-execution shards consume no steps and must preserve
their execution coordinates.  An execution shard begins exactly at `cursor`, matches its public
pc/timestamp boundary, and advances the cursor by its segment length.  The final argument exposes the
cursor after the complete ledger, allowing it to be tied to a halted prefix. -/
noncomputable def SegmentLayout {p : ℕ} {model : Machine.SP1MachineModel}
    {ctx : Machine.ExecutionCtx model} :
    ℕ → List (SP1PublicValues (ZMod p)) →
      List (Option (Machine.ExecutionSegmentWitness ctx)) → ℕ → Prop
  | cursor, [], [], endStep => endStep = cursor
  | cursor, publicValues :: publicRest, none :: segmentRest, endStep =>
      publicValues.is_execution_shard = 0 ∧
        publicValues.pc_start = publicValues.next_pc ∧
        publicValues.initial_timestamp = publicValues.last_timestamp ∧
        SegmentLayout cursor publicRest segmentRest endStep
  | cursor, publicValues :: publicRest, some execution :: segmentRest, endStep =>
      publicValues.is_execution_shard = 1 ∧
        execution.startStep = cursor ∧
        SegmentMatches publicValues.initial_timestamp.toNat publicValues.pcStartBits
          publicValues.last_timestamp.toNat publicValues.nextPcBits execution ∧
        SegmentLayout (cursor + execution.steps) publicRest segmentRest endStep
  | _, _, _, _ => False

/-- Private semantic witness for a composed proof.  The shard segments are audit evidence explaining
how individual AIR results cover the run; `execution` is the single boot-to-halt canonical prefix that
the final theorem exposes. -/
structure SP1ExecutionWitness (model : Machine.SP1MachineModel) where
  context : Machine.ExecutionCtx model
  exitCode : ℕ
  segments : List (Option (Machine.ExecutionSegmentWitness context))
  execution : Machine.HaltedExecutionWitness context exitCode

/-- The honest semantic target of recursion/shard composition.

Unlike `SP1ShardExecutionRelation`, this relation begins at semantic step zero, consumes consecutive
execution shards, and ends at SP1's halting ECALL.  It deliberately takes `shardIntegrity` as an
explicit companion relation: the Sail execution projection alone cannot validate cryptographic
digests, global cumulative sums, deferred proofs, syscall bookkeeping, or nonces. -/
noncomputable def SP1ExecutionRelation {p : ℕ} {Digest : Type}
    (layout : SP1PublicValuesLayout) (model : Machine.SP1MachineModel)
    (programBinding : ProgramBinding p Digest) (shardIntegrity : ShardIntegrity p Digest) :
    WitnessRelation.Relation (SP1ExecutionStatement (ZMod p) Digest)
      (SP1ExecutionWitness model) :=
  fun statement witness =>
    statement.verifyingKey.WellFormed layout ∧
    (∀ publicValues ∈ statement.shards,
      publicValues.WellFormed layout ∧
        (SP1ShardStatement.mk statement.verifyingKey publicValues).ConfigurationMatches) ∧
    programBinding statement.verifyingKey witness.context.program ∧
    BitVec.ofNat 64 statement.verifyingKey.pc_start.toNat = witness.context.program.pc_start ∧
    shardIntegrity statement.verifyingKey statement.shards ∧
    SP1PublicValues.ExecutionContinuous statement.shards ∧
    SegmentLayout 0 statement.shards witness.segments witness.execution.steps ∧
    (∃ publicValues ∈ statement.shards, publicValues.is_execution_shard = 1) ∧
    ∃ finalPublicValues,
      statement.shards.getLast? = some finalPublicValues ∧
        finalPublicValues.exit_code.val = witness.exitCode

end SP1Clean.Execution
