import SP1Clean.FormalModel.Relations
import SP1Clean.Model.Machine.Shard

/-! # One semantic relation for a Core shard

This is the public semantic center shared by soundness and completeness.  It has one statement
parameter, one proof-free witness (`Machine.CoreShardSemanticWitness`), and one operational model.
Native and exact AIRs specialize the small `CoreShardContract` hook; they do not define competing
execution carriers or competing notions of a valid shard.

The operational content is fixed here: a private initial state, deterministic event evaluator,
official Sail validity, clock/PC endpoints, code loading, configuration, and a
finite canonical Memory boundary.  A specialization may add profile facts (instruction routing,
commit rows, verifying-key configuration), but cannot replace those common execution clauses. -/

open LeanRV64D.Defs

namespace SP1Clean.Execution

open Sail LeanRV64D
open SP1Clean.Machine
open SP1Clean.Soundness.Target

/-- The deliberately narrow extension hook around the fixed Core-shard semantics.

`statementValid` and `programValid` describe authenticated public/profile data.  `boundaryValid`
and `executionValid` add branch-specific laws such as commit-row behavior or the ordinary
instruction routing profile.  They supplement, rather than restate, the common clauses below. -/
structure CoreShardContract (Statement : Type) where
  statementValid : Statement → Prop := fun _ => True
  programValid : Statement → GuestProgram → Prop := fun _ _ => True
  witnessValid : Statement → CoreShardSemanticWitness → Prop := fun _ _ => True
  boundaryValid : Statement → CoreShardSemanticWitness → Prop := fun _ _ => True
  executionValid : Statement → CoreShardSemanticWitness →
    EventExecutionTrace → Prop := fun _ _ _ => True

/-- The two branches of the one canonical shard relation.  The execution trace is not independent
witness data: it must be the result of evaluating the event list stored in `witness`. -/
inductive CoreShardCase {Statement : Type} (model : CoreShardModel Statement)
    (contract : CoreShardContract Statement) (statement : Statement)
    (witness : CoreShardSemanticWitness) : Prop
  | boundary :
      (model.boundary statement).isExecution = false →
      witness.events = none →
      (model.boundary statement).initialPc = (model.boundary statement).finalPc →
      (model.boundary statement).initialClock = (model.boundary statement).finalClock →
      contract.boundaryValid statement witness →
      CoreShardCase model contract statement witness
  | execution (events : List ExecutionEvent) (trace : EventExecutionTrace) :
      (model.boundary statement).isExecution = true →
      witness.events = some events →
      witness.trace? model = some trace →
      trace.Valid model.syscalls.relation witness.program →
      trace.Clocked (model.boundary statement).initialClock →
      trace.finalClock (model.boundary statement).initialClock =
        (model.boundary statement).finalClock →
      trace.initialState.regs.get? Register.PC =
        some (model.boundary statement).initialPc →
      trace.finalState.regs.get? Register.PC =
        some (model.boundary statement).finalPc →
      contract.executionValid statement witness trace →
      CoreShardCase model contract statement witness

/-- Named validity record for the single semantic Core-shard relation. -/
structure CoreShardExecutionValid {Statement : Type} (model : CoreShardModel Statement)
    (contract : CoreShardContract Statement) (statement : Statement)
    (witness : CoreShardSemanticWitness) : Prop where
  statementValid : contract.statementValid statement
  programWellFormed : witness.program.WellFormed
  programBound : model.programBound statement witness.program
  programValid : contract.programValid statement witness.program
  contractValid : contract.witnessValid statement witness
  romLoaded : RomLoaded witness.program witness.initialState
  configured : SailConfigured witness.initialState
  codeMemoryCompatible :
    SailCodeMemoryCompatible witness.program witness.initialState
  memoryWellFormed : witness.memoryBoundary.WellFormed
    (model.boundary statement).finalClock
  memoryAgrees : witness.memoryBoundary.AgreesWith witness.initialState
    (witness.evaluatedTrace model).finalState
  shardCase : CoreShardCase model contract statement witness

/-- The canonical semantic relation.  All public native/exact aliases must reduce to this
definition rather than introduce another validity structure. -/
def CoreShardExecutionRelation {Statement : Type} (model : CoreShardModel Statement)
    (contract : CoreShardContract Statement) :
    WitnessRelation.Relation Statement CoreShardSemanticWitness :=
  CoreShardExecutionValid model contract

namespace CoreShardExecutionValid

/-- Eliminate an execution shard to the uniquely evaluated official-Sail trace. -/
theorem executionTrace {Statement : Type} {model : CoreShardModel Statement}
    {contract : CoreShardContract Statement} {statement : Statement}
    {witness : CoreShardSemanticWitness}
    (valid : CoreShardExecutionValid model contract statement witness)
    (isExecution : (model.boundary statement).isExecution = true) :
    ∃ events trace,
      witness.events = some events ∧
        witness.trace? model = some trace ∧
        trace.Valid model.syscalls.relation witness.program ∧
        trace.Clocked (model.boundary statement).initialClock ∧
        trace.finalClock (model.boundary statement).initialClock =
          (model.boundary statement).finalClock ∧
        trace.initialState.regs.get? Register.PC =
          some (model.boundary statement).initialPc ∧
        trace.finalState.regs.get? Register.PC =
          some (model.boundary statement).finalPc ∧
        contract.executionValid statement witness trace := by
  cases valid.shardCase with
  | boundary notExecution => simp [isExecution] at notExecution
  | execution events trace execution hasEvents evaluated traceValid clocked finalClock initialPc
      finalPc profile =>
      exact ⟨events, trace, hasEvents, evaluated, traceValid, clocked, finalClock,
        initialPc, finalPc, profile⟩

end CoreShardExecutionValid

end SP1Clean.Execution
