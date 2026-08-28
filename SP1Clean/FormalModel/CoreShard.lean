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

`statementValid` and `programValid` describe authenticated public/profile data.  `executionValid`
adds execution-branch laws such as the ordinary instruction routing profile, and `haltValid` the
halting-branch discipline (the terminal transition's own laws travel in the shared `.halted`
constructor via `HaltsWith` and trace validity, so this field carries only profile-specific
structure such as the ordinary-prefix routing).  They supplement, rather than restate, the common
clauses below.  No field carries a default: every trivial instantiation is a visible, reviewable
choice at the specialization site. -/
structure CoreShardContract (Statement : Type) where
  statementValid : Statement → Prop
  programValid : Statement → GuestProgram → Prop
  witnessValid : Statement → CoreShardSemanticWitness → Prop
  executionValid : Statement → CoreShardSemanticWitness →
    EventExecutionTrace → Prop
  haltValid : Statement → CoreShardSemanticWitness →
    EventExecutionTrace → Prop

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
  | halted (events : List ExecutionEvent) (trace : EventExecutionTrace) :
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
      trace.HaltsWith witness.program (model.boundary statement).exit →
      contract.haltValid statement witness trace →
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

/-- **Total elimination of an execution shard**: the evaluated trace either satisfies the
ordinary execution contract or halts with the boundary's committed exit code under the halting
contract.  All common facts (validity, clocks, pc endpoints) hold in both branches. -/
theorem executionTrace_cases {Statement : Type} {model : CoreShardModel Statement}
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
        (contract.executionValid statement witness trace ∨
          (trace.HaltsWith witness.program (model.boundary statement).exit ∧
            contract.haltValid statement witness trace)) := by
  cases valid.shardCase with
  | boundary notExecution => simp [isExecution] at notExecution
  | execution events trace execution hasEvents evaluated traceValid clocked finalClock initialPc
      finalPc profile =>
      exact ⟨events, trace, hasEvents, evaluated, traceValid, clocked, finalClock,
        initialPc, finalPc, Or.inl profile⟩
  | halted events trace execution hasEvents evaluated traceValid clocked finalClock initialPc
      finalPc halts profile =>
      exact ⟨events, trace, hasEvents, evaluated, traceValid, clocked, finalClock,
        initialPc, finalPc, Or.inr ⟨halts, profile⟩⟩

/-- Eliminate an execution shard to the uniquely evaluated official-Sail trace.  The `noHalt`
premise (the evaluated trace is all-ordinary) refutes the halting branch, whose terminal
transition is a syscall. -/
theorem executionTrace {Statement : Type} {model : CoreShardModel Statement}
    {contract : CoreShardContract Statement} {statement : Statement}
    {witness : CoreShardSemanticWitness}
    (valid : CoreShardExecutionValid model contract statement witness)
    (isExecution : (model.boundary statement).isExecution = true)
    (noHalt : (witness.evaluatedTrace model).AllOrdinary) :
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
  | halted events trace execution hasEvents evaluated traceValid clocked finalClock initialPc
      finalPc halts profile =>
      exfalso
      obtain ⟨transition, event, hlast, hevent, -, -, -⟩ := halts
      have hmem : transition ∈ trace.transitions := List.mem_of_getLast? hlast
      have hord := noHalt transition
        (by rwa [witness.evaluatedTrace_eq_of_trace? evaluated])
      rw [hevent] at hord
      cases hord

end CoreShardExecutionValid

end SP1Clean.Execution
