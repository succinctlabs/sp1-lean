import SP1Clean.FormalModel.CoreShard
import SP1Clean.FormalModel.Execution
import SP1Clean.Model.Core.Profile
import SP1Clean.Model.Semantics.TransitionView
import SP1Clean.Model.Semantics.ProgramCommitment

/-!
# Exact semantic relation for the native ordinary-instruction shard

This module specializes the canonical Core-shard relation for the syscall-free 25-chip native
profile.  It deliberately contains no Clean table, physical row, provider inventory, or
field-valued instruction event.  Soundness and completeness consume the same proof-free
`Machine.CoreShardSemanticWitness`; its event transcript evaluates to an ordinary official-Sail
segment whose every fetched instruction routes through the supported profile.
-/

open LeanRV64D.Defs

namespace SP1Clean.Execution

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target

/-- One chronological transition retires normally, fetches, decodes, and routes to the canonical
supported profile.

The proof-free fields live in the one Model-layer `SP1TransitionView` consumed by both proof
directions. The decode is pinned once for every configured Sail state; its run at the actual source
is a projection of that shared fact, not a separate completeness premise. The compiler retains the
same projected view rather than reconstructing a completeness-only tuple. -/
def SupportedSP1Transition (program : GuestProgram)
    (located : Machine.LocatedTransition) : Prop :=
  located.transition.event = .ordinary ∧
    SailRetiresNormally located.source located.transition.target ∧
    SailConfigured located.source ∧
    ∃ view : SP1Clean.Semantics.SP1TransitionView,
      SP1Clean.Semantics.projectSP1Transition? program located = some view ∧
        ConfiguredDecode view.word view.decoded

/-- Every **ordinary** transition of a proof-free execution routes through the native instruction
registry.

The quantifier is arm-split rather than global.  A syscall transition's meaning does not come from
the instruction-routing profile at all: it travels in `Machine.EventStep.syscall`'s own
`SyscallTransition`, authenticated by trace validity in `CoreShardCase`.  Demanding
`SupportedSP1Transition` of it would demand `event = .ordinary`, which is exactly the restriction
this profile is dropping. -/
def AllTransitionsSupported (program : GuestProgram)
    (execution : Machine.EventExecutionTrace) : Prop :=
  ∀ located ∈ execution.locatedTransitions,
    located.transition.event = .ordinary → SupportedSP1Transition program located

/-- **The supported halting discipline**: every ordinary transition before the terminal halt is a
supported instruction, and the ordinary prefix fits the Core row budget.  The terminal
transition's own laws — the canonical HALT code, the exit-code binding, and the endpoint
states — travel in the shared `.halted` constructor through `HaltsWith` and trace validity, so
this predicate deliberately restates none of them.

The prefix is no longer required to be all-ordinary: a halting shard may take inline syscalls
before its terminal HALT, and each such transition is authenticated by `EventStep.syscall`.  The
row budget is charged against the prefix's *ordinary* transitions, which is what the native side
supplies (`realDecodedInstructionRows`, an instruction-row count that never included syscall
rows). -/
def SupportedHaltingTrace (program : GuestProgram)
    (execution : Machine.EventExecutionTrace) : Prop :=
  (∀ located ∈ execution.locatedTransitions.dropLast,
    located.transition.event = .ordinary → SupportedSP1Transition program located) ∧
  _root_.SP1Clean.Model.Core.Profile.WithinOrdinaryRowLimit
    (Machine.ordinaryTransitionCount execution.transitions.dropLast)

/-- Recover the un-split routing obligation on an all-ordinary trace: every located transition is
supported, with no side condition.  This is the shape every syscall-free consumer already wants, and
supplying it is what keeps those consumers unchanged by the arm split. -/
theorem AllTransitionsSupported.all_of_allOrdinary {program : GuestProgram}
    {execution : Machine.EventExecutionTrace}
    (supported : AllTransitionsSupported program execution)
    (ordinary : execution.AllOrdinary) :
    ∀ located ∈ execution.locatedTransitions, SupportedSP1Transition program located :=
  fun located mem => supported located mem
    (ordinary _ (Machine.EventExecutionTrace.mem_transitions_of_mem_locatedTransitions mem))

/-- Eliminate one supported transition to the exact shared projection and stable decode evidence. -/
theorem SupportedSP1Transition.view
    {program : GuestProgram} {located : Machine.LocatedTransition}
    (supported : SupportedSP1Transition program located) :
    ∃ view : SP1Clean.Semantics.SP1TransitionView,
      SP1Clean.Semantics.projectSP1Transition? program located = some view ∧
        ConfiguredDecode view.word view.decoded :=
  supported.2.2.2

/-- The shared projection exposes the actual-source official decode without choosing another
instruction or chip identity. -/
theorem SupportedSP1Transition.decodeLocated
    {program : GuestProgram} {located : Machine.LocatedTransition}
    (supported : SupportedSP1Transition program located) :
    ∃ view : SP1Clean.Semantics.SP1TransitionView,
      SP1Clean.Semantics.projectSP1Transition? program located = some view ∧
        SP1Clean.Semantics.decodeLocated? program located = some view.decoded := by
  obtain ⟨view, projected, -⟩ := supported.view
  exact ⟨view, projected, SP1Clean.Semantics.projectSP1Transition?_decode projected⟩

/-- A routed ordinary transition cannot be the host-handled `ECALL` boundary.  This derives the
negative premise of `Machine.EventStep.ordinary` from the exact transition evidence itself: the
official decoder maps the fixed ECALL word to the unsupported `.ECALL` constructor. -/
theorem SupportedSP1Transition.notAboutToExecuteEcall
    {program : GuestProgram} {located : Machine.LocatedTransition}
    (supported : SupportedSP1Transition program located) :
    ¬ Machine.AboutToExecuteEcall program located.source := by
  rintro ⟨ecallPc, ecallPcEq, ecallFetch⟩
  obtain ⟨_, _, cfg, view, projected, decode⟩ := supported
  obtain ⟨pcEq, fetch, -, -, -, routed, -⟩ :=
    SP1Clean.Semantics.projectSP1Transition?_components projected
  have ecallPcEq' : ecallPc = view.pc := by
    rw [ecallPcEq] at pcEq
    exact Option.some.inj pcEq
  subst ecallPc
  have wordEq : view.word = ECALL_ENC := by
    rw [fetch] at ecallFetch
    exact Option.some.inj ecallFetch
  rw [wordEq] at decode
  have ecallDecode :
      (ext_decode ECALL_ENC).run located.source =
        .ok (LeanRV64D.Defs.instruction.ECALL ()) located.source := by
    simpa [ECALL_ENC] using SailDecode.decode_ECALL located.source cfg.init cfg.priv
      cfg.mseccfg_disabled
  have instructionEq : view.decoded = LeanRV64D.Defs.instruction.ECALL () := by
    have same := (decode located.source cfg).symm.trans ecallDecode
    injection same
  rw [instructionEq] at routed
  simp [instructionRouteId, instructionRouteKey] at routed

/-! ## Canonical native specialization -/

/-- Decode the native prefix statement into the common public execution coordinates. -/
def supportedCoreShardBoundary {p : ℕ} [Fact p.Prime]
    (statement : SupportedCoreStatement p) : Machine.CoreShardBoundary where
  isExecution := true
  initialClock := SP1Clean.Semantics.clkNat statement.publicValues.init_clk_high
    statement.publicValues.init_clk_low
  initialPc := supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
    statement.publicValues.init_pc2
  finalClock := SP1Clean.Semantics.clkNat statement.publicValues.final_clk_high
    statement.publicValues.final_clk_low
  finalPc := supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
    statement.publicValues.final_pc2
  exit := statement.publicValues.exitCodeBits

/-- Operational model of the syscall-free native instruction profile.  Program identity is one
field of the model, so neither proof direction can silently execute a different ROM. -/
def supportedCoreShardModel {p : ℕ} [Fact p.Prime] :
    Machine.CoreShardModel (SupportedCoreStatement p) where
  boundary := supportedCoreShardBoundary
  programBound := fun statement program => program = statement.program
  syscalls := .haltOnly

/-- Profile-specific additions around the one common shard semantics. -/
def supportedCoreShardContract {p : ℕ} [Fact p.Prime] :
    CoreShardContract (SupportedCoreStatement p) where
  statementValid := fun statement => statement.publicValues.LimbBounds
  programValid := fun _ program => Commit.Encodable program
  -- Deliberately trivial: the native provider binding travels in
  -- `SupportedCoreNativeRelation`'s boundary conjunct, not in the shard contract.
  witnessValid := fun _ _ => True
  haltValid := fun _ witness execution => SupportedHaltingTrace witness.program execution
  -- `HaltFree`, not `AllOrdinary`: the execution branch's real content is that this shard does not
  -- take the terminal HALT, and that is also what keeps it disjoint from the `.halted` branch once
  -- mid-shard syscall transitions are admitted.  `AllOrdinary` used to serve both roles at once.
  executionValid := fun _ witness execution =>
    execution.HaltFree ∧
      AllTransitionsSupported witness.program execution ∧
      _root_.SP1Clean.Model.Core.Profile.WithinOrdinaryRowLimit execution.ordinarySteps

/-- The single capacity-bounded semantic language for the supported native Core profile. -/
abbrev SupportedCoreShardExecutionValid {p : ℕ} [Fact p.Prime] :=
  CoreShardExecutionValid (supportedCoreShardModel (p := p))
    (supportedCoreShardContract (p := p))

/-- Public native specialization of `CoreShardExecutionRelation`. -/
def SupportedCoreShardExecutionRelation {p : ℕ} [Fact p.Prime] :
    WitnessRelation.Relation (SupportedCoreStatement p) Machine.CoreShardSemanticWitness :=
  CoreShardExecutionRelation (supportedCoreShardModel (p := p))
    (supportedCoreShardContract (p := p))

/-- The syscall-free (all-ordinary) sub-language of the canonical semantic shard relation: the
set the deterministic native compiler currently targets.  Halting shards — the shared `.halted`
case, whose terminal transition is the canonical HALT syscall — sit outside it; they rejoin when
the compiler emits the terminal halt row. -/
noncomputable def SupportedCoreOrdinaryShardExecutionRelation {p : ℕ} [Fact p.Prime] :
    WitnessRelation.Relation (SupportedCoreStatement p) Machine.CoreShardSemanticWitness :=
  (SupportedCoreShardExecutionRelation (p := p)).restrict
    (fun _ witness =>
      (witness.evaluatedTrace (supportedCoreShardModel (p := p))).AllOrdinary)

namespace SupportedCoreShardExecutionValid

theorem program_eq {p : ℕ} [Fact p.Prime]
    {statement : SupportedCoreStatement p} {witness : Machine.CoreShardSemanticWitness}
    (valid : SupportedCoreShardExecutionValid statement witness) :
    witness.program = statement.program :=
  valid.programBound

theorem publicValuesWellFormed {p : ℕ} [Fact p.Prime]
    {statement : SupportedCoreStatement p} {witness : Machine.CoreShardSemanticWitness}
    (valid : SupportedCoreShardExecutionValid statement witness) :
    statement.publicValues.LimbBounds :=
  valid.statementValid

theorem programEncodable {p : ℕ} [Fact p.Prime]
    {statement : SupportedCoreStatement p} {witness : Machine.CoreShardSemanticWitness}
    (valid : SupportedCoreShardExecutionValid statement witness) :
    Commit.Encodable witness.program :=
  valid.programValid

/-- The deterministic trace selected by a valid common witness, together with every native profile
fact.  This is the sole trace-elimination rule used by the compiler; its `ordinary` premise is
the compiler's syscall-free domain restriction (`NativeTraceReady.syscallFree`), which also
refutes the `.halted` branch of the shared case. -/
theorem evaluatedTrace_facts {p : ℕ} [Fact p.Prime]
    {statement : SupportedCoreStatement p} {witness : Machine.CoreShardSemanticWitness}
    (valid : SupportedCoreShardExecutionValid statement witness)
    (ordinary : (witness.evaluatedTrace (supportedCoreShardModel (p := p))).AllOrdinary) :
    let execution := witness.evaluatedTrace (supportedCoreShardModel (p := p))
    execution.Valid Machine.ExecutableSyscallHandler.haltOnly.relation witness.program ∧
      execution.Clocked (supportedCoreShardBoundary statement).initialClock ∧
      execution.finalClock (supportedCoreShardBoundary statement).initialClock =
        (supportedCoreShardBoundary statement).finalClock ∧
      execution.initialState.regs.get? Register.PC =
        some (supportedCoreShardBoundary statement).initialPc ∧
      execution.finalState.regs.get? Register.PC =
        some (supportedCoreShardBoundary statement).finalPc ∧
      execution.AllOrdinary ∧
      AllTransitionsSupported witness.program execution ∧
      _root_.SP1Clean.Model.Core.Profile.WithinOrdinaryRowLimit execution.steps := by
  obtain ⟨events, trace, -, evaluated, traceValid, clocked, finalClock, initialPc, finalPc,
      supportedProfile⟩ := valid.executionTrace rfl ordinary
  obtain ⟨-, supported, limit⟩ := supportedProfile
  rw [witness.evaluatedTrace_eq_of_trace? evaluated] at ordinary ⊢
  rw [Machine.EventExecutionTrace.ordinarySteps_eq_steps_of_allOrdinary ordinary] at limit
  exact ⟨traceValid, clocked, finalClock, initialPc, finalPc, ordinary, supported, limit⟩

/-- **Halting-shard elimination on the supported profile**: a valid witness whose evaluated trace
takes a HALT is a halting shard — a supported prefix followed by the canonical HALT syscall
carrying the committed exit-code cell, between the committed public endpoints.

⚠ The hypothesis is `¬ HaltFree`, not `¬ AllOrdinary`.  Those coincided only while the profile
admitted no syscall at all; with mid-shard syscalls admitted, a non-halting mixed shard is
`¬ AllOrdinary` and yet squarely in the *execution* branch, so the old hypothesis would have made
this a false claim rather than an unprovable one. -/
theorem halted_facts {p : ℕ} [Fact p.Prime]
    {statement : SupportedCoreStatement p} {witness : Machine.CoreShardSemanticWitness}
    (valid : SupportedCoreShardExecutionValid statement witness)
    (notHaltFree :
      ¬ (witness.evaluatedTrace (supportedCoreShardModel (p := p))).HaltFree) :
    (witness.evaluatedTrace (supportedCoreShardModel (p := p))).Valid
        Machine.ExecutableSyscallHandler.haltOnly.relation witness.program ∧
      (witness.evaluatedTrace (supportedCoreShardModel (p := p))).Clocked
        (supportedCoreShardBoundary statement).initialClock ∧
      (witness.evaluatedTrace (supportedCoreShardModel (p := p))).finalClock
          (supportedCoreShardBoundary statement).initialClock =
        (supportedCoreShardBoundary statement).finalClock ∧
      (witness.evaluatedTrace (supportedCoreShardModel (p := p))).initialState.regs.get?
          Register.PC = some (supportedCoreShardBoundary statement).initialPc ∧
      (witness.evaluatedTrace (supportedCoreShardModel (p := p))).finalState.regs.get?
          Register.PC = some (supportedCoreShardBoundary statement).finalPc ∧
      (witness.evaluatedTrace (supportedCoreShardModel (p := p))).HaltsWith witness.program
        (supportedCoreShardBoundary statement).exit ∧
      SupportedHaltingTrace witness.program
        (witness.evaluatedTrace (supportedCoreShardModel (p := p))) := by
  obtain ⟨events, trace, -, evaluated, traceValid, clocked, finalClock, initialPc, finalPc,
      branch⟩ := valid.executionTrace_cases rfl
  rw [witness.evaluatedTrace_eq_of_trace? evaluated] at notHaltFree ⊢
  rcases branch with exec | ⟨halts, haltValid⟩
  · exact absurd exec.1 notHaltFree
  · exact ⟨traceValid, clocked, finalClock, initialPc, finalPc, halts, haltValid⟩

end SupportedCoreShardExecutionValid

end SP1Clean.Execution
