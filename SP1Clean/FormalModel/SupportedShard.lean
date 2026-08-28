import SP1Clean.FormalModel.CoreShard
import SP1Clean.FormalModel.Execution
import SP1Clean.FormalModel.CoreProfile
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

/-- Every transition of a proof-free execution routes through the native instruction registry. -/
def AllTransitionsSupported (program : GuestProgram)
    (execution : Machine.EventExecutionTrace) : Prop :=
  ∀ located ∈ execution.locatedTransitions,
    SupportedSP1Transition program located

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

/-- Operational model of the syscall-free native instruction profile.  Program identity is one
field of the model, so neither proof direction can silently execute a different ROM. -/
def supportedCoreShardModel {p : ℕ} [Fact p.Prime] :
    Machine.CoreShardModel (SupportedCoreStatement p) where
  boundary := supportedCoreShardBoundary
  programBound := fun statement program => program = statement.program
  syscalls := .none

/-- Profile-specific additions around the one common shard semantics. -/
def supportedCoreShardContract {p : ℕ} [Fact p.Prime] :
    CoreShardContract (SupportedCoreStatement p) where
  statementValid := fun statement => statement.publicValues.LimbBounds
  programValid := fun _ program => Commit.Encodable program
  -- Deliberately trivial: the native provider binding travels in
  -- `SupportedCoreNativeRelation`'s boundary conjunct, not in the shard contract.
  witnessValid := fun _ _ => True
  executionValid := fun _ witness execution =>
    execution.AllOrdinary ∧
      AllTransitionsSupported witness.program execution ∧
      _root_.SP1Clean.CoreProfile.WithinOrdinaryRowLimit execution.steps

/-- The single capacity-bounded semantic language for the supported native Core profile. -/
abbrev SupportedCoreShardExecutionValid {p : ℕ} [Fact p.Prime] :=
  CoreShardExecutionValid (supportedCoreShardModel (p := p))
    (supportedCoreShardContract (p := p))

/-- Public native specialization of `CoreShardExecutionRelation`. -/
def SupportedCoreShardExecutionRelation {p : ℕ} [Fact p.Prime] :
    WitnessRelation.Relation (SupportedCoreStatement p) Machine.CoreShardSemanticWitness :=
  CoreShardExecutionRelation (supportedCoreShardModel (p := p))
    (supportedCoreShardContract (p := p))

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
fact.  This is the sole trace-elimination rule used by the compiler. -/
theorem evaluatedTrace_facts {p : ℕ} [Fact p.Prime]
    {statement : SupportedCoreStatement p} {witness : Machine.CoreShardSemanticWitness}
    (valid : SupportedCoreShardExecutionValid statement witness) :
    let execution := witness.evaluatedTrace (supportedCoreShardModel (p := p))
    execution.Valid Machine.ExecutableSyscallHandler.none.relation witness.program ∧
      execution.Clocked (supportedCoreShardBoundary statement).initialClock ∧
      execution.finalClock (supportedCoreShardBoundary statement).initialClock =
        (supportedCoreShardBoundary statement).finalClock ∧
      execution.initialState.regs.get? Register.PC =
        some (supportedCoreShardBoundary statement).initialPc ∧
      execution.finalState.regs.get? Register.PC =
        some (supportedCoreShardBoundary statement).finalPc ∧
      execution.AllOrdinary ∧
      AllTransitionsSupported witness.program execution ∧
      _root_.SP1Clean.CoreProfile.WithinOrdinaryRowLimit execution.steps := by
  obtain ⟨events, trace, -, evaluated, traceValid, clocked, finalClock, initialPc, finalPc,
      ordinary, supported, limit⟩ := valid.executionTrace rfl
  rw [witness.evaluatedTrace_eq_of_trace? evaluated]
  exact ⟨traceValid, clocked, finalClock, initialPc, finalPc, ordinary, supported, limit⟩

end SupportedCoreShardExecutionValid

end SP1Clean.Execution
