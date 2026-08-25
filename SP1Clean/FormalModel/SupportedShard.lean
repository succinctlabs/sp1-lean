import SP1Clean.FormalModel.Execution
import SP1Clean.FormalModel.CoreProfile
import SP1Clean.Model.Semantics.TransitionView
import SP1Clean.Model.Semantics.ProgramCommitment

/-!
# Exact semantic relation for the native ordinary-instruction shard

This module is the semantic side shared by soundness and completeness. It deliberately contains no
Clean table, physical row, provider inventory, or field-valued instruction event. A witness is the
one proof-free `Machine.EventExecutionTrace`; validity says that it is an ordinary official-Sail
segment, that every fetched instruction routes through the canonical 25-chip profile, and that its
public endpoints and program boundary are honest.

The existing `SupportedCoreLocalExecutionRelation` is a deliberately broad Sail target useful to
soundness. `SupportedOrdinaryShardExecutionRelation` supplies the shared semantic validity, and
`SupportedCoreOrdinaryShardExecutionRelation` restricts that same relation to the pinned Core shard
budget. Keeping both views here prevents completeness from defining "supported execution" in terms
of a generated AIR trace or introducing a second execution carrier.
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

/-- Named audit surface of one native-supported semantic shard.

`segment` owns the official event-step relation, schedule, and public endpoints. The remaining
fields are exactly the program/boundary facts needed in the opposite directions: the honest encoder
can represent the program, Sail begins from loaded/configured code, code bytes remain compatible
with SP1's immutable Program table, and every normally retiring ordinary decode belongs to the
25-chip profile. -/
structure SupportedOrdinaryShardExecutionValid {p : ℕ} [Fact p.Prime]
    (handler : Machine.SyscallHandler)
    (statement : SupportedCoreStatement p)
    (execution : Machine.EventExecutionTrace) : Prop where
  publicValuesWellFormed : statement.publicValues.LimbBounds
  programWellFormed : statement.program.WellFormed
  programEncodable : Commit.Encodable statement.program
  romLoaded : RomLoaded statement.program execution.initialState
  configured : SailConfigured execution.initialState
  codeMemoryCompatible : SailCodeMemoryCompatible statement.program execution.initialState
  segment : EventSegmentMatches (handler := handler)
    (SP1Clean.Semantics.clkNat statement.publicValues.init_clk_high
      statement.publicValues.init_clk_low)
    (supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
      statement.publicValues.init_pc2)
    (SP1Clean.Semantics.clkNat statement.publicValues.final_clk_high
      statement.publicValues.final_clk_low)
    (supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
      statement.publicValues.final_pc2)
    statement.program execution
  allOrdinary : execution.AllOrdinary
  supported : AllTransitionsSupported statement.program execution

/-- Exact semantic witness relation for the native 25-chip ordinary slice. -/
def SupportedOrdinaryShardExecutionRelation {p : ℕ} [Fact p.Prime]
    (handler : Machine.SyscallHandler) :
    WitnessRelation.Relation (SupportedCoreStatement p)
      Machine.EventExecutionTrace :=
  SupportedOrdinaryShardExecutionValid handler

/-- The one capacity-bounded semantic language shared by native soundness and completeness.

This is a restriction of `SupportedOrdinaryShardExecutionRelation`, not a second semantic model:
the public statement, proof-free execution witness, and all semantic fields are literally shared.
Only the pinned v6.4.0 ordinary-row budget is added. -/
def SupportedCoreOrdinaryShardExecutionRelation {p : ℕ} [Fact p.Prime]
    (handler : Machine.SyscallHandler) :
    WitnessRelation.Relation (SupportedCoreStatement p)
      Machine.EventExecutionTrace :=
  (SupportedOrdinaryShardExecutionRelation handler).restrict fun _ execution =>
    _root_.SP1Clean.CoreProfile.WithinOrdinaryRowLimit execution.steps

/-- The exact relation exposes an official Sail chain without translating through another custom
execution model. -/
theorem SupportedOrdinaryShardExecutionValid.sailChain {p : ℕ} [Fact p.Prime]
    {handler : Machine.SyscallHandler}
    {statement : SupportedCoreStatement p}
    {execution : Machine.EventExecutionTrace}
    (valid : SupportedOrdinaryShardExecutionValid handler statement execution) :
    SailChain execution.steps execution.initialState execution.finalState :=
  execution.sailChain valid.segment.1 valid.allOrdinary

/-- Every located transition in the exact relation is ordinary, independently of the projected
view retained by `SupportedSP1Transition`. -/
theorem SupportedOrdinaryShardExecutionValid.located_event_eq_ordinary {p : ℕ}
    [Fact p.Prime]
    {handler : Machine.SyscallHandler}
    {statement : SupportedCoreStatement p}
    {execution : Machine.EventExecutionTrace}
    (valid : SupportedOrdinaryShardExecutionValid handler statement execution)
    {located : Machine.LocatedTransition} (member : located ∈ execution.locatedTransitions) :
    located.transition.event = .ordinary :=
  (valid.supported located member).1

end SP1Clean.Execution
