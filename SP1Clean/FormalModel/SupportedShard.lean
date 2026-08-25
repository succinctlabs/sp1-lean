import SP1Clean.FormalModel.Execution
import SP1Clean.FormalModel.CoreProfile
import SP1Clean.Model.Semantics.Decode
import SP1Clean.Model.Semantics.TransitionDecode
import SP1Clean.Model.Semantics.ProgramCommitment

/-!
# Exact semantic relation for the native ordinary-instruction shard

This module is the semantic side shared by soundness and completeness. It deliberately contains no
Clean table, physical row, provider inventory, or field-valued instruction event. A witness is the
one proof-free `Machine.EventExecutionTrace`; validity says that it is an ordinary official-Sail
segment, that every fetched instruction routes through the canonical 25-chip profile, and that its
public endpoints and program boundary are honest.

The existing `SupportedCoreLocalExecutionRelation` is a deliberately broad Sail target useful to
soundness. `SupportedOrdinaryShardExecutionRelation` is the exact supported image a constructive
trace compiler may consume. Keeping the exact relation here prevents completeness from defining
"supported execution" in terms of a generated AIR trace.
-/

open LeanRV64D.Defs

namespace SP1Clean.Execution

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target

/-- Public statement of the native ordinary-instruction shard, named below the Soundness layer so
both witness directions can depend on it. -/
abbrev SupportedOrdinaryShardStatement (p : ℕ) :=
  ProgramStatement (SupportedCorePrefixPublicValues (ZMod p))

/-- One chronological transition retires normally, fetches, decodes, and routes to the canonical
supported profile.

The decoded instruction and chip identity are existential facts rather than a second trace carrier.
The future compiler computes the same values from `source` and `program`; its correctness theorem
will use this predicate to show that computation cannot take an unsupported branch. -/
def SupportedDecodedTransition (program : GuestProgram)
    (located : Machine.LocatedTransition) : Prop :=
  located.transition.event = .ordinary ∧
    SailRetiresNormally located.source located.transition.target ∧
    SailConfigured located.source ∧
    ∃ pc : BitVec 64, ∃ word : BitVec 32, ∃ instruction : instruction,
      located.source.regs.get? Register.PC = some pc ∧
      program.fetchWord pc = some word ∧
      (ext_decode word).run located.source = .ok instruction located.source ∧
      ∃ chipId : InstructionChipId,
        instructionRouteId instruction = some chipId

/-- Every transition of a proof-free execution routes through the native instruction registry. -/
def AllTransitionsSupported (program : GuestProgram)
    (execution : Machine.EventExecutionTrace) : Prop :=
  ∀ located ∈ execution.locatedTransitions,
    SupportedDecodedTransition program located

/-- The precise decoder fact not supplied by `SupportedDecodedTransition`.

The exact execution relation records one official decoder run of the word fetched at the
transition's actual source PC. `decodedInROM` deliberately requires that same decoded instruction
in every configured state. This source-level premise states exactly that fetched-transition hoist;
it mentions neither a Clean row nor a Program-provider conclusion. -/
def ConfiguredDecodeStable (program : GuestProgram)
    (execution : Machine.EventExecutionTrace) : Prop :=
  ∀ located ∈ execution.locatedTransitions, ∀ pc word decoded,
    located.source.regs.get? Register.PC = some pc →
      program.fetchWord pc = some word →
      (ext_decode word).run located.source = .ok decoded located.source →
      ∀ state, SailConfigured state →
        (ext_decode word).run state = .ok decoded state

/-- The existential decode evidence in the semantic relation agrees with the compiler's total,
proof-independent decode projection. -/
theorem SupportedDecodedTransition.decodeLocated
    {program : GuestProgram} {located : Machine.LocatedTransition}
    (supported : SupportedDecodedTransition program located) :
    ∃ decoded : instruction, ∃ chipId : InstructionChipId,
      SP1Clean.Semantics.decodeLocated? program located = some decoded ∧
        instructionRouteId decoded = some chipId := by
  obtain ⟨_, _, _, pc, word, decoded, pcEq, fetch, decode, chipId, routed⟩ := supported
  exact ⟨decoded, chipId,
    SP1Clean.Semantics.decodeLocated?_eq_some_of pcEq fetch decode, routed⟩

/-- A routed ordinary transition cannot be the host-handled `ECALL` boundary.  This derives the
negative premise of `Machine.EventStep.ordinary` from the exact transition evidence itself: the
official decoder maps the fixed ECALL word to the unsupported `.ECALL` constructor. -/
theorem SupportedDecodedTransition.notAboutToExecuteEcall
    {program : GuestProgram} {located : Machine.LocatedTransition}
    (supported : SupportedDecodedTransition program located) :
    ¬ Machine.AboutToExecuteEcall program located.source := by
  rintro ⟨ecallPc, ecallPcEq, ecallFetch⟩
  obtain ⟨_, _, cfg, pc, word, instruction, pcEq, fetch, decode, chipId, routed⟩ := supported
  have ecallPcEq' : ecallPc = pc := by
    rw [ecallPcEq] at pcEq
    exact Option.some.inj pcEq
  subst ecallPc
  have wordEq : word = ECALL_ENC := by
    rw [fetch] at ecallFetch
    exact Option.some.inj ecallFetch
  subst word
  have ecallDecode :
      (ext_decode ECALL_ENC).run located.source =
        .ok (LeanRV64D.Defs.instruction.ECALL ()) located.source := by
    simpa [ECALL_ENC] using SailDecode.decode_ECALL located.source cfg.init cfg.priv
      cfg.mseccfg_disabled
  have instructionEq : instruction = LeanRV64D.Defs.instruction.ECALL () := by
    have same := decode.symm.trans ecallDecode
    injection same
  subst instruction
  simp [instructionRouteId, instructionRouteKey] at routed

/-- Named audit surface of one native-supported semantic shard.

`segment` owns the official event-step relation, schedule, and public endpoints. The remaining
fields are exactly the program/boundary facts needed in the opposite directions: the honest encoder
can represent the program, Sail begins from loaded/configured code, code bytes remain compatible
with SP1's immutable Program table, and every normally retiring ordinary decode belongs to the
25-chip profile. -/
structure SupportedOrdinaryShardExecutionValid {p : ℕ} [Fact p.Prime]
    (handler : Machine.SyscallHandler)
    (statement : SupportedOrdinaryShardStatement p)
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
    WitnessRelation.Relation (SupportedOrdinaryShardStatement p)
      Machine.EventExecutionTrace :=
  SupportedOrdinaryShardExecutionValid handler

/-- The pinned executor's ordinary-instruction row budget.  `MAX_SHARD_SIZE` is a clock budget,
and an ordinary row consumes eight ticks.  This predicate deliberately says nothing about native
representability or field capacity; those are separate properties of the compiled active witness. -/
def WithinCoreShardLimit (execution : Machine.EventExecutionTrace) : Prop :=
  execution.steps ≤ _root_.SP1Clean.CoreProfile.maxOrdinaryTransitions

/-- The exact relation exposes an official Sail chain without translating through another custom
execution model. -/
theorem SupportedOrdinaryShardExecutionValid.sailChain {p : ℕ} [Fact p.Prime]
    {handler : Machine.SyscallHandler}
    {statement : SupportedOrdinaryShardStatement p}
    {execution : Machine.EventExecutionTrace}
    (valid : SupportedOrdinaryShardExecutionValid handler statement execution) :
    SailChain execution.steps execution.initialState execution.finalState :=
  execution.sailChain valid.segment.1 valid.allOrdinary

/-- Every located transition in the exact relation is ordinary, independently of the route witness
chosen in `SupportedDecodedTransition`. -/
theorem SupportedOrdinaryShardExecutionValid.located_event_eq_ordinary {p : ℕ}
    [Fact p.Prime]
    {handler : Machine.SyscallHandler}
    {statement : SupportedOrdinaryShardStatement p}
    {execution : Machine.EventExecutionTrace}
    (valid : SupportedOrdinaryShardExecutionValid handler statement execution)
    {located : Machine.LocatedTransition} (member : located ∈ execution.locatedTransitions) :
    located.transition.event = .ordinary :=
  (valid.supported located member).1

end SP1Clean.Execution
