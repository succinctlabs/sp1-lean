import SP1Clean.Model.Semantics.Truth

/-! # Shard-local truth over an arbitrary trajectory

`Truth.lean`'s predicates are indexed by a **Sail** chain: a State message is true when some prefix
of `try_step` iteration reaches a state with that pc, and a Memory record is true when
`chainState` — `Machine.trajectory`, i.e. `try_step` again — holds that value at the micro-time.

That index is the one thing a syscall row can never satisfy. `Machine.EventStep.syscall` deliberately
declines to claim a `SailStep`, because SP1's ECALL is not RISC-V's and unmodified Sail would trap to
an M-mode handler. Widening the clock does not reach it; the *step relation* is what has to give.

The move here is to make the trajectory a parameter rather than to write the layer twice. It is free
because determinism runs both ways — `SailChain k s₀ s ↔ chainState s₀ k = some s`
(`MicroTime.lean:184, 208`) — so the Sail-indexed predicates are exactly these generic ones at
`sailTrajectory`, and the bridges below are equivalences rather than one-way implications.

The payoff is downstream: the grounding walk is proved **once** over `Trajectory` and instantiated
twice, at `sailTrajectory` (recovering today's engine unchanged) and at
`Semantics.eventTrajectory` (admitting a mid-shard syscall row). Duplicating a twelve-hundred-line
walk at a second index was the alternative.

Two conventions worth stating, because both are load-bearing:

* A `Trajectory` is `Option`-valued and may be undefined past the shard's own length. `sailTrajectory`
  happens to be total — `try_step` is — but `eventTrajectory` is not, and every predicate below is
  written so that "undefined" simply fails to witness truth rather than needing a side condition.
* The initial state is a *separate* parameter from the trajectory. Reads before the timeline's
  genesis go to that state directly, exactly as `microValue` does today; they do not consult the
  trajectory at all. -/

namespace SP1Clean.Semantics

open Sail LeanRV64D LeanRV64D.Functions
open LeanRV64D.Defs
open SP1Clean.Soundness.Target
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The machine state after `n` semantic steps, where the shard defines one. -/
abbrev Trajectory := ℕ → Option SailState

/-- The official-Sail trajectory: every step is one `try_step`. This is the instantiation that
recovers everything the engine reads today. -/
noncomputable def sailTrajectory (initial : SailState) : Trajectory := chainState initial

@[simp] theorem sailTrajectory_apply (initial : SailState) (n : ℕ) :
    sailTrajectory initial n = chainState initial n := rfl

/-- A Sail chain and the Sail trajectory say the same thing, in both directions. This is what makes
the parameterization free rather than a weakening. -/
theorem sailTrajectory_eq_some_iff {initial state : SailState} {n : ℕ} :
    sailTrajectory initial n = some state ↔ SailChain n initial state :=
  ⟨sailChain_of_chainState, chainState_of_sailChain⟩

/-! ## The predicates -/

/-- The timeline reader over an arbitrary trajectory. Below the timeline's genesis the initial state
answers directly; at or after it, step `k`'s window is read pre- or post-effect at the location's own
effect offset. -/
noncomputable def microValueG (traj : Trajectory) (s0 : SailState) (tl : Timeline)
    (loc : MemLoc) (τ : ℕ) : Option (BitVec 64) :=
  if τ < tl.start 0 then
    locContent s0 loc
  else
    let k := tl.stepOf τ
    let δ := τ - tl.start k
    let takePost : Bool := match loc with
      | .reg _ => regEffectOffset ≤ δ
      | .ram _ => ramEffectOffset ≤ δ
    (traj (if takePost then k + 1 else k)).bind (locContent · loc)

/-- `value` is the content of `location` at `time` on this trajectory. -/
def LocalValueAtG (traj : Trajectory) (s0 : SailState) (tl : Timeline) (location : MemLoc)
    (time : ℕ) (value : Word (ZMod p)) : Prop :=
  microValueG traj s0 tl location time = some (Word.toBitVec64 value)

/-- A State message is true when the trajectory reaches a state with that pc at that clock. -/
def LocalStateTruthG (program : GuestProgram) (traj : Trajectory) (tl : Timeline)
    (m : StateMsg (ZMod p)) : Prop :=
  ∃ (n : ℕ) (state : SailState),
    traj n = some state ∧
    StateMsg.timeNat m = tl.start n ∧
    state.regs.get? Register.PC = some (pcBits m.pc0 m.pc1 m.pc2) ∧
    RomLoaded program state ∧
    SailConfigured state

/-- Memory grounding: row-local hygiene in the channel's own `Guarantees` order, then the semantic
conjunct. The field order matches `LocalMemTruth`'s so the common `.1` projection is unchanged. -/
def LocalMemTruthG (traj : Trajectory) (s0 : SailState) (tl : Timeline)
    (message : MemoryMsg (ZMod p)) : Prop :=
  SP1Clean.Channels.MemoryMsg.isU64 message ∧
  SP1Clean.Channels.MemoryMsg.ClkBound message ∧
  LocalValueAtG traj s0 tl (MemoryMsg.locOf message) (MemoryMsg.timeNat message) message.value

/-- The shard-local advance obligation: pulled truth and operand currency give pushed truth. -/
def LocalStepFactG (program : GuestProgram) (traj : Trajectory) (s0 : SailState) (tl : Timeline)
    (r : RowFacts p) : Prop :=
  LocalStateTruthG program traj tl r.statePull →
  (∀ mp ∈ r.memPulls,
    SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
    SP1Clean.Channels.MemoryMsg.ClkBound mp.1 ∧
    LocalValueAtG traj s0 tl (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
  LocalStateTruthG program traj tl r.statePush ∧
    ∀ message ∈ r.memPushes, LocalMemTruthG traj s0 tl message

/-- Untouched locations keep their value across the row's window. -/
def FrameFactG (program : GuestProgram) (traj : Trajectory) (s0 : SailState) (tl : Timeline)
    (r : RowFacts p) : Prop :=
  LocalStateTruthG program traj tl r.statePull →
  (∀ mp ∈ r.memPulls, SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
      SP1Clean.Channels.MemoryMsg.ClkBound mp.1 ∧
      LocalValueAtG traj s0 tl (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
  ∀ (loc : MemLoc) (v : Word (ZMod p)),
    (∀ m ∈ r.memPushes, MemoryMsg.locOf m = loc → m.value = v) →
    LocalValueAtG traj s0 tl loc (StateMsg.timeNat r.statePull) v →
    LocalValueAtG traj s0 tl loc (StateMsg.timeNat r.statePush) v

/-- The genesis per-key frontier is true and current at the head time. -/
def LiveOKG (traj : Trajectory) (s0 : SailState) (tl : Timeline) (t : ℕ)
    (live : MemLoc → Option (MemoryMsg (ZMod p))) : Prop :=
  ∀ (loc : MemLoc) (m : MemoryMsg (ZMod p)), live loc = some m →
    MemoryMsg.locOf m = loc ∧
    LocalMemTruthG traj s0 tl m ∧
    LocalValueAtG traj s0 tl loc t m.value ∧
    MemoryMsg.timeNat m ≤ t

/-- What the walk hands back per row. -/
def GroundedG (program : GuestProgram) (traj : Trajectory) (s0 : SailState) (tl : Timeline)
    (r : RowFacts p) : Prop :=
  LocalStateTruthG program traj tl r.statePull ∧
  ∀ mp ∈ r.memPulls, LocalMemTruthG traj s0 tl mp.1 ∧
    LocalValueAtG traj s0 tl (MemoryMsg.locOf mp.1) mp.2 mp.1.value

/-! ## The Sail bridges

Each predicate at `sailTrajectory initial` **is** the corresponding `…T` predicate. `microValueG` is
definitionally `microValueT`, so the value-level bridges are `Iff.rfl`; only the state-level one has
content, and its content is exactly determinism. -/

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
@[simp] theorem microValueG_sail (initial : SailState) (tl : Timeline) (loc : MemLoc) (τ : ℕ) :
    microValueG (sailTrajectory initial) initial tl loc τ = microValueT initial tl loc τ := rfl

omit [Fact (2 ^ 17 < p)] in
@[simp] theorem localValueAtG_sail {initial : SailState} {tl : Timeline} {loc : MemLoc} {t : ℕ}
    {v : Word (ZMod p)} :
    LocalValueAtG (sailTrajectory initial) initial tl loc t v ↔ LocalValueAtT initial tl loc t v :=
  Iff.rfl

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
theorem localStateTruthG_sail {program : GuestProgram} {initial : SailState} {tl : Timeline}
    {m : StateMsg (ZMod p)} :
    LocalStateTruthG program (sailTrajectory initial) tl m ↔ LocalStateTruthT program initial tl m := by
  unfold LocalStateTruthG LocalStateTruthT
  exact exists_congr fun n => exists_congr fun state => by
    rw [sailTrajectory_eq_some_iff]

omit [Fact (2 ^ 17 < p)] in
theorem localMemTruthG_sail {initial : SailState} {tl : Timeline} {m : MemoryMsg (ZMod p)} :
    LocalMemTruthG (sailTrajectory initial) initial tl m ↔ LocalMemTruthT initial tl m := Iff.rfl

omit [Fact (2 ^ 17 < p)] in
theorem localStepFactG_sail {program : GuestProgram} {initial : SailState} {tl : Timeline}
    {r : RowFacts p} :
    LocalStepFactG program (sailTrajectory initial) initial tl r ↔
      LocalStepFactT program initial tl r := by
  unfold LocalStepFactG LocalStepFactT
  simp only [localStateTruthG_sail, localValueAtG_sail, localMemTruthG_sail]

/-! The `FrameFactG` / `LiveOKG` / `GroundedG` bridges need their `…T` counterparts, which live in
`Soundness/TimedGrounding.lean`; they are stated there, beside `walkG`. -/

end SP1Clean.Semantics
