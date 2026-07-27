import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Extracted.CPUState
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `CPUState` reader — SP1's `CPUState::eval` as a Clean `FormalAssertion`

Faithful to SP1's `CPUState::eval(builder, cols, next_pc, clk_increment, is_real)`
(`crates/core/machine/src/adapter/state.rs`): the **composing chip owns and witnesses the `cols` block**
(clk limbs + `pc`) and passes it in, along with the `next_pc` it transitions to (for a straight-line ALU
chip, `[pc[0] + PC_INC, pc[1], pc[2]]` formed from the chip's own `cols.pc`; SP1 `add.rs:eval`) and the
clock increment `clk_inc` (`CLK_INC = 8`). The reader **witnesses nothing** — it is a `FormalAssertion`
that, given those inputs, imposes exactly SP1's per-row checks/interactions:

- two clock byte-range checks via the **byte bus** (`send_byte(Range/U8Range, …)`), as `byteChannel`
  gated receives — a 13-bit `Range` pull `⟨6, (clk_0_16-1)·8⁻¹, 13, 0⟩` and a `U8Range` pull
  `⟨3, 0, clk_16_24, 0⟩` (the byte in the `b` slot, matching SP1's `send_byte(U8Range, 0, clk_16_24, 0)`
  from `slice_range_check_u8(&[clk_16_24, 0])`, `state.rs`); and
- the two **State** bus interactions: `receive_state(clk, pc)` (`emit (-is_real)`) and
  `send_state(clk + clk_inc, next_pc)` (`emit (is_real)`).

The `Spec` is the two clock byte bounds (`is_real`-gated, exactly `Faithful/CPUState.lean`'s
`cpustate_constraints_faithful`): **soundness derives them from the byte-bus pull `Guarantees`**, and
**completeness consumes them** to discharge the pulls. The composing chip witnesses `cols` with a
padding-safe clock (`clk_0_16 = 1`, `clk_16_24 = 0`), establishing the bounds. The cross-row PC chain
stays at the trace level (`Soundness/StateConsistency.lean`). -/

namespace SP1Clean.Readers.CPUState

open Circuit
open SP1Clean.Channels (stateChannel byteChannel StateMsg)

variable {p : ℕ} [Fact p.Prime]

/-- Component-wise evaluation of the canonical CPU-state row. -/
@[circuit_norm] theorem eval_cols {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.CPUState (Expression F)) :
    Eval.eval env cols =
      ({ clk_high := Eval.eval env cols.clk_high,
         clk_16_24 := Eval.eval env cols.clk_16_24,
         clk_0_16 := Eval.eval env cols.clk_0_16,
         pc := Eval.eval env cols.pc } : Extracted.CPUState F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_clk0 {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.CPUState (Expression F)) :
    (Eval.eval env cols).clk_0_16 = Expression.eval env cols.clk_0_16 := by
  rw [eval_cols]
  simp only [circuit_norm]

@[circuit_norm] theorem eval_clk1 {F : Type} [FiniteField F]
    (env : Environment F) (cols : Extracted.CPUState (Expression F)) :
    (Eval.eval env cols).clk_16_24 = Expression.eval env cols.clk_16_24 := by
  rw [eval_cols]
  simp only [circuit_norm]

instance [Fact (2 ^ 17 < p)] : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `2 ^ 13 < p`, from which `13 < p` (the `Range` width-column round-trip in `byteRowSpec_range`)
follows. -/
lemma hn13 [Fact (2 ^ 17 < p)] : 2 ^ 13 < p := by
  have h := Fact.out (p := 2 ^ 17 < p)
  have : (2 : ℕ) ^ 13 < 2 ^ 17 := by norm_num
  omega

/-- Current-state message emitted by the reader.  Shared by `main` and its exposed-channel interface. -/
@[circuit_norm] def currentMsg (input : Var Inputs (ZMod p)) : StateMsg (Expression (ZMod p)) :=
  ⟨input.cols.clk_high, input.cols.clk_0_16 + input.cols.clk_16_24 * 65536,
    input.cols.pc[0], input.cols.pc[1], input.cols.pc[2]⟩

/-- Successor-state message emitted by the reader.  Shared by `main` and its exposed-channel interface. -/
@[circuit_norm] def nextMsg (input : Var Inputs (ZMod p)) : StateMsg (Expression (ZMod p)) :=
  ⟨input.cols.clk_high, input.cols.clk_0_16 + input.cols.clk_16_24 * 65536 + input.clk_inc,
    input.next_pc[0], input.next_pc[1], input.next_pc[2]⟩

/-- Typed State interactions emitted by `CPUState`, reusable by every composing chip. -/
def stateInteractions (input : Var Inputs (ZMod p)) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [stateChannel.pulledIf input.is_real (currentMsg input),
    stateChannel.pushedIf input.is_real (nextMsg input)]

/-- The exposed-channel form of `stateInteractions`. -/
def exposedState (input : Var Inputs (ZMod p)) : List (ExposedChannel (ZMod p)) :=
  expose stateChannel (stateInteractions input)

/-- The `cols` block is an **input** (the composing chip witnesses it), so `main` witnesses nothing and
imposes the two `is_real`-gated clock byte checks (`byteChannel` gated receives, mult `-is_real`, **raw**
value — `toRaw` (gated post-#398), padding owes nothing) plus the two State-bus interactions — `receive` the
current `(clk, cols.pc)` with `-is_real`, `send` the next `(clk + clk_inc, next_pc)` with `+is_real`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let cols := input.cols
  -- Local, shallow `is_real` boolean gate (faithful — SP1's adapter `assert_bool(is_real)`); kept inline
  -- (`assertZero`, not `=== 0`) so it is visible to `ConstraintsHold.Shallow`, discharging the off-gate
  -- byte-pull `Requirements` without keeping `byteChannel` in `channelsWithRequirements`.
  assertZero (input.is_real * (input.is_real - 1))
  byteChannel.pullIf input.is_real
    (⟨6, (cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹, Expression.const ((13 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf input.is_real
    (⟨3, 0, cols.clk_16_24, 0⟩ : ByteRow (Expression (ZMod p)))
  -- The State bus is structural. `toAccess` ignores `assumeGuarantees`, so using the typed pull/push
  -- pair preserves exactly the extracted interaction projection.
  stateChannel.pullIf input.is_real (currentMsg input)
  stateChannel.pushIf input.is_real (nextMsg input)

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  -- Channel metadata records which buses this reader touches, independently of how strong their
  -- predicates are.  The State guarantee is now `True`, but the State pull is still a genuine
  -- guarantee-bearing interaction and must remain visible to composing circuits.
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw]
  channelsLawful := by
    dsimp only [ElaboratedCircuit.ChannelsLawful]
    intro input offset
    change Operations.ChannelsLawful
      ([.assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p))
        [byteChannel.toRaw, stateChannel.toRaw]
    refine ⟨?_, ?_, ?_⟩
    · intro channel h_channel
      simp only [Operations.subcircuitChannelsWithGuarantees_assert,
        Operations.subcircuitChannelsWithGuarantees_interact,
        Operations.subcircuitChannelsWithGuarantees_nil, List.not_mem_nil] at h_channel
    · intro env
      rw [Operations.inChannelsOrGuarantees_iff_forall_mem]
      intro interaction h_interaction
      simp only [Operations.shallowInteractions_assert,
        Operations.shallowInteractions_interact, Operations.shallowInteractions_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h_interaction
      rcases h_interaction with rfl | rfl | rfl | rfl
      · exact Or.inl List.mem_cons_self
      · exact Or.inl List.mem_cons_self
      · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
    · rw [Operations.subcircuitChannelsLawful_iff_forall]
      intro subcircuit h_subcircuit
      simp only [Operations.subcircuits_assert, Operations.subcircuits_interact,
        Operations.subcircuits_nil, List.not_mem_nil] at h_subcircuit

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    (elaborated (p := p)).channelsWithGuarantees
      = ([byteChannel.toRaw, stateChannel.toRaw] : List (RawChannel (ZMod p))) := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real` is binary — the precondition for the genuinely `is_real`-gated byte receives.
Discharged by the composing chip's `is_real * (is_real - 1) = 0` gate. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

/-! ### `ProverData`-lifted forms

The reader remains a `GeneralFormalCircuit` so composing chips keep one uniform interface, but its
local contract is again purely structural.  Execution truth is derived globally. -/

/-- Soundness assumption, lifted to ignore `ProverData`. -/
def AssumptionsD (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Assumptions input

/-- Soundness spec: the two clock bounds (Contract `Spec`, unchanged), data-ignored. -/
def SpecD (input : Inputs (ZMod p)) (_ : unit (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Spec input

def ProverAssumptionsD (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Assumptions input ∧ Spec input

theorem soundness [Fact (2 ^ 17 < p)] :
    GeneralFormalCircuit.Soundness (ZMod p) main AssumptionsD SpecD := by
  circuit_proof_start
  have h13p : (13 : ℕ) < p := lt_trans (Nat.lt_two_pow_self) hn13
  simp only [circuit_norm, AssumptionsD, SpecD, Spec, Assumptions, byteChannel, stateChannel]
    at h_holds h_assumptions ⊢
  obtain ⟨h_gate, h_b1, h_b2⟩ := h_holds
  refine ⟨fun hr1 => ?_, fun h1 h0 => off_gate_vacuous h_assumptions h1 h0,
    fun h1 h0 => off_gate_vacuous h_assumptions h1 h0⟩
  have hneg : -(input_is_real) = -1 := by rw [hr1]
  refine ⟨(byteRowSpec_range _ h13p).mp ?_, ((byteRowSpec_u8range_pair _ _).mp (h_b2 hneg)).1⟩
  rw [Nat.cast_ofNat]
  exact h_b1 hneg

theorem completeness [Fact (2 ^ 17 < p)] :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main ProverAssumptionsD
      (fun _ _ _ => True) := by
  circuit_proof_start
  have h13p : (13 : ℕ) < p := lt_trans (Nat.lt_two_pow_self) hn13
  simp only [ProverAssumptionsD, Assumptions, Spec] at h_assumptions
  obtain ⟨h_bin, h_spec⟩ := h_assumptions
  simp only [circuit_norm, byteChannel, stateChannel]
  refine ⟨?_, ?_, ?_⟩
  · rcases h_bin with h | h <;> simp [h]
  · intro hneg
    obtain ⟨hb1, _⟩ := h_spec (neg_inj.mp hneg)
    have key := (byteRowSpec_range _ h13p).mpr hb1
    rw [Nat.cast_ofNat] at key
    exact key
  · intro hneg
    obtain ⟨_, hb2⟩ := h_spec (neg_inj.mp hneg)
    exact (byteRowSpec_u8range_pair _ _).mpr ⟨hb2, by rw [ZMod.val_zero]; norm_num⟩

/-- The native CPUState reader as a Clean `GeneralFormalCircuit`: takes the chip-owned `cols` block plus
`next_pc`/`clk_inc`/`is_real`, imposes the two `is_real`-gated clock byte checks and emits the structural
State interactions, with `Spec` the two clock bounds. -/
def circuit [Fact (2 ^ 17 < p)] : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  elaborated
  Assumptions := AssumptionsD
  Spec := SpecD
  ProverAssumptions := ProverAssumptionsD
  ProverSpec := fun _ _ _ => True
  soundness := soundness
  completeness := completeness
  -- This is the canonical State interface for every chip that composes `CPUState`; parent circuits
  -- recover it compositionally rather than unfolding this reader again.
  exposedChannels := fun input _ => exposedState input
  exposedChannels_eq input offset := by
    simp only [exposedState, stateInteractions]
    rw [Operations.exposedChannelsLawful_expose]
    simp only [main, currentMsg, nextMsg, circuit_norm,
      Channels.byteChannel_eq_stateChannel_false, if_false]
  channelsWithRequirements := []
  requirementsChannelsLawful input_var i₀ := by
    change Operations.RequirementsChannelsLawful
      ([.assert _, .interact _, .interact _, .interact _, .interact _] : Operations (ZMod p))
        [byteChannel.toRaw, stateChannel.toRaw] []
    dsimp only [Operations.RequirementsChannelsLawful]
    refine ⟨?_, ?_, ?_⟩
    · intro channel h_channel
      simp only [Operations.subcircuitChannelsWithRequirements_assert,
        Operations.subcircuitChannelsWithRequirements_interact,
        Operations.subcircuitChannelsWithRequirements_nil, List.not_mem_nil] at h_channel
    · intro channel h_channel
      simp only [Operations.shallowChannels_assert, Operations.shallowChannels_interact,
        Operations.shallowChannels_nil, List.mem_cons, List.not_mem_nil, or_false] at h_channel
      rcases h_channel with rfl | rfl | rfl | rfl
      · exact Or.inl List.mem_cons_self
      · exact Or.inl List.mem_cons_self
      · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
      · exact Or.inl (List.mem_cons_of_mem _ List.mem_cons_self)
    · intro env h_constraints
      have h_bool : (ProvableStruct.eval env input_var).is_real = 0 ∨
          (ProvableStruct.eval env input_var).is_real = 1 := by
        apply bool_of_mul_pred
        simpa only [circuit_norm] using h_constraints.1
      rw [Operations.inChannelsOrRequirements_iff_forall_mem]
      intro interaction h_interaction
      simp only [Operations.shallowInteractions_assert,
        Operations.shallowInteractions_interact, Operations.shallowInteractions_nil,
        List.mem_cons, List.not_mem_nil, or_false] at h_interaction
      rcases h_interaction with rfl | rfl | rfl | rfl
      · right
        rw [ChannelInteraction.toRaw_requirements]
        intro h1 h0
        simp only [circuit_norm] at h1 h0
        exact off_gate_vacuous h_bool h1 h0
      · right
        rw [ChannelInteraction.toRaw_requirements]
        intro h1 h0
        simp only [circuit_norm] at h1 h0
        exact off_gate_vacuous h_bool h1 h0
      · right
        simp only [ChannelInteraction.toRaw_requirements, ChannelInteraction.Requirements,
          stateChannel]
        intros
        trivial
      · right
        simp only [ChannelInteraction.toRaw_requirements, ChannelInteraction.Requirements,
          stateChannel]
        intros
        trivial

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength [Fact (2 ^ 17 < p)] (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq [Fact (2 ^ 17 < p)] :
    (circuit (p := p)).channelsWithRequirements
      = ([] : List (RawChannel (ZMod p))) := rfl

/-- The canonical State interaction pair contributed when `CPUState` is composed as a subcircuit. -/
lemma interactionsWith_state_subcircuit [Fact (2 ^ 17 < p)]
    (input : Var Inputs (ZMod p)) (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith stateChannel.toRaw
        (.subcircuit ((circuit (p := p)).toSubcircuit offset input) :: ops) =
      (stateInteractions input).map ChannelInteraction.toRaw ++
        Operations.interactionsWith stateChannel.toRaw ops := by
  refine InteractionRecovery.interactionsWith_generalSubcircuit_eq_of_singleton_exposure
    (circuit (p := p))
    ⟨stateChannel.toRaw, (stateInteractions input).map ChannelInteraction.toRaw⟩ input ops ?_
  rfl

end SP1Clean.Readers.CPUState
