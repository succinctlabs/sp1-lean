import SP1Clean.FormalModel.Contracts.Readers
import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
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
open SP1Clean.Semantics (StateTruth)

variable {p : ℕ} [Fact p.Prime]

instance [Fact (2 ^ 17 < p)] : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

omit [Fact p.Prime] in
/-- `2 ^ 13 < p`, from which `13 < p` (the `Range` width-column round-trip in `byteRowSpec_range`)
follows. -/
lemma hn13 [Fact (2 ^ 17 < p)] : 2 ^ 13 < p := by
  have h := Fact.out (p := 2 ^ 17 < p)
  have : (2 : ℕ) ^ 13 < 2 ^ 17 := by norm_num
  omega

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
  let clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536
  -- State bus as a gated VM channel (W11): `receive_state` is a `pullIf` (mult `-is_real`,
  -- `assumeGuarantees := true`), `send_state` a `pushIf` (mult `+is_real`). Switching the receive from
  -- `emit (-is_real)` to `pullIf is_real` is harmless (`StateMsg.Spec = True`, so the assumed guarantee is
  -- vacuous) but is required so each chip can `expose` the `[pulledIf, pushedIf]` pair Clean's `VmTables`
  -- consumes (`tables_channel`). `toAccess` ignores `assumeGuarantees`, so the trace projection is unchanged.
  stateChannel.pullIf input.is_real ⟨cols.clk_high, clk_low, cols.pc[0], cols.pc[1], cols.pc[2]⟩
  stateChannel.pushIf input.is_real
    ⟨cols.clk_high, clk_low + input.clk_inc, input.next_pc[0], input.next_pc[1], input.next_pc[2]⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  -- The State bus is now a semantic `VmChannel`: its `pullIf` (`assumeGuarantees := true`) receives
  -- `StateTruth`, which is *not* trivially true, so `stateChannel` must join `channelsWithGuarantees`
  -- (else `InChannelsOrGuarantees` can't discharge the pull). Byte stays (its pulls receive `ByteRowSpec`).
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw]
  channelsLawful := by
    simp [circuit_norm, main, byteChannel, stateChannel]

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

/-! ### `ProverData`-lifted forms (SC Phase 2c — the State semantic flip)

`CPUState` upgrades `FormalAssertion → GeneralFormalCircuit` because its State `pullIf` now receives the
data-relative `StateTruth` guarantee (the State channel is a semantic `VmChannel`). Soundness *ignores*
the received `StateTruth` (no consumer yet — the `Spec` is the unchanged clock bounds); completeness must
*supply* it — a state push cannot prove reachability row-locally, so the honest prover (the trace
generator, which has the real Sail execution) provides it via `ProverAssumptions`. -/

/-- Soundness assumption, lifted to ignore `ProverData`. -/
def AssumptionsD (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Assumptions input

/-- Soundness spec: the two clock bounds (Contract `Spec`, unchanged), data-ignored. -/
def SpecD (input : Inputs (ZMod p)) (_ : unit (ZMod p)) (_ : ProverData (ZMod p)) : Prop := Spec input

/-- Completeness assumption: the clock bounds plus the state pull's `StateTruth` (supplied by the honest
prover — the row is a real execution step of the committed program). -/
def ProverAssumptionsD (input : Inputs (ZMod p)) (data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Assumptions input ∧ Spec input ∧ (input.is_real = 1 → StateTruth (stateMsgOf input.cols) data)

theorem soundness [Fact (2 ^ 17 < p)] :
    GeneralFormalCircuit.Soundness (ZMod p) main AssumptionsD SpecD := by
  circuit_proof_start
  have h13p : (13 : ℕ) < p := lt_trans (Nat.lt_two_pow_self) hn13
  simp only [circuit_norm, AssumptionsD, SpecD, Spec, Assumptions, byteChannel, stateChannel]
    at h_holds h_assumptions ⊢
  -- `h_holds`: gate, byte1, byte2, and the **state pull's `StateTruth`** (`h_spull`, ignored — no
  -- consumer yet). Goal: the clock bounds (from the byte pulls) + the two byte off-gate requirements.
  obtain ⟨h_gate, h_b1, h_b2, _h_spull⟩ := h_holds
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
  obtain ⟨h_bin, h_spec, h_state⟩ := h_assumptions
  -- pc limbs: the in-circuit message evaluates `var_cols_pc[i]`; the `statePullMsg` carries the value
  -- `input_cols_pc[i]` — equal by `h_input`'s vector-map (the `RTypeReader` eval-bridge idiom).
  have e : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_cols_pc[i] = input_cols_pc[i] := by
    intro i hi; have := congrArg (fun v => v[i]'hi) h_input.1.2.2.2; simpa using this
  -- The two byte pulls' completeness obligation fires only on real rows (`-is_real = -1`); the `Spec`
  -- clock bounds supply it. The State `pullIf`'s obligation is its `StateTruth` — supplied by `h_state`.
  simp only [circuit_norm, byteChannel, stateChannel]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rcases h_bin with h | h <;> simp [h]
  · intro hneg
    obtain ⟨hb1, _⟩ := h_spec (neg_inj.mp hneg)
    have key := (byteRowSpec_range _ h13p).mpr hb1
    rw [Nat.cast_ofNat] at key
    exact key
  · intro hneg
    obtain ⟨_, hb2⟩ := h_spec (neg_inj.mp hneg)
    exact (byteRowSpec_u8range_pair _ _).mpr ⟨hb2, by rw [ZMod.val_zero]; norm_num⟩
  · intro hneg
    simp only [stateMsgOf] at h_state
    rw [e 0 (by norm_num), e 1 (by norm_num), e 2 (by norm_num)]
    exact h_state (neg_inj.mp hneg)

/-- The native CPUState reader as a Clean `GeneralFormalCircuit`: takes the chip-owned `cols` block plus
`next_pc`/`clk_inc`/`is_real`, imposes the two `is_real`-gated clock byte checks and emits the (now
semantic) State bus, with `Spec` the two clock bounds and `ProverAssumptions` supplying the state pull's
`StateTruth`. -/
def circuit [Fact (2 ^ 17 < p)] : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  elaborated
  Assumptions := AssumptionsD
  Spec := SpecD
  ProverAssumptions := ProverAssumptionsD
  ProverSpec := fun _ _ _ => True
  soundness := soundness
  completeness := completeness
  -- The State bus stays — its `pushIf` owes `Owed = True` (and the `pullIf`'s off-gate requirement is
  -- vacuous via the inline `is_real` gate), so `channelsWithRequirements` is just the State channel.
  channelsWithRequirements := [stateChannel.toRaw]
  requirementsChannelsLawful input_var i₀ := by
    simp only [circuit_norm, main, byteChannel, stateChannel]; grind

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength [Fact (2 ^ 17 < p)] (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq [Fact (2 ^ 17 < p)] :
    (circuit (p := p)).channelsWithRequirements
      = ([stateChannel.toRaw] : List (RawChannel (ZMod p))) := rfl

end SP1Clean.Readers.CPUState
