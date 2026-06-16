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
  byteChannel.pullIf input.is_real
    (⟨6, (cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹, Expression.const ((13 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf input.is_real
    (⟨3, 0, cols.clk_16_24, 0⟩ : ByteRow (Expression (ZMod p)))
  let clk_low := cols.clk_0_16 + cols.clk_16_24 * 65536
  stateChannel.emit (-input.is_real) ⟨cols.clk_high, clk_low, cols.pc[0], cols.pc[1], cols.pc[2]⟩
  stateChannel.emit input.is_real
    ⟨cols.clk_high, clk_low + input.clk_inc, input.next_pc[0], input.next_pc[1], input.next_pc[2]⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRaw]
  channelsWithRequirements := [byteChannel.toRaw, stateChannel.toRaw]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    (elaborated (p := p)).channelsWithGuarantees
      = ([byteChannel.toRaw] : List (RawChannel (ZMod p))) := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    (elaborated (p := p)).channelsWithRequirements
      = ([byteChannel.toRaw, stateChannel.toRaw] : List (RawChannel (ZMod p))) := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real` is binary — the precondition for the genuinely `is_real`-gated byte receives.
Discharged by the composing chip's `is_real * (is_real - 1) = 0` gate. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

theorem soundness [Fact (2 ^ 17 < p)] : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have h13p : (13 : ℕ) < p := lt_trans (Nat.lt_two_pow_self) hn13
  simp only [circuit_norm, byteChannel, stateChannel, StateMsg.Spec] at h_holds ⊢
  -- `Spec`: `is_real = 1 → clk bounds`, derived from the byte-pull guarantees (fire at `mult = -1`).
  -- Post-#398 the receives owe no padding requirement and the State emit requirements are trivial
  -- (`Guarantees := True`), so the Spec implication is the only goal.
  intro hr1
  have hneg : -input_is_real = -1 := by rw [hr1]
  have hb1 := h_holds.1 hneg
  have hb2 := h_holds.2 hneg
  refine ⟨(byteRowSpec_range _ h13p).mp ?_, ((byteRowSpec_u8range_pair _ _).mp hb2).1⟩
  rw [sub_eq_add_neg, Nat.cast_ofNat]
  exact hb1

theorem completeness [Fact (2 ^ 17 < p)] : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  have h13p : (13 : ℕ) < p := lt_trans (Nat.lt_two_pow_self) hn13
  -- The two byte pulls' completeness obligation (their `ByteRowSpec` guarantee) only fires on real rows
  -- (`-is_real = -1`, i.e. `is_real = 1`); there the `Spec` clock bounds supply it. The State emits add no
  -- completeness obligation (`Guarantees := True`).
  simp only [circuit_norm, byteChannel]
  refine ⟨?_, ?_⟩
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨hb1, _⟩ := h_spec hr1
    rw [sub_eq_add_neg] at hb1
    have key := (byteRowSpec_range _ h13p).mpr hb1
    rw [Nat.cast_ofNat] at key
    exact key
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    obtain ⟨_, hb2⟩ := h_spec hr1
    exact (byteRowSpec_u8range_pair _ _).mpr ⟨hb2, by rw [ZMod.val_zero]; norm_num⟩

/-- The native CPUState reader as a Clean `FormalAssertion`: takes the chip-owned `cols` block plus
`next_pc`/`clk_inc`/`is_real`, imposes the two `is_real`-gated clock byte checks and emits the State bus,
with `Spec` the two clock bounds (derived from the byte bus). -/
def circuit [Fact (2 ^ 17 < p)] : FormalAssertion (ZMod p) Inputs where
  main
  elaborated
  Assumptions := Assumptions
  Spec := Spec
  soundness := soundness
  completeness := completeness

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength [Fact (2 ^ 17 < p)] (x : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength x = 0 := rfl

end SP1Clean.Readers.CPUState
