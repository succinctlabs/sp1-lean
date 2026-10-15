import SP1Clean.FormalModel.Contracts.OrdinaryObservation
import SP1Clean.Native.Operations.InstructionReceipt
import SP1Clean.Native.Operations.ClockOrder
import SP1Clean.Native.Operations.WordRangeCheck
import SP1Clean.Proofs.Operations.AddOperation.Formal

/-! # Consuming ordinary receipts in strict clock order

Every row consumes one receipt, with no padding selector. The existing clock comparator and
addition gadget establish chronological retirement, including 64-bit counter wraparound.
Counter result ranges use the actual Byte ledger; the complete mixed installation must retain
these pulls. Endpoint binding and exhaustive ordering are separate global obligations.
-/

namespace SP1Clean.OrdinaryObservation

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

/-- The existing word gadgets need only the weaker field bound. -/
local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- An instruction receipt advances the observation chain and retirement counter. -/
def main (enabled : Bool) (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let _ ← ClockOrder.circuit input.clock
  assertion WordRangeCheck.circuit input.previous.counter
  assertion AddOperation.circuit ⟨input.previous.counter, increment enabled, ⟨input.counter⟩, 1⟩
  InstructionReceipt.channel.pull input.receipt
  stateChannel.pull input.previous
  stateChannel.push input.next

/-- Compose the original gadgets' metadata without a second arithmetic implementation. -/
instance elaborated (enabled : Bool) : ElaboratedCircuit (ZMod p) Inputs unit (main enabled) := by
  cases enabled <;> elaborate_circuit

omit [Fact (2 ^ 25 < p)] in
/-- The selected increment is a bounded word for either retirement mode. -/
theorem increment_isU64 (enabled : Bool) : Word.isU64 (increment (R := ZMod p) enabled) := by
  cases enabled <;> apply Word.isU64_of_cases <;> norm_num [increment, ZMod.val_one]

omit [Fact (2 ^ 25 < p)] in
/-- The limb encoding denotes the official zero-or-one counter increment. -/
theorem increment_bits (enabled : Bool) :
    Word.toBitVec64 (increment (R := ZMod p) enabled) = if enabled then 1 else 0 := by
  cases enabled <;> norm_num [increment, Word.toBitVec64, Word.toNat, ZMod.val_one] <;> rfl

omit [Fact (2 ^ 25 < p)] in
private theorem eval_increment (enabled : Bool) (env : Environment (ZMod p)) :
    Vector.map (Expression.eval env) (increment enabled) = increment enabled := by
  cases enabled <;> simp only [increment, circuit_norm]

/-- Local arithmetic and ordering follow from the composed circuit contracts. -/
theorem soundness (enabled : Bool) :
    GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) (main enabled)
      (fun _ _ => True) (fun input _ _ => Spec enabled input) := by
  circuit_proof_start [ClockOrder.circuit, WordRangeCheck.circuit, WordRangeCheck.Spec,
    WordRangeCheck.Assumptions, AddOperation.circuit, Inputs.clock,
    InstructionReceipt.channel, stateChannel]
  obtain ⟨clock, previous, addition⟩ := h_holds
  rw [eval_increment] at addition
  have result := addition ⟨fun _ => ⟨previous, increment_isU64 enabled⟩, Or.inr rfl⟩ rfl
  exact ⟨clock, previous, result.1, by simpa only [increment_bits] using result.2⟩

/-- Any semantic observation update supplies the existing gadgets' completeness premises. -/
theorem completeness (enabled : Bool) :
    GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) (main enabled)
      (fun input _ _ => Spec enabled input) (fun _ _ _ => True) := by
  circuit_proof_start [ClockOrder.circuit, WordRangeCheck.circuit, WordRangeCheck.Spec,
    WordRangeCheck.Assumptions, AddOperation.circuit, Inputs.clock,
    InstructionReceipt.channel, stateChannel]
  obtain ⟨clock, previous, bounded, addition⟩ := h_assumptions
  rw [eval_increment]
  refine ⟨clock, previous, ?_⟩
  exact ⟨⟨fun _ => ⟨previous, increment_isU64 enabled⟩, Or.inr rfl⟩,
    fun _ => ⟨bounded, by simpa only [increment_bits] using addition⟩⟩

/-- A complete local observation contract with explicit receipt and state-link requirements. -/
def circuit (enabled : Bool) : GeneralFormalCircuit (ZMod p) Inputs unit where
  main := main enabled
  elaborated := elaborated enabled
  Spec input _ _ := Spec enabled input
  ProverAssumptions input _ _ := Spec enabled input
  soundness := soundness enabled
  completeness := completeness enabled
  channelsWithRequirements := [InstructionReceipt.channel.toRaw, stateChannel.toRaw]

/-- Data-only construction uses the existing addition population algorithm. -/
def populate (enabled : Bool) (previous : State (ZMod p)) (receipt : StateMsg (ZMod p)) : Inputs (ZMod p) :=
  ⟨receipt, previous, AddOperation.populate previous.counter (increment enabled)⟩

/-- Population is total for any bounded incoming counter and strictly increasing source clock. -/
theorem populate_spec (enabled : Bool) (previous : State (ZMod p)) (receipt : StateMsg (ZMod p))
    (bounded : Word.isU64 previous.counter)
    (clock : ClockOrder.Spec (populate enabled previous receipt).clock) :
    Spec enabled (populate enabled previous receipt) := by
  have result := AddOperation.spec_populate bounded (increment_isU64 enabled) 1 rfl
  exact ⟨clock, bounded, result.1, by simpa only [increment_bits, populate] using result.2⟩

/-- Recovering the source clock does not hide field wraparound. The successor low limb may
exceed the 24-bit window by up to seven; it still equals the recovered source plus eight in ℕ. -/
theorem receipt_clock (enabled : Bool) (input : Inputs (ZMod p)) (valid : Spec enabled input) :
    input.receipt.clk_high.val < 2 ^ 24 ∧
      input.receipt.clk_low.val = (input.receipt.clk_low - 8).val + 8 := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have low := valid.1.2.2.2.1
  change (input.receipt.clk_low - 8).val < 2 ^ 24 at low
  refine ⟨valid.1.2.2.1, ?_⟩
  have eight : (8 : ZMod p).val = 8 := ZMod.val_natCast_of_lt (n := p) (a := 8) (by omega)
  have sum := ZMod.val_add_of_lt (a := input.receipt.clk_low - 8) (b := (8 : ZMod p))
    (by rw [eight]; omega)
  simpa only [sub_add_cancel, eight] using sum

end SP1Clean.OrdinaryObservation
