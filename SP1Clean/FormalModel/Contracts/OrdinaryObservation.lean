import SP1Clean.FormalModel.Contracts.ClockOrder
import SP1Clean.Model.BusMessages
import SP1Clean.Math.Word

/-! # Ordered observations of ordinary instruction retirement

This is an observation accumulator, not an execution state. The receipt supplies the original
successor State message. Ordering uses its source clock (subtracting the ordinary eight ticks),
so a successor crossing the low-limb window remains admissible. PC limbs are retained exactly
as emitted; this contract does not impose a new canonical representation on the State bus.
-/

namespace SP1Clean.OrdinaryObservation

open Circuit Channels

/-- The latest ordinary source clock, retirement counter and raw successor PC. -/
structure State (F : Type) where
  /-- High limb of the latest ordinary source clock. -/
  clkHigh : F
  /-- Low limb of the latest ordinary source clock. -/
  clkLow : F
  /-- Architectural retirement counter after the latest observation. -/
  counter : Word F
  /-- The latest receipt's PC limbs, with their original State-bus representation. -/
  pc : Vector F 3
deriving ProvableStruct
provable_struct_eval_lemmas State

/-- One authenticated receipt and the counter value after observing it. -/
structure Inputs (F : Type) where
  /-- Successor message authenticated by the ordinary producer. -/
  receipt : StateMsg F
  /-- Incoming observation link. -/
  previous : State F
  /-- Counter after this ordinary instruction. -/
  counter : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The eight-tick ordinary successor retains its high limb even at a window crossing. -/
def Inputs.clock {R : Type} [Sub R] [OfNat R 8] (input : Inputs R) : ClockOrder.Inputs R :=
  ⟨input.previous.clkHigh, input.previous.clkLow, input.receipt.clk_high, input.receipt.clk_low - 8⟩

/-- Record the new counter and the exact successor PC, ranked by the ordinary source clock. -/
def Inputs.next {R : Type} [Sub R] [OfNat R 8] (input : Inputs R) : State R :=
  ⟨input.receipt.clk_high, input.receipt.clk_low - 8, input.counter,
    #v[input.receipt.pc0, input.receipt.pc1, input.receipt.pc2]⟩

/-- A fixed retirement enable bit selects zero or one in the existing four-limb encoding. -/
def increment {R : Type} [Zero R] [One R] (enabled : Bool) : Word R :=
  #v[if enabled then 1 else 0, 0, 0, 0]

/-- A strictly later ordinary observation updates the architectural counter modulo 2^64. -/
def Spec {p : ℕ} [Fact p.Prime] (enabled : Bool) (input : Inputs (ZMod p)) : Prop :=
  ClockOrder.Spec input.clock ∧ Word.isU64 input.previous.counter ∧ Word.isU64 input.counter ∧
    Word.toBitVec64 input.counter = Word.toBitVec64 input.previous.counter + if enabled then 1 else 0

/-- Private observation links; complete endpoint meaning is established by ordered consumption. -/
def stateChannel {p : ℕ} : Channel (ZMod p) State where
  name := "SP1OrdinaryObservation"
  Guarantees _ _ := True

end SP1Clean.OrdinaryObservation
