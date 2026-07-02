import SP1Clean.Math.Word
import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native `RegisterWrite` primitive — the `rd` write Memory-bus push as a Clean `FormalAssertion`

The op_a (`rd`) **write** half of SP1's register adapter, factored out of the readers (W11 memory flip).
After the flip, a memory `pushIf` **owes** `MemoryMsg.isU64` of the pushed value; for the op_a write that
value is the ALU result, whose `isU64` the composing chip derives from its operation (the operand `isU64`
flows in from the *read* pulls, the result `isU64` from the operation's result range-check). Keeping the write
in the readers would force the reader to *assume* `isU64 wv`, which the chip could only discharge circularly
(operand `isU64` ⇐ reader `Spec` ⇐ `isU64 wv` ⇐ result `isU64` ⇐ operand `isU64`). Pulling the write out
breaks that cycle: the readers become pure reads, and each write-chip composes this `RegisterWrite` *after*
its operation, feeding `isU64 value`.

SP1-faithful: this emits exactly the op_a write interaction the reader used to
(`⟨clk_high, clk_low, op_a, 0, 0, value⟩`, `+is_real`), so a chip's *combined* Memory-bus faithfulness anchor
is unchanged — the interaction merely moves from the reader sub-assertion to this one. The chip passes the
write access clock (`recombined_clk + 4`) as `clk_low`. -/

namespace SP1Clean.Readers.RegisterWrite

open Circuit
open SP1Clean.Channels (memoryChannel MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The cross-block inputs: the write access timestamp (`clk_high`, `clk_low` = the recombined clock `+ 4`),
the destination register index `op_a`, the written `value : Word` (the ALU result / loaded word), and the row
selector `is_real`. -/
structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  op_a : F
  value : Word F
  is_real : F
deriving ProvableStruct

/-- Emit the single op_a (`rd`) write Memory interaction: `pushIf is_real` of the new value at the current
write timestamp (`+is_real`, the W11-flipped polarity). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  memoryChannel.pushIf input.is_real
    (⟨input.clk_high, input.clk_low, input.op_a, 0, 0, input.value⟩ : MemoryMsg (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := []
  channelsLawful := by simp [circuit_norm, main, memoryChannel]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) = [] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- `is_real` binary + (on a real row) the written `value` is `U64` — the precondition for the write
`pushIf`'s `MemoryMsg.isU64` requirement. The composing chip discharges `isU64 value` from its operation's
result range-check (an ALU result) or the loaded-word read pull. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧ (input.is_real = 1 → Word.isU64 input.value)

/-- No local semantic guarantee — `RegisterWrite` only emits the write interaction. -/
def Spec (_ : Inputs (ZMod p)) : Prop := True

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [circuit_norm, memoryChannel, MemoryMsg.isU64] at h_holds ⊢
  -- The only obligation is the write `pushIf`'s requirement, `¬is_real=-1 → ¬is_real=0 → isU64 value`.
  exact fun _ h0 => h_assumptions.2 ((h_assumptions.1).resolve_left h0)

theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start

/-- The native `rd` write as a Clean `FormalAssertion`: emits the op_a write Memory-bus push, requiring
`isU64` of the written value (discharged by the composing chip). -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements := [memoryChannel.toRaw],
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, memoryChannel] }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.Readers.RegisterWrite
