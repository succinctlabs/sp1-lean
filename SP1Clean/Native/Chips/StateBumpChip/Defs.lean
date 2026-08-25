import SP1Clean.FormalModel.Contracts.SystemChips
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The StateBump system table as a Clean circuit (W3, external report Finding 2)

SP1's `StateBumpChip::eval` (`../sp1 crates/core/machine/src/adapter/bump.rs`), constraint-for-
constraint in the same order: pull the possibly-non-canonical State message, push the canonically
re-limbed one, range-check every pushed limb on the Byte bus, tie the two clocks together through
the `is_clk · 2^24` carry, and propagate the pc's `2^16` limb carries through the ungated borrow
cascade (binary borrows, no carry out of the top limb — so the 48-bit pc value is preserved as a
field identity even on padding rows, exactly as upstream).

The chip is a **flat own-assert table**: it deliberately does *not* compose `Readers.MemoryAccess`
or `Readers.CPUState` — no reader matches its shape (there is no instruction here, and the readers'
contracts carry the instruction-row clock discipline a bump row does not satisfy). All fourteen
cells are inputs (`localLength = 0`); the row struct and semantic `Spec` live on the audit surface
in `FormalModel/Contracts/SystemChips.lean`, the soundness/completeness proofs in
`Proofs/Chips/StateBumpChip/Formal.lean`. -/

namespace SP1Clean.StateBumpChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel StateMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The pulled (possibly non-canonical) State message. Shared by `main` and the trace layer. -/
@[circuit_norm] def pulledMsg (r : Var Inputs (ZMod p)) : StateMsg (Expression (ZMod p)) :=
  ⟨r.clk_high, r.clk_low, r.pc0, r.pc1, r.pc2⟩

/-- The pushed canonically-re-limbed State message. Shared by `main` and the trace layer. -/
@[circuit_norm] def pushedMsg (r : Var Inputs (ZMod p)) : StateMsg (Expression (ZMod p)) :=
  ⟨r.next_clk_24_32 + r.next_clk_32_48 * 256, r.next_clk_0_16 + r.next_clk_16_24 * 65536,
    r.next_pc0, r.next_pc1, r.next_pc2⟩

/-- SP1's `StateBumpChip::eval`, in its constraint order: the `is_real` boolean gate, the State
pull/push pair, the three pushed-clock byte checks (13-bit scaled low limb, 16-bit top limb, the two
middle bytes as a `U8Range` pair), the `is_clk` boolean gate, the two `is_real`-gated clock-carry
equations, the ungated pc borrow cascade, and the three pushed-pc 16-bit checks. -/
def main (r : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- Inline shallow boolean gate (`assertZero`, visible to `ConstraintsHold.Shallow`) — it discharges
  -- every gated pull's off-gate `Requirements` without keeping `byteChannel` in
  -- `channelsWithRequirements`.
  assertZero (r.is_real * (r.is_real - 1))
  stateChannel.pullIf r.is_real (pulledMsg r)
  stateChannel.pushIf r.is_real (pushedMsg r)
  byteChannel.pullIf r.is_real
    (⟨6, (r.next_clk_0_16 - 1) * (8 : ZMod p)⁻¹, Expression.const ((13 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf r.is_real
    (⟨6, r.next_clk_32_48, Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf r.is_real
    (⟨3, 0, r.next_clk_16_24, r.next_clk_24_32⟩ : ByteRow (Expression (ZMod p)))
  assertZero (r.is_clk * (r.is_clk - 1))
  assertZero (r.is_real *
    (r.next_clk_24_32 + r.next_clk_32_48 * 256 - (r.clk_high + r.is_clk)))
  assertZero (r.is_real *
    (r.next_clk_0_16 + r.next_clk_16_24 * 65536 + r.is_clk * 16777216 - r.clk_low))
  -- The pc borrow cascade, ungated as upstream. The borrows are inverse-scaled *expressions*, not
  -- witness cells — exactly SP1's `carry` accumulator — so the only constraint content is their
  -- binarity and the vanishing top borrow.
  let b0 := (r.pc0 - r.next_pc0) * (65536 : ZMod p)⁻¹
  assertZero (b0 * (b0 - 1))
  let b1 := (b0 + r.pc1 - r.next_pc1) * (65536 : ZMod p)⁻¹
  assertZero (b1 * (b1 - 1))
  let b2 := (b1 + r.pc2 - r.next_pc2) * (65536 : ZMod p)⁻¹
  assertZero (b2 * (b2 - 1))
  assertZero b2
  byteChannel.pullIf r.is_real
    (⟨6, r.next_pc0, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf r.is_real
    (⟨6, r.next_pc1, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf r.is_real
    (⟨6, r.next_pc2, Expression.const ((16 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRaw, stateChannel.toRaw]
  channelsLawful := by
    simp only [circuit_norm, main, pulledMsg, pushedMsg]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, stateChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

end SP1Clean.StateBumpChip
