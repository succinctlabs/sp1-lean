import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Model.Channels
import SP1Clean.Model.ByteTable
import Clean.Circuit.Basic
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Local subtraction gadget circuit

This is a proof-oriented Clean gadget, not an extraction of SP1 Rust's `SubOperation`. It checks the
base-2^16 two's-complement carry chain and range-checks the four result limbs. Faithfulness is
established only after the gadget is assembled into a chip and reconfigured to that chip's extracted
Rust row. -/

namespace SP1Clean.SubOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Four-limb subtraction through `a + (2^64 - b)`, gated by `is_real`. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let c0 :=
    (input.a[0] + (65536 : Expression (ZMod p)) - (1 : Expression (ZMod p)) - input.b[0] -
      input.cols.value[0] + (1 : Expression (ZMod p))) *
      (65536 : ZMod p)⁻¹
  let c1 :=
    (input.a[1] + (65536 : Expression (ZMod p)) - (1 : Expression (ZMod p)) - input.b[1] -
      input.cols.value[1] + c0) *
      (65536 : ZMod p)⁻¹
  let c2 :=
    (input.a[2] + (65536 : Expression (ZMod p)) - (1 : Expression (ZMod p)) - input.b[2] -
      input.cols.value[2] + c1) *
      (65536 : ZMod p)⁻¹
  let c3 :=
    (input.a[3] + (65536 : Expression (ZMod p)) - (1 : Expression (ZMod p)) - input.b[3] -
      input.cols.value[3] + c2) *
      (65536 : ZMod p)⁻¹
  byteChannel.pullIf input.is_real
    (⟨6, input.cols.value[0], Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf input.is_real
    (⟨6, input.cols.value[1], Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf input.is_real
    (⟨6, input.cols.value[2], Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  byteChannel.pullIf input.is_real
    (⟨6, input.cols.value[3], Expression.const ((16 : ℕ) : ZMod p), 0⟩ :
      ByteRow (Expression (ZMod p)))
  assertZero (input.is_real * (input.is_real - 1))
  assertZero (input.is_real * (c0 * (c0 - 1)))
  assertZero (input.is_real * (c1 * (c1 - 1)))
  assertZero (input.is_real * (c2 * (c2 - 1)))
  assertZero (input.is_real * (c3 * (c3 - 1)))

/-- Structural metadata is derived compositionally from the local circuit. -/
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    (elaborated (p := p)).channelsWithGuarantees =
      ([(byteChannel (p := p)).toRaw, byteChannel.toRaw, byteChannel.toRaw,
        byteChannel.toRaw] : List (RawChannel (ZMod p))) := rfl

end SP1Clean.SubOperation
