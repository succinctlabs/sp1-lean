import SP1Clean.FormalModel.Contracts.HostControl
import SP1Clean.Native.Operations.BoundedWord
import SP1Clean.Model.HostExit
import Clean.Gadgets.Equality

/-! # The native HALT host consumer

One row consumes one full instruction handoff and checks its canonical exit argument. There is
no padding. The instruction emits the public Exit value; this handler separately emits the
complete terminal receipt that authenticates optional outgoing status.
-/

namespace SP1Clean.HostHaltChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The exit-code bound fits a word; named so the bundle's `fits` argument is a constant whose
type is literally `bound p < 2 ^ 64` (a `by simp` proof term carries a different spelling of the
same type, which Lean ≥ 4.33 no longer accepts inside rewrites). -/
theorem bound_fits : bound p < 2 ^ 64 := by simp [bound]

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion (Gadgets.Equality.circuit Word) (input.call.code, const (0 : Word (ZMod p)))
  assertion (Gadgets.Equality.circuit Word) (input.call.result, const (0 : Word (ZMod p)))
  assertion (Gadgets.Equality.circuit Word) (input.call.length, const (0 : Word (ZMod p)))
  let _ ← BoundedWord.circuit (bound p) bound_fits ⟨input.call.arg1, input.comparison⟩
  HostCallChip.channel.pull input.call
  HostExitBoundary.channel.push input.call.arg1

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main := by
  elaborate_circuit

end SP1Clean.HostHaltChip
