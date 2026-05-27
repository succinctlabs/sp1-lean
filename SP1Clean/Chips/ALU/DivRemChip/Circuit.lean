import SP1Clean.Chips.ALU.DivRemChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `DivRemChip` Clean circuit + `FormalAssertion`

**Placeholder `main`** — the real DivRem main composes
`CPUState.Gated` + `RTypeReader.Gated` + `MulOp.assertion` × 2 +
`IsEqualWordOp.assertion` × 4 + `IsZeroWordOp.assertion` +
`AddOp.assertion` × 2 + `LtUnsignedOp.assertion` +
`U16MSBOp.assertion` × 7 + 117 inline aux-gates + scalar gates.

For breadth alignment with the other 5 ALU chips, the placeholder
emits no constraints. Soundness/completeness sorry'd at every layer
pending the full main composition. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.DivRem

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

variable [Fact (2 ^ 24 < p)]

/-- Placeholder main: emits no constraints. Lifted full main from
`Aggregate.lean` (~210 LoC composing 18+ subcircuits) deferred — see
file docstring. -/
@[reducible]
def main (_cols : Var DivRemCols (ZMod p)) : Circuit (ZMod p) Unit := pure ()

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) DivRemCols unit where
  name := "SP1Clean.DivRem"
  main := main
  localLength _ := 0

def Assumptions (_ : DivRemCols (ZMod p)) : Prop := True

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

def assertion [Fact (2 ^ 24 < p)] : FormalAssertion (ZMod p) DivRemCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.DivRem
