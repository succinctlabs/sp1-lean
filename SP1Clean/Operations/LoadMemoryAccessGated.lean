import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Foundations.Word
import SP1Clean.ByteOpcodeTable
import SP1Clean.MemoryBusTable

/-! # `LoadMemoryAccessGated` sub-circuit (stubbed)

Wraps the load-side RAM memory access SP1 emits in Load chips:
- `send .byte (Range) load_memory_diff_low 16 0` gated by `mult`
- `send .byte (U8Range) 0 load_memory_diff_high 0` gated by `mult`
- `send .memory <prev_high, prev_low, addr, prev_value>` gated by `mult`
- `receive .memory <clk_high, clk_low+1, addr, prev_value>` gated by `mult`
- `flag * (flag - 1) === 0` (gated)
- `flag * (clk_high - prev_high) === 0` (gated)
- flag-based timestamp equation:
    `flag * (clk_low + 1) + (1 - flag) * clk_high
       - (flag * prev_low + (1 - flag) * prev_high) - 1
     = diff_low + diff_high * 65536`
  (gated by `mult`)

Per the `load-store-ram-access-deferred` marker — this primitive closes
that gap. Spec is disjunctive: `mult = 0 ∨ <byte+timestamp+flag facts>`.

**Status:** structural placeholder (AddwChip Phase-5 pattern):
`main := pure ()`, `Spec := mult = 0 ∨ True` marked `@[reducible]`. The
faithful contract is a follow-up that threads `mult` through leaf
`RegisterAccessTimestamp.assertion`, `WordRange.assertion`,
`byteOpcodeGated`, and `memoryBusGated` calls. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LoadMemoryAccessGated

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Inputs: clock components, address, prior-access value/timestamp,
diff witnesses, the in-page flag, and the gating multiplicity. -/
structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  addr : Vector F 3
  prev_value : Vector F 4
  prev_high : F
  prev_low : F
  diff_low : F
  diff_high : F
  flag : F
  mult : F
deriving ProvableStruct

namespace Assertion

open Circuit

@[reducible]
def main (_input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := pure ()

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.LoadMemoryAccessGated"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Disjunctive placeholder Spec: vacuous when `mult = 0`; otherwise
`True`. Marked `@[reducible]` so chip-level proofs auto-unfold. -/
@[reducible]
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.mult = 0 ∨ True

omit [Fact (2 ^ 17 < p)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  intro _ _ _ _ _ _ _; exact Or.inr trivial

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  intro _ _ _ _ _ _ _ _; trivial

end Assertion

def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.LoadMemoryAccessGated
