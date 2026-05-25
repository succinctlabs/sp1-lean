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

**Status:** structural stub. `main := pure ()`, `Spec` is the real contract,
proofs are `sorry`. -/

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

/-- Disjunctive Spec: vacuous when `mult = 0`; otherwise the load-side
RAM-access fact set. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.mult = 0 ∨
    ((input.flag = 0 ∨ input.flag = 1) ∧
     (input.flag = 0 ∨ input.clk_high = input.prev_high) ∧
     input.flag * (input.clk_low + 1) +
         (1 - input.flag) * input.clk_high -
         (input.flag * input.prev_low +
           (1 - input.flag) * input.prev_high) - 1
       = input.diff_low + input.diff_high * 65536 ∧
     input.diff_low.val < 65536 ∧
     input.diff_high.val < 256 ∧
     Word.isU64 input.prev_value)

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  sorry

end Assertion

def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.LoadMemoryAccessGated
