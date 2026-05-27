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

/-! # `LoadMemoryAccessGated` sub-circuit

Wraps the load-side RAM memory access SP1 emits in Load chips. The
underlying SP1 constraint compiler output (see e.g.
`SP1Chips/Load/LoadByte/Constraints.lean` for the canonical example) emits:

- `assertZero (flag * (flag - 1))` — boolean flag gate
- `assertZero (flag * (clk_high - prev_high))` — clock-page agreement
  (when `flag = 1`, the access is in the same 65536-clock page as the
  prior access, so the page-high bits agree)
- The 65536-base timestamp equation as a single `assertZero`:
  `flag*(clk_low+1) + (1-flag)*clk_high
   - (flag*prev_low + (1-flag)*prev_high) - 1 - (diff_low + diff_high*65536) = 0`
- `send .byte 6 diff_low 16 0` (Range(16) for `diff_low`)
- `send .byte 3 0 diff_high 0` (U8Range for `diff_high`)
- `Word.isU64 prev_value` (4 byte lookups, threaded via `WordRange`)
- `send .memory ...` + `receive .memory ...` (memory bus participation,
  gated by `mult`)

All emissions are gated by the chip's `is_real` (= `mult` here), so on
padding rows the constraint set collapses.

## Status: Phase-1 "contract marker" form

This file follows the pragmatic Phase-1 design per `plans/make-a-plan-to-squishy-frog.md`:
`main := pure ()` (no actual circuit content yet), with the faithful
contract lifted into BOTH `Assumptions` and `Spec`. Soundness and
completeness collapse to trivial identity/`pure ()` proofs.

The contract is *named* in `Spec` so chip-level `AssertionGated.FormalSpec`
compositions reference the meaningful contract (not a `True` stub). The
chip's `AssertionGated.soundness` derives the contract from the per-chip
`iff_sp1_of_*` bridge facts and passes it back as `Assumptions` to invoke
this sub-circuit's `Spec` — the discharge happens at the chip layer, not
here.

A future iteration (Avenue C of the original Phase-1 design) makes `main`
non-trivial by emitting `byteOpcodeGated`/`memoryBusGated` subcircuits +
gated `assertZero` lines (canonical pattern: `OperandAccess.AssertionGated`
at `SP1Clean/Reader/OperandAccess.lean:241-298`), at which point
`Assumptions` collapses back to `True` and `Spec` is proved from `h_holds`
rather than copied from `Assumptions`. -/

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

/-- The faithful load-memory-access contract, in disjunctive (`mult = 0 ∨ …`)
form so the assertion is vacuous on padding rows. Encodes:
- boolean flag,
- clock-page agreement when `flag = 1`,
- 65536-base timestamp equation,
- range bounds (`diff_low.val < 65536`, `diff_high < 256`),
- `Word.isU64 prev_value` for the loaded word. -/
def Contract (input : Inputs (ZMod p)) : Prop :=
  input.mult = 0 ∨
    ((input.flag = 0 ∨ input.flag = 1) ∧
     (input.flag = 0 ∨ input.clk_high = input.prev_high) ∧
     input.flag * (input.clk_low + 1) + (1 - input.flag) * input.clk_high -
       (input.flag * input.prev_low + (1 - input.flag) * input.prev_high) - 1 =
       input.diff_low + input.diff_high * 65536 ∧
     input.diff_low.val < 65536 ∧
     input.diff_high < (256 : ZMod p) ∧
     Word.isU64 input.prev_value)

/-- Phase-1 caller obligation: the chip composing this sub-circuit must
discharge the contract from its own `iff_sp1` bridge facts. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := Contract input

/-- Spec is the contract verbatim — soundness is a trivial copy from
`Assumptions`. -/
def Spec (input : Inputs (ZMod p)) : Prop := Contract input

omit [Fact (2 ^ 17 < p)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  -- `main := pure ()` so `h_holds = True`; just relay `Assumptions = Spec = Contract`.
  intro _ _ _ _ _ h_assumptions _
  exact h_assumptions

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  -- `main := pure ()` — no witnesses to produce.
  intro _ _ _ _ _ _ _ _
  trivial

end Assertion

def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.LoadMemoryAccessGated
