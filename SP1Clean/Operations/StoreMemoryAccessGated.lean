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

/-! # `StoreMemoryAccessGated` sub-circuit

Mirror of `LoadMemoryAccessGated` for the store side. SP1's Store chips
emit the same memory-access shape as Load — boolean `flag`, clock-page
agreement when `flag = 1`, 65536-base timestamp equation, range bounds,
`Word.isU64` on the prior word — plus an explicit `write_value : Vector F 4`
(the bytes being written). The send/receive memory-bus pair on the store
side carries `write_value` in the receive (post-write state) instead of
`prev_value`.

## Status: Phase-1 "contract marker" form

Same Phase-1 design as `LoadMemoryAccessGated`: `main := pure ()` with
the faithful contract lifted into both `Assumptions` and `Spec`. The
chip-level `AssertionGated.soundness` derives the contract from the per-chip
`iff_sp1_of_*` bridge facts and passes it back as `Assumptions` to invoke
this sub-circuit's `Spec`. See `SP1Clean/Operations/LoadMemoryAccessGated.lean`
for the detailed rationale and future-work pointers. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.StoreMemoryAccessGated

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Inputs: same as `LoadMemoryAccessGated` plus the explicit
`write_value` the store emits to the receive side. -/
structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  addr : Vector F 3
  prev_value : Vector F 4
  write_value : Vector F 4
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
  name := "SP1Clean.StoreMemoryAccessGated"
  main := main
  localLength _ := 0

/-- The faithful store-memory-access contract, in disjunctive
(`mult = 0 ∨ …`) form so the assertion is vacuous on padding rows.
Mirrors `LoadMemoryAccessGated.Contract` plus an extra `Word.isU64 write_value`
clause for the bytes being written. -/
def Contract (input : Inputs (ZMod p)) : Prop :=
  input.mult = 0 ∨
    ((input.flag = 0 ∨ input.flag = 1) ∧
     (input.flag = 0 ∨ input.clk_high = input.prev_high) ∧
     input.flag * (input.clk_low + 1) + (1 - input.flag) * input.clk_high -
       (input.flag * input.prev_low + (1 - input.flag) * input.prev_high) - 1 =
       input.diff_low + input.diff_high * 65536 ∧
     input.diff_low.val < 65536 ∧
     input.diff_high < (256 : ZMod p) ∧
     Word.isU64 input.prev_value ∧
     Word.isU64 input.write_value)

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

end SP1Clean.StoreMemoryAccessGated
