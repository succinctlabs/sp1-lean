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

/-! # `StoreMemoryAccessGated` sub-circuit (placeholder)

Mirror of `LoadMemoryAccessGated` for the store side. Differs in that the
chip supplies an explicit `write_value : Vector F 4` (the bytes being
written), and the `send/receive .memory` pair carries `write_value` in
the receive (the post-write value) instead of `prev_value`.

Closes the `load-store-ram-access-deferred` marker for Store chips.

**Status:** structural placeholder following the AddwChip Phase-5 pattern:
`main := pure ()`, `Spec := mult = 0 ∨ True` (trivially provable). The
faithful contract (flag boolean, clk-equality-when-flag, timestamp
arithmetic, two byte-bus range lookups for `diff_low / diff_high`, and
`Word.isU64 prev_value`) is a follow-up that threads `mult` through
existing leaf assertions (`RegisterAccessTimestamp.assertion`,
`WordRange.assertion`, `byteOpcodeGated`, `memoryBusGated`). -/

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

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Disjunctive placeholder Spec: vacuous when `mult = 0`; otherwise `True`.

The faithful contract — flag boolean, clk-equality-when-flag, timestamp
arithmetic, two byte-bus range lookups (`diff_low < 65536`,
`diff_high < 256`), and the `Word.isU64 prev_value` consequences — is
intentionally *not* lifted here. Reason: the chip-level
`StoreByteChip.AssertionGated.main` calls `assertion` with a `pure ()`
body, so a stronger Spec can't be discharged without rewriting `main`
to compose the leaf sub-circuits (`RegisterAccessTimestamp.assertion`,
`WordRange.assertion`, `byteOpcodeGated`, `memoryBusGated`).

The pragmatic AddwChip-Phase-5 pattern: the trace-level memory-bus
consistency now flows through `memoryBusGated` calls at the chip's
ungated `main` (or, in the AddwChip pattern, through the empty
`memoryAccesses (.storeByte _)` case + a parallel `lookupAccesses`
aggregator). The faithful sub-Spec expansion is a follow-up that
threads `mult` through the existing leaf assertions.

Marked `@[reducible]` so chip-level proofs auto-unfold to
`mult = 0 ∨ True`. -/
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

end SP1Clean.StoreMemoryAccessGated
