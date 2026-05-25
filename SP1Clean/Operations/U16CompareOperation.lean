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
import SP1Operations.Compare.U16CompareOperation.U16CompareOperation
import SP1Clean.ByteOpcodeTable

/-! # `U16CompareOperation` Clean mirror (scaffold)

SP1's `U16CompareOperation` compares two 16-bit values `a` and `b` and
asserts via a `bit : F` witness that:
- `bit` is boolean,
- `a - b + bit * 65536` is `< 65536` (i.e., `bit = 1 ↔ a < b`).

Rust source (proxy via SP1Operations):
`SP1Operations/Compare/U16CompareOperation/Constraints.lean`. The
constraint list under `is_real = 1` is:
```
[ .assertZero (bit*(bit-1))
, .send (.byte Range (a - b + bit*65536) 16 0) is_real ]
```
plus the chip-level `is_real * (is_real - 1)` gate (which lives at the
chip layer, not inside the wrapper).

This is the leaf atomic byte-comparison sub-op — no recursive sub-ops.
Proof bodies (`iff_sp1`, `soundness`, `completeness`) are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.U16CompareOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Takes the two compared values `a`, `b` and the
externally supplied compare bit; asserts `bit` is boolean and that the
shifted difference fits in `< 65536`. -/
def main (a b bit : Expression (ZMod p)) : Circuit (ZMod p) Unit := do
  bit * (bit - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), a - b + bit * 65536, 16, 0]
      : Vector (Expression (ZMod p)) 4)

/-- Pilot Spec: `bit` is boolean and the shifted difference is a u16. -/
def Spec (a b bit : ZMod p) : Prop :=
  bit * (bit - 1) = 0 ∧
  (a - b + bit * 65536).val < 65536

/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. -/
theorem iff_sp1 (a b : ZMod p) (cols : U16CompareOperation (ZMod p)) :
    (U16CompareOperation.constraints (F := ZMod p) a b cols 1).allHold ↔
      Spec a b cols.bit := by
  sorry

/-! ## Full `FormalAssertion` promotion -/

/-- Bundled FormalAssertion input: the two compared values + the compare bit. -/
structure Inputs (F : Type) where
  a : F
  b : F
  bit : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Wrapper around `SP1Clean.U16CompareOp.main`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Clean.U16CompareOp.main input.a input.b input.bit

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.U16CompareOp"
  main := main
  localLength _ := 0

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The FormalAssertion's spec, identical in shape to the top-level
`SP1Clean.U16CompareOp.Spec`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.bit * (input.bit - 1) = 0 ∧
  (input.a - input.b + input.bit * 65536).val < 65536

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `U16CompareOperation`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.U16CompareOp
