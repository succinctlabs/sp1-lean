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
import SP1Operations.Operation.U16toU8OperationUnsafe.U16toU8OperationUnsafe
import SP1Clean.ByteOpcodeTable

/-! # `U16toU8OperationUnsafe` Clean mirror (scaffold)

SP1's `U16toU8OperationUnsafe` algebraically decomposes 4 u16 values
into 8 u8 byte values without enforcing the byte-range constraints —
that safety check lives in the `Safe` variant. The constraint list is
EMPTY (`[]`); the operation produces only the algebraic 8-byte output
vector.

Rust source: `SP1Operations/Operation/U16toU8OperationUnsafe/Constraints.lean`
returns `(Vector F 8) × SP1ConstraintList F` with an empty constraint
list. The 8-vector is
`#v[low_bytes[0], (u16_values[0] - low_bytes[0]) / 256,
    low_bytes[1], (u16_values[1] - low_bytes[1]) / 256, …]`.

Since the constraint surface is empty, this wrapper's `main` and
`Assertion.main` are no-op `pure ()`, the `Spec` is `True`, and the
`assertion` is structurally a trivial FormalAssertion. It exists to
satisfy the Rust nesting graph — `U16toU8OperationSafe` composes the
Unsafe variant inline; the Clean mirror does the same. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.U16toU8OpUnsafe

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Emits no constraints — the Unsafe variant only
provides the algebraic byte decomposition without enforcing byte ranges. -/
def main (_u16_values : Vector (Expression (ZMod p)) 4)
    (_low_bytes : Vector (Expression (ZMod p)) 4) :
    Circuit (ZMod p) Unit := pure ()

/-- Pilot Spec — trivially `True` since the constraint list is empty. -/
def Spec (_u16_values : Vector (ZMod p) 4) (_low_bytes : Vector (ZMod p) 4) :
    Prop := True

/-- The bridge to SP1: trivially `True ↔ True`. -/
theorem iff_sp1 (u16_values : Vector (ZMod p) 4)
    (cols : U16toU8Operation (ZMod p)) :
    List.Forall SP1Constraint.toProp
      (U16toU8OperationUnsafe.constraints u16_values cols).2 ↔
      Spec u16_values cols.low_bytes := by
  sorry

/-! ## Full `FormalAssertion` promotion -/

/-- Bundled FormalAssertion input: the 4-limb u16 word + 4 low-byte
witnesses. -/
structure Inputs (F : Type) where
  u16_values : fields 4 F
  low_bytes : fields 4 F
deriving ProvableStruct

namespace Assertion

open Circuit

@[reducible]
def main (_input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  pure ()

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.U16toU8OpUnsafe"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

def Spec (_input : Inputs (ZMod p)) : Prop := True

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `U16toU8OperationUnsafe`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.U16toU8OpUnsafe
