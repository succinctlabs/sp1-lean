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
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Clean.Operations.LtOperationUnsigned
import SP1Clean.Operations.U16MSBOperation

/-! # `LtOperationSigned` Clean mirror (scaffold)

SP1's `LtOperationSigned` extends `LtOperationUnsigned` with sign
handling via two `U16MSBOperation` sub-calls on the high limbs and a
limb-3 sign-XOR transform (`b[3] + is_signed*32768 - 65536*b_msb`).
Rust nesting: 3 subcircuit calls + 5 surrounding gates.

Composes:
- `SP1Clean.U16MSBOp.assertion` on `b[3]` (gated by `is_signed`)
- `SP1Clean.U16MSBOp.assertion` on `c[3]` (gated by `is_signed`)
- `SP1Clean.LtUnsignedOp.assertion` on sign-flipped operands (gated by `is_real`)

The `is_signed : F` toggle lets the SAME wrapper handle signed (SLT/SLTI)
and unsigned (SLTU/SLTIU) comparisons — when `is_signed = 0`, the U16MSB
sub-calls become vacuous and the limb-3 transform reduces to identity. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LtSignedOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled FormalAssertion input. Mirrors Rust `LtOperationSigned<T>`'s
cols struct: an embedded `LtOperationUnsigned`-cols + two `U16MSBOp`-cols
(`b_msb`, `c_msb`), plus the two compared words and the `is_signed`
toggle (taken as part of the input rather than a separate parameter so
the chip-level destructure is uniform). -/
structure Inputs (F : Type) where
  b : fields 4 F
  c : fields 4 F
  is_signed : F
  -- Embedded `LtOperationUnsigned` cols:
  compare_bit : F
  u16_flags : fields 4 F
  not_eq_inv : F
  comparison_limbs : fields 2 F
  -- The two U16MSBOp witnesses:
  b_msb : F
  c_msb : F
deriving ProvableStruct

/-- Clean-side circuit. Composes 3 subcircuits per Rust nesting + 5
trailing scalar gates wiring the sign-handling discipline. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- Sub-circuit 1: U16MSB on b[3] (sign bit of high limb).
  SP1Clean.U16MSBOp.assertion
    (⟨input.b[3], input.b_msb⟩ : Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  -- Sub-circuit 2: U16MSB on c[3].
  SP1Clean.U16MSBOp.assertion
    (⟨input.c[3], input.c_msb⟩ : Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  -- Sub-circuit 3: unsigned `<` on sign-flipped operands.
  -- Limb-3 transform: `b'[3] = b[3] + is_signed*32768 - 65536*b_msb`.
  let b3' := input.b[3] + input.is_signed * 32768 - 65536 * input.b_msb
  let c3' := input.c[3] + input.is_signed * 32768 - 65536 * input.c_msb
  SP1Clean.LtUnsignedOp.assertion
    (⟨#v[input.b[0], input.b[1], input.b[2], b3'],
       #v[input.c[0], input.c[1], input.c[2], c3'],
       input.compare_bit,
       input.u16_flags,
       input.not_eq_inv,
       input.comparison_limbs⟩ :
      Var SP1Clean.LtUnsignedOp.Inputs (ZMod p))
  -- 5 trailing scalar gates (`E1, E3, E5, E7, E9` from SP1):
  -- `is_signed` is boolean.
  input.is_signed * (input.is_signed - 1) === 0
  -- `is_real` discipline is delegated to the caller (chip level supplies
  -- `is_real = 1`, so the `is_real * (is_real - 1) = 0` gate is vacuous
  -- inside this wrapper).
  -- `(is_real - 1) * is_signed === 0`: when is_real = 0, is_signed must
  -- be 0 too. Again delegated to caller.
  -- `(is_signed - 1) * b_msb === 0`: when not signed, b_msb = 0.
  (input.is_signed - 1) * input.b_msb === 0
  -- `(is_signed - 1) * c_msb === 0`: when not signed, c_msb = 0.
  (input.is_signed - 1) * input.c_msb === 0

set_option maxHeartbeats 800000 in
-- 3 subcircuits + 3 scalar gates exceeds default `subcircuitsConsistent`.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.LtSignedOp"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Spec composes the three sub-Specs by direct field reference + the 3
surviving trailing gates (is_signed binary + 2 sign-vacuity gates). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  SP1Clean.U16MSBOp.Assertion.Spec ⟨input.b[3], input.b_msb⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec ⟨input.c[3], input.c_msb⟩ ∧
  (let b3' := input.b[3] + input.is_signed * 32768 - 65536 * input.b_msb
   let c3' := input.c[3] + input.is_signed * 32768 - 65536 * input.c_msb
   SP1Clean.LtUnsignedOp.Spec
    ⟨#v[input.b[0], input.b[1], input.b[2], b3'],
     #v[input.c[0], input.c[1], input.c[2], c3'],
     input.compare_bit,
     input.u16_flags,
     input.not_eq_inv,
     input.comparison_limbs⟩) ∧
  input.is_signed * (input.is_signed - 1) = 0 ∧
  (input.is_signed - 1) * input.b_msb = 0 ∧
  (input.is_signed - 1) * input.c_msb = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  sorry

/-- The full Clean `FormalAssertion` for `LtOperationSigned`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

/-- Bridge to SP1: `Spec input` is equivalent to SP1's
`LtOperationSigned.constraints` `allHold` form under `is_real = 1`. -/
theorem iff_sp1 (input : Inputs (ZMod p)) :
    Spec input ↔
      (LtOperationSigned.constraints input.b input.c
        { result := { u16_compare_operation := { bit := input.compare_bit },
                      u16_flags := input.u16_flags,
                      not_eq_inv := input.not_eq_inv,
                      comparison_limbs := input.comparison_limbs },
          b_msb := { msb := input.b_msb },
          c_msb := { msb := input.c_msb } }
        input.is_signed 1).allHold := by
  sorry

end SP1Clean.LtSignedOp
