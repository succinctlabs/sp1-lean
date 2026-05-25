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
import SP1Operations.Operation.MulOperation.MulOperation
import SP1Clean.Operations.U16toU8OperationSafe
import SP1Clean.Operations.U16MSBOperation

/-! # `MulOperation` Clean mirror (scaffold)

SP1's `MulOperation` is the 16-byte unsigned product carry-chain
implementing MUL/MULH/MULHU/MULHSU/MULW. Rust nesting (from
`SP1Operations/Operation/MulOperation/Constraints.lean`):

- `U16toU8OperationSafe::eval` ×2 — decompose `b_word` and `c_word`
  into 8-byte limb vectors and assert each byte is `< 256`.
- `U16MSBOperation::eval` ×1 — extract the MSB of `a_word[1]` for the
  MULW sign-extend pathway (gated by `is_mulw`).
- Inline 16-byte carry-chain `assertZero` gates (43 of them) plus 2
  `send (.byte LessThanOrEq128 b_msb E7 0)` byte lookups for the
  MULHSU sign-extend witnessing. These are the operation's own
  arithmetic — they don't fan out to another sub-op, so they're emitted
  inline.

This scaffold composes the 3 subcircuit calls faithfully and leaves the
16-byte carry chain + sign-extend gates as `pure ()` placeholders + TODO
comment — those are the chip-specific arithmetic that have no upstream
sub-op to delegate to. Soundness and completeness bodies are `sorry`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.MulOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled FormalAssertion input. Mirrors Rust `MulOperation<T>` cols
plus the three operand words and 5 variant selectors. -/
structure Inputs (F : Type) where
  a_word : fields 4 F
  b_word : fields 4 F
  c_word : fields 4 F
  -- MulOperation cols struct:
  carry : fields 16 F
  product : fields 16 F
  b_low_bytes : fields 4 F
  c_low_bytes : fields 4 F
  b_msb : F
  c_msb : F
  product_msb : F
  b_sign_extend : F
  c_sign_extend : F
  -- Variant selectors (passed-through, MUL/MULH/MULHU/MULHSU/MULW):
  is_mul : F
  is_mulh : F
  is_mulhu : F
  is_mulhsu : F
  is_mulw : F
deriving ProvableStruct

/-- Clean-side circuit. Composes the 3 Rust subcircuit calls:
`U16toU8OpSafe.assertion` ×2 + `U16MSBOp.assertion` ×1. The 16-byte
carry-chain inline gates + 2 sign-extend byte lookups are **TODO** —
they're the operation's own arithmetic with no upstream sub-op. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- Sub-circuit 1: decompose b_word into low/high bytes (with U8-range checks).
  SP1Clean.U16toU8OpSafe.assertion
    (⟨input.b_word, input.b_low_bytes⟩ : Var SP1Clean.U16toU8OpSafe.Inputs (ZMod p))
  -- Sub-circuit 2: decompose c_word.
  SP1Clean.U16toU8OpSafe.assertion
    (⟨input.c_word, input.c_low_bytes⟩ : Var SP1Clean.U16toU8OpSafe.Inputs (ZMod p))
  -- Sub-circuit 3: MSB of a_word[1] (used by MULW sign-extend).
  SP1Clean.U16MSBOp.assertion
    (⟨input.a_word[1], input.product_msb⟩ : Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  -- TODO: emit the 16-byte product carry chain (43 assertZeros over
  -- `carry` and `product` columns) and the 2 LessThanOrEq128 byte
  -- lookups for `b_msb` / `c_msb` (MULHSU sign-extend discipline).
  -- These are the operation's own arithmetic — they don't fan out to
  -- another sub-op, so emit them inline once `iff_sp1` is filled in.
  pure ()

set_option maxHeartbeats 800000 in
-- 3 subcircuits exceed default `subcircuitsConsistent` budget.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.MulOp"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Spec composes the 3 sub-Specs by direct field reference. The 16-byte
product carry-chain invariant and sign-extend discipline are TODO. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  SP1Clean.U16toU8OpSafe.Spec ⟨input.b_word, input.b_low_bytes⟩ ∧
  SP1Clean.U16toU8OpSafe.Spec ⟨input.c_word, input.c_low_bytes⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec ⟨input.a_word[1], input.product_msb⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  sorry

/-- The full Clean `FormalAssertion` for `MulOperation`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

/-- Bridge to SP1: `Spec input` is equivalent to SP1's
`MulOperation.constraints` `allHold` form under `is_real = 1`. -/
theorem iff_sp1 (input : Inputs (ZMod p)) :
    Spec input ↔
      (MulOperation.constraints
        input.a_word input.b_word input.c_word
        { carry := input.carry, product := input.product,
          b_lower_byte := { low_bytes := input.b_low_bytes },
          c_lower_byte := { low_bytes := input.c_low_bytes },
          b_msb := input.b_msb, c_msb := input.c_msb,
          product_msb := { msb := input.product_msb },
          b_sign_extend := input.b_sign_extend,
          c_sign_extend := input.c_sign_extend }
        1 input.is_mul input.is_mulh input.is_mulw input.is_mulhu
        input.is_mulhsu).allHold := by
  sorry

end SP1Clean.MulOp
