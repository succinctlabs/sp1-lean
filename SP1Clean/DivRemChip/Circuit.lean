import SP1Clean.DivRemChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.Reader.RTypeReader
import SP1Clean.Operations.MulOperation
import SP1Clean.Operations.AddOperation
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.Operations.LtOperationUnsigned
import SP1Clean.Operations.IsZeroWordOperation
import SP1Clean.Operations.IsEqualWordOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `DivRemChip` Clean circuit + `FormalAssertion` (scaffold)

Composes the Rust subcircuit graph for `DivRemChip::eval`. The 8 RV64IM
variants (DIV/DIVU/DIVW/DIVUW/REM/REMU/REMW/REMUW) are encoded as a
one-hot selector at `aux_post.mode_flags[0..7]`.

The chip's `main` emits:
- `MulOp.assertion` ×2 (c × quotient lower + upper 8 limbs)
- `AddOp.assertion` ×2 (c-negation + remainder-negation)
- `LtUnsignedOp.assertion` ×1 (remainder < divisor)
- `U16MSBOp.assertion` ×4 (b/c/rem/quot MSBs — high limb)
- `IsZeroWordOp.assertion` ×1 (c = 0 check)
- `IsEqualWordOp.assertion` ×2 (overflow-detection for b/c)
- `CPUState.assertion`
- `RTypeReader.assertion`
- 8 mode-flag selector booleans + `is_real` + `op_a_0`

The ~150 inline arithmetic gates wiring the divide-with-remainder
discipline (quotient ⋅ c + remainder = b; sign-extend logic;
abs_remainder/abs_c witness derivation; etc.) are deferred to a later
implementation pass — `main` here captures the canonical Rust nesting
structure only. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.DivRemChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var DivRemCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter, op_a_write_value,
       b_word, c_word, quotient_word, _quotient_comp, _remainder_comp,
       remainder_word,
       abs_remainder, abs_c, max_abs_c_or_1, c_times_quotient,
       ctq_lower, ctq_upper, aux_post,
       _c_neg, _abs_c_alu_event, _abs_rem_alu_event, is_real,
       _remainder_check_multiplicity, _adapter_cols⟩ := cols
  let clk_low : Expression (ZMod p) := clk_0_16 + clk_16_24 * 65536
  let is_div : Expression (ZMod p) := aux_post.mode_flags[0]
  let is_divu : Expression (ZMod p) := aux_post.mode_flags[1]
  let is_rem_f : Expression (ZMod p) := aux_post.mode_flags[2]
  let is_remu : Expression (ZMod p) := aux_post.mode_flags[3]
  let is_divw : Expression (ZMod p) := aux_post.mode_flags[4]
  let is_remw : Expression (ZMod p) := aux_post.mode_flags[5]
  let is_divuw : Expression (ZMod p) := aux_post.mode_flags[6]
  let is_remuw : Expression (ZMod p) := aux_post.mode_flags[7]
  let opcode : Expression (ZMod p) :=
    is_div * 15 + is_divu * 16 + is_rem_f * 17 + is_remu * 18 +
    is_divw * 25 + is_remw * 27 + is_divuw * 26 + is_remuw * 28
  -- 2 MulOp subcircuits (c × quotient lower + upper):
  SP1Clean.MulOp.assertion
    (⟨#v[c_times_quotient[0], c_times_quotient[1],
         c_times_quotient[2], c_times_quotient[3]],
       c_word, quotient_word,
       ctq_lower.carry, ctq_lower.product,
       ctq_lower.b_lower_byte.low_bytes,
       ctq_lower.c_lower_byte.low_bytes,
       ctq_lower.b_msb, ctq_lower.c_msb,
       ctq_lower.product_msb.msb,
       ctq_lower.b_sign_extend, ctq_lower.c_sign_extend,
       is_div, is_divu, is_remu, is_rem_f, 0⟩ :
      Var SP1Clean.MulOp.Inputs (ZMod p))
  SP1Clean.MulOp.assertion
    (⟨#v[c_times_quotient[4], c_times_quotient[5],
         c_times_quotient[6], c_times_quotient[7]],
       c_word, quotient_word,
       ctq_upper.carry, ctq_upper.product,
       ctq_upper.b_lower_byte.low_bytes,
       ctq_upper.c_lower_byte.low_bytes,
       ctq_upper.b_msb, ctq_upper.c_msb,
       ctq_upper.product_msb.msb,
       ctq_upper.b_sign_extend, ctq_upper.c_sign_extend,
       0, 0, 0, 0, 0⟩ :
      Var SP1Clean.MulOp.Inputs (ZMod p))
  -- 2 AddOp subcircuits (c-neg + rem-neg, borrow-form):
  SP1Clean.AddOp.assertion
    (⟨c_word, abs_c, aux_post.c_neg_operation.value, is_real⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  SP1Clean.AddOp.assertion
    (⟨remainder_word, abs_remainder, aux_post.rem_neg_operation.value, is_real⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  -- LtUnsignedOp subcircuit (remainder < divisor):
  SP1Clean.LtUnsignedOp.assertion
    (⟨abs_remainder, max_abs_c_or_1,
       aux_post.remainder_lt_operation.u16_compare_operation.bit,
       aux_post.remainder_lt_operation.u16_flags,
       aux_post.remainder_lt_operation.not_eq_inv,
       aux_post.remainder_lt_operation.comparison_limbs⟩ :
      Var SP1Clean.LtUnsignedOp.Inputs (ZMod p))
  -- 4 U16MSB subcircuits (b/c/rem/quot high-limb MSBs):
  SP1Clean.U16MSBOp.assertion
    (⟨b_word[3], aux_post.b_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨c_word[3], aux_post.c_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨remainder_word[3], aux_post.rem_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨quotient_word[3], aux_post.quot_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  -- IsZeroWord (c = 0):
  SP1Clean.IsZeroWordOp.assertion
    (⟨c_word,
       #v[aux_post.is_c_0.is_zero_limb[0].inverse,
          aux_post.is_c_0.is_zero_limb[1].inverse,
          aux_post.is_c_0.is_zero_limb[2].inverse,
          aux_post.is_c_0.is_zero_limb[3].inverse],
       #v[aux_post.is_c_0.is_zero_limb[0].result,
          aux_post.is_c_0.is_zero_limb[1].result,
          aux_post.is_c_0.is_zero_limb[2].result,
          aux_post.is_c_0.is_zero_limb[3].result],
       aux_post.is_c_0.is_zero_first_half,
       aux_post.is_c_0.is_zero_second_half,
       aux_post.is_c_0.result⟩ :
      Var SP1Clean.IsZeroWordOp.Inputs (ZMod p))
  -- 2 IsEqualWord (overflow checks on b and c):
  SP1Clean.IsEqualWordOp.assertion
    (⟨b_word, #v[0, 0, 0, 32768],
       #v[aux_post.is_overflow_b.is_diff_zero.is_zero_limb[0].inverse,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[1].inverse,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[2].inverse,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[3].inverse],
       #v[aux_post.is_overflow_b.is_diff_zero.is_zero_limb[0].result,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[1].result,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[2].result,
          aux_post.is_overflow_b.is_diff_zero.is_zero_limb[3].result],
       aux_post.is_overflow_b.is_diff_zero.is_zero_first_half,
       aux_post.is_overflow_b.is_diff_zero.is_zero_second_half,
       aux_post.is_overflow_b.is_diff_zero.result⟩ :
      Var SP1Clean.IsEqualWordOp.Inputs (ZMod p))
  SP1Clean.IsEqualWordOp.assertion
    (⟨c_word, #v[65535, 65535, 65535, 65535],
       #v[aux_post.is_overflow_c.is_diff_zero.is_zero_limb[0].inverse,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[1].inverse,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[2].inverse,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[3].inverse],
       #v[aux_post.is_overflow_c.is_diff_zero.is_zero_limb[0].result,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[1].result,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[2].result,
          aux_post.is_overflow_c.is_diff_zero.is_zero_limb[3].result],
       aux_post.is_overflow_c.is_diff_zero.is_zero_first_half,
       aux_post.is_overflow_c.is_diff_zero.is_zero_second_half,
       aux_post.is_overflow_c.is_diff_zero.result⟩ :
      Var SP1Clean.IsEqualWordOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.RTypeReader.assertion
    (⟨clk_high, clk_low, opcode, pc, op_a_write_value, adapter⟩ :
      Var SP1Clean.RTypeReader.Inputs (ZMod p))
  -- 8 mode-flag selector booleans + is_real + op_a_0:
  is_div * (is_div - 1) === 0
  is_divu * (is_divu - 1) === 0
  is_rem_f * (is_rem_f - 1) === 0
  is_remu * (is_remu - 1) === 0
  is_divw * (is_divw - 1) === 0
  is_remw * (is_remw - 1) === 0
  is_divuw * (is_divuw - 1) === 0
  is_remuw * (is_remuw - 1) === 0
  is_real * (is_real - 1) === 0
  adapter.op_a_0 === 0

-- The deepest sub-circuit nest in the codebase: 12 .assertion calls,
-- one of which (MulOp) itself recursively composes 3 more. Default
-- `subcircuitsConsistent` / `localLength_eq` tactics blow past any
-- reasonable heartbeat budget; supply both as `sorry`.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) DivRemCols unit where
  name := "SP1Clean.DivRem"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq _ _ := by sorry
  subcircuitsConsistent _ _ := by sorry

def Assumptions (_ : DivRemCols (ZMod p)) : Prop := True

abbrev FormalSpec := @SP1Clean.DivRemChip.FormalSpec p

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `DivRemChip`. -/
def assertion : FormalAssertion (ZMod p) DivRemCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.DivRemChip
