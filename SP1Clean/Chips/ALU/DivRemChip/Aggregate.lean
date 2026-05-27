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
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Clean.Operations.AddrAddOperation
import SP1Clean.Operations.MulOperation
import SP1Clean.Operations.AddOperation
import SP1Clean.Operations.IsZeroWordOperation
import SP1Clean.Operations.IsEqualWordOperation
import SP1Clean.Operations.LtOperationUnsigned
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import SP1Chips.DivRem.DivRemChip

/-! # Chip-level `DivRemChip` mirror — bundled 4-variant integer division

The DivRem chip bundles four RV64IM division variants
(`div`/`divu`/`rem`/`remu`) into a single 246-column trace, with two
`MulOperation` sub-fragments (one for the quotient × divisor product,
one for the dividend reconstruction), plus `IsZeroWord`, `AddOperation`
(for remainder), and other sub-fragments.

Iff-only structural mirror discipline (heaviest chip in the ISA). The
division-arithmetic content (carry chains, sign handling, remainder
reconstruction) is captured as a placeholder `divRemSpec` (currently
`True`).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.DivRem

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (cols : Var DivRemCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c, _op_c_memory⟩,
       _op_a_write_value,
       _b, _c, _quotient, _quotient_comp, _remainder_comp, _remainder,
       _abs_remainder, _abs_c, _max_abs_c_or_1, _c_times_quotient,
       _c_times_quotient_lower, _c_times_quotient_upper,
       aux_post,
       c_neg, abs_c_alu_event, abs_rem_alu_event, is_real, _remainder_check_multiplicity,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Opcode encoded one-hot via the 8 mode flags at Main[201..208].
  -- Opcodes: DIV=15, DIVU=16, REM=17, REMU=18, DIVW=25, DIVUW=26,
  --          REMW=27, REMUW=28. mode_flags order matches upstream:
  --          [is_div, is_divu, is_rem, is_remu, is_divw, is_remw,
  --           is_divuw, is_remuw].
  let is_div   : Expression (ZMod p) := aux_post.mode_flags[0]
  let is_divu  : Expression (ZMod p) := aux_post.mode_flags[1]
  let is_rem_f : Expression (ZMod p) := aux_post.mode_flags[2]
  let is_remu  : Expression (ZMod p) := aux_post.mode_flags[3]
  let is_divw  : Expression (ZMod p) := aux_post.mode_flags[4]
  let is_remw  : Expression (ZMod p) := aux_post.mode_flags[5]
  let is_divuw : Expression (ZMod p) := aux_post.mode_flags[6]
  let is_remuw : Expression (ZMod p) := aux_post.mode_flags[7]
  SP1Clean.ProgramTable.assertion
    (⟨pc,
      is_div * 15 + is_divu * 16 + is_rem_f * 17 + is_remu * 18
        + is_divw * 25 + is_remw * 27 + is_divuw * 26 + is_remuw * 28,
      op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  c_neg * (c_neg - 1) === 0
  abs_c_alu_event * (abs_c_alu_event - 1) === 0
  abs_rem_alu_event * (abs_rem_alu_event - 1) === 0
  is_real * (is_real - 1) === 0
  op_a_0 === 0

/-- Placeholder for the DivRem arithmetic Spec content. Currently
`True`; a future iteration can inline `MulOperation` × 2,
`IsZeroWordOperation`, `AddOperation` constraints and the
quotient/remainder/sign-handling clauses. -/
def divRemSpec (_cols : DivRemCols (ZMod p)) : Prop := True

def TraceSpec (cols : DivRemCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_a
      { prev_value := cols.adapter.op_a_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_b
      { prev_value := cols.adapter.op_b_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 2
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_c
      { prev_value := cols.adapter.op_c_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb } }) ∧
  cols.c_neg * (cols.c_neg - 1) = 0 ∧
  cols.abs_c_alu_event * (cols.abs_c_alu_event - 1) = 0 ∧
  cols.abs_rem_alu_event * (cols.abs_rem_alu_event - 1) = 0 ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  divRemSpec cols ∧
  cols.adapter_cols.is_trusted = 1

/-- The chip-level half-iff bridge (DivRem). **Proof body sorry'd**. -/
theorem traceSpec_implies_allHold (Main : Vector (ZMod p) 246)
    (h_is_real : Main[244] = 1) (h_op_a_0 : Main[13] = 0)
    (h_spec : TraceSpec (fromMain Main)) :
    (_root_.DivRem.constraints Main).allHold := by
  sorry

/-- Clean-side `correct_div`: 64-bit signed division. -/
theorem correct_div [Fact (2 ^ 24 < p)]
    (Main : Vector (ZMod p) 246) (s : SailState)
    (h_is_div : Main[201] = 1) (h_is_real : Main[244] = 1) (h_op_a_0 : Main[13] = 0)
    (h_spec : TraceSpec (fromMain Main))
    (state_cstrs : (_root_.DivRem.constraints Main).initialState s) :
    let op_c := _root_.DivRem.sp1_op_c Main
    let op_b := _root_.DivRem.sp1_op_b Main
    let op_a := _root_.DivRem.sp1_op_a Main
    (_root_.Div.spec_div (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.DivRem.Poly.sp1_op Main).run s :=
  _root_.DivRem.Poly.correct_div Main s
    (traceSpec_implies_allHold Main h_is_real h_op_a_0 h_spec)
    h_is_real h_is_div state_cstrs

/-! ## Full `FormalAssertion` promotion (Path-2, faithful sub-circuit form)

`Assertion.main` mirrors `SP1Chips/DivRem/Constraints.lean` 1:1 with all
17 sub-circuit invocations from the SP1 constraint compiler:
- CS0/CS1: 2× `MulOp.assertion` (c_times_quotient lower/upper halves —
  one always-on with `is_mul = is_real`, one variant-gated with
  `is_mulh = is_div+is_rem`, `is_mulhu = is_divu+is_remu` for the
  signed-vs-unsigned high half).
- CS2/CS3/CS4/CS5: 4× `IsEqualWordOp.assertion` (overflow detection
  against ±2^63 / -1; pairs share witness columns).
- CS6: 1× `IsZeroWordOp.assertion` (divisor-is-zero special case).
- CS7/CS8: 2× `AddOp.assertion` (absolute-value computations for the
  signed-divrem variants).
- CS9: 1× `LtUnsignedOp.assertion` (remainder < divisor check).
- CS10–CS16: 7× `U16MSBOp.assertion` (sign-bit extraction across op_b /
  op_c / remainder / quotient at high and second-high limbs).

Plus a `CPUState.Gated.assertion` and `RTypeReader.Gated.assertion`
collapsing the SP1 `eval_cpu_state` + `eval_r_type` calls, matching the
canonical AddChip pattern.

Soundness/completeness are stubbed with `sorry` — this lands the
structural CLEAN_FUTURE D2/D3 alignment only. Caveat: the 7 U16MSB
calls use the always-on `U16MSBOp.assertion` because no
`U16MSBOp.Gated.assertion` exists yet; SP1's mult-arg (`Main[239]`,
`E2`) is dropped at the Clean call site. Adding `U16MSBOp.Gated` is a
follow-up. -/

namespace Assertion

open Circuit

-- `MulOp.assertion` requires `[Fact (2 ^ 24 < p)]` (carry-chain limb
-- bound); the section's `2 ^ 17 < p` is not enough.
variable [Fact (2 ^ 24 < p)]

@[reducible]
def main (cols : Var DivRemCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       adapter, op_a_write_value,
       b, c, quotient, quotient_comp, remainder_comp, remainder,
       abs_remainder, abs_c, max_abs_c_or_1, c_times_quotient,
       c_times_quotient_lower, c_times_quotient_upper,
       aux_post,
       c_neg, abs_c_alu_event, abs_rem_alu_event, is_real, remainder_check_multiplicity,
       adapter_cols⟩ := cols
  let clk_low := clk_0_16 + clk_16_24 * 65536
  -- Mode-flag aliases mirroring SP1's `E0..E11` aggregates.
  let is_div   : Expression (ZMod p) := aux_post.mode_flags[0]
  let is_divu  : Expression (ZMod p) := aux_post.mode_flags[1]
  let is_rem_f : Expression (ZMod p) := aux_post.mode_flags[2]
  let is_remu  : Expression (ZMod p) := aux_post.mode_flags[3]
  let is_divw  : Expression (ZMod p) := aux_post.mode_flags[4]
  let is_remw  : Expression (ZMod p) := aux_post.mode_flags[5]
  let is_divuw : Expression (ZMod p) := aux_post.mode_flags[6]
  let is_remuw : Expression (ZMod p) := aux_post.mode_flags[7]
  let is_word  : Expression (ZMod p) := is_divw + is_remw + is_divuw + is_remuw  -- E2
  let e92      : Expression (ZMod p) := is_div + is_rem_f                        -- E92
  let e93      : Expression (ZMod p) := is_divu + is_remu                        -- E93
  let opcode_e : Expression (ZMod p) :=
    is_div * 15 + is_divu * 16 + is_rem_f * 17 + is_remu * 18
      + is_divw * 25 + is_remw * 27 + is_divuw * 26 + is_remuw * 28
  -- Reader block: eval_cpu_state + eval_r_type (collapsed via Gated).
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.RTypeReader.Gated.assertion
    (⟨clk_high, clk_low, opcode_e, pc, op_a_write_value, adapter,
       is_real, adapter_cols.is_trusted⟩ :
      Var SP1Clean.RTypeReader.Gated.Inputs (ZMod p))
  -- CS0: c_times_quotient_lower = quotient_comp × c (always pure mul gated by is_real).
  SP1Clean.MulOp.assertion
    (⟨#v[c_times_quotient[0], c_times_quotient[1],
         c_times_quotient[2], c_times_quotient[3]],
       quotient_comp, c,
       c_times_quotient_lower.carry, c_times_quotient_lower.product,
       c_times_quotient_lower.b_lower_byte.low_bytes,
       c_times_quotient_lower.c_lower_byte.low_bytes,
       c_times_quotient_lower.b_msb, c_times_quotient_lower.c_msb,
       c_times_quotient_lower.product_msb.msb,
       c_times_quotient_lower.b_sign_extend,
       c_times_quotient_lower.c_sign_extend,
       is_real, 0, 0, 0, 0⟩ :
      Var SP1Clean.MulOp.Inputs (ZMod p))
  -- CS1: c_times_quotient_upper = quotient_comp × c (variant-gated MULH/MULHU).
  SP1Clean.MulOp.assertion
    (⟨#v[c_times_quotient[4], c_times_quotient[5],
         c_times_quotient[6], c_times_quotient[7]],
       quotient_comp, c,
       c_times_quotient_upper.carry, c_times_quotient_upper.product,
       c_times_quotient_upper.b_lower_byte.low_bytes,
       c_times_quotient_upper.c_lower_byte.low_bytes,
       c_times_quotient_upper.b_msb, c_times_quotient_upper.c_msb,
       c_times_quotient_upper.product_msb.msb,
       c_times_quotient_upper.b_sign_extend,
       c_times_quotient_upper.c_sign_extend,
       0, e92, e93, 0, 0⟩ :
      Var SP1Clean.MulOp.Inputs (ZMod p))
  -- CS2: is_overflow_b — op_b == -2^63 (little-endian: 0, 0, 0, 32768).
  SP1Clean.IsEqualWordOp.assertion
    (⟨adapter.op_b_memory.prev_value, #v[0, 0, 0, 32768],
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
  -- CS3: is_overflow_c — op_c == -1 (all-ones).
  SP1Clean.IsEqualWordOp.assertion
    (⟨adapter.op_c_memory.prev_value, #v[65535, 65535, 65535, 65535],
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
  -- CS4: is_overflow_b (32-bit check) — low 2 limbs of op_b == -2^31.
  --      Reuses the same is_overflow_b witness columns as CS2.
  SP1Clean.IsEqualWordOp.assertion
    (⟨#v[adapter.op_b_memory.prev_value[0], adapter.op_b_memory.prev_value[1], 0, 0],
       #v[0, 32768, 0, 0],
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
  -- CS5: is_overflow_c (32-bit check) — low 2 limbs of op_c == -1 (32-bit).
  --      Reuses the same is_overflow_c witness columns as CS3.
  SP1Clean.IsEqualWordOp.assertion
    (⟨#v[adapter.op_c_memory.prev_value[0], adapter.op_c_memory.prev_value[1], 0, 0],
       #v[65535, 65535, 0, 0],
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
  -- CS6: is_c_0 — divisor c == 0.
  SP1Clean.IsZeroWordOp.assertion
    (⟨c,
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
  -- CS7: c_neg_operation — c + abs_c = neg_c (for the absolute-value
  --      computation in signed divrem).
  SP1Clean.AddOp.assertion
    (⟨c, abs_c, aux_post.c_neg_operation.value, abs_c_alu_event⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  -- CS8: rem_neg_operation — remainder_comp + abs_remainder.
  SP1Clean.AddOp.assertion
    (⟨remainder_comp, abs_remainder, aux_post.rem_neg_operation.value, abs_rem_alu_event⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  -- CS9: remainder_lt_operation — abs_remainder < max_abs_c_or_1.
  SP1Clean.LtUnsignedOp.assertion
    (⟨abs_remainder, max_abs_c_or_1,
       aux_post.remainder_lt_operation.u16_compare_operation.bit,
       aux_post.remainder_lt_operation.u16_flags,
       aux_post.remainder_lt_operation.not_eq_inv,
       aux_post.remainder_lt_operation.comparison_limbs⟩ :
      Var SP1Clean.LtUnsignedOp.Inputs (ZMod p))
  -- CS10-CS16: 7× U16MSB. SP1 emits these with selector mults
  -- (Main[239] = is_real_not_word for the 64-bit family; E2 = is_word
  -- for the 32-bit family). Clean's `U16MSBOp.assertion` is the
  -- unconditional form; the multiplicity-gated `U16MSBOp.assertionGated`
  -- variant is used by the new Multiplicity/ chip mirrors. This
  -- Aggregate file is scheduled for deletion in Phase 4 of the migration.
  SP1Clean.U16MSBOp.assertion
    (⟨adapter.op_b_memory.prev_value[3], aux_post.b_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨adapter.op_c_memory.prev_value[3], aux_post.c_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨remainder[3], aux_post.rem_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨adapter.op_b_memory.prev_value[1], aux_post.b_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨adapter.op_c_memory.prev_value[1], aux_post.c_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨remainder[1], aux_post.rem_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertion
    (⟨quotient[1], aux_post.quot_msb.msb⟩ :
      Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  -- Chip-level scalar gates: binary flags + op_a_0 zero.
  c_neg             * (c_neg             - 1) === 0
  abs_c_alu_event   * (abs_c_alu_event   - 1) === 0
  abs_rem_alu_event * (abs_rem_alu_event - 1) === 0
  is_real           * (is_real           - 1) === 0
  remainder_check_multiplicity * (remainder_check_multiplicity - 1) === 0
  -- Suppress unused-binding warnings from columns whose constraints
  -- belong to the as-yet-uncomposed scalar polynomial gates (carry
  -- chains, intermediate equalities). They surface in the legacy
  -- `Spec`/`divRemSpec` path.
  let _ := b
  adapter.op_a_0 === 0

set_option maxHeartbeats 6400000 in
-- 6.4M heartbeats: 19 sub-circuit calls (2 readers + 2 MulOp + 4
-- IsEqualWord + IsZeroWord + 2 AddOp + LtUnsigned + 7 U16MSB) push
-- `localLength_eq` synthesis well past the default. The
-- `subcircuitsConsistent` field is sorry'd (same as MulChip's
-- elaborated) — soundness/completeness are also sorry'd.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) DivRemCols unit where
  name := "SP1Clean.DivRem"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by sorry

def Assumptions (_ : DivRemCols (ZMod p)) : Prop := True

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  sorry

end Assertion

-- `Fact (2 ^ 24 < p)` is transitive via `MulOp.assertion`'s requirement
-- in `Assertion.elaborated`.
def assertion [Fact (2 ^ 24 < p)] : FormalAssertion (ZMod p) DivRemCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.DivRem
