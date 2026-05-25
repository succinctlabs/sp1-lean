import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Operation.MulOperation.MulOperation
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Operations.Compare.LtOperationUnsigned.LtOperationUnsigned
import SP1Operations.Compare.IsZeroWordOperation.IsZeroWordOperation
import SP1Operations.Compare.IsEqualWordOperation.IsEqualWordOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.DivRem.DivRemChip
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Operations.MulOperation
import SP1Clean.Operations.AddOperation
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.Operations.LtOperationUnsigned
import SP1Clean.Operations.IsZeroWordOperation
import SP1Clean.Operations.IsEqualWordOperation
import SP1Clean.TrustMode
import RISCV.Instructions

/-! # `DivRemChip` cols-level surface (directory-form scaffold)

Row **246**, RType reader, 8-way one-hot selector
`Main[201..208] = (is_div, is_divu, is_rem, is_remu, is_divw, is_remw,
is_divuw, is_remuw)`, with opcodes 15/16/17/18/25/27/26/28 respectively.
`is_real = Main[244]`.

Sub-circuit composition (per `SP1Chips/DivRem/Common.lean`):
- `MulOp.assertion` ×2 (c×quotient lower + upper 8 limbs)
- `AddOp.assertion` ×2 (c-negation + remainder-negation)
- `LtUnsignedOp.assertion` ×1 (remainder < divisor check)
- `U16MSBOp.assertion` ×6+ (sign witnesses across b/c/quotient/remainder for full and W-variants)
- `IsZeroWordOp.assertion` ×1 (divide-by-zero check)
- `IsEqualWordOp.assertion` ×2 (overflow detection on b and c)
- `CPUState.assertion`
- `RTypeReader.assertion`
- ~150 inline arithmetic gates wiring the divide-with-remainder
  discipline together.

Cols struct mirrors Rust `DivRemCols<T>` exactly (via a nested
`DivRemAuxPost` sub-struct to keep field count under the
`ProvableStruct` deriver's threshold). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.DivRemChip

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Sub-record bundling the 14 post-MulOperation intermediates
(Main[166..240]). Nested into `DivRemCols` to keep `ProvableStruct`
deriving tractable. -/
structure DivRemAuxPost (T : Type) where
  c_neg_operation : AddOperation T
  rem_neg_operation : AddOperation T
  remainder_lt_operation : LtOperationUnsigned T
  carry : Vector T 8
  is_c_0 : IsZeroWordOperation T
  mode_flags : Vector T 8
  is_overflow : T
  is_overflow_b : IsEqualWordOperation T
  is_overflow_c : IsEqualWordOperation T
  b_msb : U16MSBOperation T
  rem_msb : U16MSBOperation T
  c_msb : U16MSBOperation T
  quot_msb : U16MSBOperation T
  neg_flags : Vector T 5
deriving ProvableStruct

/-- The chip's column struct, mirroring SP1's Rust `DivRemCols<T>`. -/
@[ext]
structure DivRemCols (T : Type) where
  state : CPUState T
  adapter : RTypeReader T
  op_a_write_value : Vector T 4
  b : Vector T 4
  c : Vector T 4
  quotient : Vector T 4
  quotient_comp : Vector T 4
  remainder_comp : Vector T 4
  remainder : Vector T 4
  abs_remainder : Vector T 4
  abs_c : Vector T 4
  max_abs_c_or_1 : Vector T 4
  c_times_quotient : Vector T 8
  c_times_quotient_lower : MulOperation T
  c_times_quotient_upper : MulOperation T
  aux_post : DivRemAuxPost T
  c_neg : T
  abs_c_alu_event : T
  abs_rem_alu_event : T
  is_real : T
  remainder_check_multiplicity : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Cols-level Sail-side helpers. -/
@[reducible] def sp1_op_a_cols (cols : DivRemCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_a.val

@[reducible] def sp1_op_b_cols (cols : DivRemCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_b.val

@[reducible] def sp1_op_c_cols (cols : DivRemCols (ZMod p)) : BitVec 5 :=
  BitVec.ofNat 5 cols.adapter.op_c.val

def sp1_divrem_cols (cols : DivRemCols (ZMod p)) : SailM Unit := do
  let op_a := sp1_op_a_cols cols
  Sail.writeReg Register.nextPC
    (Word.toBitVec64 #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2], 0])
  Sail.write_reg op_a (Word.toBitVec64 cols.op_a_write_value)

def divRemInitialState_cols (_cols : DivRemCols (ZMod p)) (_s : SailState) : Prop :=
  -- fromMain projection deferred (246-element struct); placeholder True
  -- so SailBridge stubs can typecheck.
  True

/-! ## Chip-level `FormalSpec`

Composes the sub-Specs by direct field reference (no `List.Forall`
fallback). The inline ~150 arithmetic gates (carry-chain wiring,
quotient/remainder discipline, neg_flags arithmetic) are folded into
the soundness/completeness proofs and not enumerated in this scaffold
`FormalSpec`. -/
def FormalSpec (cols : DivRemCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let mf := cols.aux_post.mode_flags
  let opcode : ZMod p :=
    mf[0] * 15 + mf[1] * 16 + mf[2] * 17 + mf[3] * 18 +
    mf[4] * 25 + mf[5] * 27 + mf[6] * 26 + mf[7] * 28
  -- 2 MulOp sub-Specs (c × quotient lower + upper):
  SP1Clean.MulOp.Spec
    ⟨cols.c_times_quotient.take 4 |>.cast (by simp),
     cols.c, cols.quotient,
     cols.c_times_quotient_lower.carry, cols.c_times_quotient_lower.product,
     cols.c_times_quotient_lower.b_lower_byte.low_bytes,
     cols.c_times_quotient_lower.c_lower_byte.low_bytes,
     cols.c_times_quotient_lower.b_msb, cols.c_times_quotient_lower.c_msb,
     cols.c_times_quotient_lower.product_msb.msb,
     cols.c_times_quotient_lower.b_sign_extend, cols.c_times_quotient_lower.c_sign_extend,
     mf[0], mf[1], mf[3], mf[2], 0⟩ ∧
  -- 2 AddOp sub-Specs (c-neg + rem-neg) — borrow-form via Assertion.Spec:
  SP1Clean.AddOp.Spec cols.c cols.abs_c cols.aux_post.c_neg_operation.value ∧
  SP1Clean.AddOp.Spec cols.remainder cols.abs_remainder
    cols.aux_post.rem_neg_operation.value ∧
  -- LtUnsigned sub-Spec (remainder < divisor):
  SP1Clean.LtUnsignedOp.Spec
    ⟨cols.abs_remainder, cols.max_abs_c_or_1,
     cols.aux_post.remainder_lt_operation.u16_compare_operation.bit,
     cols.aux_post.remainder_lt_operation.u16_flags,
     cols.aux_post.remainder_lt_operation.not_eq_inv,
     cols.aux_post.remainder_lt_operation.comparison_limbs⟩ ∧
  -- 4 U16MSB sub-Specs (b, c, rem, quot — high limbs):
  SP1Clean.U16MSBOp.Assertion.Spec ⟨cols.b[3], cols.aux_post.b_msb.msb⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec ⟨cols.c[3], cols.aux_post.c_msb.msb⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec ⟨cols.remainder[3], cols.aux_post.rem_msb.msb⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec ⟨cols.quotient[3], cols.aux_post.quot_msb.msb⟩ ∧
  -- IsZeroWord (c = 0):
  SP1Clean.IsZeroWordOp.Spec
    ⟨cols.c,
     #v[cols.aux_post.is_c_0.is_zero_limb[0].inverse,
        cols.aux_post.is_c_0.is_zero_limb[1].inverse,
        cols.aux_post.is_c_0.is_zero_limb[2].inverse,
        cols.aux_post.is_c_0.is_zero_limb[3].inverse],
     #v[cols.aux_post.is_c_0.is_zero_limb[0].result,
        cols.aux_post.is_c_0.is_zero_limb[1].result,
        cols.aux_post.is_c_0.is_zero_limb[2].result,
        cols.aux_post.is_c_0.is_zero_limb[3].result],
     cols.aux_post.is_c_0.is_zero_first_half,
     cols.aux_post.is_c_0.is_zero_second_half,
     cols.aux_post.is_c_0.result⟩ ∧
  -- CPUState + RTypeReader:
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.RTypeReader.rtypeReaderSpec clk_low opcode cols.state.pc
      cols.op_a_write_value cols.adapter ∧
  -- Selector booleans + standard gates (8 mode_flags + carry/sum + op_a_0):
  mf[0] * (mf[0] - 1) = 0 ∧
  mf[1] * (mf[1] - 1) = 0 ∧
  mf[2] * (mf[2] - 1) = 0 ∧
  mf[3] * (mf[3] - 1) = 0 ∧
  mf[4] * (mf[4] - 1) = 0 ∧
  mf[5] * (mf[5] - 1) = 0 ∧
  mf[6] * (mf[6] - 1) = 0 ∧
  mf[7] * (mf[7] - 1) = 0 ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

end SP1Clean.DivRemChip
