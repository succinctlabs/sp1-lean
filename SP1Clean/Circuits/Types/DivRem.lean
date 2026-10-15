module

public import SP1Clean.Math.Word
public import SP1Clean.Circuits.Types.CPUState
public import SP1Clean.Circuits.Types.RTypeReader
public import SP1Clean.Circuits.Types.MulOperation
public import SP1Clean.Circuits.Types.AddOperation
public import SP1Clean.Circuits.Types.LtOperationUnsigned
public import SP1Clean.Circuits.Types.IsZeroWordOperation
public import SP1Clean.Circuits.Types.IsEqualWordOperation
public import SP1Clean.Circuits.Types.U16MSBOperation
public import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native division/remainder inputs and columns

The 246-cell native row owns its shared arithmetic blocks independently of generated Rust types.
`Faithful.divRemChipReconfigure` relates it to the legacy Rust oracle. The explicit ProvableStruct
instance avoids the elaboration cost of deriving the 45-field layout.
-/

@[expose] public section

namespace SP1Clean.DivRemChip

open SP1Clean.Circuits.Types

/-- Division/remainder inputs: row activity, reader columns and seven opcode selectors.
The selectors are ordered DIV, REM, REMU, DIVW, REMW, DIVUW, REMUW. DIVU is derived
as one minus their sum, so seven zero selectors choose DIVU, including padding.
The normalized arithmetic operands remain separate committed output columns. -/
structure Inputs (F : Type) where
  /-- One for an active row, zero for padding. -/
  is_real : F
  /-- Machine state before the instruction. -/
  state : CPUState F
  /-- R-type register and memory accesses. -/
  adapter : RTypeReader F
  /-- Supplied variant selectors, with DIVU omitted. -/
  selectors : Vector F 7
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Component-wise verifier evaluation of the DivRem chip input. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ is_real := Eval.eval env input.is_real,
         state := Eval.eval env input.state,
         adapter := Eval.eval env input.adapter,
         selectors := Eval.eval env input.selectors } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Raw dividend register read. W-variant semantics truncate it to the low 32 bits. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value

/-- Raw divisor register read. W-variant semantics truncate it to the low 32 bits. -/
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- Committed columns for all eight division and remainder variants. -/
structure Columns (F : Type) where
  /-- Machine state before the instruction. -/
  state : (CPUState F)
  /-- R-type register and memory accesses. -/
  adapter : (RTypeReader F)
  /-- Result selected for the destination register. -/
  a : (Word F)
  /-- Normalized dividend. -/
  b : (Word F)
  /-- Normalized divisor. -/
  c : (Word F)
  /-- Quotient used by the arithmetic identity. -/
  quotient : (Word F)
  /-- Quotient extended for the product check. -/
  quotient_comp : (Word F)
  /-- Remainder extended for the arithmetic identity. -/
  remainder_comp : (Word F)
  /-- Remainder used by result selection. -/
  remainder : (Word F)
  /-- Absolute value of the remainder. -/
  abs_remainder : (Word F)
  /-- Absolute value of the divisor. -/
  abs_c : (Word F)
  /-- Nonzero bound used to compare the remainder. -/
  max_abs_c_or_1 : (Word F)
  /-- Full divisor-times-quotient product limbs. -/
  c_times_quotient : (Vector F 8)
  /-- Lower product witness. -/
  c_times_quotient_lower : (MulOperation F)
  /-- Upper product witness. -/
  c_times_quotient_upper : (MulOperation F)
  /-- Witness for negating the divisor. -/
  c_neg_operation : (AddOperation F)
  /-- Witness for negating the remainder. -/
  rem_neg_operation : (AddOperation F)
  /-- Unsigned remainder-bound comparison. -/
  remainder_lt_operation : (LtOperationUnsigned F)
  /-- Carries in the quotient/remainder identity. -/
  carry : (Vector F 8)
  /-- Divisor zero-test witness. -/
  is_c_0 : (IsZeroWordOperation F)
  /-- Selector for DIV. -/
  is_div : F
  /-- Selector for DIVU. -/
  is_divu : F
  /-- Selector for REM. -/
  is_rem : F
  /-- Selector for REMU. -/
  is_remu : F
  /-- Selector for DIVW. -/
  is_divw : F
  /-- Selector for REMW. -/
  is_remw : F
  /-- Selector for DIVUW. -/
  is_divuw : F
  /-- Selector for REMUW. -/
  is_remuw : F
  /-- Signed division overflow indicator. -/
  is_overflow : F
  /-- Comparison of the dividend with the minimum signed value. -/
  is_overflow_b : (IsEqualWordOperation F)
  /-- Comparison of the divisor with minus one. -/
  is_overflow_c : (IsEqualWordOperation F)
  /-- Dividend sign-bit witness. -/
  b_msb : (U16MSBOperation F)
  /-- Remainder sign-bit witness. -/
  rem_msb : (U16MSBOperation F)
  /-- Divisor sign-bit witness. -/
  c_msb : (U16MSBOperation F)
  /-- Quotient sign-bit witness. -/
  quot_msb : (U16MSBOperation F)
  /-- Dividend negativity indicator. -/
  b_neg : F
  /-- Negative dividend without signed overflow. -/
  b_neg_not_overflow : F
  /-- Nonnegative dividend without signed overflow. -/
  b_not_neg_not_overflow : F
  /-- Activity flag for a full-width instruction. -/
  is_real_not_word : F
  /-- Remainder negativity indicator. -/
  rem_neg : F
  /-- Divisor negativity indicator. -/
  c_neg : F
  /-- Activity flag for divisor negation. -/
  abs_c_alu_event : F
  /-- Activity flag for remainder negation. -/
  abs_rem_alu_event : F
  /-- One for an active row, zero for padding. -/
  is_real : F
  /-- Activity flag for the remainder-bound comparison. -/
  remainder_check_multiplicity : F

instance : ProvableStruct Columns where
  components := [⟨CPUState, inferInstance⟩, ⟨RTypeReader, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨fields 8, inferInstance⟩, ⟨MulOperation, inferInstance⟩, ⟨MulOperation, inferInstance⟩, ⟨AddOperation, inferInstance⟩, ⟨AddOperation, inferInstance⟩, ⟨LtOperationUnsigned, inferInstance⟩, ⟨fields 8, inferInstance⟩, ⟨IsZeroWordOperation, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨IsEqualWordOperation, inferInstance⟩, ⟨IsEqualWordOperation, inferInstance⟩, ⟨U16MSBOperation, inferInstance⟩, ⟨U16MSBOperation, inferInstance⟩, ⟨U16MSBOperation, inferInstance⟩, ⟨U16MSBOperation, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩]
  toComponents := fun ⟨state, adapter, a, b, c, quotient, quotient_comp, remainder_comp, remainder, abs_remainder, abs_c, max_abs_c_or_1, c_times_quotient, c_times_quotient_lower, c_times_quotient_upper, c_neg_operation, rem_neg_operation, remainder_lt_operation, carry, is_c_0, is_div, is_divu, is_rem, is_remu, is_divw, is_remw, is_divuw, is_remuw, is_overflow, is_overflow_b, is_overflow_c, b_msb, rem_msb, c_msb, quot_msb, b_neg, b_neg_not_overflow, b_not_neg_not_overflow, is_real_not_word, rem_neg, c_neg, abs_c_alu_event, abs_rem_alu_event, is_real, remainder_check_multiplicity⟩ => .cons state (.cons adapter (.cons a (.cons b (.cons c (.cons quotient (.cons quotient_comp (.cons remainder_comp (.cons remainder (.cons abs_remainder (.cons abs_c (.cons max_abs_c_or_1 (.cons c_times_quotient (.cons c_times_quotient_lower (.cons c_times_quotient_upper (.cons c_neg_operation (.cons rem_neg_operation (.cons remainder_lt_operation (.cons carry (.cons is_c_0 (.cons is_div (.cons is_divu (.cons is_rem (.cons is_remu (.cons is_divw (.cons is_remw (.cons is_divuw (.cons is_remuw (.cons is_overflow (.cons is_overflow_b (.cons is_overflow_c (.cons b_msb (.cons rem_msb (.cons c_msb (.cons quot_msb (.cons b_neg (.cons b_neg_not_overflow (.cons b_not_neg_not_overflow (.cons is_real_not_word (.cons rem_neg (.cons c_neg (.cons abs_c_alu_event (.cons abs_rem_alu_event (.cons is_real (.cons remainder_check_multiplicity .nil))))))))))))))))))))))))))))))))))))))))))))
  fromComponents := fun (.cons state (.cons adapter (.cons a (.cons b (.cons c (.cons quotient (.cons quotient_comp (.cons remainder_comp (.cons remainder (.cons abs_remainder (.cons abs_c (.cons max_abs_c_or_1 (.cons c_times_quotient (.cons c_times_quotient_lower (.cons c_times_quotient_upper (.cons c_neg_operation (.cons rem_neg_operation (.cons remainder_lt_operation (.cons carry (.cons is_c_0 (.cons is_div (.cons is_divu (.cons is_rem (.cons is_remu (.cons is_divw (.cons is_remw (.cons is_divuw (.cons is_remuw (.cons is_overflow (.cons is_overflow_b (.cons is_overflow_c (.cons b_msb (.cons rem_msb (.cons c_msb (.cons quot_msb (.cons b_neg (.cons b_neg_not_overflow (.cons b_not_neg_not_overflow (.cons is_real_not_word (.cons rem_neg (.cons c_neg (.cons abs_c_alu_event (.cons abs_rem_alu_event (.cons is_real (.cons remainder_check_multiplicity .nil))))))))))))))))))))))))))))))))))))))))))))) => Columns.mk state adapter a b c quotient quotient_comp remainder_comp remainder abs_remainder abs_c max_abs_c_or_1 c_times_quotient c_times_quotient_lower c_times_quotient_upper c_neg_operation rem_neg_operation remainder_lt_operation carry is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c b_msb rem_msb c_msb quot_msb b_neg b_neg_not_overflow b_not_neg_not_overflow is_real_not_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event is_real remainder_check_multiplicity

provable_struct_eval_lemmas Columns

end SP1Clean.DivRemChip
