import SP1Clean.Math.Word
import SP1Clean.Extracted.CPUState
import SP1Clean.Extracted.RTypeReader
import SP1Clean.Extracted.MulOperation
import SP1Clean.Extracted.AddOperation
import SP1Clean.Extracted.LtOperationUnsigned
import SP1Clean.Extracted.IsZeroWordOperation
import SP1Clean.Extracted.IsEqualWordOperation
import SP1Clean.Extracted.U16MSBOperation
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native DIVREM-chip row

The native `DivRemChip.Columns` struct: field-for-field the shape of SP1 Rust's 246-cell
`DivRemCols` row, with every nested arithmetic block kept at the shared standalone generated
column structs (`Extracted.MulOperation`, `Extracted.AddOperation`, ...) that other chips also
compose. `Faithful.divRemChipReconfigure` is the sole bridge to Rust's separately generated
whole-chip oracle row (`Extracted.DivRemOracle.DivRemCols`).

Lives below `Native/Operations/DivRemOperation/OwnAsserts.lean` in the import DAG (the chip's own
assert tail is typed at this row), so it cannot sit in `Contracts/Chips.lean` like the smaller
chips' rows. The `ProvableStruct` instance is spelled explicitly, mirroring the generated form,
because `deriving` on a 45-field struct is elaboration-heavy. -/

namespace SP1Clean.DivRemChip

open SP1Clean.Extracted

structure Columns (F : Type) where
  state : (CPUState F)
  adapter : (RTypeReader F)
  a : (Word F)
  b : (Word F)
  c : (Word F)
  quotient : (Word F)
  quotient_comp : (Word F)
  remainder_comp : (Word F)
  remainder : (Word F)
  abs_remainder : (Word F)
  abs_c : (Word F)
  max_abs_c_or_1 : (Word F)
  c_times_quotient : (Vector F 8)
  c_times_quotient_lower : (MulOperation F)
  c_times_quotient_upper : (MulOperation F)
  c_neg_operation : (AddOperation F)
  rem_neg_operation : (AddOperation F)
  remainder_lt_operation : (LtOperationUnsigned F)
  carry : (Vector F 8)
  is_c_0 : (IsZeroWordOperation F)
  is_div : F
  is_divu : F
  is_rem : F
  is_remu : F
  is_divw : F
  is_remw : F
  is_divuw : F
  is_remuw : F
  is_overflow : F
  is_overflow_b : (IsEqualWordOperation F)
  is_overflow_c : (IsEqualWordOperation F)
  b_msb : (U16MSBOperation F)
  rem_msb : (U16MSBOperation F)
  c_msb : (U16MSBOperation F)
  quot_msb : (U16MSBOperation F)
  b_neg : F
  b_neg_not_overflow : F
  b_not_neg_not_overflow : F
  is_real_not_word : F
  rem_neg : F
  c_neg : F
  abs_c_alu_event : F
  abs_rem_alu_event : F
  is_real : F
  remainder_check_multiplicity : F

instance : ProvableStruct Columns where
  components := [⟨CPUState, inferInstance⟩, ⟨RTypeReader, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨Word, inferInstance⟩, ⟨fields 8, inferInstance⟩, ⟨MulOperation, inferInstance⟩, ⟨MulOperation, inferInstance⟩, ⟨AddOperation, inferInstance⟩, ⟨AddOperation, inferInstance⟩, ⟨LtOperationUnsigned, inferInstance⟩, ⟨fields 8, inferInstance⟩, ⟨IsZeroWordOperation, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨IsEqualWordOperation, inferInstance⟩, ⟨IsEqualWordOperation, inferInstance⟩, ⟨U16MSBOperation, inferInstance⟩, ⟨U16MSBOperation, inferInstance⟩, ⟨U16MSBOperation, inferInstance⟩, ⟨U16MSBOperation, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩, ⟨field, inferInstance⟩]
  toComponents := fun ⟨state, adapter, a, b, c, quotient, quotient_comp, remainder_comp, remainder, abs_remainder, abs_c, max_abs_c_or_1, c_times_quotient, c_times_quotient_lower, c_times_quotient_upper, c_neg_operation, rem_neg_operation, remainder_lt_operation, carry, is_c_0, is_div, is_divu, is_rem, is_remu, is_divw, is_remw, is_divuw, is_remuw, is_overflow, is_overflow_b, is_overflow_c, b_msb, rem_msb, c_msb, quot_msb, b_neg, b_neg_not_overflow, b_not_neg_not_overflow, is_real_not_word, rem_neg, c_neg, abs_c_alu_event, abs_rem_alu_event, is_real, remainder_check_multiplicity⟩ => .cons state (.cons adapter (.cons a (.cons b (.cons c (.cons quotient (.cons quotient_comp (.cons remainder_comp (.cons remainder (.cons abs_remainder (.cons abs_c (.cons max_abs_c_or_1 (.cons c_times_quotient (.cons c_times_quotient_lower (.cons c_times_quotient_upper (.cons c_neg_operation (.cons rem_neg_operation (.cons remainder_lt_operation (.cons carry (.cons is_c_0 (.cons is_div (.cons is_divu (.cons is_rem (.cons is_remu (.cons is_divw (.cons is_remw (.cons is_divuw (.cons is_remuw (.cons is_overflow (.cons is_overflow_b (.cons is_overflow_c (.cons b_msb (.cons rem_msb (.cons c_msb (.cons quot_msb (.cons b_neg (.cons b_neg_not_overflow (.cons b_not_neg_not_overflow (.cons is_real_not_word (.cons rem_neg (.cons c_neg (.cons abs_c_alu_event (.cons abs_rem_alu_event (.cons is_real (.cons remainder_check_multiplicity .nil))))))))))))))))))))))))))))))))))))))))))))
  fromComponents := fun (.cons state (.cons adapter (.cons a (.cons b (.cons c (.cons quotient (.cons quotient_comp (.cons remainder_comp (.cons remainder (.cons abs_remainder (.cons abs_c (.cons max_abs_c_or_1 (.cons c_times_quotient (.cons c_times_quotient_lower (.cons c_times_quotient_upper (.cons c_neg_operation (.cons rem_neg_operation (.cons remainder_lt_operation (.cons carry (.cons is_c_0 (.cons is_div (.cons is_divu (.cons is_rem (.cons is_remu (.cons is_divw (.cons is_remw (.cons is_divuw (.cons is_remuw (.cons is_overflow (.cons is_overflow_b (.cons is_overflow_c (.cons b_msb (.cons rem_msb (.cons c_msb (.cons quot_msb (.cons b_neg (.cons b_neg_not_overflow (.cons b_not_neg_not_overflow (.cons is_real_not_word (.cons rem_neg (.cons c_neg (.cons abs_c_alu_event (.cons abs_rem_alu_event (.cons is_real (.cons remainder_check_multiplicity .nil))))))))))))))))))))))))))))))))))))))))))))) => Columns.mk state adapter a b c quotient quotient_comp remainder_comp remainder abs_remainder abs_c max_abs_c_or_1 c_times_quotient c_times_quotient_lower c_times_quotient_upper c_neg_operation rem_neg_operation remainder_lt_operation carry is_c_0 is_div is_divu is_rem is_remu is_divw is_remw is_divuw is_remuw is_overflow is_overflow_b is_overflow_c b_msb rem_msb c_msb quot_msb b_neg b_neg_not_overflow b_not_neg_not_overflow is_real_not_word rem_neg c_neg abs_c_alu_event abs_rem_alu_event is_real remainder_check_multiplicity

end SP1Clean.DivRemChip
