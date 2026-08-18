import SP1Clean.Faithful.ChipOracle
import SP1Clean.Faithful.AddOperation
import SP1Clean.Faithful.IsEqualWordOperation
import SP1Clean.Faithful.LtOperationUnsigned
import SP1Clean.Faithful.MulChip
import SP1Clean.Faithful.U16MSBOperation
import SP1Clean.Extracted.ChipOracle.DivRem
import SP1Clean.Proofs.Chips.DivRemChip.Formal

/-!
# Exact whole-chip faithfulness for SP1 `DivRem`

This file relates the proof-oriented native Clean `DivRemChip` row to the complete generated
row-level oracle for pinned SP1 v6.4.0.

The native circuit uses an input-first physical row, whereas Rust's `DivRemCols` follows the
`#[repr(C)]` column order.  The four folded local chunks and explicit readback proof below give
the complete, auditable permutation between those 246 cells.  They avoid unfolding the 217-bind
populate routine in every downstream proof and make the row codec independent of honest witness
generation.
-/

namespace SP1Clean.Faithful

open SP1Clean
open SP1Clean.Extracted
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private theorem divRemCols_size :
    size DivRemChip.Columns = 246 := rfl

private theorem divRemInputs_size :
    size DivRemChip.Inputs = 29 := rfl

private theorem divRemMulOperation_size :
    size Extracted.MulOperation = 45 := rfl

private theorem divRemIsEqualWordOperation_size :
    size Extracted.IsEqualWordOperation = 11 := rfl

private theorem divRemIsZeroWordOperation_size :
    size Extracted.IsZeroWordOperation = 11 := rfl

private theorem divRemWord_size :
    size Word = 4 := rfl

private theorem divRemFieldsEight_size :
    size (fields 8) = 8 := rfl

private theorem divRemFieldsFour_size :
    size (fields 4) = 4 := rfl

private theorem divRemFieldsTwo_size :
    size (fields 2) = 2 := rfl

private theorem divRemFieldsSeven_size :
    size (fields 7) = 7 := rfl

private theorem divRemFieldsThree_size :
    size (fields 3) = 3 := rfl

private theorem divRemField_size :
    size field = 1 := rfl

private theorem divRemAddOperation_size :
    size Extracted.AddOperation = 4 := rfl

private theorem divRemU16MSBOperation_size :
    size Extracted.U16MSBOperation = 1 := rfl

private theorem divRem_toElements_fields {F : Type} {n : ℕ}
    (v : Vector F n) :
    toElements (M := fields n) v = v := rfl

private theorem divRem_toElements_field {F : Type} (x : F) :
    toElements (M := field) x = #v[x] := rfl

private theorem divRem_toElements_addOperation {F : Type}
    (op : Extracted.AddOperation F) :
    toElements op = op.value := rfl

private theorem divRem_toElements_u16MSBOperation {F : Type}
    (op : Extracted.U16MSBOperation F) :
    toElements op = #v[op.msb] := rfl

/-- Copy a shared standalone arithmetic block into the DivRem oracle's chip-private struct copy.
Same field names; definitional field-copy, not an operation-level faithfulness claim. -/
def divRemOracleMulOperation {F : Type} (cols : Extracted.MulOperation F) :
    Extracted.DivRemOracle.MulOperation F :=
  { carry := cols.carry
    product := cols.product
    b_lower_byte := { low_bytes := cols.b_lower_byte.low_bytes }
    c_lower_byte := { low_bytes := cols.c_lower_byte.low_bytes }
    b_msb := cols.b_msb
    c_msb := cols.c_msb
    product_msb := { msb := cols.product_msb.msb }
    b_sign_extend := cols.b_sign_extend
    c_sign_extend := cols.c_sign_extend }

/-- Inverse of `divRemOracleMulOperation`. -/
def divRemNativeMulOperation {F : Type} (cols : Extracted.DivRemOracle.MulOperation F) :
    Extracted.MulOperation F :=
  { carry := cols.carry
    product := cols.product
    b_lower_byte := { low_bytes := cols.b_lower_byte.low_bytes }
    c_lower_byte := { low_bytes := cols.c_lower_byte.low_bytes }
    b_msb := cols.b_msb
    c_msb := cols.c_msb
    product_msb := { msb := cols.product_msb.msb }
    b_sign_extend := cols.b_sign_extend
    c_sign_extend := cols.c_sign_extend }

/-- `Extracted.LtOperationUnsigned` → the DivRem oracle's embedded copy. -/
def divRemOracleLtOperation {F : Type} (cols : Extracted.LtOperationUnsigned F) :
    Extracted.DivRemOracle.LtOperationUnsigned F :=
  { u16_compare_operation := { bit := cols.u16_compare_operation.bit }
    u16_flags := cols.u16_flags
    not_eq_inv := cols.not_eq_inv
    comparison_limbs := cols.comparison_limbs }

/-- Inverse of `divRemOracleLtOperation`. -/
def divRemNativeLtOperation {F : Type} (cols : Extracted.DivRemOracle.LtOperationUnsigned F) :
    Extracted.LtOperationUnsigned F :=
  { u16_compare_operation := { bit := cols.u16_compare_operation.bit }
    u16_flags := cols.u16_flags
    not_eq_inv := cols.not_eq_inv
    comparison_limbs := cols.comparison_limbs }

/-- `Extracted.IsZeroWordOperation` → the DivRem oracle's embedded copy. -/
def divRemOracleIsZeroWord {F : Type} (cols : Extracted.IsZeroWordOperation F) :
    Extracted.DivRemOracle.IsZeroWordOperation F :=
  { is_zero_limb_0 := { inverse := cols.is_zero_limb_0.inverse, result := cols.is_zero_limb_0.result }
    is_zero_limb_1 := { inverse := cols.is_zero_limb_1.inverse, result := cols.is_zero_limb_1.result }
    is_zero_limb_2 := { inverse := cols.is_zero_limb_2.inverse, result := cols.is_zero_limb_2.result }
    is_zero_limb_3 := { inverse := cols.is_zero_limb_3.inverse, result := cols.is_zero_limb_3.result }
    is_zero_first_half := cols.is_zero_first_half
    is_zero_second_half := cols.is_zero_second_half
    result := cols.result }

/-- Inverse of `divRemOracleIsZeroWord`. -/
def divRemNativeIsZeroWord {F : Type} (cols : Extracted.DivRemOracle.IsZeroWordOperation F) :
    Extracted.IsZeroWordOperation F :=
  { is_zero_limb_0 := { inverse := cols.is_zero_limb_0.inverse, result := cols.is_zero_limb_0.result }
    is_zero_limb_1 := { inverse := cols.is_zero_limb_1.inverse, result := cols.is_zero_limb_1.result }
    is_zero_limb_2 := { inverse := cols.is_zero_limb_2.inverse, result := cols.is_zero_limb_2.result }
    is_zero_limb_3 := { inverse := cols.is_zero_limb_3.inverse, result := cols.is_zero_limb_3.result }
    is_zero_first_half := cols.is_zero_first_half
    is_zero_second_half := cols.is_zero_second_half
    result := cols.result }

/-- `Extracted.IsEqualWordOperation` → the DivRem oracle's embedded copy. -/
def divRemOracleIsEqualWord {F : Type} (cols : Extracted.IsEqualWordOperation F) :
    Extracted.DivRemOracle.IsEqualWordOperation F :=
  { is_diff_zero := divRemOracleIsZeroWord cols.is_diff_zero }

/-- Inverse of `divRemOracleIsEqualWord`. -/
def divRemNativeIsEqualWord {F : Type} (cols : Extracted.DivRemOracle.IsEqualWordOperation F) :
    Extracted.IsEqualWordOperation F :=
  { is_diff_zero := divRemNativeIsZeroWord cols.is_diff_zero }

/-- Whole-chip row reconfiguration. The reader blocks and the scalar/word columns are already the
canonical generated substrate; each nested arithmetic block is copied into Rust's chip-private
struct copies. This is not an operation-level faithfulness claim. -/
def divRemChipReconfigure {F : Type} (cols : DivRemChip.Columns F) :
    Extracted.DivRemOracle.DivRemCols F :=
  { state := cols.state
    adapter := cols.adapter
    a := cols.a
    b := cols.b
    c := cols.c
    quotient := cols.quotient
    quotient_comp := cols.quotient_comp
    remainder_comp := cols.remainder_comp
    remainder := cols.remainder
    abs_remainder := cols.abs_remainder
    abs_c := cols.abs_c
    max_abs_c_or_1 := cols.max_abs_c_or_1
    c_times_quotient := cols.c_times_quotient
    c_times_quotient_lower := divRemOracleMulOperation cols.c_times_quotient_lower
    c_times_quotient_upper := divRemOracleMulOperation cols.c_times_quotient_upper
    c_neg_operation := { value := cols.c_neg_operation.value }
    rem_neg_operation := { value := cols.rem_neg_operation.value }
    remainder_lt_operation := divRemOracleLtOperation cols.remainder_lt_operation
    carry := cols.carry
    is_c_0 := divRemOracleIsZeroWord cols.is_c_0
    is_div := cols.is_div
    is_divu := cols.is_divu
    is_rem := cols.is_rem
    is_remu := cols.is_remu
    is_divw := cols.is_divw
    is_remw := cols.is_remw
    is_divuw := cols.is_divuw
    is_remuw := cols.is_remuw
    is_overflow := cols.is_overflow
    is_overflow_b := divRemOracleIsEqualWord cols.is_overflow_b
    is_overflow_c := divRemOracleIsEqualWord cols.is_overflow_c
    b_msb := { msb := cols.b_msb.msb }
    rem_msb := { msb := cols.rem_msb.msb }
    c_msb := { msb := cols.c_msb.msb }
    quot_msb := { msb := cols.quot_msb.msb }
    b_neg := cols.b_neg
    b_neg_not_overflow := cols.b_neg_not_overflow
    b_not_neg_not_overflow := cols.b_not_neg_not_overflow
    is_real_not_word := cols.is_real_not_word
    rem_neg := cols.rem_neg
    c_neg := cols.c_neg
    abs_c_alu_event := cols.abs_c_alu_event
    abs_rem_alu_event := cols.abs_rem_alu_event
    is_real := cols.is_real
    remainder_check_multiplicity := cols.remainder_check_multiplicity }

/-- Inverse whole-row map used to reconstruct the native proof row from an arbitrary Rust row. -/
def divRemChipDeconfigure {F : Type} (cols : Extracted.DivRemOracle.DivRemCols F) :
    DivRemChip.Columns F :=
  { state := cols.state
    adapter := cols.adapter
    a := cols.a
    b := cols.b
    c := cols.c
    quotient := cols.quotient
    quotient_comp := cols.quotient_comp
    remainder_comp := cols.remainder_comp
    remainder := cols.remainder
    abs_remainder := cols.abs_remainder
    abs_c := cols.abs_c
    max_abs_c_or_1 := cols.max_abs_c_or_1
    c_times_quotient := cols.c_times_quotient
    c_times_quotient_lower := divRemNativeMulOperation cols.c_times_quotient_lower
    c_times_quotient_upper := divRemNativeMulOperation cols.c_times_quotient_upper
    c_neg_operation := { value := cols.c_neg_operation.value }
    rem_neg_operation := { value := cols.rem_neg_operation.value }
    remainder_lt_operation := divRemNativeLtOperation cols.remainder_lt_operation
    carry := cols.carry
    is_c_0 := divRemNativeIsZeroWord cols.is_c_0
    is_div := cols.is_div
    is_divu := cols.is_divu
    is_rem := cols.is_rem
    is_remu := cols.is_remu
    is_divw := cols.is_divw
    is_remw := cols.is_remw
    is_divuw := cols.is_divuw
    is_remuw := cols.is_remuw
    is_overflow := cols.is_overflow
    is_overflow_b := divRemNativeIsEqualWord cols.is_overflow_b
    is_overflow_c := divRemNativeIsEqualWord cols.is_overflow_c
    b_msb := { msb := cols.b_msb.msb }
    rem_msb := { msb := cols.rem_msb.msb }
    c_msb := { msb := cols.c_msb.msb }
    quot_msb := { msb := cols.quot_msb.msb }
    b_neg := cols.b_neg
    b_neg_not_overflow := cols.b_neg_not_overflow
    b_not_neg_not_overflow := cols.b_not_neg_not_overflow
    is_real_not_word := cols.is_real_not_word
    rem_neg := cols.rem_neg
    c_neg := cols.c_neg
    abs_c_alu_event := cols.abs_c_alu_event
    abs_rem_alu_event := cols.abs_rem_alu_event
    is_real := cols.is_real
    remainder_check_multiplicity := cols.remainder_check_multiplicity }

/-- SP1 Rust's complete DivRem-chip oracle, viewed from the native Lean row. -/
def divRemChipOracle {F : Type} [FiniteField F] [CoeHead F ℕ] :
    ChipOracle F DivRemChip.Columns Extracted.DivRemOracle.DivRemCols where
  reconfigure := divRemChipReconfigure
  deconfigure := divRemChipDeconfigure
  reconfigure_deconfigure := by intro cols; cases cols; rfl
  deconfigure_reconfigure := by intro cols; cases cols; rfl
  assertZeros := Extracted.DivRemOracle.DivRemCols.asserts
  interactions := Extracted.DivRemOracle.DivRemCols.interactions

def divRemChipInput {F : Type}
    (cols : DivRemChip.Columns F) : DivRemChip.Inputs F :=
  { is_real := cols.is_real
    state := cols.state
    adapter := cols.adapter }

/-- Selector, operand, and multiplication witness prefix (native local offsets `0..113`). -/
def divRemHeaderLocals {F : Type}
    (cols : DivRemChip.Columns F) : Vector F 114 :=
  Vector.cast (by rfl)
    (#v[cols.is_div, cols.is_divu, cols.is_rem, cols.is_remu,
        cols.is_divw, cols.is_remw, cols.is_divuw, cols.is_remuw] ++
      cols.quotient_comp ++ cols.a ++ cols.b ++ cols.c ++
      toElements cols.c_times_quotient_lower ++
      toElements cols.c_times_quotient_upper)

/-- Sign, product, and zero/equality witness block (native local offsets `114..169`). -/
def divRemComparisonLocals {F : Type}
    (cols : DivRemChip.Columns F) : Vector F 56 :=
  Vector.cast (by rfl)
    (
      #v[cols.is_overflow, cols.b_neg, cols.b_neg_not_overflow,
        cols.b_not_neg_not_overflow, cols.is_real_not_word,
        cols.rem_neg, cols.c_neg] ++
      cols.c_times_quotient ++ cols.carry ++
      toElements cols.is_overflow_b ++
      toElements cols.is_overflow_c ++
      toElements cols.is_c_0)

/-- Arithmetic/comparison tail (native local offsets `170..204`). -/
def divRemArithmeticLocals {F : Type}
    (cols : DivRemChip.Columns F) : Vector F 35 :=
  Vector.cast (by rfl)
    (
      cols.abs_c ++ cols.abs_remainder ++ cols.remainder_comp ++
      cols.max_abs_c_or_1 ++ cols.c_neg_operation.value ++
      cols.rem_neg_operation.value ++
      #v[cols.abs_c_alu_event, cols.abs_rem_alu_event,
        cols.remainder_check_multiplicity] ++
      cols.remainder_lt_operation.comparison_limbs ++
      cols.remainder_lt_operation.u16_flags ++
      #v[cols.remainder_lt_operation.not_eq_inv,
        cols.remainder_lt_operation.u16_compare_operation.bit])

/-- Result words and sign bits (native local offsets `205..216`). -/
def divRemResultLocals {F : Type}
    (cols : DivRemChip.Columns F) : Vector F 12 :=
  Vector.cast (by rfl)
    (cols.remainder ++ cols.quotient ++
      #v[cols.b_msb.msb, cols.c_msb.msb,
        cols.rem_msb.msb, cols.quot_msb.msb])

/-- The 217 local cells in the exact order witnessed by `DivRemChip.populateRow`.

This is deliberately written from Rust row fields rather than by evaluating the native witness
generator.  It therefore works for every adversarial row and exposes the complete layout at the
whole-chip boundary.  The four opaque chunks keep projection proofs below Clean's kernel-size
cliff without changing a single physical cell. -/
def divRemChipLocals {F : Type}
    (cols : DivRemChip.Columns F) : Vector F 217 :=
  Vector.cast (by rfl)
    (divRemHeaderLocals cols ++ divRemComparisonLocals cols ++
      divRemArithmeticLocals cols ++ divRemResultLocals cols)

def divRemChipPhysicalRow {F : Type}
    (cols : DivRemChip.Columns F) : Array F :=
  inputFirstRow (divRemChipInput cols) (divRemChipLocals cols)

/-- Decode one typed block from the native local-witness suffix. -/
def divRemLocalBlock {F : Type} (M : TypeMap) [ProvableType M]
    (locals : Vector F 217) (offset : ℕ)
    (hbound : offset + size M ≤ 217) : M F :=
  fromElements (Vector.ofFn fun i =>
    locals[offset + i.val]'(by omega))

/-- The row returned by the native circuit, reconstructed from an arbitrary local suffix. -/
def divRemColumnsOfInput {F : Type}
    (input : DivRemChip.Inputs F) (locals : Vector F 217) :
    DivRemChip.Columns F :=
  let flags := divRemLocalBlock (fields 8) locals 0 (by decide)
  let scalars := divRemLocalBlock (fields 7) locals 114 (by decide)
  let misc := divRemLocalBlock (fields 3) locals 194 (by decide)
  { state := input.state
    adapter := input.adapter
    a := divRemLocalBlock Word locals 12 (by decide)
    b := divRemLocalBlock Word locals 16 (by decide)
    c := divRemLocalBlock Word locals 20 (by decide)
    quotient := divRemLocalBlock Word locals 209 (by decide)
    quotient_comp := divRemLocalBlock Word locals 8 (by decide)
    remainder_comp := divRemLocalBlock Word locals 178 (by decide)
    remainder := divRemLocalBlock Word locals 205 (by decide)
    abs_remainder := divRemLocalBlock Word locals 174 (by decide)
    abs_c := divRemLocalBlock Word locals 170 (by decide)
    max_abs_c_or_1 := divRemLocalBlock Word locals 182 (by decide)
    c_times_quotient :=
      divRemLocalBlock (fields 8) locals 121 (by decide)
    c_times_quotient_lower :=
      divRemLocalBlock Extracted.MulOperation locals 24 (by decide)
    c_times_quotient_upper :=
      divRemLocalBlock Extracted.MulOperation locals 69 (by decide)
    c_neg_operation :=
      divRemLocalBlock Extracted.AddOperation locals 186 (by decide)
    rem_neg_operation :=
      divRemLocalBlock Extracted.AddOperation locals 190 (by decide)
    remainder_lt_operation :=
      { u16_compare_operation :=
          ⟨divRemLocalBlock field locals 204 (by decide)⟩
        u16_flags := divRemLocalBlock (fields 4) locals 199 (by decide)
        not_eq_inv := divRemLocalBlock field locals 203 (by decide)
        comparison_limbs :=
          divRemLocalBlock (fields 2) locals 197 (by decide) }
    carry := divRemLocalBlock (fields 8) locals 129 (by decide)
    is_c_0 :=
      divRemLocalBlock Extracted.IsZeroWordOperation locals 159 (by decide)
    is_div := flags[0]
    is_divu := flags[1]
    is_rem := flags[2]
    is_remu := flags[3]
    is_divw := flags[4]
    is_remw := flags[5]
    is_divuw := flags[6]
    is_remuw := flags[7]
    is_overflow := scalars[0]
    is_overflow_b :=
      divRemLocalBlock Extracted.IsEqualWordOperation locals 137 (by decide)
    is_overflow_c :=
      divRemLocalBlock Extracted.IsEqualWordOperation locals 148 (by decide)
    b_msb :=
      divRemLocalBlock Extracted.U16MSBOperation locals 213 (by decide)
    rem_msb :=
      divRemLocalBlock Extracted.U16MSBOperation locals 215 (by decide)
    c_msb :=
      divRemLocalBlock Extracted.U16MSBOperation locals 214 (by decide)
    quot_msb :=
      divRemLocalBlock Extracted.U16MSBOperation locals 216 (by decide)
    b_neg := scalars[1]
    b_neg_not_overflow := scalars[2]
    b_not_neg_not_overflow := scalars[3]
    is_real_not_word := scalars[4]
    rem_neg := scalars[5]
    c_neg := scalars[6]
    abs_c_alu_event := misc[0]
    abs_rem_alu_event := misc[1]
    is_real := input.is_real
    remainder_check_multiplicity := misc[2] }

private theorem divRemLocalBlock_eq_of_get {F : Type}
    (M : TypeMap) [ProvableType M] (locals : Vector F 217)
    (offset : ℕ) (hbound : offset + size M ≤ 217) (value : M F)
    (hget : ∀ i (hi : i < size M),
      locals[offset + i] = (toElements value)[i]) :
    divRemLocalBlock M locals offset hbound = value := by
  unfold divRemLocalBlock
  rw [ProvableType.fromElements_eq_iff]
  ext i hi
  rw [Vector.getElem_ofFn]
  exact hget i hi

/-- `Vector` index congruence over opaque arguments. The block round-trips end on goals of the
shape `v[bigOffsetArithmetic] = v[i]`; discharging those with `congr` makes the elaborator descend
structurally through the index arithmetic, which is what drove this file's recursion budget. -/
private theorem vector_getElem_congr_idx {α : Type} {n : ℕ} (v : Vector α n)
    {a b : ℕ} (ha : a < n) (hb : b < n) (h : a = b) : v[a] = v[b] := by
  subst h; rfl

set_option linter.unusedSimpArgs false in
private theorem divRemHeaderBlocks_roundtrip {F : Type}
    (cols : DivRemChip.Columns F) :
    divRemLocalBlock (fields 8) (divRemChipLocals cols) 0 (by decide) =
        #v[cols.is_div, cols.is_divu, cols.is_rem, cols.is_remu,
          cols.is_divw, cols.is_remw, cols.is_divuw, cols.is_remuw] ∧
      divRemLocalBlock Word (divRemChipLocals cols) 8 (by decide) =
        cols.quotient_comp ∧
      divRemLocalBlock Word (divRemChipLocals cols) 12 (by decide) =
        cols.a ∧
      divRemLocalBlock Word (divRemChipLocals cols) 16 (by decide) =
        cols.b ∧
      divRemLocalBlock Word (divRemChipLocals cols) 20 (by decide) =
        cols.c ∧
      divRemLocalBlock Extracted.MulOperation
          (divRemChipLocals cols) 24 (by decide) =
        cols.c_times_quotient_lower ∧
      divRemLocalBlock Extracted.MulOperation
          (divRemChipLocals cols) 69 (by decide) =
        cols.c_times_quotient_upper := by
  repeat' apply And.intro
  all_goals
    apply divRemLocalBlock_eq_of_get
    intro i hi
    simp only [divRemChipLocals, divRemHeaderLocals,
      Vector.getElem_cast]
    have hMul := divRemMulOperation_size
    have hEq := divRemIsEqualWordOperation_size
    have hZero := divRemIsZeroWordOperation_size
    have hWord := divRemWord_size
    have hEight := divRemFieldsEight_size
    have hFour := divRemFieldsFour_size
    have hTwo := divRemFieldsTwo_size
    have hSeven := divRemFieldsSeven_size
    have hThree := divRemFieldsThree_size
    have hField := divRemField_size
    have hAdd := divRemAddOperation_size
    have hMsb := divRemU16MSBOperation_size
    repeat
      first
      | (rw [Vector.getElem_append_left (by omega)] <;>
          try simp only [Vector.getElem_cast])
      | (rw [Vector.getElem_append_right (by omega) (by omega)] <;>
          try simp only [Vector.getElem_cast])
  all_goals try rw [divRem_toElements_fields]
  all_goals exact vector_getElem_congr_idx _ _ _ (by omega)

set_option linter.unusedSimpArgs false in
private theorem divRemComparisonBlocks_roundtrip {F : Type}
    (cols : DivRemChip.Columns F) :
    divRemLocalBlock (fields 7) (divRemChipLocals cols) 114 (by decide) =
        #v[cols.is_overflow, cols.b_neg, cols.b_neg_not_overflow,
          cols.b_not_neg_not_overflow, cols.is_real_not_word,
          cols.rem_neg, cols.c_neg] ∧
      divRemLocalBlock (fields 8) (divRemChipLocals cols) 121 (by decide) =
        cols.c_times_quotient ∧
      divRemLocalBlock (fields 8) (divRemChipLocals cols) 129 (by decide) =
        cols.carry ∧
      divRemLocalBlock Extracted.IsEqualWordOperation
          (divRemChipLocals cols) 137 (by decide) =
        cols.is_overflow_b ∧
      divRemLocalBlock Extracted.IsEqualWordOperation
          (divRemChipLocals cols) 148 (by decide) =
        cols.is_overflow_c ∧
      divRemLocalBlock Extracted.IsZeroWordOperation
          (divRemChipLocals cols) 159 (by decide) =
        cols.is_c_0 := by
  repeat' apply And.intro
  all_goals
    apply divRemLocalBlock_eq_of_get
    intro i hi
    simp only [divRemChipLocals, divRemComparisonLocals,
      Vector.getElem_cast]
    have hMul := divRemMulOperation_size
    have hEq := divRemIsEqualWordOperation_size
    have hZero := divRemIsZeroWordOperation_size
    have hWord := divRemWord_size
    have hEight := divRemFieldsEight_size
    have hFour := divRemFieldsFour_size
    have hTwo := divRemFieldsTwo_size
    have hSeven := divRemFieldsSeven_size
    have hThree := divRemFieldsThree_size
    have hField := divRemField_size
    have hAdd := divRemAddOperation_size
    have hMsb := divRemU16MSBOperation_size
    repeat
      first
      | (rw [Vector.getElem_append_left (by omega)] <;>
          try simp only [Vector.getElem_cast])
      | (rw [Vector.getElem_append_right (by omega) (by omega)] <;>
          try simp only [Vector.getElem_cast])
  all_goals try rw [divRem_toElements_fields]
  all_goals exact vector_getElem_congr_idx _ _ _ (by omega)

set_option linter.unusedSimpArgs false in
private theorem divRemArithmeticBlocks_roundtrip {F : Type}
    (cols : DivRemChip.Columns F) :
    divRemLocalBlock Word (divRemChipLocals cols) 170 (by decide) =
        cols.abs_c ∧
      divRemLocalBlock Word (divRemChipLocals cols) 174 (by decide) =
        cols.abs_remainder ∧
      divRemLocalBlock Word (divRemChipLocals cols) 178 (by decide) =
        cols.remainder_comp ∧
      divRemLocalBlock Word (divRemChipLocals cols) 182 (by decide) =
        cols.max_abs_c_or_1 ∧
      divRemLocalBlock Extracted.AddOperation
          (divRemChipLocals cols) 186 (by decide) =
        cols.c_neg_operation ∧
      divRemLocalBlock Extracted.AddOperation
          (divRemChipLocals cols) 190 (by decide) =
        cols.rem_neg_operation ∧
      divRemLocalBlock (fields 3) (divRemChipLocals cols) 194 (by decide) =
        #v[cols.abs_c_alu_event, cols.abs_rem_alu_event,
          cols.remainder_check_multiplicity] ∧
      divRemLocalBlock (fields 2) (divRemChipLocals cols) 197 (by decide) =
        cols.remainder_lt_operation.comparison_limbs ∧
      divRemLocalBlock (fields 4) (divRemChipLocals cols) 199 (by decide) =
        cols.remainder_lt_operation.u16_flags ∧
      divRemLocalBlock field (divRemChipLocals cols) 203 (by decide) =
        cols.remainder_lt_operation.not_eq_inv ∧
      divRemLocalBlock field (divRemChipLocals cols) 204 (by decide) =
        cols.remainder_lt_operation.u16_compare_operation.bit := by
  repeat' apply And.intro
  all_goals
    apply divRemLocalBlock_eq_of_get
    intro i hi
    simp only [divRemChipLocals, divRemArithmeticLocals,
      Vector.getElem_cast]
    have hMul := divRemMulOperation_size
    have hEq := divRemIsEqualWordOperation_size
    have hZero := divRemIsZeroWordOperation_size
    have hWord := divRemWord_size
    have hEight := divRemFieldsEight_size
    have hFour := divRemFieldsFour_size
    have hTwo := divRemFieldsTwo_size
    have hSeven := divRemFieldsSeven_size
    have hThree := divRemFieldsThree_size
    have hField := divRemField_size
    have hAdd := divRemAddOperation_size
    have hMsb := divRemU16MSBOperation_size
    repeat
      first
      | (rw [Vector.getElem_append_left (by omega)] <;>
          try simp only [Vector.getElem_cast])
      | (rw [Vector.getElem_append_right (by omega) (by omega)] <;>
          try simp only [Vector.getElem_cast])
  all_goals try rw [divRem_toElements_fields]
  all_goals try rw [divRem_toElements_field]
  all_goals try rw [divRem_toElements_addOperation]
  all_goals try
    (have hi_zero : i = 0 := by omega
     subst i
     rfl)
  all_goals exact vector_getElem_congr_idx _ _ _ (by omega)

set_option linter.unusedSimpArgs false in
private theorem divRemResultBlocks_roundtrip {F : Type}
    (cols : DivRemChip.Columns F) :
    divRemLocalBlock Word (divRemChipLocals cols) 205 (by decide) =
        cols.remainder ∧
      divRemLocalBlock Word (divRemChipLocals cols) 209 (by decide) =
        cols.quotient ∧
      divRemLocalBlock Extracted.U16MSBOperation
          (divRemChipLocals cols) 213 (by decide) =
        cols.b_msb ∧
      divRemLocalBlock Extracted.U16MSBOperation
          (divRemChipLocals cols) 214 (by decide) =
        cols.c_msb ∧
      divRemLocalBlock Extracted.U16MSBOperation
          (divRemChipLocals cols) 215 (by decide) =
        cols.rem_msb ∧
      divRemLocalBlock Extracted.U16MSBOperation
          (divRemChipLocals cols) 216 (by decide) =
        cols.quot_msb := by
  repeat' apply And.intro
  all_goals
    apply divRemLocalBlock_eq_of_get
    intro i hi
    simp only [divRemChipLocals, divRemResultLocals,
      Vector.getElem_cast]
    have hMul := divRemMulOperation_size
    have hEq := divRemIsEqualWordOperation_size
    have hZero := divRemIsZeroWordOperation_size
    have hWord := divRemWord_size
    have hEight := divRemFieldsEight_size
    have hFour := divRemFieldsFour_size
    have hTwo := divRemFieldsTwo_size
    have hSeven := divRemFieldsSeven_size
    have hThree := divRemFieldsThree_size
    have hField := divRemField_size
    have hAdd := divRemAddOperation_size
    have hMsb := divRemU16MSBOperation_size
    repeat
      first
      | (rw [Vector.getElem_append_left (by omega)] <;>
          try simp only [Vector.getElem_cast])
      | (rw [Vector.getElem_append_right (by omega) (by omega)] <;>
          try simp only [Vector.getElem_cast])
  all_goals try rw [divRem_toElements_fields]
  all_goals try rw [divRem_toElements_u16MSBOperation]
  all_goals try
    (have hi_zero : i = 0 := by omega
     subst i
     rfl)
  all_goals exact vector_getElem_congr_idx _ _ _ (by omega)

private theorem divRemColumnsOfInput_roundtrip {F : Type}
    (cols : DivRemChip.Columns F) :
    divRemColumnsOfInput (divRemChipInput cols) (divRemChipLocals cols) =
      cols := by
  obtain ⟨hflags, hqc, ha, hb, hc, hlo, hup⟩ :=
    divRemHeaderBlocks_roundtrip cols
  obtain ⟨hscalars, hctq, hcarry, hovb, hovc, hisc0⟩ :=
    divRemComparisonBlocks_roundtrip cols
  obtain ⟨habsc, habsr, hremc, hmax, hcneg, hrneg, hmisc,
    hltc, hltf, hltinv, hltbit⟩ :=
    divRemArithmeticBlocks_roundtrip cols
  obtain ⟨hrem, hquot, hbmsb, hcmsb, hrmsb, hqmsb⟩ :=
    divRemResultBlocks_roundtrip cols
  unfold divRemColumnsOfInput divRemChipInput
  rw [hflags, hqc, ha, hb, hc, hlo, hup, hscalars, hctq,
    hcarry, hovb, hovc, hisc0, habsc, habsr, hremc, hmax,
    hcneg, hrneg, hmisc, hltc, hltf, hltinv, hltbit,
    hrem, hquot, hbmsb, hcmsb, hrmsb, hqmsb]
  rw [DivRemChip.Columns.mk.injEq]
  simp

omit [Fact (2 ^ 24 < p)] in
private theorem eval_divRemLocalBlock
    (input : DivRemChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 217) (data : ProverData (ZMod p))
    (M : TypeMap) [ProvableType M] (offset : ℕ)
    (hbound : offset + size M ≤ 217) :
    Eval.eval
        (Environment.fromArray (inputFirstRow input locals) data)
        (varFromOffset M (size DivRemChip.Inputs + offset) :
          M (Expression (ZMod p))) =
      divRemLocalBlock M locals offset hbound := by
  rw [ProvableType.eval_varFromOffset, ProvableType.fromElements_eq_iff]
  ext i hi
  rw [Vector.getElem_mapRange]
  unfold divRemLocalBlock
  rw [ProvableType.toElements_fromElements, Vector.getElem_ofFn]
  have hlocal := eval_local_inputFirstRow input locals data
    (offset + i) (by omega)
  simp only [Expression.eval] at hlocal
  simpa only [Nat.add_assoc] using hlocal

private theorem eval_divRemIsC0OfLocals
    (input : DivRemChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 217) (data : ProverData (ZMod p))
    (hbound : 159 + size Extracted.IsZeroWordOperation ≤ 217) :
    Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (DivRemChip.populatedRowAt
          (varFromOffset (F := ZMod p) DivRemChip.Inputs 0)
          (size DivRemChip.Inputs)).is_c_0 =
      divRemLocalBlock Extracted.IsZeroWordOperation locals 159 hbound := by
  rw [DivRemChip.populatedRowAt_isC0_eq,
    ProvableType.eval_fromElements]
  unfold divRemLocalBlock
  apply congrArg ProvableType.fromElements
  change
    Vector.map
        (Expression.eval
          (Environment.fromArray (inputFirstRow input locals) data))
        (Vector.mapRange 11 fun i =>
          var { index := size DivRemChip.Inputs + 8 + 4 + 4 + 4 + 4 +
            45 + 45 + 7 + 8 + 8 + 11 + 11 + i }) =
      Vector.ofFn (fun i : Fin 11 =>
        locals[159 + i.val]'(by
          have hsize := divRemIsZeroWordOperation_size
          omega))
  ext i hi
  rw [Vector.getElem_map, Vector.getElem_mapRange, Vector.getElem_ofFn]
  have hlocal := eval_local_inputFirstRow input locals data (159 + i) (by
    have hsize := divRemIsZeroWordOperation_size
    omega)
  have hindex :
      size DivRemChip.Inputs + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 +
          8 + 8 + 11 + 11 + i =
        size DivRemChip.Inputs + (159 + i) := by omega
  rw [hindex]
  exact hlocal

private theorem eval_divRemIsOverflowBOfLocals
    (input : DivRemChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 217) (data : ProverData (ZMod p))
    (hbound : 137 + size Extracted.IsEqualWordOperation ≤ 217) :
    Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (DivRemChip.populatedRowAt
          (varFromOffset (F := ZMod p) DivRemChip.Inputs 0)
          (size DivRemChip.Inputs)).is_overflow_b =
      divRemLocalBlock Extracted.IsEqualWordOperation locals 137 hbound := by
  rw [DivRemChip.populatedRowAt_isOverflowB_eq,
    ProvableType.eval_fromElements]
  unfold divRemLocalBlock
  apply congrArg ProvableType.fromElements
  change
    Vector.map
        (Expression.eval
          (Environment.fromArray (inputFirstRow input locals) data))
        (Vector.mapRange 11 fun i =>
          var { index := size DivRemChip.Inputs + 8 + 4 + 4 + 4 + 4 +
            45 + 45 + 7 + 8 + 8 + i }) =
      Vector.ofFn (fun i : Fin 11 =>
        locals[137 + i.val]'(by
          have hsize := divRemIsEqualWordOperation_size
          omega))
  ext i hi
  rw [Vector.getElem_map, Vector.getElem_mapRange, Vector.getElem_ofFn]
  have hlocal := eval_local_inputFirstRow input locals data (137 + i) (by
    have hsize := divRemIsEqualWordOperation_size
    omega)
  have hindex :
      size DivRemChip.Inputs + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 +
          8 + 8 + i =
        size DivRemChip.Inputs + (137 + i) := by omega
  rw [hindex]
  exact hlocal

private theorem eval_divRemIsOverflowCOfLocals
    (input : DivRemChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 217) (data : ProverData (ZMod p))
    (hbound : 148 + size Extracted.IsEqualWordOperation ≤ 217) :
    Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (DivRemChip.populatedRowAt
          (varFromOffset (F := ZMod p) DivRemChip.Inputs 0)
          (size DivRemChip.Inputs)).is_overflow_c =
      divRemLocalBlock Extracted.IsEqualWordOperation locals 148 hbound := by
  rw [DivRemChip.populatedRowAt_isOverflowC_eq,
    ProvableType.eval_fromElements]
  unfold divRemLocalBlock
  apply congrArg ProvableType.fromElements
  change
    Vector.map
        (Expression.eval
          (Environment.fromArray (inputFirstRow input locals) data))
        (Vector.mapRange 11 fun i =>
          var { index := size DivRemChip.Inputs + 8 + 4 + 4 + 4 + 4 +
            45 + 45 + 7 + 8 + 8 + 11 + i }) =
      Vector.ofFn (fun i : Fin 11 =>
        locals[148 + i.val]'(by
          have hsize := divRemIsEqualWordOperation_size
          omega))
  ext i hi
  rw [Vector.getElem_map, Vector.getElem_mapRange, Vector.getElem_ofFn]
  have hlocal := eval_local_inputFirstRow input locals data (148 + i) (by
    have hsize := divRemIsEqualWordOperation_size
    omega)
  have hindex :
      size DivRemChip.Inputs + 8 + 4 + 4 + 4 + 4 + 45 + 45 + 7 +
          8 + 8 + 11 + i =
        size DivRemChip.Inputs + (148 + i) := by omega
  rw [hindex]
  exact hlocal

omit [Fact (2 ^ 24 < p)] in
private theorem eval_divRemLocalFieldsGet
    (input : DivRemChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 217) (data : ProverData (ZMod p))
    (n offset i : ℕ) (hbound : offset + n ≤ 217) (hi : i < n) :
    Expression.eval
        (Environment.fromArray (inputFirstRow input locals) data)
        (var { index := size DivRemChip.Inputs + offset + i }) =
      (divRemLocalBlock (fields n) locals offset hbound)[i] := by
  have h := congrArg (fun value => value[i])
    (eval_divRemLocalBlock input locals data (fields n) offset hbound)
  rw [← ProvableType.getElem_eval_fields,
    ProvableType.varFromOffset_fields, Vector.getElem_mapRange] at h
  simpa only [Nat.add_assoc] using h

private theorem eval_divRemLtUnsigned {F : Type} [FiniteField F]
    (env : Environment F)
    (cols : Extracted.LtOperationUnsigned (Expression F)) :
    Eval.eval env cols =
      ({ u16_compare_operation := Eval.eval env cols.u16_compare_operation
         u16_flags := Eval.eval env cols.u16_flags
         not_eq_inv := Eval.eval env cols.not_eq_inv
         comparison_limbs := Eval.eval env cols.comparison_limbs } :
        Extracted.LtOperationUnsigned F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

private theorem eval_divRemU16Compare {F : Type} [FiniteField F]
    (env : Environment F)
    (cols : Extracted.U16CompareOperation (Expression F)) :
    Eval.eval env cols =
      ({ bit := Eval.eval env cols.bit } :
        Extracted.U16CompareOperation F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

private theorem eval_divRemLtOfLocals
    (input : DivRemChip.Inputs (ZMod p))
    (locals : Vector (ZMod p) 217) (data : ProverData (ZMod p)) :
    Eval.eval (Environment.fromArray (inputFirstRow input locals) data)
        (DivRemChip.populatedRowAt
          (varFromOffset (F := ZMod p) DivRemChip.Inputs 0)
          (size DivRemChip.Inputs)).remainder_lt_operation =
      ({ u16_compare_operation :=
           ⟨divRemLocalBlock field locals 204 (by decide)⟩
         u16_flags := divRemLocalBlock (fields 4) locals 199 (by decide)
         not_eq_inv := divRemLocalBlock field locals 203 (by decide)
         comparison_limbs :=
           divRemLocalBlock (fields 2) locals 197 (by decide) } :
        Extracted.LtOperationUnsigned (ZMod p)) := by
  rw [eval_divRemLtUnsigned,
    Extracted.LtOperationUnsigned.mk.injEq]
  constructor
  · rw [eval_divRemU16Compare,
      Extracted.U16CompareOperation.mk.injEq]
    rw [DivRemChip.populatedRowAt_ltBit_eq]
    exact eval_divRemLocalBlock input locals data field 204 (by decide)
  constructor
  · rw [DivRemChip.populatedRowAt_ltU16Flags_eq]
    exact eval_divRemLocalBlock input locals data (fields 4) 199 (by decide)
  constructor
  · rw [DivRemChip.populatedRowAt_ltNotEqInv_eq]
    exact eval_divRemLocalBlock input locals data field 203 (by decide)
  · rw [DivRemChip.populatedRowAt_ltComparisonLimbs_eq]
    exact eval_divRemLocalBlock input locals data (fields 2) 197 (by decide)

theorem eval_divRemChipDirectOutput
    (cols : DivRemChip.Columns (ZMod p))
    (data : ProverData (ZMod p)) :
    ProvableType.eval
        (Environment.fromArray (divRemChipPhysicalRow cols) data)
        ((DivRemChip.elaborated (p := p)).output
          (varFromOffset DivRemChip.Inputs 0)
          (size DivRemChip.Inputs)) =
      cols := by
  let input := divRemChipInput cols
  let locals := divRemChipLocals cols
  change ProvableType.eval
      (Environment.fromArray (inputFirstRow input locals) data)
      ((DivRemChip.elaborated (p := p)).output
        (varFromOffset DivRemChip.Inputs 0)
        (size DivRemChip.Inputs)) = cols
  rw [← DivRemChip.elaborated.output_eq,
    DivRemChip.main_output_eq_populateRow,
    DivRemChip.populateRow_output_eq]
  rw [← CircuitType.eval_expression,
    DivRemChip.eval_divRemCols_verifier]
  rw [DivRemChip.Columns.mk.injEq]
  obtain ⟨hflags, hqc, ha, hb, hc, hlo, hup⟩ :=
    divRemHeaderBlocks_roundtrip cols
  obtain ⟨hscalars, hctq, hcarry, hovb, hovc, hisc0⟩ :=
    divRemComparisonBlocks_roundtrip cols
  obtain ⟨habsc, habsr, hremc, hmax, hcneg, hrneg, hmisc,
    hltc, hltf, hltinv, hltbit⟩ :=
    divRemArithmeticBlocks_roundtrip cols
  obtain ⟨hrem, hquot, hbmsb, hcmsb, hrmsb, hqmsb⟩ :=
    divRemResultBlocks_roundtrip cols
  have hinputEval := eval_inputFirstRow input locals data
  rw [DivRemChip.eval_inputs, DivRemChip.Inputs.mk.injEq] at hinputEval
  constructor
  · rw [DivRemChip.populatedRowAt_state_eq]
    simpa only [input, divRemChipInput] using hinputEval.2.1
  constructor
  · rw [DivRemChip.populatedRowAt_adapter_eq]
    simpa only [input, divRemChipInput] using hinputEval.2.2
  constructor
  · rw [DivRemChip.populatedRowAt_a_eq]
    exact (eval_divRemLocalBlock input locals data Word 12 (by decide)).trans ha
  constructor
  · rw [DivRemChip.populatedRowAt_b_eq]
    exact (eval_divRemLocalBlock input locals data Word 16 (by decide)).trans hb
  constructor
  · rw [DivRemChip.populatedRowAt_c_eq]
    exact (eval_divRemLocalBlock input locals data Word 20 (by decide)).trans hc
  constructor
  · rw [DivRemChip.populatedRowAt_quotient_eq]
    exact (eval_divRemLocalBlock input locals data Word 209 (by decide)).trans hquot
  constructor
  · rw [DivRemChip.populatedRowAt_quotientComp_eq]
    exact (eval_divRemLocalBlock input locals data Word 8 (by decide)).trans hqc
  constructor
  · rw [DivRemChip.populatedRowAt_remainderComp_eq]
    exact (eval_divRemLocalBlock input locals data Word 178 (by decide)).trans hremc
  constructor
  · rw [DivRemChip.populatedRowAt_remainder_eq]
    exact (eval_divRemLocalBlock input locals data Word 205 (by decide)).trans hrem
  constructor
  · rw [DivRemChip.populatedRowAt_absRemainder_eq]
    exact (eval_divRemLocalBlock input locals data Word 174 (by decide)).trans habsr
  constructor
  · rw [DivRemChip.populatedRowAt_absC_eq]
    exact (eval_divRemLocalBlock input locals data Word 170 (by decide)).trans habsc
  constructor
  · rw [DivRemChip.populatedRowAt_maxAbsCOr1_eq]
    exact (eval_divRemLocalBlock input locals data Word 182 (by decide)).trans hmax
  constructor
  · rw [DivRemChip.populatedRowAt_ctq_eq]
    exact (eval_divRemLocalBlock input locals data (fields 8) 121 (by decide)).trans hctq
  constructor
  · rw [DivRemChip.populatedRowAt_mulLower_eq]
    exact (eval_divRemLocalBlock input locals data
      Extracted.MulOperation 24 (by decide)).trans hlo
  constructor
  · rw [DivRemChip.populatedRowAt_mulUpper_eq]
    exact (eval_divRemLocalBlock input locals data
      Extracted.MulOperation 69 (by decide)).trans hup
  constructor
  · rw [DivRemChip.populatedRowAt_cNegOperation_eq]
    exact (eval_divRemLocalBlock input locals data
      Extracted.AddOperation 186 (by decide)).trans hcneg
  constructor
  · rw [DivRemChip.populatedRowAt_remNegOperation_eq]
    exact (eval_divRemLocalBlock input locals data
      Extracted.AddOperation 190 (by decide)).trans hrneg
  constructor
  · refine (eval_divRemLtOfLocals input locals data).trans ?_
    rw [Extracted.LtOperationUnsigned.mk.injEq,
      Extracted.U16CompareOperation.mk.injEq]
    exact ⟨hltbit, hltf, hltinv, hltc⟩
  constructor
  · rw [DivRemChip.populatedRowAt_carry_eq]
    exact (eval_divRemLocalBlock input locals data
      (fields 8) 129 (by decide)).trans hcarry
  constructor
  · let h159 : 159 + size Extracted.IsZeroWordOperation ≤ 217 := by decide
    have hisc0' := hisc0
    change divRemLocalBlock Extracted.IsZeroWordOperation
      locals 159 h159 = cols.is_c_0 at hisc0'
    exact (eval_divRemIsC0OfLocals input locals data h159).trans hisc0'
  constructor
  · rw [DivRemChip.populatedRowAt_isDiv_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      8 0 0 (by decide) (by decide)).trans
        (congrArg (fun value => value[0]) hflags)
  constructor
  · rw [DivRemChip.populatedRowAt_isDivu_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      8 0 1 (by decide) (by decide)).trans
        (congrArg (fun value => value[1]) hflags)
  constructor
  · rw [DivRemChip.populatedRowAt_isRem_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      8 0 2 (by decide) (by decide)).trans
        (congrArg (fun value => value[2]) hflags)
  constructor
  · rw [DivRemChip.populatedRowAt_isRemu_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      8 0 3 (by decide) (by decide)).trans
        (congrArg (fun value => value[3]) hflags)
  constructor
  · rw [DivRemChip.populatedRowAt_isDivw_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      8 0 4 (by decide) (by decide)).trans
        (congrArg (fun value => value[4]) hflags)
  constructor
  · rw [DivRemChip.populatedRowAt_isRemw_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      8 0 5 (by decide) (by decide)).trans
        (congrArg (fun value => value[5]) hflags)
  constructor
  · rw [DivRemChip.populatedRowAt_isDivuw_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      8 0 6 (by decide) (by decide)).trans
        (congrArg (fun value => value[6]) hflags)
  constructor
  · rw [DivRemChip.populatedRowAt_isRemuw_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      8 0 7 (by decide) (by decide)).trans
        (congrArg (fun value => value[7]) hflags)
  constructor
  · rw [DivRemChip.populatedRowAt_isOverflow_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      7 114 0 (by decide) (by decide)).trans
        (congrArg (fun value => value[0]) hscalars)
  constructor
  · let h137 : 137 + size Extracted.IsEqualWordOperation ≤ 217 := by decide
    have hovb' := hovb
    change divRemLocalBlock Extracted.IsEqualWordOperation
      locals 137 h137 = cols.is_overflow_b at hovb'
    exact (eval_divRemIsOverflowBOfLocals input locals data h137).trans hovb'
  constructor
  · let h148 : 148 + size Extracted.IsEqualWordOperation ≤ 217 := by decide
    have hovc' := hovc
    change divRemLocalBlock Extracted.IsEqualWordOperation
      locals 148 h148 = cols.is_overflow_c at hovc'
    exact (eval_divRemIsOverflowCOfLocals input locals data h148).trans hovc'
  constructor
  · rw [DivRemChip.populatedRowAt_bMsbOperation_eq]
    exact (eval_divRemLocalBlock input locals data
      Extracted.U16MSBOperation 213 (by decide)).trans hbmsb
  constructor
  · rw [DivRemChip.populatedRowAt_remMsbOperation_eq]
    exact (eval_divRemLocalBlock input locals data
      Extracted.U16MSBOperation 215 (by decide)).trans hrmsb
  constructor
  · rw [DivRemChip.populatedRowAt_cMsbOperation_eq]
    exact (eval_divRemLocalBlock input locals data
      Extracted.U16MSBOperation 214 (by decide)).trans hcmsb
  constructor
  · rw [DivRemChip.populatedRowAt_quotMsbOperation_eq]
    exact (eval_divRemLocalBlock input locals data
      Extracted.U16MSBOperation 216 (by decide)).trans hqmsb
  constructor
  · rw [DivRemChip.populatedRowAt_bNeg_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      7 114 1 (by decide) (by decide)).trans
        (congrArg (fun value => value[1]) hscalars)
  constructor
  · rw [DivRemChip.populatedRowAt_bNegNotOverflow_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      7 114 2 (by decide) (by decide)).trans
        (congrArg (fun value => value[2]) hscalars)
  constructor
  · rw [DivRemChip.populatedRowAt_bNotNegNotOverflow_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      7 114 3 (by decide) (by decide)).trans
        (congrArg (fun value => value[3]) hscalars)
  constructor
  · rw [DivRemChip.populatedRowAt_isRealNotWord_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      7 114 4 (by decide) (by decide)).trans
        (congrArg (fun value => value[4]) hscalars)
  constructor
  · rw [DivRemChip.populatedRowAt_remNeg_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      7 114 5 (by decide) (by decide)).trans
        (congrArg (fun value => value[5]) hscalars)
  constructor
  · rw [DivRemChip.populatedRowAt_cNeg_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      7 114 6 (by decide) (by decide)).trans
        (congrArg (fun value => value[6]) hscalars)
  constructor
  · rw [DivRemChip.populatedRowAt_absCEvent_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      3 194 0 (by decide) (by decide)).trans
        (congrArg (fun value => value[0]) hmisc)
  constructor
  · rw [DivRemChip.populatedRowAt_absRemEvent_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      3 194 1 (by decide) (by decide)).trans
        (congrArg (fun value => value[1]) hmisc)
  constructor
  · rw [DivRemChip.populatedRowAt_isReal_eq]
    simpa only [input, divRemChipInput] using hinputEval.1
  · rw [DivRemChip.populatedRowAt_remainderCheckMultiplicity_eq,
      CircuitType.eval_expr]
    simpa using (eval_divRemLocalFieldsGet input locals data
      3 194 2 (by decide) (by decide)).trans
        (congrArg (fun value => value[2]) hmisc)

def divRemChipRowCodec :
    ChipRowCodec DivRemChip.Inputs DivRemChip.Columns
      (DivRemChip.circuit (p := p)) where
  assignment cols data := {
    row := divRemChipPhysicalRow cols
    input := divRemChipInput cols
    width_eq := by
      rw [divRemChipPhysicalRow, inputFirstRow_size,
        Air.Flat.Component.width, DivRemChip.circuit_size_eq,
        divRemInputs_size]
    rowInput_eq := by
      exact rowInput_inputFirstRow (DivRemChip.circuit (p := p))
        (divRemChipInput cols) (divRemChipLocals cols) data
    rowOutput_eq := by
      change ProvableType.eval _ ((DivRemChip.main _).output _) = _
      rw [DivRemChip.elaborated.output_eq]
      rw [Air.Flat.Component.rowInputVar_mk,
        Air.Flat.Component.rowOffset_mk]
      exact eval_divRemChipDirectOutput (p := p) cols data }

theorem divRemChip_lookups_empty :
    (⟨DivRemChip.circuit (p := p)⟩ :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq,
    Air.Flat.Component.rowOperations_mk,
    DivRemChip.circuit_main_eq]
  simp [DivRemChip.main, DivRemChip.populateRow,
    DivRemChip.constrainRow,
    Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.RTypeReader.circuit, Readers.RTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main,
    DivRemCompare.circuit, DivRemCompare.main,
    DivRemCore.circuit, DivRemCore.main,
    IsEqualWordOperation.circuit, IsEqualWordOperation.main,
    IsZeroWordOperation.circuit, IsZeroWordOperation.main,
    IsZeroOperation.circuit, IsZeroOperation.main,
    AddOperation.circuit, AddOperation.main,
    LtOperationUnsigned.circuit, LtOperationUnsigned.main,
    U16CompareOperation.circuit, U16CompareOperation.main,
    U16MSBOperation.circuit, U16MSBOperation.main,
    MulOperation.circuit, MulOperation.main,
    U16toU8OperationSafe.circuit, U16toU8OperationSafe.main,
    DivRemChip.assertZeros, Gadgets.Equality.main, circuit_norm]

/-- Evaluate the large Rust-shaped own-assert tail without unfolding it at the chip boundary.
`DivRemCore.ownAsserts_map_eval` is the expensive carrier-generic theorem; this wrapper supplies
its projection pins from the standard `ProvableStruct` evaluators once. The exact whole-chip
proof imports this folded boundary instead of re-normalizing all 246 columns. -/
theorem divRemOwnAsserts_eval
    (env : Environment (ZMod p))
    (cols : Var DivRemChip.Columns (ZMod p)) :
    (DivRemChip.ownAsserts cols).map (Expression.eval env) =
      DivRemChip.ownAsserts (Eval.eval env cols) := by
  apply DivRemCore.ownAsserts_map_eval env cols (Eval.eval env cols)
  all_goals rw [DivRemChip.eval_divRemCols_verifier]
  all_goals simp [ProvableType.eval_field,
    ProvableType.eval_fields, eval_rTypeReader,
    eval_registerAccessCols, eval_u16MSBColumns,
    eval_isEqualWordColumns, eval_isZeroWordColumns,
    eval_extractedAddColumns, eval_ltUnsignedColumns,
    eval_u16CompareColumns]

end SP1Clean.Faithful
