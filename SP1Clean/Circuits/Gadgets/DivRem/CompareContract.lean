module

public import SP1Clean.Semantics.Specs.DivRem
public import SP1Clean.FormalModel.Contracts.Operations
public import SP1Clean.Semantics.Specs.IsEqualWord
public import SP1Clean.Semantics.Specs.IsZeroWord
public import SP1Clean.Semantics.Specs.LtUnsigned
public import SP1Clean.Semantics.Specs.U16MSB
import Clean.Utils.Tactics.ProvableStructSimp

/-! # DivRem comparison-cluster contract

The compact input view avoids flattening the whole row during child-circuit proofs. Its contract
composes the fifteen comparison and sign subcircuits; the public division semantics is independent
of this decomposition. The bundled implementation is `DivRemCompare.circuit`.
-/

@[expose] public section

namespace SP1Clean.DivRemCompare

open Circuit

/-- The comparison/sign cluster's explicit view of a DivRem row. Passing this compact constructor
literal to the child circuit is semantically identical to passing the whole row, but lets Clean
evaluate the fields component-wise instead of reducing `Eval.eval` over all 246 columns merely to
project the fifteen sub-operation inputs. The view witnesses nothing and adds no AIR columns. -/
structure Inputs (F : Type) where
  op_b_prev_value : Word F
  op_c_prev_value : Word F
  c : Word F
  quotient : Word F
  remainder_comp : Word F
  remainder : Word F
  abs_remainder : Word F
  abs_c : Word F
  max_abs_c_or_1 : Word F
  is_c_0 : Circuits.Types.IsZeroWordOperation F
  is_overflow_b : Circuits.Types.IsEqualWordOperation F
  is_overflow_c : Circuits.Types.IsEqualWordOperation F
  c_neg_operation : Circuits.Types.AddOperation F
  rem_neg_operation : Circuits.Types.AddOperation F
  remainder_lt_operation : Circuits.Types.LtOperationUnsigned F
  b_msb : Circuits.Types.U16MSBOperation F
  rem_msb : Circuits.Types.U16MSBOperation F
  c_msb : Circuits.Types.U16MSBOperation F
  quot_msb : Circuits.Types.U16MSBOperation F
  is_divw : F
  is_remw : F
  is_divuw : F
  is_remuw : F
  is_real_not_word : F
  abs_c_alu_event : F
  abs_rem_alu_event : F
  is_real : F
  remainder_check_multiplicity : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Component-wise evaluation of the comparison input.  Keep this next to the derived
`ProvableStruct` instance: large chip proofs can rewrite this theorem before projecting a field,
instead of reducing the complete flattened evaluator merely to reach one nested operation. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ op_b_prev_value := Eval.eval env input.op_b_prev_value,
         op_c_prev_value := Eval.eval env input.op_c_prev_value,
         c := Eval.eval env input.c,
         quotient := Eval.eval env input.quotient,
         remainder_comp := Eval.eval env input.remainder_comp,
         remainder := Eval.eval env input.remainder,
         abs_remainder := Eval.eval env input.abs_remainder,
         abs_c := Eval.eval env input.abs_c,
         max_abs_c_or_1 := Eval.eval env input.max_abs_c_or_1,
         is_c_0 := Eval.eval env input.is_c_0,
         is_overflow_b := Eval.eval env input.is_overflow_b,
         is_overflow_c := Eval.eval env input.is_overflow_c,
         c_neg_operation := Eval.eval env input.c_neg_operation,
         rem_neg_operation := Eval.eval env input.rem_neg_operation,
         remainder_lt_operation := Eval.eval env input.remainder_lt_operation,
         b_msb := Eval.eval env input.b_msb,
         rem_msb := Eval.eval env input.rem_msb,
         c_msb := Eval.eval env input.c_msb,
         quot_msb := Eval.eval env input.quot_msb,
         is_divw := Eval.eval env input.is_divw,
         is_remw := Eval.eval env input.is_remw,
         is_divuw := Eval.eval env input.is_divuw,
         is_remuw := Eval.eval env input.is_remuw,
         is_real_not_word := Eval.eval env input.is_real_not_word,
         abs_c_alu_event := Eval.eval env input.abs_c_alu_event,
         abs_rem_alu_event := Eval.eval env input.abs_rem_alu_event,
         is_real := Eval.eval env input.is_real,
         remainder_check_multiplicity := Eval.eval env input.remainder_check_multiplicity } :
        Inputs F) := by
  provable_struct_simp

/-- Project exactly the committed columns consumed by the comparison/sign cluster. -/
def Inputs.ofCols {F : Type} (cols : DivRemChip.Columns F) : Inputs F :=
  { op_b_prev_value := cols.adapter.op_b_memory.prev_value,
    op_c_prev_value := cols.adapter.op_c_memory.prev_value,
    c := cols.c,
    quotient := cols.quotient,
    remainder_comp := cols.remainder_comp,
    remainder := cols.remainder,
    abs_remainder := cols.abs_remainder,
    abs_c := cols.abs_c,
    max_abs_c_or_1 := cols.max_abs_c_or_1,
    is_c_0 := cols.is_c_0,
    is_overflow_b := cols.is_overflow_b,
    is_overflow_c := cols.is_overflow_c,
    c_neg_operation := cols.c_neg_operation,
    rem_neg_operation := cols.rem_neg_operation,
    remainder_lt_operation := cols.remainder_lt_operation,
    b_msb := cols.b_msb,
    rem_msb := cols.rem_msb,
    c_msb := cols.c_msb,
    quot_msb := cols.quot_msb,
    is_divw := cols.is_divw,
    is_remw := cols.is_remw,
    is_divuw := cols.is_divuw,
    is_remuw := cols.is_remuw,
    is_real_not_word := cols.is_real_not_word,
    abs_c_alu_event := cols.abs_c_alu_event,
    abs_rem_alu_event := cols.abs_rem_alu_event,
    is_real := cols.is_real,
    remainder_check_multiplicity := cols.remainder_check_multiplicity }

/-- The generated core row enables the remainder-range comparison exactly on a real row whose
divisor is nonzero. The `IsZeroWordOperation` inside the comparison cluster proves that
`is_c_0.result` is boolean; keeping this cross-cluster gate equation separate lets that proof derive
the multiplicity's booleanness without asking the parent for a circular consequence. -/
def RemainderCheckGateSpec {p : ℕ} (cols : Inputs (ZMod p)) : Prop :=
  cols.remainder_check_multiplicity = (1 - cols.is_c_0.result) * cols.is_real

/-- The semantic evidence certified by the DivRem row's **comparison/sign assertion cluster**
(`Native/Operations/DivRemOperation/Compare.lean`): the conjunction of the fifteen composed
sub-operations' semantic `Spec`s, instantiated at the committed `DivRemChip.Columns` fields and gated
exactly as the chip gates them (`is_real_not_word` / the word-variant sum `e2` / `is_real` /
`abs_c_alu_event` / `abs_rem_alu_event` / `remainder_check_multiplicity`).

Each conjunct is the exact hypothesis shape the evidence-extraction layer consumes
(`Proofs/Chips/DivRemChip/Extract.lean`: `overflow_of_iseqword`/`overflow_of_iseqword_word` take
the four `IsEqualWordOperation.Spec`s, the divide-by-zero readout takes the
`IsZeroWordOperation.Spec`, and the `Cases.lean` evidence families take the two `AddOperation`
negation identities, the `LtOperationUnsigned` range fact, and the seven `U16MSBOperation` sign
bits via each op's `result_semantic`), so chip-level assembly is pure plumbing. Per the
semantic-not-structural principle, no constraint equation is restated here — the sub-operations'
own `Spec`s are the semantic currency. -/
def CompareSpec {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] (cols : Inputs (ZMod p)) : Prop :=
  let bpv := cols.op_b_prev_value
  let cpv := cols.op_c_prev_value
  let irnw := cols.is_real_not_word
  let e2 := cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw
  -- (1-4) signed-overflow detection: `b` vs `i64::MIN`, `c` vs `-1` — full-word @ `irnw`,
  -- low-half @ `e2`.
  IsEqualWordOperation.Spec
    ⟨#v[bpv[0], bpv[1], bpv[2], bpv[3]], #v[0, 0, 0, 32768], cols.is_overflow_b, irnw⟩ ∧
  IsEqualWordOperation.Spec
    ⟨#v[cpv[0], cpv[1], cpv[2], cpv[3]], #v[65535, 65535, 65535, 65535],
     cols.is_overflow_c, irnw⟩ ∧
  IsEqualWordOperation.Spec
    ⟨#v[bpv[0], bpv[1], 0, 0], #v[0, 32768, 0, 0], cols.is_overflow_b, e2⟩ ∧
  IsEqualWordOperation.Spec
    ⟨#v[cpv[0], cpv[1], 0, 0], #v[65535, 65535, 0, 0], cols.is_overflow_c, e2⟩ ∧
  -- (5) divide-by-zero detection on the committed operand `c`.
  IsZeroWordOperation.Spec ⟨cols.c, cols.is_c_0, cols.is_real⟩ ∧
  -- (6-7) the `|c|` and `|remainder|` two's-complement negation identities.
  AddOperation.Spec
    ⟨cols.c, cols.abs_c, ⟨cols.c_neg_operation.value⟩, cols.abs_c_alu_event⟩ ∧
  AddOperation.Spec
    ⟨cols.remainder_comp, cols.abs_remainder, ⟨cols.rem_neg_operation.value⟩,
     cols.abs_rem_alu_event⟩ ∧
  -- (8) the Euclidean remainder range comparison `|remainder| < max(|c|, 1)`.
  LtOperationUnsigned.Spec
    ⟨cols.abs_remainder, cols.max_abs_c_or_1, cols.remainder_lt_operation,
     cols.remainder_check_multiplicity⟩ ∧
  -- (9-15) sign-bit extractions: b/c/remainder high u16 (@ `irnw`), b/c/remainder/quotient
  -- low-half-high u16 (@ `e2`).
  U16MSBOperation.Spec ⟨bpv[3], cols.b_msb, irnw⟩ ∧
  U16MSBOperation.Spec ⟨cpv[3], cols.c_msb, irnw⟩ ∧
  U16MSBOperation.Spec ⟨cols.remainder[3], cols.rem_msb, irnw⟩ ∧
  U16MSBOperation.Spec ⟨bpv[1], cols.b_msb, e2⟩ ∧
  U16MSBOperation.Spec ⟨cpv[1], cols.c_msb, e2⟩ ∧
  U16MSBOperation.Spec ⟨cols.remainder[1], cols.rem_msb, e2⟩ ∧
  U16MSBOperation.Spec ⟨cols.quotient[1], cols.quot_msb, e2⟩

end SP1Clean.DivRemCompare
