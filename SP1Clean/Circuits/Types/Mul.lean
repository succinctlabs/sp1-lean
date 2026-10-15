module

public import SP1Clean.Math.Word
public import SP1Clean.Circuits.Types.CPUState
public import SP1Clean.Circuits.Types.RTypeReader
public import SP1Clean.Circuits.Types.MulOperation
public import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Native multiplication inputs and columns

The row layout and its basic evaluation lemmas are independent of circuit implementations.
Five committed selectors determine activity; the arithmetic block is shared with DivRem.
-/

@[expose] public section

namespace SP1Clean.MulChip

open Circuit

/-- Multiplication row with register-reader state, arithmetic witnesses and committed selectors. -/
structure Columns (F : Type) where
  /-- Execution clock and program counter for this row. -/
  state : Circuits.Types.CPUState F
  /-- Register operands, prior values and access timestamps. -/
  adapter : Circuits.Types.RTypeReader F
  /-- Result word written to the destination register. -/
  a : Word F
  /-- Shared 45-cell multiplication witness. -/
  mul_operation : Circuits.Types.MulOperation F
  /-- Low 64-bit product selector. -/
  is_mul : F
  /-- High signed product selector. -/
  is_mulh : F
  /-- High unsigned product selector. -/
  is_mulhu : F
  /-- High product selector for signed first and unsigned second operands. -/
  is_mulhsu : F
  /-- Sign-extended low 32-bit product selector. -/
  is_mulw : F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- Register-reader inputs and the five committed multiplication selectors. Activity is their
sum, so the physical row needs no separate activity cell or external selector hint. -/
structure Inputs (F : Type) where
  /-- Current execution clock and program counter. -/
  state : Circuits.Types.CPUState F
  /-- Register indices, prior values and access timestamps. -/
  adapter : Circuits.Types.RTypeReader F
  /-- Selects the low 64-bit product. -/
  isMul : F
  /-- Selects the high signed product. -/
  isMulh : F
  /-- Selects the high unsigned product. -/
  isMulhu : F
  /-- Selects the high product with a signed first operand. -/
  isMulhsu : F
  /-- Selects the sign-extended low 32-bit product. -/
  isMulw : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Row activity is the sum of the committed opcode selectors, as in SP1's AIR. -/
@[reducible] def Inputs.is_real {F : Type} [Add F] (input : Inputs F) : F :=
  input.isMul + input.isMulh + input.isMulhu + input.isMulhsu + input.isMulw

/-- First source operand read by the register adapter. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
/-- Second source operand read by the register adapter. -/
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- The five committed dispatch cells, projected away from MUL's large arithmetic witness.  Control
proofs use this small view so neither Lean nor an auditor must normalize the 45-cell multiplication
block merely to determine the selected instruction. -/
structure SelectorValues (F : Type) where
  /-- Low 64-bit product selector. -/
  is_mul : F
  /-- High signed product selector. -/
  is_mulh : F
  /-- High unsigned product selector. -/
  is_mulhu : F
  /-- High product selector for signed first and unsigned second operands. -/
  is_mulhsu : F
  /-- Sign-extended low 32-bit product selector. -/
  is_mulw : F
deriving ProvableStruct
provable_struct_eval_lemmas SelectorValues

/-- Project the dispatch cells from a complete MUL row. -/
def selectors {F : Type} (cols : Columns F) : SelectorValues F :=
  ⟨cols.is_mul, cols.is_mulh, cols.is_mulhu, cols.is_mulhsu, cols.is_mulw⟩

/-- Component-wise evaluation of MUL's independent input row. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ state := Eval.eval env input.state, adapter := Eval.eval env input.adapter,
         isMul := Eval.eval env input.isMul, isMulh := Eval.eval env input.isMulh,
         isMulhu := Eval.eval env input.isMulhu, isMulhsu := Eval.eval env input.isMulhsu,
         isMulw := Eval.eval env input.isMulw } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Evaluation commutes with activity derived from the five input selectors. -/
@[circuit_norm] theorem eval_isReal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).is_real = Expression.eval env input.is_real := by
  rw [← ProvableStruct.eval_eq_eval]
  simpa only [Inputs.is_real, CircuitType.eval_expr, Expression.eval] using
    congrArg (fun value : Inputs F => value.is_real) (eval_inputs env input)

/-- Component-wise evaluation of a completed Mul row. -/
@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state
         adapter := Eval.eval env cols.adapter
         a := Eval.eval env cols.a
         mul_operation := Eval.eval env cols.mul_operation
         is_mul := Eval.eval env cols.is_mul
         is_mulh := Eval.eval env cols.is_mulh
         is_mulhu := Eval.eval env cols.is_mulhu
         is_mulhsu := Eval.eval env cols.is_mulhsu
         is_mulw := Eval.eval env cols.is_mulw } :
        Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

end SP1Clean.MulChip
