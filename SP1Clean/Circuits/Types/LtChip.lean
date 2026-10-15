module

public import SP1Clean.Circuits.Types.CPUState
public import SP1Clean.Circuits.Types.ALUTypeReader
public import SP1Clean.Circuits.Types.LtOperationSigned

/-! # Native less-than instruction rows

Reader inputs and committed SLT/SLTU selectors determine activity and comparison mode.
The completed row follows SP1's field order. Types and evaluation laws are independent of
circuit implementations and witness generation.
-/

@[expose] public section

namespace SP1Clean.LtChip

open Circuit

/-- Reader inputs and the two committed instruction selectors. -/
structure Inputs (F : Type) where
  /-- Execution clock and program counter. -/
  state : Circuits.Types.CPUState F
  /-- Register and immediate operand accesses. -/
  adapter : Circuits.Types.ALUTypeReader F
  /-- Select signed comparison. -/
  isSlt : F
  /-- Select unsigned comparison. -/
  isSltu : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Row activity is the selector sum, as in SP1's AIR. -/
@[reducible] def Inputs.is_real {F : Type} [Add F] (input : Inputs F) : F :=
  input.isSlt + input.isSltu

/-- First source operand read from the ALU adapter. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
/-- Second source operand, including the adapter's synthetic immediate access. -/
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- Completed native Lt row, in SP1's field order. -/
structure Columns (F : Type) where
  /-- Execution clock and program counter. -/
  state : Circuits.Types.CPUState F
  /-- Register and immediate operand accesses. -/
  adapter : Circuits.Types.ALUTypeReader F
  /-- Signed selector. -/
  is_slt : F
  /-- Unsigned selector. -/
  is_sltu : F
  /-- Comparison certificate and operand sign bits. -/
  lt_operation : Circuits.Types.LtOperationSigned F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ state := Eval.eval env input.state, adapter := Eval.eval env input.adapter,
         isSlt := Eval.eval env input.isSlt, isSltu := Eval.eval env input.isSltu } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state, adapter := Eval.eval env cols.adapter,
         is_slt := Eval.eval env cols.is_slt, is_sltu := Eval.eval env cols.is_sltu,
         lt_operation := Eval.eval env cols.lt_operation } : Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

@[circuit_norm] theorem eval_inputAdapter {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).adapter = Eval.eval env input.adapter := by
  rw [eval_inputs]

@[circuit_norm] theorem eval_inputIsReal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).is_real = Expression.eval env input.is_real := by
  simpa only [Inputs.is_real, CircuitType.eval_expr, Expression.eval] using
    congrArg (fun value : Inputs F => value.is_real) (eval_inputs env input)

/-- Evaluation of derived activity at the struct boundary. -/
theorem eval_isReal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).is_real = Expression.eval env input.is_real := by
  rw [← ProvableStruct.eval_eq_eval]
  exact eval_inputIsReal env input

end SP1Clean.LtChip
