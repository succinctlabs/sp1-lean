module

public import SP1Clean.Circuits.Types.CPUState
public import SP1Clean.Circuits.Types.ALUTypeReader
public import SP1Clean.Circuits.Types.Bitwise

/-! # Native Bitwise row types

The circuit inputs, completed row layout and evaluation lemmas have no implementation
or witness-generation dependency. The ALU adapter supports register and immediate operands.
-/

@[expose] public section

namespace SP1Clean.BitwiseChip

open Circuit

/-- Reader inputs and the three committed instruction selectors. Their sum supplies activity. -/
structure Inputs (F : Type) where
  /-- Execution clock and program counter. -/
  state : Circuits.Types.CPUState F
  /-- Register and immediate operand accesses. -/
  adapter : Circuits.Types.ALUTypeReader F
  /-- Select XOR. -/
  isXor : F
  /-- Select OR. -/
  isOr : F
  /-- Select AND. -/
  isAnd : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Row activity is the sum of the committed selectors, as in SP1's AIR. -/
@[reducible] def Inputs.is_real {F : Type} [Add F] (input : Inputs F) : F :=
  input.isXor + input.isOr + input.isAnd

/-- Native Bitwise-chip row (Rust field order — the chip has no separate `is_real` column; the
real-row selector is the flag sum). The reader blocks reuse the project substrate; only the composed
u16 bitwise block is owned by the local Lean gadget. `Faithful.BitwiseChip.bitwiseChipReconfigure` is
the sole bridge to Rust's separately generated whole-chip row. -/
structure Columns (F : Type) where
  /-- Execution clock and program counter. -/
  state : Circuits.Types.CPUState F
  /-- Register and immediate operand accesses. -/
  adapter : Circuits.Types.ALUTypeReader F
  /-- Operand decomposition and result bytes. -/
  bitwise_operation : BitwiseU16Operation.Columns F
  /-- XOR selector. -/
  is_xor : F
  /-- OR selector. -/
  is_or : F
  /-- AND selector. -/
  is_and : F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- First source operand read from the ALU adapter. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value
/-- Second source operand, including the adapter's synthetic immediate access. -/
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ state := Eval.eval env input.state, adapter := Eval.eval env input.adapter,
         isXor := Eval.eval env input.isXor, isOr := Eval.eval env input.isOr,
         isAnd := Eval.eval env input.isAnd } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state, adapter := Eval.eval env cols.adapter,
         bitwise_operation := Eval.eval env cols.bitwise_operation,
         is_xor := Eval.eval env cols.is_xor, is_or := Eval.eval env cols.is_or,
         is_and := Eval.eval env cols.is_and } : Columns F) := by
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

end SP1Clean.BitwiseChip
