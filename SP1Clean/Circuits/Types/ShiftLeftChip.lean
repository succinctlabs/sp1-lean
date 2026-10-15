module

public import SP1Clean.Circuits.Types.CPUState
public import SP1Clean.Circuits.Types.ALUTypeReader
public import SP1Clean.Circuits.Types.U16MSBOperation

/-! # Native shift-left instruction rows

CPU and register accesses, shift witnesses, and SLL/SLLW selectors. These row types
are independent of circuit implementations and witness generation.
-/

@[expose] public section

namespace SP1Clean.ShiftLeftChip

open Circuit

/-- Committed CPU/ALU reader columns and instruction selectors. -/
structure Inputs (F : Type) where
  /-- Execution clock and program counter. -/
  state : Circuits.Types.CPUState F
  /-- Register and immediate operand accesses. -/
  adapter : Circuits.Types.ALUTypeReader F
  /-- Select a 64-bit logical shift. -/
  isSll : F
  /-- Select a sign-extended 32-bit shift. -/
  isSllw : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Row activity is the selector sum, as in SP1. -/
@[reducible] def Inputs.is_real {F : Type} [Add F] (input : Inputs F) : F :=
  input.isSll + input.isSllw

/-- Source B is the prior register value read by the ALU adapter. -/
@[reducible] def Inputs.op_b_val {F} (i : Inputs F) : Word F := i.adapter.op_b_memory.prev_value

/-- Source C is the adapter's prior value. On immediate rows the reader constrains it to the
committed decoded shift amount. -/
@[reducible] def Inputs.op_c_val {F} (i : Inputs F) : Word F := i.adapter.op_c_memory.prev_value

/-- Completed native ShiftLeft row, in SP1 field order. -/
structure Columns (F : Type) where
  /-- Execution clock and program counter. -/
  state : Circuits.Types.CPUState F
  /-- Register and immediate operand accesses. -/
  adapter : Circuits.Types.ALUTypeReader F
  /-- Result word. -/
  a : Word F
  /-- Low six bits of the shift amount. -/
  c_bits : Vector F 6
  /-- Power of two from the low two shift bits. -/
  v_01 : F
  /-- Power of two from the low three shift bits. -/
  v_012 : F
  /-- Power of two from the low four shift bits. -/
  v_0123 : F
  /-- One-hot placement by 16-bit limbs. -/
  shift_u16 : Vector F 4
  /-- Low portion of each source limb. -/
  lower_limb : Word F
  /-- High portion of each source limb. -/
  higher_limb : Word F
  /-- Reassembled result before limb placement. -/
  limb_result : Word F
  /-- Sign bit of the 32-bit result. -/
  sllw_msb : Circuits.Types.U16MSBOperation F
  /-- Selector for a 64-bit logical shift. -/
  is_sll : F
  /-- Selector for a sign-extended 32-bit shift. -/
  is_sllw : F
  /-- Product of the SLLW and immediate selectors. -/
  is_sllw_imm : F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ state := Eval.eval env input.state, adapter := Eval.eval env input.adapter,
         isSll := Eval.eval env input.isSll, isSllw := Eval.eval env input.isSllw } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state, adapter := Eval.eval env cols.adapter,
         a := Eval.eval env cols.a, c_bits := Eval.eval env cols.c_bits,
         v_01 := Eval.eval env cols.v_01, v_012 := Eval.eval env cols.v_012,
         v_0123 := Eval.eval env cols.v_0123,
         shift_u16 := Eval.eval env cols.shift_u16,
         lower_limb := Eval.eval env cols.lower_limb,
         higher_limb := Eval.eval env cols.higher_limb,
         limb_result := Eval.eval env cols.limb_result,
         sllw_msb := Eval.eval env cols.sllw_msb,
         is_sll := Eval.eval env cols.is_sll, is_sllw := Eval.eval env cols.is_sllw,
         is_sllw_imm := Eval.eval env cols.is_sllw_imm } : Columns F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_inputIsReal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).is_real = Expression.eval env input.is_real := by
  simpa only [Inputs.is_real, CircuitType.eval_expr, Expression.eval] using
    congrArg (fun value : Inputs F => value.is_real) (eval_inputs env input)

/-- Activity evaluation at the struct boundary. -/
@[circuit_norm] theorem eval_isReal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).is_real = Expression.eval env input.is_real := by
  rw [← ProvableStruct.eval_eq_eval]
  exact eval_inputIsReal env input

end SP1Clean.ShiftLeftChip
