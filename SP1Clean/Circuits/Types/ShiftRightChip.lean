module

public import SP1Clean.Circuits.Types.CPUState
public import SP1Clean.Circuits.Types.ALUTypeReader
public import SP1Clean.Circuits.Types.U16MSBOperation

/-! # Native shift-right instruction rows

CPU and register accesses, shift witnesses, and SRL/SRA/SRLW/SRAW selectors.
These row types are independent of circuit implementations and witness generation.
-/

@[expose] public section

namespace SP1Clean.ShiftRightChip

open Circuit

/-- Committed CPU and ALU reader columns and instruction selectors. -/
structure Inputs (F : Type) where
  /-- Execution clock and program counter. -/
  state : Circuits.Types.CPUState F
  /-- Register and immediate operand accesses. -/
  adapter : Circuits.Types.ALUTypeReader F
  /-- Select a 64-bit logical shift. -/
  isSrl : F
  /-- Select a 64-bit arithmetic shift. -/
  isSra : F
  /-- Select a sign-extended 32-bit logical shift. -/
  isSrlw : F
  /-- Select a sign-extended 32-bit arithmetic shift. -/
  isSraw : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Row activity is the selector sum, as in SP1. -/
@[reducible] def Inputs.is_real {F : Type} [Add F] (input : Inputs F) : F :=
  input.isSrl + input.isSra + input.isSrlw + input.isSraw

/-- Completed native ShiftRight row, in SP1 field order. -/
structure Columns (F : Type) where
  /-- Execution clock and program counter. -/
  state : Circuits.Types.CPUState F
  /-- Register and immediate operand accesses. -/
  adapter : Circuits.Types.ALUTypeReader F
  /-- Result word. -/
  a : Word F
  /-- Sign bit of the selected source width. -/
  b_msb : Circuits.Types.U16MSBOperation F
  /-- Sign bit of the 32-bit result. -/
  srw_msb : Circuits.Types.U16MSBOperation F
  /-- Low six bits of the shift amount. -/
  c_bits : Vector F 6
  /-- Source sign bit times the inverted shift power. -/
  sra_msb_v0123 : F
  /-- Inverted power from the low four shift bits. -/
  v_0123 : F
  /-- Inverted power from the low three shift bits. -/
  v_012 : F
  /-- Inverted power from the low two shift bits. -/
  v_01 : F
  /-- Low portion of each effective source limb. -/
  lower_limb : Word F
  /-- High portion of each effective source limb. -/
  higher_limb : Word F
  /-- Reassembled result before limb placement. -/
  limb_result : Vector F 4
  /-- One-hot placement by 16-bit limbs. -/
  shift_u16 : Vector F 4
  /-- Selector for a 64-bit logical shift. -/
  is_srl : F
  /-- Selector for a 64-bit arithmetic shift. -/
  is_sra : F
  /-- Selector for a sign-extended 32-bit logical shift. -/
  is_srlw : F
  /-- Selector for a sign-extended 32-bit arithmetic shift. -/
  is_sraw : F
  /-- Product of the word-shift and immediate selectors. -/
  is_w_imm : F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ state := Eval.eval env input.state, adapter := Eval.eval env input.adapter,
         isSrl := Eval.eval env input.isSrl, isSra := Eval.eval env input.isSra,
         isSrlw := Eval.eval env input.isSrlw, isSraw := Eval.eval env input.isSraw } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]
  rfl

@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state, adapter := Eval.eval env cols.adapter,
         a := Eval.eval env cols.a, b_msb := Eval.eval env cols.b_msb,
         srw_msb := Eval.eval env cols.srw_msb, c_bits := Eval.eval env cols.c_bits,
         sra_msb_v0123 := Eval.eval env cols.sra_msb_v0123,
         v_0123 := Eval.eval env cols.v_0123, v_012 := Eval.eval env cols.v_012,
         v_01 := Eval.eval env cols.v_01,
         lower_limb := Eval.eval env cols.lower_limb,
         higher_limb := Eval.eval env cols.higher_limb,
         limb_result := Eval.eval env cols.limb_result,
         shift_u16 := Eval.eval env cols.shift_u16,
         is_srl := Eval.eval env cols.is_srl, is_sra := Eval.eval env cols.is_sra,
         is_srlw := Eval.eval env cols.is_srlw, is_sraw := Eval.eval env cols.is_sraw,
         is_w_imm := Eval.eval env cols.is_w_imm } : Columns F) := by
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

end SP1Clean.ShiftRightChip
