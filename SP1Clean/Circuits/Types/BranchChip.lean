module

public import SP1Clean.Circuits.Types.CPUState
public import SP1Clean.Circuits.Types.ITypeReader
public import SP1Clean.Circuits.Types.LtOperationSigned

/-! # Native conditional-branch rows

CPU state, immutable source-register reads, opcode selectors and branch witnesses.
These types and evaluation lemmas are independent of circuit implementations.
-/

@[expose] public section

namespace SP1Clean.BranchChip

open Circuit

/-- Completed native Branch row, in SP1 field order. -/
structure Columns (F : Type) where
  /-- Execution clock and program counter. -/
  state : Circuits.Types.CPUState F
  /-- Immutable source-register reads and branch offset. -/
  adapter : Circuits.Types.ITypeReader F
  /-- Selected next program counter. -/
  next_pc : Vector F 3
  /-- Select equality. -/
  is_beq : F
  /-- Select inequality. -/
  is_bne : F
  /-- Select signed less-than. -/
  is_blt : F
  /-- Select signed greater-than or equal. -/
  is_bge : F
  /-- Select unsigned less-than. -/
  is_bltu : F
  /-- Select unsigned greater-than or equal. -/
  is_bgeu : F
  /-- The taken-branch decision. -/
  is_branching : F
  /-- Signed or unsigned comparison certificate. -/
  compare_operation : Circuits.Types.LtOperationSigned F
deriving ProvableStruct
provable_struct_eval_lemmas Columns

/-- CPU state, immutable source reads and committed opcode selectors. -/
structure Inputs (F : Type) where
  /-- Execution clock and program counter. -/
  state : Circuits.Types.CPUState F
  /-- Immutable source-register reads and branch offset. -/
  adapter : Circuits.Types.ITypeReader F
  /-- Select equality. -/
  isBeq : F
  /-- Select inequality. -/
  isBne : F
  /-- Select signed less-than. -/
  isBlt : F
  /-- Select signed greater-than or equal. -/
  isBge : F
  /-- Select unsigned less-than. -/
  isBltu : F
  /-- Select unsigned greater-than or equal. -/
  isBgeu : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- Selectors in SP1's BEQ/BNE/BLT/BGE/BLTU/BGEU order. -/
@[reducible] def Inputs.flags {F : Type} (input : Inputs F) : Vector F 6 :=
  #v[input.isBeq, input.isBne, input.isBlt, input.isBge, input.isBltu, input.isBgeu]

/-- Row activity is the selector sum, as in SP1. -/
@[reducible] def Inputs.is_real {F : Type} [Add F] (input : Inputs F) : F :=
  input.isBeq + input.isBne + input.isBlt + input.isBge + input.isBltu + input.isBgeu

/-- The field-valued branch decision from opcode selectors, comparison bit and inequality flag. -/
def branchDecision {F : Type} [Add F] [Sub F] [Mul F] [OfNat F 1]
    (b0 b1 b2 b3 b4 b5 bit sum : F) : F :=
  b0 * (1 - sum) + b1 * (1 - (1 - sum)) + (b3 + b5) * (1 - bit) + (b2 + b4) * bit

/-- Component-wise evaluation of the independent Branch input prefix. -/
@[circuit_norm] theorem eval_inputs {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    Eval.eval env input =
      ({ state := Eval.eval env input.state, adapter := Eval.eval env input.adapter,
         isBeq := Eval.eval env input.isBeq, isBne := Eval.eval env input.isBne,
         isBlt := Eval.eval env input.isBlt, isBge := Eval.eval env input.isBge,
         isBltu := Eval.eval env input.isBltu, isBgeu := Eval.eval env input.isBgeu } : Inputs F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

/-- Evaluate derived activity without unfolding the completed circuit. -/
@[circuit_norm] theorem eval_inputIsReal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (Eval.eval env input).is_real = Expression.eval env input.is_real := by
  simpa only [Inputs.is_real, CircuitType.eval_expr, Expression.eval] using
    congrArg (fun value : Inputs F => value.is_real) (eval_inputs env input)

/-- Evaluation of derived activity at the struct boundary. -/
@[circuit_norm] theorem eval_isReal {F : Type} [FiniteField F]
    (env : Environment F) (input : Inputs (Expression F)) :
    (ProvableStruct.eval env input).is_real = Expression.eval env input.is_real := by
  rw [← ProvableStruct.eval_eq_eval]
  exact eval_inputIsReal env input

@[circuit_norm] theorem eval_columns {F : Type} [FiniteField F]
    (env : Environment F) (cols : Columns (Expression F)) :
    Eval.eval env cols =
      ({ state := Eval.eval env cols.state,
         adapter := Eval.eval env cols.adapter,
         next_pc := Eval.eval env cols.next_pc,
         is_beq := Eval.eval env cols.is_beq,
         is_bne := Eval.eval env cols.is_bne,
         is_blt := Eval.eval env cols.is_blt,
         is_bge := Eval.eval env cols.is_bge,
         is_bltu := Eval.eval env cols.is_bltu,
         is_bgeu := Eval.eval env cols.is_bgeu,
         is_branching := Eval.eval env cols.is_branching,
         compare_operation := Eval.eval env cols.compare_operation } :
        Columns F) := by
  rw [ProvableStruct.eval_eq_eval]; rfl

end SP1Clean.BranchChip
