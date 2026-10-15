module

public import SP1Clean.Semantics.Specs.IsZeroWord
public import SP1Clean.Circuits.Types.IsEqualWordOperation

/-! # Word equality contract

The semantic relation and its result interpretation are independent of the circuit.
The contract includes padding behavior and the shared auxiliary columns used by composition.
-/

@[expose] public section

namespace SP1Clean.IsEqualWordOperation

/-- Inputs for the native word-equality test. -/
structure Inputs (F : Type) where
  /-- The first input word. -/
  a : Word F
  /-- The second input word. -/
  b : Word F
  /-- The witnessed zero-test columns. -/
  cols : Circuits.Types.IsEqualWordOperation F
  /-- One for an active row, zero for padding. -/
  is_real : F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

variable {p : ℕ} [Fact p.Prime]

/-- The limb-wise difference word `a - b` (as the operand the sub-operation runs on). -/
def diff (input : Inputs (ZMod p)) : Word (ZMod p) :=
  #v[input.a[0] - input.b[0], input.a[1] - input.b[1], input.a[2] - input.b[2], input.a[3] - input.b[3]]

/-- The activity flag is binary; the word limbs can be any field elements. -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.is_real = 0 ∨ input.is_real = 1

/-- Equality is the zero test of the limb-wise difference, including its auxiliary-column and
padding contract. `result_semantic` gives the resulting equality indicator on active rows. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  IsZeroWordOperation.Spec ⟨diff input, input.cols.is_diff_zero, input.is_real⟩

/-- Semantic exposure: on a real row the `Spec` forces `is_diff_zero.result` to be the equality
indicator of `a` and `b`. -/
theorem result_semantic {input : Inputs (ZMod p)} (h : Spec input) (hr : input.is_real = 1) :
    input.cols.is_diff_zero.result =
      if (input.a[0] = input.b[0] ∧ input.a[1] = input.b[1] ∧
          input.a[2] = input.b[2] ∧ input.a[3] = input.b[3]) then 1 else 0 := by
  have hz := IsZeroWordOperation.result_semantic h hr
  simp only [diff, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ, sub_eq_zero] at hz
  exact hz

end SP1Clean.IsEqualWordOperation
