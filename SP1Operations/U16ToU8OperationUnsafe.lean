import SP1Foundations

-- Probably good to still namespace things
namespace U16ToU8OperationUnsafe

/-- Representation of extracted constraints:
{
  Expr 0: Const(3)
  Expr 1: Const(0)
  Expr 2: Var(SymbolicVar(2))
  Expr 3: Var(SymbolicVar(0))
  Expr 4: Sub(3, 2)
  Expr 5: Const(2005401601)
  Expr 6: Mul(4, 5)
  Expr 7: Var(SymbolicVar(4))
  Expr 8: Var(SymbolicVar(3))
  Expr 9: Var(SymbolicVar(1))
  Expr 10: Sub(9, 8)
  Expr 11: Mul(10, 5)
}
-/
def ConstraintSet
    (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear) : Finset SP1Constraint :=
  sorry

/- Nicer description of contraints in terms of a proposition. -/
def ConstraintProp
    (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear) : Prop :=
  sorry

/-- Equivalence between the two versions of the constraints. -/
lemma toProp_constraintSet_iff_constraintProp
    (Input0 Input1 Input2 Input3 Input4 Input5 Input6 : BabyBear) :
    True :=
  sorry

/-- Expected behavior of the add operation. Note that we assume first inputs are `U16` -/
def Spec
    (Input0 Input1 Input2 Input3 : U16)
    (Input4 Input5 Input6 : BabyBear) : Prop :=
  (Input6 = 0 ∨ Input6 = 1) ∧
  (Input6 ≠ 0 → (
    (Input4.val < 65536) ∧ (Input5.val < 65536) ∧
    ((Input0.val + Input1.val * 65536) + (Input2.val + Input3.val * 65536)) % 4294967296 = (Input4.val + Input5.val * 65536)
  ))

theorem spec_of_constraintSet
    (Input0 Input1 Input2 Input3 : U16) (Input4 Input5 Input6 : BabyBear)
    (h : constraintSet_toProp (ConstraintSet Input0 Input1 Input2 Input3 Input4 Input5 Input6)) :
    Spec Input0 Input1 Input2 Input3 Input4 Input5 Input6 := by
  sorry

end U16ToU8OperationUnsafe
