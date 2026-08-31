import SP1Clean.Proofs.Chips.LoadX0Chip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # LoadX0 — physical routing contract

This file exposes the one structural fact the whole-machine decoder needs from LoadX0's complete
native assertion system: every active row is routed to `x0`. The proof projects the literal
`is_real * (op_a_0 - 1) === 0` assertion from the folded `main`; it does not obtain routing from
the semantic `Spec` or a trace-generator convention.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

-- General expression/membership helpers: none of them needs a magnitude fact, so it is
-- introduced further down, over exactly the two declarations that carry it.
variable {p : ℕ} [Fact p.Prime]

private theorem expression_eval_sub (env : Environment (ZMod p))
    (a b : Expression (ZMod p)) :
    Expression.eval env (a - b) = Expression.eval env a - Expression.eval env b :=
  eval_sub env a b

private theorem expression_eval_mul (env : Environment (ZMod p))
    (a b : Expression (ZMod p)) :
    Expression.eval env (a * b) = Expression.eval env a * Expression.eval env b :=
  eval_mul env a b

private theorem expression_eval_add (env : Environment (ZMod p))
    (a b : Expression (ZMod p)) :
    Expression.eval env (a + b) = Expression.eval env a + Expression.eval env b :=
  eval_add env a b

private theorem evalSelectorSum (env : Environment (ZMod p))
    (input : Var LoadX0Chip.Inputs (ZMod p)) :
    Expression.eval env
        (input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
          input.is_lw + input.is_lwu + input.is_ld) =
      Expression.eval env input.is_lb + Expression.eval env input.is_lbu +
        Expression.eval env input.is_lh + Expression.eval env input.is_lhu +
          Expression.eval env input.is_lw + Expression.eval env input.is_lwu +
            Expression.eval env input.is_ld := by
  simp only [expression_eval_add]

private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

section RouteProjection
variable [Fact (2 ^ 17 < p)]

private theorem loadX0RouteConstraint_mem
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    (input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
      input.is_lw + input.is_lwu + input.is_ld) *
        (input.adapter.op_a_0 - 1) - 0 ∈
      ((LoadX0Chip.main input).operations offset).constraints := by
  simp only [LoadX0Chip.main, circuit_norm]
  iterate 15 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem
      ((input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
        input.is_lw + input.is_lwu + input.is_ld) *
          (input.adapter.op_a_0 - 1)) 0 _

-- Runs at the plain default: the former 1000000 ceiling was ~25x over; measured floor <= 40000.
/-- Project LoadX0's active `x0` route while its completed circuit stays folded. -/
theorem LoadX0Chip.eval_inputOpA0_eq_one_of_mainConstraints
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env
      ((LoadX0Chip.main input).operations offset))
    (real : Expression.eval env input.is_lb + Expression.eval env input.is_lbu +
      Expression.eval env input.is_lh + Expression.eval env input.is_lhu +
        Expression.eval env input.is_lw + Expression.eval env input.is_lwu +
          Expression.eval env input.is_ld = 1) :
    Expression.eval env input.adapter.op_a_0 = 1 := by
  have route : Expression.eval env
      (((input.is_lb + input.is_lbu + input.is_lh + input.is_lhu +
        input.is_lw + input.is_lwu + input.is_ld) *
          (input.adapter.op_a_0 - 1)) - 0) = 0 :=
    constraints.1 _ (loadX0RouteConstraint_mem input offset)
  rw [expression_eval_sub, expression_eval_mul, evalSelectorSum, real,
    expression_eval_sub] at route
  simp only [Expression.eval, one_mul, sub_zero] at route
  exact sub_eq_zero.mp route

end RouteProjection

/-! ## Physical opcode discriminant (committed-fragment strengthening) -/

/-- Lift a binary field flag to its `ℕ` value. -/
private theorem flagNatValue {x : ZMod p} (hx : x = 0 ∨ x = 1) :
    ∃ b : ℕ, b ≤ 1 ∧ x = (b : ZMod p) := by
  rcases hx with rfl | rfl
  · exact ⟨0, Nat.zero_le 1, by norm_num⟩
  · exact ⟨1, le_rfl, by norm_num⟩

section PhysicalOpcode
variable [Fact (2 ^ 17 < p)]

/-- The completed LoadX0 columns at one physical component row. -/
noncomputable def LoadX0Chip.physicalCols (env : Environment (ZMod p)) :
    LoadX0Chip.Columns (ZMod p) :=
  (⟨LoadX0Chip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env

/-- The completed LoadX0 row view at one physical component row. -/
noncomputable def LoadX0Chip.physicalView (env : Environment (ZMod p)) :
    Trace.RowView (ZMod p) :=
  LoadX0Chip.rowView
    ((⟨LoadX0Chip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    (LoadX0Chip.physicalCols env)

private theorem LoadX0Chip.isLbBinaryConstraint_mem
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_lb * (input.is_lb - 1) - 0 ∈
      ((LoadX0Chip.main input).operations offset).constraints := by
  simp only [LoadX0Chip.main, circuit_norm]
  iterate 4 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_lb * (input.is_lb - 1)) 0 _

private theorem LoadX0Chip.isLbuBinaryConstraint_mem
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_lbu * (input.is_lbu - 1) - 0 ∈
      ((LoadX0Chip.main input).operations offset).constraints := by
  simp only [LoadX0Chip.main, circuit_norm]
  iterate 5 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_lbu * (input.is_lbu - 1)) 0 _

private theorem LoadX0Chip.isLhBinaryConstraint_mem
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_lh * (input.is_lh - 1) - 0 ∈
      ((LoadX0Chip.main input).operations offset).constraints := by
  simp only [LoadX0Chip.main, circuit_norm]
  iterate 6 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_lh * (input.is_lh - 1)) 0 _

private theorem LoadX0Chip.isLhuBinaryConstraint_mem
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_lhu * (input.is_lhu - 1) - 0 ∈
      ((LoadX0Chip.main input).operations offset).constraints := by
  simp only [LoadX0Chip.main, circuit_norm]
  iterate 7 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_lhu * (input.is_lhu - 1)) 0 _

private theorem LoadX0Chip.isLwBinaryConstraint_mem
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_lw * (input.is_lw - 1) - 0 ∈
      ((LoadX0Chip.main input).operations offset).constraints := by
  simp only [LoadX0Chip.main, circuit_norm]
  iterate 8 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_lw * (input.is_lw - 1)) 0 _

private theorem LoadX0Chip.isLwuBinaryConstraint_mem
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_lwu * (input.is_lwu - 1) - 0 ∈
      ((LoadX0Chip.main input).operations offset).constraints := by
  simp only [LoadX0Chip.main, circuit_norm]
  iterate 9 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_lwu * (input.is_lwu - 1)) 0 _

private theorem LoadX0Chip.isLdBinaryConstraint_mem
    (input : Var LoadX0Chip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_ld * (input.is_ld - 1) - 0 ∈
      ((LoadX0Chip.main input).operations offset).constraints := by
  simp only [LoadX0Chip.main, circuit_norm]
  iterate 10 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_ld * (input.is_ld - 1)) 0 _

/-- `Nat.cast` into `ZMod p` is injective below `2 ^ 17 < p`. -/
private theorem natCastSmall_inj {a b : ℕ} (ha : a < 2 ^ 17) (hb : b < 2 ^ 17)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have hp : (2 : ℕ) ^ 17 < p := Fact.out
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv

/-- A real physical LoadX0 row's Program-bus opcode is never the `ECALL` discriminant `50`
(the committed-fragment re-base's per-chip strengthening fact). -/
theorem LoadX0Chip.physicalViewOpcode_ne_ecall (env : Environment (ZMod p))
    (constraints :
      (⟨LoadX0Chip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (real : (LoadX0Chip.physicalView env).is_real = 1) :
    (LoadX0Chip.physicalView env).opcode ≠ (50 : ZMod p) := by
  let input : Var LoadX0Chip.Inputs (ZMod p) := varFromOffset LoadX0Chip.Inputs 0
  let offset := size LoadX0Chip.Inputs
  have mainConstraints : ((LoadX0Chip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have gLb := mainConstraints.1 _ (LoadX0Chip.isLbBinaryConstraint_mem input offset)
  have gLbu := mainConstraints.1 _ (LoadX0Chip.isLbuBinaryConstraint_mem input offset)
  have gLh := mainConstraints.1 _ (LoadX0Chip.isLhBinaryConstraint_mem input offset)
  have gLhu := mainConstraints.1 _ (LoadX0Chip.isLhuBinaryConstraint_mem input offset)
  have gLw := mainConstraints.1 _ (LoadX0Chip.isLwBinaryConstraint_mem input offset)
  have gLwu := mainConstraints.1 _ (LoadX0Chip.isLwuBinaryConstraint_mem input offset)
  have gLd := mainConstraints.1 _ (LoadX0Chip.isLdBinaryConstraint_mem input offset)
  simp only [eval_sub, Expression.eval, sub_zero] at gLb gLbu gLh gLhu gLw gLwu gLd
  obtain ⟨a, ha, hea⟩ := flagNatValue (bool_of_mul_pred gLb)
  obtain ⟨b, hb, heb⟩ := flagNatValue (bool_of_mul_pred gLbu)
  obtain ⟨c, hc, hec⟩ := flagNatValue (bool_of_mul_pred gLh)
  obtain ⟨d, hd, hed⟩ := flagNatValue (bool_of_mul_pred gLhu)
  obtain ⟨e, he, hee⟩ := flagNatValue (bool_of_mul_pred gLw)
  obtain ⟨f, hf, hef⟩ := flagNatValue (bool_of_mul_pred gLwu)
  obtain ⟨g, hg, heg⟩ := flagNatValue (bool_of_mul_pred gLd)
  have inputEq : Eval.eval env input =
      (⟨LoadX0Chip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset LoadX0Chip.Inputs 0 env
  have projLb : (Eval.eval env input).is_lb = Expression.eval env input.is_lb := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadX0Chip.Inputs (ZMod p) => v.is_lb)
        (LoadX0Chip.eval_inputs env input)
  have projLbu : (Eval.eval env input).is_lbu = Expression.eval env input.is_lbu := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadX0Chip.Inputs (ZMod p) => v.is_lbu)
        (LoadX0Chip.eval_inputs env input)
  have projLh : (Eval.eval env input).is_lh = Expression.eval env input.is_lh := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadX0Chip.Inputs (ZMod p) => v.is_lh)
        (LoadX0Chip.eval_inputs env input)
  have projLhu : (Eval.eval env input).is_lhu = Expression.eval env input.is_lhu := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadX0Chip.Inputs (ZMod p) => v.is_lhu)
        (LoadX0Chip.eval_inputs env input)
  have projLw : (Eval.eval env input).is_lw = Expression.eval env input.is_lw := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadX0Chip.Inputs (ZMod p) => v.is_lw)
        (LoadX0Chip.eval_inputs env input)
  have projLwu : (Eval.eval env input).is_lwu = Expression.eval env input.is_lwu := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadX0Chip.Inputs (ZMod p) => v.is_lwu)
        (LoadX0Chip.eval_inputs env input)
  have projLd : (Eval.eval env input).is_ld = Expression.eval env input.is_ld := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadX0Chip.Inputs (ZMod p) => v.is_ld)
        (LoadX0Chip.eval_inputs env input)
  have realSum : Expression.eval env input.is_lb + Expression.eval env input.is_lbu +
      Expression.eval env input.is_lh + Expression.eval env input.is_lhu +
      Expression.eval env input.is_lw + Expression.eval env input.is_lwu +
      Expression.eval env input.is_ld = 1 := by
    have h : (Eval.eval env input).is_lb + (Eval.eval env input).is_lbu +
        (Eval.eval env input).is_lh + (Eval.eval env input).is_lhu +
        (Eval.eval env input).is_lw + (Eval.eval env input).is_lwu +
        (Eval.eval env input).is_ld = 1 := by
      rw [inputEq]; exact real
    rw [projLb, projLbu, projLh, projLhu, projLw, projLwu, projLd] at h
    exact h
  have opcodeEq : (LoadX0Chip.physicalView env).opcode =
      29 * Expression.eval env input.is_lb + 32 * Expression.eval env input.is_lbu +
      30 * Expression.eval env input.is_lh + 33 * Expression.eval env input.is_lhu +
      31 * Expression.eval env input.is_lw + 34 * Expression.eval env input.is_lwu +
      35 * Expression.eval env input.is_ld := by
    have h : (LoadX0Chip.physicalView env).opcode =
        29 * (Eval.eval env input).is_lb + 32 * (Eval.eval env input).is_lbu +
        30 * (Eval.eval env input).is_lh + 33 * (Eval.eval env input).is_lhu +
        31 * (Eval.eval env input).is_lw + 34 * (Eval.eval env input).is_lwu +
        35 * (Eval.eval env input).is_ld := by
      rw [inputEq]; rfl
    rw [projLb, projLbu, projLh, projLhu, projLw, projLwu, projLd] at h
    exact h
  rw [hea, heb, hec, hed, hee, hef, heg] at realSum
  have habSum : a + b + c + d + e + f + g = 1 :=
    natCastSmall_inj (by omega) (by omega) (by exact_mod_cast realSum)
  intro hEq
  rw [opcodeEq, hea, heb, hec, hed, hee, hef, heg] at hEq
  have hcontra : 29 * a + 32 * b + 30 * c + 33 * d + 31 * e + 34 * f + 35 * g = 50 :=
    natCastSmall_inj (by omega) (by omega) (by exact_mod_cast hEq)
  omega

end PhysicalOpcode

end SP1Clean.Soundness
