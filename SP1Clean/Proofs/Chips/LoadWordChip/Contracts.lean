import SP1Clean.Proofs.Chips.LoadWordChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # LoadWord — physical routing contract -/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

-- Runs at the plain default: the former 1000000 ceiling was ~25x over; measured floor <= 40000.
/-- Project LoadWord's literal `op_a_0 === 0` assertion from the folded native `main`. -/
theorem LoadWordChip.eval_inputOpA0_eq_zero_of_mainConstraints
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env
      ((LoadWordChip.main input).operations offset)) :
    Expression.eval env input.adapter.op_a_0 = 0 := by
  have routeConstraint : Expression.eval env (input.adapter.op_a_0 - 0) = 0 := by
    apply constraints.1
    simp only [LoadWordChip.main, circuit_norm]
    right; right; right; right; right; right; right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem input.adapter.op_a_0 0 _
  rw [eval_sub] at routeConstraint
  simpa only [Expression.eval] using sub_eq_zero.mp routeConstraint

/-! ## Physical opcode discriminant (committed-fragment strengthening) -/

/-- The completed LoadWord columns at one physical component row. -/
noncomputable def LoadWordChip.physicalCols (env : Environment (ZMod p)) :
    LoadWordChip.Columns (ZMod p) :=
  (⟨LoadWordChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env

/-- The completed LoadWord row view at one physical component row. -/
noncomputable def LoadWordChip.physicalView (env : Environment (ZMod p)) :
    Trace.RowView (ZMod p) :=
  LoadWordChip.rowView
    ((⟨LoadWordChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    (LoadWordChip.physicalCols env)

private theorem LoadWordChip.isLwBinaryConstraint_mem
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_lw * (input.is_lw - 1) - 0 ∈
      ((LoadWordChip.main input).operations offset).constraints := by
  simp only [LoadWordChip.main, circuit_norm]
  iterate 12 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_lw * (input.is_lw - 1)) 0 _

private theorem LoadWordChip.isLwuBinaryConstraint_mem
    (input : Var LoadWordChip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_lwu * (input.is_lwu - 1) - 0 ∈
      ((LoadWordChip.main input).operations offset).constraints := by
  simp only [LoadWordChip.main, circuit_norm]
  iterate 13 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_lwu * (input.is_lwu - 1)) 0 _

omit [Fact (2 ^ 17 < p)] in
/-- Lift a binary field flag to its `ℕ` value. -/
private theorem flagNatValue {x : ZMod p} (hx : x = 0 ∨ x = 1) :
    ∃ b : ℕ, b ≤ 1 ∧ x = (b : ZMod p) := by
  rcases hx with rfl | rfl
  · exact ⟨0, Nat.zero_le 1, by norm_num⟩
  · exact ⟨1, le_rfl, by norm_num⟩

/-- `Nat.cast` into `ZMod p` is injective below `2 ^ 17 < p`. -/
private theorem natCastSmall_inj {a b : ℕ} (ha : a < 2 ^ 17) (hb : b < 2 ^ 17)
    (h : (a : ZMod p) = (b : ZMod p)) : a = b := by
  have hp : (2 : ℕ) ^ 17 < p := Fact.out
  have hv := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at hv

/-- A real physical LoadWord row's Program-bus opcode is never the `ECALL` discriminant `50`
(the committed-fragment re-base's per-chip strengthening fact). -/
theorem LoadWordChip.physicalViewOpcode_ne_ecall (env : Environment (ZMod p))
    (constraints :
      (⟨LoadWordChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (real : (LoadWordChip.physicalView env).is_real = 1) :
    (LoadWordChip.physicalView env).opcode ≠ (50 : ZMod p) := by
  let input : Var LoadWordChip.Inputs (ZMod p) := varFromOffset LoadWordChip.Inputs 0
  let offset := size LoadWordChip.Inputs
  have mainConstraints : ((LoadWordChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have gLw := mainConstraints.1 _ (LoadWordChip.isLwBinaryConstraint_mem input offset)
  have gLwu := mainConstraints.1 _ (LoadWordChip.isLwuBinaryConstraint_mem input offset)
  simp only [eval_sub, Expression.eval, sub_zero] at gLw gLwu
  obtain ⟨a, ha, hea⟩ := flagNatValue (bool_of_mul_pred gLw)
  obtain ⟨b, hb, heb⟩ := flagNatValue (bool_of_mul_pred gLwu)
  have inputEq : Eval.eval env input =
      (⟨LoadWordChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset LoadWordChip.Inputs 0 env
  have projLw : (Eval.eval env input).is_lw = Expression.eval env input.is_lw := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadWordChip.Inputs (ZMod p) => v.is_lw)
        (LoadWordChip.eval_inputs env input)
  have projLwu : (Eval.eval env input).is_lwu = Expression.eval env input.is_lwu := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadWordChip.Inputs (ZMod p) => v.is_lwu)
        (LoadWordChip.eval_inputs env input)
  have realSum : Expression.eval env input.is_lw + Expression.eval env input.is_lwu = 1 := by
    have h : (Eval.eval env input).is_lw + (Eval.eval env input).is_lwu = 1 := by
      rw [inputEq]; exact real
    rw [projLw, projLwu] at h
    exact h
  have opcodeEq : (LoadWordChip.physicalView env).opcode =
      Expression.eval env input.is_lw * 31 + Expression.eval env input.is_lwu * 34 := by
    have h : (LoadWordChip.physicalView env).opcode =
        (Eval.eval env input).is_lw * 31 + (Eval.eval env input).is_lwu * 34 := by
      rw [inputEq]; rfl
    rw [projLw, projLwu] at h
    exact h
  rw [hea, heb] at realSum
  have habSum : a + b = 1 :=
    natCastSmall_inj (by omega) (by omega) (by exact_mod_cast realSum)
  intro hEq
  rw [opcodeEq, hea, heb] at hEq
  have hcontra : a * 31 + b * 34 = 50 :=
    natCastSmall_inj (by omega) (by omega) (by exact_mod_cast hEq)
  omega

end SP1Clean.Soundness
