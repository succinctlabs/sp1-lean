import SP1Clean.Proofs.Chips.LoadHalfChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # LoadHalf — physical routing contract -/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

-- Runs at the plain default: the former 1000000 ceiling was ~25x over; measured floor <= 40000.
/-- Project LoadHalf's literal `op_a_0 === 0` assertion from the folded native `main`. -/
theorem LoadHalfChip.eval_inputOpA0_eq_zero_of_mainConstraints
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env
      ((LoadHalfChip.main input).operations offset)) :
    Expression.eval env input.adapter.op_a_0 = 0 := by
  have routeConstraint : Expression.eval env (input.adapter.op_a_0 - 0) = 0 := by
    apply constraints.1
    simp only [LoadHalfChip.main, circuit_norm]
    right; right; right; right; right; right; right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem input.adapter.op_a_0 0 _
  rw [eval_sub] at routeConstraint
  simpa only [Expression.eval] using sub_eq_zero.mp routeConstraint

/-! ## Physical opcode discriminant (committed-fragment strengthening) -/

/-- The completed LoadHalf columns at one physical component row. -/
noncomputable def LoadHalfChip.physicalCols (env : Environment (ZMod p)) :
    LoadHalfChip.Columns (ZMod p) :=
  (⟨LoadHalfChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env

/-- The completed LoadHalf row view at one physical component row. -/
noncomputable def LoadHalfChip.physicalView (env : Environment (ZMod p)) :
    Trace.RowView (ZMod p) :=
  LoadHalfChip.rowView
    ((⟨LoadHalfChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    (LoadHalfChip.physicalCols env)

private theorem LoadHalfChip.isLhBinaryConstraint_mem
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_lh * (input.is_lh - 1) - 0 ∈
      ((LoadHalfChip.main input).operations offset).constraints := by
  simp only [LoadHalfChip.main, circuit_norm]
  iterate 12 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_lh * (input.is_lh - 1)) 0 _

private theorem LoadHalfChip.isLhuBinaryConstraint_mem
    (input : Var LoadHalfChip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_lhu * (input.is_lhu - 1) - 0 ∈
      ((LoadHalfChip.main input).operations offset).constraints := by
  simp only [LoadHalfChip.main, circuit_norm]
  iterate 13 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_lhu * (input.is_lhu - 1)) 0 _

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

/-- A real physical LoadHalf row's Program-bus opcode is never the `ECALL` discriminant `50`
(the committed-fragment re-base's per-chip strengthening fact). -/
theorem LoadHalfChip.physicalViewOpcode_ne_ecall (env : Environment (ZMod p))
    (constraints :
      (⟨LoadHalfChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (real : (LoadHalfChip.physicalView env).is_real = 1) :
    (LoadHalfChip.physicalView env).opcode ≠ (50 : ZMod p) := by
  let input : Var LoadHalfChip.Inputs (ZMod p) := varFromOffset LoadHalfChip.Inputs 0
  let offset := size LoadHalfChip.Inputs
  have mainConstraints : ((LoadHalfChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have gLh := mainConstraints.1 _ (LoadHalfChip.isLhBinaryConstraint_mem input offset)
  have gLhu := mainConstraints.1 _ (LoadHalfChip.isLhuBinaryConstraint_mem input offset)
  simp only [eval_sub, Expression.eval, sub_zero] at gLh gLhu
  obtain ⟨a, ha, hea⟩ := flagNatValue (bool_of_mul_pred gLh)
  obtain ⟨b, hb, heb⟩ := flagNatValue (bool_of_mul_pred gLhu)
  have inputEq : Eval.eval env input =
      (⟨LoadHalfChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset LoadHalfChip.Inputs 0 env
  have projLh : (Eval.eval env input).is_lh = Expression.eval env input.is_lh := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadHalfChip.Inputs (ZMod p) => v.is_lh)
        (LoadHalfChip.eval_inputs env input)
  have projLhu : (Eval.eval env input).is_lhu = Expression.eval env input.is_lhu := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadHalfChip.Inputs (ZMod p) => v.is_lhu)
        (LoadHalfChip.eval_inputs env input)
  have realSum : Expression.eval env input.is_lh + Expression.eval env input.is_lhu = 1 := by
    have h : (Eval.eval env input).is_lh + (Eval.eval env input).is_lhu = 1 := by
      rw [inputEq]; exact real
    rw [projLh, projLhu] at h
    exact h
  have opcodeEq : (LoadHalfChip.physicalView env).opcode =
      Expression.eval env input.is_lh * 30 + Expression.eval env input.is_lhu * 33 := by
    have h : (LoadHalfChip.physicalView env).opcode =
        (Eval.eval env input).is_lh * 30 + (Eval.eval env input).is_lhu * 33 := by
      rw [inputEq]; rfl
    rw [projLh, projLhu] at h
    exact h
  rw [hea, heb] at realSum
  have habSum : a + b = 1 :=
    natCastSmall_inj (by omega) (by omega) (by push_cast; exact realSum)
  intro hEq
  rw [opcodeEq, hea, heb] at hEq
  have hcontra : a * 30 + b * 33 = 50 :=
    natCastSmall_inj (by omega) (by omega) (by exact_mod_cast hEq)
  omega

end SP1Clean.Soundness
