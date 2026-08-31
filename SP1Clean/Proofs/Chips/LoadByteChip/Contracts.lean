import SP1Clean.Proofs.Chips.LoadByteChip.Bridge
import SP1Clean.Soundness.TypedMemory

/-! # LoadByte — physical routing contract

This file exposes the one structural fact the whole-machine decoder needs from LoadByte's
complete native assertion system: ordinary LB/LBU rows are routed away from `x0`.  The proof
projects the literal `op_a_0 === 0` assertion from the folded `main`; it does not obtain routing
from the semantic `Spec` or from a trace-generator convention.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
private theorem equalityConstraint_mem (x y : Expression (ZMod p)) (offset : ℕ) :
    x - y ∈ ((Gadgets.Equality.main (M := field) (x, y)).operations offset).constraints := by
  simp [Gadgets.Equality.main, Circuit.forEach.operations_eq, circuit_norm]
  rfl

-- Runs at the plain default: the former 1000000 ceiling was ~25x over; measured floor <= 40000.
/-- Project LoadByte's physical non-`x0` route while its circuit input stays folded. -/
theorem LoadByteChip.eval_inputOpA0_eq_zero_of_mainConstraints
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : Operations.ConstraintsHold env
      ((LoadByteChip.main input).operations offset)) :
    Expression.eval env input.adapter.op_a_0 = 0 := by
  have routeConstraint : Expression.eval env (input.adapter.op_a_0 - 0) = 0 := by
    apply constraints.1
    simp only [LoadByteChip.main, circuit_norm]
    right; right; right; right; right; right; right; right; right; right; left
    simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
      Operations.constraints_toFlat, Gadgets.Equality.circuit] using
      equalityConstraint_mem input.adapter.op_a_0 0 _
  rw [eval_sub] at routeConstraint
  simpa only [Expression.eval] using sub_eq_zero.mp routeConstraint

/-! ## Physical opcode discriminant (committed-fragment strengthening) -/

/-- The completed LoadByte columns at one physical component row. -/
noncomputable def LoadByteChip.physicalCols (env : Environment (ZMod p)) :
    LoadByteChip.Columns (ZMod p) :=
  (⟨LoadByteChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env

/-- The completed LoadByte row view at one physical component row. -/
noncomputable def LoadByteChip.physicalView (env : Environment (ZMod p)) :
    Trace.RowView (ZMod p) :=
  LoadByteChip.rowView
    ((⟨LoadByteChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    (LoadByteChip.physicalCols env)

private theorem LoadByteChip.isLbBinaryConstraint_mem
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_lb * (input.is_lb - 1) ∈
      ((LoadByteChip.main input).operations offset).constraints := by
  simp [LoadByteChip.main, circuit_norm]

private theorem LoadByteChip.isLbuBinaryConstraint_mem
    (input : Var LoadByteChip.Inputs (ZMod p)) (offset : ℕ) :
    input.is_lbu * (input.is_lbu - 1) - 0 ∈
      ((LoadByteChip.main input).operations offset).constraints := by
  simp only [LoadByteChip.main, circuit_norm]
  iterate 13 right
  left
  simpa only [FormalAssertion.toSubcircuit, Operations.toNested_toFlat,
    Operations.constraints_toFlat, Gadgets.Equality.circuit] using
    equalityConstraint_mem (input.is_lbu * (input.is_lbu - 1)) 0 _

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

/-- A real physical LoadByte row's Program-bus opcode is never the `ECALL` discriminant `50`
(the committed-fragment re-base's per-chip strengthening fact). -/
theorem LoadByteChip.physicalViewOpcode_ne_ecall (env : Environment (ZMod p))
    (constraints :
      (⟨LoadByteChip.circuit (p := p)⟩ : Component (ZMod p)).operations.ConstraintsHold env)
    (real : (LoadByteChip.physicalView env).is_real = 1) :
    (LoadByteChip.physicalView env).opcode ≠ (50 : ZMod p) := by
  let input : Var LoadByteChip.Inputs (ZMod p) := varFromOffset LoadByteChip.Inputs 0
  let offset := size LoadByteChip.Inputs
  have mainConstraints : ((LoadByteChip.main input).operations offset).ConstraintsHold env :=
    (Component.constraintsHold_iff env).mp constraints
  have gLb := mainConstraints.1 _ (LoadByteChip.isLbBinaryConstraint_mem input offset)
  have gLbu := mainConstraints.1 _ (LoadByteChip.isLbuBinaryConstraint_mem input offset)
  simp only [eval_sub, Expression.eval, sub_zero] at gLb gLbu
  obtain ⟨a, ha, hea⟩ := flagNatValue (bool_of_mul_pred gLb)
  obtain ⟨b, hb, heb⟩ := flagNatValue (bool_of_mul_pred gLbu)
  have inputEq : Eval.eval env input =
      (⟨LoadByteChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset LoadByteChip.Inputs 0 env
  have projLb : (Eval.eval env input).is_lb = Expression.eval env input.is_lb := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadByteChip.Inputs (ZMod p) => v.is_lb)
        (LoadByteChip.eval_inputs env input)
  have projLbu : (Eval.eval env input).is_lbu = Expression.eval env input.is_lbu := by
    simpa only [CircuitType.eval_expr] using
      congrArg (fun v : LoadByteChip.Inputs (ZMod p) => v.is_lbu)
        (LoadByteChip.eval_inputs env input)
  have realSum : Expression.eval env input.is_lb + Expression.eval env input.is_lbu = 1 := by
    have h : (Eval.eval env input).is_lb + (Eval.eval env input).is_lbu = 1 := by
      rw [inputEq]; exact real
    rw [projLb, projLbu] at h
    exact h
  have opcodeEq : (LoadByteChip.physicalView env).opcode =
      Expression.eval env input.is_lb * 29 + Expression.eval env input.is_lbu * 32 := by
    have h : (LoadByteChip.physicalView env).opcode =
        (Eval.eval env input).is_lb * 29 + (Eval.eval env input).is_lbu * 32 := by
      rw [inputEq]; rfl
    rw [projLb, projLbu] at h
    exact h
  rw [hea, heb] at realSum
  have habSum : a + b = 1 :=
    natCastSmall_inj (by omega) (by omega) (by exact_mod_cast realSum)
  intro hEq
  rw [opcodeEq, hea, heb] at hEq
  have hcontra : a * 29 + b * 32 = 50 :=
    natCastSmall_inj (by omega) (by omega) (by exact_mod_cast hEq)
  omega

end SP1Clean.Soundness
