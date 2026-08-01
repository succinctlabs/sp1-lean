import SP1Clean.Native.Operations.DivRemOperation.Core
import SP1Clean.FormalModel.Contracts.DivRem
import SP1Clean.Proofs.Chips.DivRemChip.Extract
import SP1Clean.Proofs.CircuitProofStart

/-! # `DivRemCore` — the `FormalAssertion` bundle (soundness / completeness / contract)

The DivRem product/own-assert/byte-range assertion cluster as a Clean `FormalAssertion` over the
whole committed row (`DivRemChip.Columns`). The circuit
(`Native/Operations/DivRemOperation/Core.lean`) witnesses nothing, so both directions are
input-level repackaging: soundness maps the two composed `MulOperation` implications, the eight
product-glue equations, the own-assert tail (through the `ownAsserts_map_eval` var↔value
transport), and the 32 gated byte-pull guarantees onto the matching `CoreSpec` conjuncts — deriving
the selection block (`is_real`/flag binariness, one-hot, `SelectionSpec`) from the gate equations
inside the own-assert tail via the `OwnAsserts.lean` membership lemmas — and completeness feeds
each constraint back from the same conjuncts. -/

namespace SP1Clean.DivRemCore

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

set_option linter.unusedSectionVars false in
private lemma evalSub (env : Environment (ZMod p)) (a b : Expression (ZMod p)) :
    Expression.eval env (a - b) = Expression.eval env a - Expression.eval env b := by
  show Expression.eval env (.add a (.mul (.const (-1)) b)) = _
  simp only [Expression.eval]
  ring

set_option linter.unusedSectionVars false in
/-- Pointwise form of a `Vector.map (Expression.eval env)` pin, i.e. one of the vector-valued
`circuit_proof_start` `h_input` components read at a single index. The three transport proofs below
need 176 such instances between them; each is only ever consumed as a `simp only` rewrite rule, so
the inferred type is exactly the hand-written ascription this replaces. -/
private lemma eval_getElem {n : ℕ} {env : Environment (ZMod p)}
    {v : Vector (Expression (ZMod p)) n} {w : Vector (ZMod p) n}
    (h : Vector.map (Expression.eval env) v = w) (i : ℕ) (hi : i < n) :
    Expression.eval env v[i] = w[i] := by
  rw [← h, Vector.getElem_map]

/-- **Var↔value transport for the own-assert tail.** Mapping `Expression.eval` over the
carrier-generic `ownAsserts` chain at `R = Expression (ZMod p)` yields the same chain at
`R = ZMod p`, given the per-field evaluation pins (exactly the components of a
`circuit_proof_start` `h_input`). This is the one lemma that lets `CoreSpec`'s raw
`OwnAssertsHold` bundle be stated over the evaluated row while both `FormalAssertion`
directions stay pure repackaging. -/
theorem ownAsserts_map_eval (env : Environment (ZMod p)) (colsV : Var DivRemChip.Columns (ZMod p))
    (cols : DivRemChip.Columns (ZMod p))
    (pDiv : Expression.eval env colsV.is_div = cols.is_div)
    (pDivu : Expression.eval env colsV.is_divu = cols.is_divu)
    (pRem : Expression.eval env colsV.is_rem = cols.is_rem)
    (pRemu : Expression.eval env colsV.is_remu = cols.is_remu)
    (pDivw : Expression.eval env colsV.is_divw = cols.is_divw)
    (pRemw : Expression.eval env colsV.is_remw = cols.is_remw)
    (pDivuw : Expression.eval env colsV.is_divuw = cols.is_divuw)
    (pRemuw : Expression.eval env colsV.is_remuw = cols.is_remuw)
    (pIr : Expression.eval env colsV.is_real = cols.is_real)
    (pIrnw : Expression.eval env colsV.is_real_not_word = cols.is_real_not_word)
    (pOv : Expression.eval env colsV.is_overflow = cols.is_overflow)
    (pBn : Expression.eval env colsV.b_neg = cols.b_neg)
    (pBnno : Expression.eval env colsV.b_neg_not_overflow = cols.b_neg_not_overflow)
    (pBnnno : Expression.eval env colsV.b_not_neg_not_overflow = cols.b_not_neg_not_overflow)
    (pRn : Expression.eval env colsV.rem_neg = cols.rem_neg)
    (pCn : Expression.eval env colsV.c_neg = cols.c_neg)
    (pAce : Expression.eval env colsV.abs_c_alu_event = cols.abs_c_alu_event)
    (pAre : Expression.eval env colsV.abs_rem_alu_event = cols.abs_rem_alu_event)
    (pRcm : Expression.eval env colsV.remainder_check_multiplicity = cols.remainder_check_multiplicity)
    (pBm : Expression.eval env colsV.b_msb.msb = cols.b_msb.msb)
    (pRm : Expression.eval env colsV.rem_msb.msb = cols.rem_msb.msb)
    (pCm : Expression.eval env colsV.c_msb.msb = cols.c_msb.msb)
    (pQm : Expression.eval env colsV.quot_msb.msb = cols.quot_msb.msb)
    (pOvb : Expression.eval env colsV.is_overflow_b.is_diff_zero.result = cols.is_overflow_b.is_diff_zero.result)
    (pOvc : Expression.eval env colsV.is_overflow_c.is_diff_zero.result = cols.is_overflow_c.is_diff_zero.result)
    (pIsc0 : Expression.eval env colsV.is_c_0.result = cols.is_c_0.result)
    (pLtb : Expression.eval env colsV.remainder_lt_operation.u16_compare_operation.bit = cols.remainder_lt_operation.u16_compare_operation.bit)
    (pOpa0 : Expression.eval env colsV.adapter.op_a_0 = cols.adapter.op_a_0)
    (vBpv : Vector.map (Expression.eval env) colsV.adapter.op_b_memory.prev_value = cols.adapter.op_b_memory.prev_value)
    (vCpv : Vector.map (Expression.eval env) colsV.adapter.op_c_memory.prev_value = cols.adapter.op_c_memory.prev_value)
    (vA : Vector.map (Expression.eval env) colsV.a = cols.a)
    (vB : Vector.map (Expression.eval env) colsV.b = cols.b)
    (vC : Vector.map (Expression.eval env) colsV.c = cols.c)
    (vQ : Vector.map (Expression.eval env) colsV.quotient = cols.quotient)
    (vQC : Vector.map (Expression.eval env) colsV.quotient_comp = cols.quotient_comp)
    (vR : Vector.map (Expression.eval env) colsV.remainder = cols.remainder)
    (vRC : Vector.map (Expression.eval env) colsV.remainder_comp = cols.remainder_comp)
    (vAR : Vector.map (Expression.eval env) colsV.abs_remainder = cols.abs_remainder)
    (vAC : Vector.map (Expression.eval env) colsV.abs_c = cols.abs_c)
    (vMax : Vector.map (Expression.eval env) colsV.max_abs_c_or_1 = cols.max_abs_c_or_1)
    (vCnegV : Vector.map (Expression.eval env) colsV.c_neg_operation.value = cols.c_neg_operation.value)
    (vRnegV : Vector.map (Expression.eval env) colsV.rem_neg_operation.value = cols.rem_neg_operation.value)
    (vCtq : Vector.map (Expression.eval env) colsV.c_times_quotient = cols.c_times_quotient)
    (vCarry : Vector.map (Expression.eval env) colsV.carry = cols.carry) :
    (DivRemChip.ownAsserts colsV).map (Expression.eval env)
      = DivRemChip.ownAsserts cols := by
  have gvBpv := eval_getElem vBpv
  have gvCpv := eval_getElem vCpv
  have gvA := eval_getElem vA
  have gvB := eval_getElem vB
  have gvC := eval_getElem vC
  have gvQ := eval_getElem vQ
  have gvQC := eval_getElem vQC
  have gvR := eval_getElem vR
  have gvRC := eval_getElem vRC
  have gvAR := eval_getElem vAR
  have gvAC := eval_getElem vAC
  have gvMax := eval_getElem vMax
  have gvCnegV := eval_getElem vCnegV
  have gvRnegV := eval_getElem vRnegV
  have gvCtq := eval_getElem vCtq
  have gvCarry := eval_getElem vCarry
  simp only [DivRemChip.ownAsserts, List.map_cons, List.map_nil, evalSub, Expression.eval,
    pDiv, pDivu, pRem, pRemu, pDivw, pRemw, pDivuw, pRemuw, pIr, pIrnw, pOv, pBn, pBnno, pBnnno,
    pRn, pCn, pAce, pAre, pRcm, pBm, pRm, pCm, pQm, pOvb, pOvc, pIsc0, pLtb, pOpa0,
    gvBpv, gvCpv, gvA, gvB, gvC, gvQ, gvQC, gvR, gvRC, gvAR, gvAC, gvMax, gvCnegV, gvRnegV,
    gvCtq, gvCarry]

/-- Soundness-direction transport: the var-level own-assert equations (the `assertZeros
(ownAsserts cols)` block's `h_holds` content) give the evaluated-row `OwnAssertsHold` bundle.
`colsV`/`cols` are implicit so both solve structurally from `h` and the goal — the pins then
land on fully-instantiated fields. -/
theorem ownAssertsHold_of_forall (env : Environment (ZMod p)) {colsV : Var DivRemChip.Columns (ZMod p)}
    {cols : DivRemChip.Columns (ZMod p)}
    (h : ∀ e ∈ DivRemChip.ownAsserts colsV, Expression.eval env e = 0)
        (pDiv : Expression.eval env colsV.is_div = cols.is_div)
    (pDivu : Expression.eval env colsV.is_divu = cols.is_divu)
    (pRem : Expression.eval env colsV.is_rem = cols.is_rem)
    (pRemu : Expression.eval env colsV.is_remu = cols.is_remu)
    (pDivw : Expression.eval env colsV.is_divw = cols.is_divw)
    (pRemw : Expression.eval env colsV.is_remw = cols.is_remw)
    (pDivuw : Expression.eval env colsV.is_divuw = cols.is_divuw)
    (pRemuw : Expression.eval env colsV.is_remuw = cols.is_remuw)
    (pIr : Expression.eval env colsV.is_real = cols.is_real)
    (pIrnw : Expression.eval env colsV.is_real_not_word = cols.is_real_not_word)
    (pOv : Expression.eval env colsV.is_overflow = cols.is_overflow)
    (pBn : Expression.eval env colsV.b_neg = cols.b_neg)
    (pBnno : Expression.eval env colsV.b_neg_not_overflow = cols.b_neg_not_overflow)
    (pBnnno : Expression.eval env colsV.b_not_neg_not_overflow = cols.b_not_neg_not_overflow)
    (pRn : Expression.eval env colsV.rem_neg = cols.rem_neg)
    (pCn : Expression.eval env colsV.c_neg = cols.c_neg)
    (pAce : Expression.eval env colsV.abs_c_alu_event = cols.abs_c_alu_event)
    (pAre : Expression.eval env colsV.abs_rem_alu_event = cols.abs_rem_alu_event)
    (pRcm : Expression.eval env colsV.remainder_check_multiplicity = cols.remainder_check_multiplicity)
    (pBm : Expression.eval env colsV.b_msb.msb = cols.b_msb.msb)
    (pRm : Expression.eval env colsV.rem_msb.msb = cols.rem_msb.msb)
    (pCm : Expression.eval env colsV.c_msb.msb = cols.c_msb.msb)
    (pQm : Expression.eval env colsV.quot_msb.msb = cols.quot_msb.msb)
    (pOvb : Expression.eval env colsV.is_overflow_b.is_diff_zero.result = cols.is_overflow_b.is_diff_zero.result)
    (pOvc : Expression.eval env colsV.is_overflow_c.is_diff_zero.result = cols.is_overflow_c.is_diff_zero.result)
    (pIsc0 : Expression.eval env colsV.is_c_0.result = cols.is_c_0.result)
    (pLtb : Expression.eval env colsV.remainder_lt_operation.u16_compare_operation.bit = cols.remainder_lt_operation.u16_compare_operation.bit)
    (pOpa0 : Expression.eval env colsV.adapter.op_a_0 = cols.adapter.op_a_0)
    (vBpv : Vector.map (Expression.eval env) colsV.adapter.op_b_memory.prev_value = cols.adapter.op_b_memory.prev_value)
    (vCpv : Vector.map (Expression.eval env) colsV.adapter.op_c_memory.prev_value = cols.adapter.op_c_memory.prev_value)
    (vA : Vector.map (Expression.eval env) colsV.a = cols.a)
    (vB : Vector.map (Expression.eval env) colsV.b = cols.b)
    (vC : Vector.map (Expression.eval env) colsV.c = cols.c)
    (vQ : Vector.map (Expression.eval env) colsV.quotient = cols.quotient)
    (vQC : Vector.map (Expression.eval env) colsV.quotient_comp = cols.quotient_comp)
    (vR : Vector.map (Expression.eval env) colsV.remainder = cols.remainder)
    (vRC : Vector.map (Expression.eval env) colsV.remainder_comp = cols.remainder_comp)
    (vAR : Vector.map (Expression.eval env) colsV.abs_remainder = cols.abs_remainder)
    (vAC : Vector.map (Expression.eval env) colsV.abs_c = cols.abs_c)
    (vMax : Vector.map (Expression.eval env) colsV.max_abs_c_or_1 = cols.max_abs_c_or_1)
    (vCnegV : Vector.map (Expression.eval env) colsV.c_neg_operation.value = cols.c_neg_operation.value)
    (vRnegV : Vector.map (Expression.eval env) colsV.rem_neg_operation.value = cols.rem_neg_operation.value)
    (vCtq : Vector.map (Expression.eval env) colsV.c_times_quotient = cols.c_times_quotient)
    (vCarry : Vector.map (Expression.eval env) colsV.carry = cols.carry) :
    OwnAssertsHold cols := by
  intro x hx
  rw [← ownAsserts_map_eval env colsV cols pDiv pDivu pRem pRemu pDivw pRemw pDivuw pRemuw pIr pIrnw pOv pBn pBnno pBnnno pRn pCn pAce pAre pRcm pBm pRm pCm pQm pOvb pOvc pIsc0 pLtb pOpa0 vBpv vCpv vA vB vC vQ vQC vR vRC vAR vAC vMax vCnegV vRnegV vCtq vCarry] at hx
  obtain ⟨e, he, rfl⟩ := List.mem_map.mp hx
  exact h e he

/-- Completeness-direction transport: the evaluated-row `OwnAssertsHold` bundle discharges the
var-level own-assert equations. -/
theorem forall_of_ownAssertsHold (env : Environment (ZMod p)) {colsV : Var DivRemChip.Columns (ZMod p)}
    {cols : DivRemChip.Columns (ZMod p)}
    (h : OwnAssertsHold cols)
        (pDiv : Expression.eval env colsV.is_div = cols.is_div)
    (pDivu : Expression.eval env colsV.is_divu = cols.is_divu)
    (pRem : Expression.eval env colsV.is_rem = cols.is_rem)
    (pRemu : Expression.eval env colsV.is_remu = cols.is_remu)
    (pDivw : Expression.eval env colsV.is_divw = cols.is_divw)
    (pRemw : Expression.eval env colsV.is_remw = cols.is_remw)
    (pDivuw : Expression.eval env colsV.is_divuw = cols.is_divuw)
    (pRemuw : Expression.eval env colsV.is_remuw = cols.is_remuw)
    (pIr : Expression.eval env colsV.is_real = cols.is_real)
    (pIrnw : Expression.eval env colsV.is_real_not_word = cols.is_real_not_word)
    (pOv : Expression.eval env colsV.is_overflow = cols.is_overflow)
    (pBn : Expression.eval env colsV.b_neg = cols.b_neg)
    (pBnno : Expression.eval env colsV.b_neg_not_overflow = cols.b_neg_not_overflow)
    (pBnnno : Expression.eval env colsV.b_not_neg_not_overflow = cols.b_not_neg_not_overflow)
    (pRn : Expression.eval env colsV.rem_neg = cols.rem_neg)
    (pCn : Expression.eval env colsV.c_neg = cols.c_neg)
    (pAce : Expression.eval env colsV.abs_c_alu_event = cols.abs_c_alu_event)
    (pAre : Expression.eval env colsV.abs_rem_alu_event = cols.abs_rem_alu_event)
    (pRcm : Expression.eval env colsV.remainder_check_multiplicity = cols.remainder_check_multiplicity)
    (pBm : Expression.eval env colsV.b_msb.msb = cols.b_msb.msb)
    (pRm : Expression.eval env colsV.rem_msb.msb = cols.rem_msb.msb)
    (pCm : Expression.eval env colsV.c_msb.msb = cols.c_msb.msb)
    (pQm : Expression.eval env colsV.quot_msb.msb = cols.quot_msb.msb)
    (pOvb : Expression.eval env colsV.is_overflow_b.is_diff_zero.result = cols.is_overflow_b.is_diff_zero.result)
    (pOvc : Expression.eval env colsV.is_overflow_c.is_diff_zero.result = cols.is_overflow_c.is_diff_zero.result)
    (pIsc0 : Expression.eval env colsV.is_c_0.result = cols.is_c_0.result)
    (pLtb : Expression.eval env colsV.remainder_lt_operation.u16_compare_operation.bit = cols.remainder_lt_operation.u16_compare_operation.bit)
    (pOpa0 : Expression.eval env colsV.adapter.op_a_0 = cols.adapter.op_a_0)
    (vBpv : Vector.map (Expression.eval env) colsV.adapter.op_b_memory.prev_value = cols.adapter.op_b_memory.prev_value)
    (vCpv : Vector.map (Expression.eval env) colsV.adapter.op_c_memory.prev_value = cols.adapter.op_c_memory.prev_value)
    (vA : Vector.map (Expression.eval env) colsV.a = cols.a)
    (vB : Vector.map (Expression.eval env) colsV.b = cols.b)
    (vC : Vector.map (Expression.eval env) colsV.c = cols.c)
    (vQ : Vector.map (Expression.eval env) colsV.quotient = cols.quotient)
    (vQC : Vector.map (Expression.eval env) colsV.quotient_comp = cols.quotient_comp)
    (vR : Vector.map (Expression.eval env) colsV.remainder = cols.remainder)
    (vRC : Vector.map (Expression.eval env) colsV.remainder_comp = cols.remainder_comp)
    (vAR : Vector.map (Expression.eval env) colsV.abs_remainder = cols.abs_remainder)
    (vAC : Vector.map (Expression.eval env) colsV.abs_c = cols.abs_c)
    (vMax : Vector.map (Expression.eval env) colsV.max_abs_c_or_1 = cols.max_abs_c_or_1)
    (vCnegV : Vector.map (Expression.eval env) colsV.c_neg_operation.value = cols.c_neg_operation.value)
    (vRnegV : Vector.map (Expression.eval env) colsV.rem_neg_operation.value = cols.rem_neg_operation.value)
    (vCtq : Vector.map (Expression.eval env) colsV.c_times_quotient = cols.c_times_quotient)
    (vCarry : Vector.map (Expression.eval env) colsV.carry = cols.carry) :
    ∀ e ∈ DivRemChip.ownAsserts colsV, Expression.eval env e = 0 := by
  intro e he
  have hx : Expression.eval env e ∈ (DivRemChip.ownAsserts colsV).map (Expression.eval env) :=
    List.mem_map_of_mem he
  rw [ownAsserts_map_eval env colsV cols pDiv pDivu pRem pRemu pDivw pRemw pDivuw pRemuw pIr pIrnw pOv pBn pBnno pBnnno pRn pCn pAce pAre pRcm pBm pRm pCm pQm pOvb pOvc pIsc0 pLtb pOpa0 vBpv vCpv vA vB vC vQ vQC vR vRC vAR vAC vMax vCnegV vRnegV vCtq vCarry] at hx
  exact h _ hx


/-- A width-16 `Range` byte-table row from a `< 2^16` bound (the completeness direction of the
byte-pull guarantees; numeral-width sibling of `Model/ByteTable`'s `byteRowSpec_range`). -/
private lemma byteRowSpec_of_isU16 {v : ZMod p} (h : v.val < 2 ^ 16) :
    ByteRowSpec (⟨6, v, 16, 0⟩ : ByteRow (ZMod p)) := by
  refine ⟨ByteOpcode.Range, by norm_cast, ?_⟩
  simp only [ByteOpcode.constrain, DivRemChip.val_16_zmod_p]
  exact h

set_option linter.unusedSectionVars false in
/-- One-hot flags select a committed case: with all eight variant flags binary and their `val`s
summing to one, some `Case` carries flag `1` and every other flag is `0`. -/
theorem selection_of_flags {cols : DivRemChip.Columns (ZMod p)}
    (b0 : cols.is_div = 0 ∨ cols.is_div = 1) (b1 : cols.is_divu = 0 ∨ cols.is_divu = 1)
    (b2 : cols.is_rem = 0 ∨ cols.is_rem = 1) (b3 : cols.is_remu = 0 ∨ cols.is_remu = 1)
    (b4 : cols.is_divw = 0 ∨ cols.is_divw = 1) (b5 : cols.is_remw = 0 ∨ cols.is_remw = 1)
    (b6 : cols.is_divuw = 0 ∨ cols.is_divuw = 1) (b7 : cols.is_remuw = 0 ∨ cols.is_remuw = 1)
    (hsum : cols.is_div.val + cols.is_divu.val + cols.is_rem.val + cols.is_remu.val
      + cols.is_divw.val + cols.is_remw.val + cols.is_divuw.val + cols.is_remuw.val = 1) :
    ∃ case, DivRemContract.Selected cols case := by
  have hval1 : ∀ x : ZMod p, (x = 0 ∨ x = 1) → x.val = 1 → x = 1 := by
    rintro x (rfl | rfl) h
    · simp [ZMod.val_zero] at h
    · rfl
  have hval0 : ∀ x : ZMod p, x.val = 0 → x = 0 := fun x h => (ZMod.val_eq_zero x).mp h
  have h0 := bool_val_le b0
  have h1 := bool_val_le b1
  have h2 := bool_val_le b2
  have h3 := bool_val_le b3
  have h4 := bool_val_le b4
  have h5 := bool_val_le b5
  have h6 := bool_val_le b6
  have h7 := bool_val_le b7
  have hcase : cols.is_div.val = 1 ∨ cols.is_divu.val = 1 ∨ cols.is_rem.val = 1 ∨
      cols.is_remu.val = 1 ∨ cols.is_divw.val = 1 ∨ cols.is_remw.val = 1 ∨
      cols.is_divuw.val = 1 ∨ cols.is_remuw.val = 1 := by omega
  rcases hcase with h | h | h | h | h | h | h | h
  · refine ⟨.div, hval1 _ b0 h, fun other hne => ?_⟩
    cases other <;> dsimp only [DivRemContract.Case.flag] <;>
      first | exact absurd rfl hne | exact hval0 _ (by omega)
  · refine ⟨.divu, hval1 _ b1 h, fun other hne => ?_⟩
    cases other <;> dsimp only [DivRemContract.Case.flag] <;>
      first | exact absurd rfl hne | exact hval0 _ (by omega)
  · refine ⟨.rem, hval1 _ b2 h, fun other hne => ?_⟩
    cases other <;> dsimp only [DivRemContract.Case.flag] <;>
      first | exact absurd rfl hne | exact hval0 _ (by omega)
  · refine ⟨.remu, hval1 _ b3 h, fun other hne => ?_⟩
    cases other <;> dsimp only [DivRemContract.Case.flag] <;>
      first | exact absurd rfl hne | exact hval0 _ (by omega)
  · refine ⟨.divw, hval1 _ b4 h, fun other hne => ?_⟩
    cases other <;> dsimp only [DivRemContract.Case.flag] <;>
      first | exact absurd rfl hne | exact hval0 _ (by omega)
  · refine ⟨.remw, hval1 _ b5 h, fun other hne => ?_⟩
    cases other <;> dsimp only [DivRemContract.Case.flag] <;>
      first | exact absurd rfl hne | exact hval0 _ (by omega)
  · refine ⟨.divuw, hval1 _ b6 h, fun other hne => ?_⟩
    cases other <;> dsimp only [DivRemContract.Case.flag] <;>
      first | exact absurd rfl hne | exact hval0 _ (by omega)
  · refine ⟨.remuw, hval1 _ b7 h, fun other hne => ?_⟩
    cases other <;> dsimp only [DivRemContract.Case.flag] <;>
      first | exact absurd rfl hne | exact hval0 _ (by omega)

/-- The core cluster is self-contained. Its composed multiplications recover operand limb bounds
from their own safe byte-decomposition pulls, while the gate/flag facts come from the core's
own-assert tail. No range fact has to be assumed by the parent chip. -/
def Assumptions (_cols : DivRemChip.Columns (ZMod p)) : Prop := True

set_option maxHeartbeats 500000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions CoreSpec := by
  circuit_proof_start [CoreSpec]
  clear h_assumptions
  obtain ⟨-, ⟨-, -, hopa0, -, ⟨hbpv, -, -⟩, -, ⟨hcpv, -, -⟩⟩, ha, hb, hc, hq, hqc, hrc, hr,
    har, hac, hmax, hctq, ⟨-, hloProd, -, -, -, -, -, -, -⟩, ⟨-, hupProd, -, -, -, -, -, -, -⟩,
    hcnegv, hrnegv, ⟨hltbit, -, -, -⟩, hcarry, ⟨-, -, -, -, -, -, hisc0res⟩, hdiv, hdivu, hrem,
    hremu, hdivw, hremw, hdivuw, hremuw, hov, ⟨-, -, -, -, -, -, hovbres⟩,
    ⟨-, -, -, -, -, -, hovcres⟩, hbm, hrm, hcm, hqm, hbn, hbnno, hbnnno, hirnw, hrn, hcn, hace,
    hare, hir, hrcm⟩ := h_input
  obtain ⟨hMulLo, hMulUp, hg0, hg1, hg2, hg3, hg4, hg5, hg6, hg7, hOwn,
    hp0, hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15,
    hp16, hp17, hp18, hp19, hp20, hp21, hp22, hp23, hp24, hp25, hp26, hp27, hp28, hp29,
    hp30, hp31⟩ := h_holds
  -- normalize the own-assert block to list-membership form
  simp only [DivRemChip.assertZeros, DivRemChip.forAllNoOffset_map_assert] at hOwn
  -- the gate/flag binaries and the one-hot sum, extracted from the own-assert tail by membership
  have e355 := hOwn _ (DivRemChip.isReal_gate_mem_ownAsserts _)
  have e343 := hOwn _ (DivRemChip.isRealNotWord_gate_mem_ownAsserts _)
  have e325 := hOwn _ (DivRemChip.isDiv_gate_mem_ownAsserts _)
  have e327 := hOwn _ (DivRemChip.isDivu_gate_mem_ownAsserts _)
  have e329 := hOwn _ (DivRemChip.isRem_gate_mem_ownAsserts _)
  have e331 := hOwn _ (DivRemChip.isRemu_gate_mem_ownAsserts _)
  have e333 := hOwn _ (DivRemChip.isDivw_gate_mem_ownAsserts _)
  have e335 := hOwn _ (DivRemChip.isRemw_gate_mem_ownAsserts _)
  have e337 := hOwn _ (DivRemChip.isDivuw_gate_mem_ownAsserts _)
  have e339 := hOwn _ (DivRemChip.isRemuw_gate_mem_ownAsserts _)
  have e367 := hOwn _ (DivRemChip.flagsSum_mem_ownAsserts _)
  simp only [circuit_norm, evalSub, hdiv, hdivu, hrem, hremu, hdivw, hremw, hdivuw, hremuw, hir,
    hirnw] at e355 e343 e325 e327 e329 e331 e333 e335 e337 e339 e367
  have bIr := bool_of_mul_pred e355
  have bIrnw := bool_of_mul_pred e343
  have bDiv := bool_of_mul_pred e325
  have bDivu := bool_of_mul_pred e327
  have bRem := bool_of_mul_pred e329
  have bRemu := bool_of_mul_pred e331
  have bDivw := bool_of_mul_pred e333
  have bRemw := bool_of_mul_pred e335
  have bDivuw := bool_of_mul_pred e337
  have bRemuw := bool_of_mul_pred e339
  have hsum1 : input_is_divu + input_is_remu + input_is_div + input_is_rem + input_is_divw
      + input_is_remw + input_is_divuw + input_is_remuw = 1 := by linear_combination - e367
  have hvals := DivRemChip.flags_val_sum bDivu bRemu bDiv bRem bDivw bRemw bDivuw bRemuw hsum1
  have hsum2 : input_is_div.val + input_is_divu.val + input_is_rem.val + input_is_remu.val
      + input_is_divw.val + input_is_remw.val + input_is_divuw.val + input_is_remuw.val = 1 := by
    omega
  have bDR := DivRemChip.group_binary2 bDiv bRem (by omega)
  have bDRu := DivRemChip.group_binary2 bDivu bRemu (by omega)
  -- the two composed Mul contracts
  have hSpecLo := hMulLo ⟨bIr, fun h => absurd h zero_ne_one, bIr, Or.inl rfl,
    Or.inl rfl, Or.inl rfl, Or.inl rfl, by simpa using bIr⟩
  have hSpecUp := hMulUp ⟨bIrnw, fun h => absurd h zero_ne_one, Or.inl rfl, bDR,
    bDRu, Or.inl rfl, Or.inl rfl, by
      rcases DivRemChip.group_binary4 bDiv bRem bDivu bRemu (by omega) with h | h
      · left; linear_combination h
      · right; linear_combination h⟩
  have eCtq := eval_getElem hctq
  have eCar := eval_getElem hcarry
  have eRc := eval_getElem hrc
  have eAc := eval_getElem hac
  have eAr := eval_getElem har
  have eQ := eval_getElem hq
  have eR := eval_getElem hr
  have eLoP := eval_getElem hloProd
  have eUpP := eval_getElem hupProd
  simp only [eCtq, eLoP, eUpP] at hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7
  refine ⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · -- the two products and their u16-limb glue
    unfold ProductSpec
    refine And.intro hSpecLo (And.intro hSpecUp (And.intro ?_ ?_))
    · rw [LowerProductPlacement]
      intro hir1
      change input_is_real = 1 at hir1
      change
        input_c_times_quotient[0] =
            input_c_times_quotient_lower_product[0] +
              input_c_times_quotient_lower_product[1] * 256 ∧
          input_c_times_quotient[1] =
            input_c_times_quotient_lower_product[2] +
              input_c_times_quotient_lower_product[3] * 256 ∧
          input_c_times_quotient[2] =
            input_c_times_quotient_lower_product[4] +
              input_c_times_quotient_lower_product[5] * 256 ∧
          input_c_times_quotient[3] =
            input_c_times_quotient_lower_product[6] +
              input_c_times_quotient_lower_product[7] * 256
      rw [hir1, one_mul] at hg0 hg1 hg2 hg3
      exact ⟨by linear_combination hg0, by linear_combination hg1,
        by linear_combination hg2, by linear_combination hg3⟩
    · rw [UpperProductPlacement]
      intro h64
      change input_is_div + input_is_divu + input_is_rem + input_is_remu = 1 at h64
      change
        input_c_times_quotient[4] =
            input_c_times_quotient_upper_product[8] +
              input_c_times_quotient_upper_product[9] * 256 ∧
          input_c_times_quotient[5] =
            input_c_times_quotient_upper_product[10] +
              input_c_times_quotient_upper_product[11] * 256 ∧
          input_c_times_quotient[6] =
            input_c_times_quotient_upper_product[12] +
              input_c_times_quotient_upper_product[13] * 256 ∧
          input_c_times_quotient[7] =
            input_c_times_quotient_upper_product[14] +
              input_c_times_quotient_upper_product[15] * 256
      rw [h64, one_mul] at hg4 hg5 hg6 hg7
      exact ⟨by linear_combination hg4, by linear_combination hg5, by linear_combination hg6,
        by linear_combination hg7⟩
  · -- the raw own-assert bundle, transported to the evaluated row
    exact ownAssertsHold_of_forall env hOwn hdiv hdivu hrem hremu hdivw hremw hdivuw hremuw hir
      hirnw hov hbn hbnno hbnnno hrn hcn hace hare hrcm hbm hrm hcm hqm hovbres hovcres hisc0res
      hltbit hopa0 hbpv hcpv ha hb hc hq hqc hr hrc har hac hmax hcnegv hrnegv hctq hcarry
  · -- the binary gates, one-hot equation, and committed case selection
    simp only [SelectionEvidenceSpec]
    exact ⟨bIr, bIrnw, bDiv, bDivu, bRem, bRemu, bDivw, bRemw, bDivuw, bRemuw, hsum1,
      fun _ => selection_of_flags bDiv bDivu bRem bRemu bDivw bRemw bDivuw bRemuw hsum2⟩
  · -- the byte-range evidence
    simp only [RangeSpec, Nat.cast_ofNat]
    intro hr1
    have hneg : - input_is_real = -1 := neg_inj.mpr hr1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [eCtq, eRc, eCar] using DivRemChip.isU16_of_byteRowSpec (hp0 hneg)
    · simpa only [eCtq, eRc, eCar] using DivRemChip.isU16_of_byteRowSpec (hp1 hneg)
    · simpa only [eCtq, eRc, eCar] using DivRemChip.isU16_of_byteRowSpec (hp2 hneg)
    · simpa only [eCtq, eRc, eCar] using DivRemChip.isU16_of_byteRowSpec (hp3 hneg)
    · simpa only [eCtq, eCar] using DivRemChip.isU16_of_byteRowSpec (hp4 hneg)
    · simpa only [eCtq, eCar] using DivRemChip.isU16_of_byteRowSpec (hp5 hneg)
    · simpa only [eCtq, eCar] using DivRemChip.isU16_of_byteRowSpec (hp6 hneg)
    · simpa only [eCtq, eCar] using DivRemChip.isU16_of_byteRowSpec (hp7 hneg)
    · intro i hi
      interval_cases i
      · simpa only [eAc] using DivRemChip.isU16_of_byteRowSpec (hp8 hneg)
      · simpa only [eAc] using DivRemChip.isU16_of_byteRowSpec (hp9 hneg)
      · simpa only [eAc] using DivRemChip.isU16_of_byteRowSpec (hp10 hneg)
      · simpa only [eAc] using DivRemChip.isU16_of_byteRowSpec (hp11 hneg)
    · intro i hi
      interval_cases i
      · simpa only [eAr] using DivRemChip.isU16_of_byteRowSpec (hp12 hneg)
      · simpa only [eAr] using DivRemChip.isU16_of_byteRowSpec (hp13 hneg)
      · simpa only [eAr] using DivRemChip.isU16_of_byteRowSpec (hp14 hneg)
      · simpa only [eAr] using DivRemChip.isU16_of_byteRowSpec (hp15 hneg)
    · intro i hi
      interval_cases i
      · simpa only [eQ] using DivRemChip.isU16_of_byteRowSpec (hp16 hneg)
      · simpa only [eQ] using DivRemChip.isU16_of_byteRowSpec (hp17 hneg)
      · simpa only [eQ] using DivRemChip.isU16_of_byteRowSpec (hp18 hneg)
      · simpa only [eQ] using DivRemChip.isU16_of_byteRowSpec (hp19 hneg)
    · intro i hi
      interval_cases i
      · simpa only [eR] using DivRemChip.isU16_of_byteRowSpec (hp20 hneg)
      · simpa only [eR] using DivRemChip.isU16_of_byteRowSpec (hp21 hneg)
      · simpa only [eR] using DivRemChip.isU16_of_byteRowSpec (hp22 hneg)
      · simpa only [eR] using DivRemChip.isU16_of_byteRowSpec (hp23 hneg)
    · intro i hi
      interval_cases i
      · simpa only [eCtq] using DivRemChip.isU16_of_byteRowSpec (hp24 hneg)
      · simpa only [eCtq] using DivRemChip.isU16_of_byteRowSpec (hp25 hneg)
      · simpa only [eCtq] using DivRemChip.isU16_of_byteRowSpec (hp26 hneg)
      · simpa only [eCtq] using DivRemChip.isU16_of_byteRowSpec (hp27 hneg)
      · simpa only [eCtq] using DivRemChip.isU16_of_byteRowSpec (hp28 hneg)
      · simpa only [eCtq] using DivRemChip.isU16_of_byteRowSpec (hp29 hneg)
      · simpa only [eCtq] using DivRemChip.isU16_of_byteRowSpec (hp30 hneg)
      · simpa only [eCtq] using DivRemChip.isU16_of_byteRowSpec (hp31 hneg)
  · -- the requirements tail: subcircuits owe nothing; the pulls' off-gate cases are vacuous
    and_intros <;>
      first
        | exact Or.inl rfl
        | trivial
        | (intro h1 h0; exact off_gate_vacuous bIr h1 h0)

set_option maxHeartbeats 400000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions CoreSpec := by
  circuit_proof_start [CoreSpec]
  clear h_assumptions
  obtain ⟨-, ⟨-, -, hopa0, -, ⟨hbpv, -, -⟩, -, ⟨hcpv, -, -⟩⟩, ha, hb, hc, hq, hqc, hrc, hr,
    har, hac, hmax, hctq, ⟨-, hloProd, -, -, -, -, -, -, -⟩, ⟨-, hupProd, -, -, -, -, -, -, -⟩,
    hcnegv, hrnegv, ⟨hltbit, -, -, -⟩, hcarry, ⟨-, -, -, -, -, -, hisc0res⟩, hdiv, hdivu, hrem,
    hremu, hdivw, hremw, hdivuw, hremuw, hov, ⟨-, -, -, -, -, -, hovbres⟩,
    ⟨-, -, -, -, -, -, hovcres⟩, hbm, hrm, hcm, hqm, hbn, hbnno, hbnnno, hirnw, hrn, hcn, hace,
    hare, hir, hrcm⟩ := h_input
  obtain ⟨hProduct, hOwnH, hSelection, hRange⟩ := h_spec
  unfold ProductSpec at hProduct
  obtain ⟨hSpecLo, hSpecUp, hglLo, hglUp⟩ := hProduct
  rw [LowerProductPlacement] at hglLo
  rw [UpperProductPlacement] at hglUp
  change
    input_is_real = 1 →
      input_c_times_quotient[0] =
          input_c_times_quotient_lower_product[0] +
            input_c_times_quotient_lower_product[1] * 256 ∧
        input_c_times_quotient[1] =
          input_c_times_quotient_lower_product[2] +
            input_c_times_quotient_lower_product[3] * 256 ∧
        input_c_times_quotient[2] =
          input_c_times_quotient_lower_product[4] +
            input_c_times_quotient_lower_product[5] * 256 ∧
        input_c_times_quotient[3] =
          input_c_times_quotient_lower_product[6] +
            input_c_times_quotient_lower_product[7] * 256 at hglLo
  change
    input_is_div + input_is_divu + input_is_rem + input_is_remu = 1 →
      input_c_times_quotient[4] =
          input_c_times_quotient_upper_product[8] +
            input_c_times_quotient_upper_product[9] * 256 ∧
        input_c_times_quotient[5] =
          input_c_times_quotient_upper_product[10] +
            input_c_times_quotient_upper_product[11] * 256 ∧
        input_c_times_quotient[6] =
          input_c_times_quotient_upper_product[12] +
            input_c_times_quotient_upper_product[13] * 256 ∧
        input_c_times_quotient[7] =
          input_c_times_quotient_upper_product[14] +
            input_c_times_quotient_upper_product[15] * 256 at hglUp
  simp only [SelectionEvidenceSpec] at hSelection
  obtain ⟨bIr, bIrnw, bDiv, bDivu, bRem, bRemu, bDivw, bRemw, bDivuw, bRemuw,
    hsum1, hsel⟩ := hSelection
  simp only [RangeSpec, Nat.cast_ofNat] at hRange
  let hByte := hRange
  have hvals := DivRemChip.flags_val_sum bDivu bRemu bDiv bRem bDivw bRemw bDivuw bRemuw hsum1
  have bDR := DivRemChip.group_binary2 bDiv bRem (by omega)
  have bDRu := DivRemChip.group_binary2 bDivu bRemu (by omega)
  have eCtq := eval_getElem hctq
  have eCar := eval_getElem hcarry
  have eRc := eval_getElem hrc
  have eAc := eval_getElem hac
  have eAr := eval_getElem har
  have eQ := eval_getElem hq
  have eR := eval_getElem hr
  have eLoP := eval_getElem hloProd
  have eUpP := eval_getElem hupProd
  refine ⟨⟨⟨bIr, fun h => absurd h zero_ne_one, bIr, Or.inl rfl, Or.inl rfl,
      Or.inl rfl, Or.inl rfl, by simpa using bIr⟩, hSpecLo⟩,
    ⟨⟨bIrnw, fun h => absurd h zero_ne_one, Or.inl rfl, bDR, bDRu, Or.inl rfl,
      Or.inl rfl, by
        rcases DivRemChip.group_binary4 bDiv bRem bDivu bRemu (by omega) with h | h
        · left; linear_combination h
        · right; linear_combination h⟩, hSpecUp⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eCtq, eLoP]
    rcases bIr with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglLo h).1, sub_self]
  · simp only [eCtq, eLoP]
    rcases bIr with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglLo h).2.1, sub_self]
  · simp only [eCtq, eLoP]
    rcases bIr with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglLo h).2.2.1, sub_self]
  · simp only [eCtq, eLoP]
    rcases bIr with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglLo h).2.2.2, sub_self]
  · simp only [eCtq, eUpP]
    rcases DivRemChip.group_binary4 bDiv bDivu bRem bRemu (by omega) with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglUp h).1, sub_self]
  · simp only [eCtq, eUpP]
    rcases DivRemChip.group_binary4 bDiv bDivu bRem bRemu (by omega) with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglUp h).2.1, sub_self]
  · simp only [eCtq, eUpP]
    rcases DivRemChip.group_binary4 bDiv bDivu bRem bRemu (by omega) with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglUp h).2.2.1, sub_self]
  · simp only [eCtq, eUpP]
    rcases DivRemChip.group_binary4 bDiv bDivu bRem bRemu (by omega) with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglUp h).2.2.2, sub_self]
  · simp only [DivRemChip.assertZeros, DivRemChip.forAllNoOffset_map_assert]
    exact forall_of_ownAssertsHold env.toEnvironment hOwnH hdiv hdivu hrem hremu hdivw hremw
      hdivuw hremuw hir hirnw hov hbn hbnno hbnnno hrn hcn hace hare hrcm hbm hrm hcm hqm hovbres
      hovcres hisc0res hltbit hopa0 hbpv hcpv ha hb hc hq hqc hr hrc har hac hmax hcnegv hrnegv
      hctq hcarry
  all_goals intro hneg
  all_goals replace hByte := hByte (neg_inj.mp hneg)
  all_goals obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ := hByte
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq, eRc, eCar] using c0)
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq, eRc, eCar] using c1)
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq, eRc, eCar] using c2)
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq, eRc, eCar] using c3)
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq, eCar] using c4)
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq, eCar] using c5)
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq, eCar] using c6)
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq, eCar] using c7)
  · exact byteRowSpec_of_isU16 (by simpa only [eAc] using fAc 0 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eAc] using fAc 1 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eAc] using fAc 2 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eAc] using fAc 3 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eAr] using fAr 0 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eAr] using fAr 1 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eAr] using fAr 2 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eAr] using fAr 3 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eQ] using fQ 0 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eQ] using fQ 1 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eQ] using fQ 2 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eQ] using fQ 3 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eR] using fR 0 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eR] using fR 1 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eR] using fR 2 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eR] using fR 3 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq] using fCtq 0 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq] using fCtq 1 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq] using fCtq 2 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq] using fCtq 3 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq] using fCtq 4 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq] using fCtq 5 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq] using fCtq 6 (by norm_num))
  · exact byteRowSpec_of_isU16 (by simpa only [eCtq] using fCtq 7 (by norm_num))
private theorem main_requirementsChannelsLawful (input_var : Var DivRemChip.Columns (ZMod p)) (i₀ : ℕ) :
    ((main input_var).operations i₀).RequirementsChannelsLawful
      (elaborated (p := p)).channelsWithGuarantees [] := by
  have h_byte : (byteChannel (p := p)).toRaw ∈ (elaborated (p := p)).channelsWithGuarantees := by
    simp only [circuit_norm]
  dsimp only [Operations.RequirementsChannelsLawful]
  refine ⟨?_, ?_, ?_⟩
  · simp only [main, Circuit.operations, Circuit.bind_def, assertion,
      DivRemChip.assertZeros, Channel.pullIf, HasAssertEq.assert_eq, Expression.assertEquals,
      Operations.localLength]
    simp only [Operations.subcircuitChannelsWithRequirements_append,
      Operations.subcircuitChannelsWithRequirements_subcircuit,
      Operations.subcircuitChannelsWithRequirements_interact,
      Operations.subcircuitChannelsWithRequirements_nil,
      DivRemChip.subChannelsR_map_assert,
      FormalAssertion.toSubcircuit_channelsWithRequirements,
      Gadgets.Equality.channelsWithRequirements_eq,
      MulOperation.circuit, List.append_nil, List.nil_subset]
  · intro channel h_channel
    simp only [main, Circuit.operations, Circuit.bind_def, assertion,
      DivRemChip.assertZeros, Channel.pullIf, HasAssertEq.assert_eq, Expression.assertEquals,
      Operations.localLength] at h_channel
    simp only [Operations.shallowChannels_append, Operations.shallowChannels_subcircuit,
      Operations.shallowChannels_interact, Operations.shallowChannels_nil,
      DivRemChip.shallowChannels_map_assert, List.nil_append] at h_channel
    simp only [ChannelInteraction.toRaw_channel, List.mem_append, List.mem_singleton,
      or_self] at h_channel
    subst channel
    exact Or.inl h_byte
  · intro env h_constraints
    simp only [main, Circuit.operations, Circuit.bind_def, assertion,
      DivRemChip.assertZeros, Channel.pullIf, HasAssertEq.assert_eq, Expression.assertEquals,
      Operations.localLength] at h_constraints ⊢
    simp only [ConstraintsHold.Shallow, Operations.forAllNoOffset_append,
      Operations.forAllNoOffset, DivRemChip.forAllNoOffset_map_assert, true_and,
      and_true] at h_constraints
    have h_all := h_constraints
    have e355 := h_all _ (DivRemChip.isReal_gate_mem_ownAsserts _)
    have e325 := h_all _ (DivRemChip.isDiv_gate_mem_ownAsserts _)
    have e327 := h_all _ (DivRemChip.isDivu_gate_mem_ownAsserts _)
    have e329 := h_all _ (DivRemChip.isRem_gate_mem_ownAsserts _)
    have e331 := h_all _ (DivRemChip.isRemu_gate_mem_ownAsserts _)
    have e333 := h_all _ (DivRemChip.isDivw_gate_mem_ownAsserts _)
    have e335 := h_all _ (DivRemChip.isRemw_gate_mem_ownAsserts _)
    have e337 := h_all _ (DivRemChip.isDivuw_gate_mem_ownAsserts _)
    have e339 := h_all _ (DivRemChip.isRemuw_gate_mem_ownAsserts _)
    have e367 := h_all _ (DivRemChip.flagsSum_mem_ownAsserts _)
    simp only [circuit_norm, evalSub] at e355 e325 e327 e329 e331 e333 e335 e337 e339 e367
    have bIr := bool_of_mul_pred e355
    have bDiv := bool_of_mul_pred e325
    have bDivu := bool_of_mul_pred e327
    have bRem := bool_of_mul_pred e329
    have bRemu := bool_of_mul_pred e331
    have bDivw := bool_of_mul_pred e333
    have bRemw := bool_of_mul_pred e335
    have bDivuw := bool_of_mul_pred e337
    have bRemuw := bool_of_mul_pred e339
    have hvals := DivRemChip.flags_val_sum bDivu bRemu bDiv bRem bDivw bRemw bDivuw bRemuw
      (by linear_combination - e367)
    have h_pull_ir (msg : ByteRow (Expression (ZMod p))) :
        (byteChannel.pulledIf input_var.is_real msg).toRaw.Requirements env := by
      rw [ChannelInteraction.toRaw_requirements]
      intro h1 h0
      simp only [pulledIf_mult, circuit_norm] at h1 h0
      exact off_gate_vacuous bIr h1 h0
    simp only [Operations.InChannelsOrRequirements, Operations.forAllNoOffset_append,
      Operations.forAllNoOffset, DivRemChip.forAllNoOffset_map_assert, List.not_mem_nil,
      false_or, true_and, and_true]
    and_intros
    all_goals first
      | exact h_pull_ir _
      | (intro e he; trivial)

/-- The DivRem product/own-assert/byte-range assertion cluster as a Clean-native
`FormalAssertion`: two composed `MulOperation` assertions, the eight product-glue asserts, the
chip's own assertZero tail, and the 32 gated byte-range pulls over the committed row; no fresh
witnesses, semantic contract `DivRemCore.CoreSpec`. -/
def circuit : FormalAssertion (ZMod p) DivRemChip.Columns :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := CoreSpec,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [],
    requirementsChannelsLawful := main_requirementsChannelsLawful }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    (circuit (p := p)).channelsWithRequirements = [] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var DivRemChip.Columns (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.DivRemCore
