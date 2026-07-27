import SP1Clean.Native.Operations.DivRemOperation.Core
import SP1Clean.FormalModel.Contracts.DivRem
import SP1Clean.Proofs.Chips.DivRemChip.Extract
import SP1Clean.Proofs.CircuitProofStart

/-! # `DivRemCore` — the `FormalAssertion` bundle (soundness / completeness / contract)

The DivRem product/own-assert/byte-range assertion cluster as a Clean `FormalAssertion` over the
whole committed row (`Extracted.DivRemCols`). The circuit
(`Native/Operations/DivRemOperation/Core.lean`) witnesses nothing, so both directions are
input-level repackaging: soundness maps the two composed `MulOperation` implications, the eight
product-glue equations, the own-assert tail (through the `ownAsserts_map_eval` var↔value
transport), and the 32 gated byte-pull guarantees onto the matching `CoreSpec` conjuncts — deriving
the selection block (`is_real`/flag binariness, one-hot, `SelectionSpec`) from the gate equations
inside the own-assert tail via the `OwnAsserts.lean` membership lemmas — and completeness feeds
each constraint back from the same conjuncts. -/

namespace SP1Clean.DivRemCore

open Circuit
open Extracted (DivRemCols)
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

set_option linter.unusedSectionVars false in
private lemma evalSub (env : Environment (ZMod p)) (a b : Expression (ZMod p)) :
    Expression.eval env (a - b) = Expression.eval env a - Expression.eval env b := by
  show Expression.eval env (.add a (.mul (.const (-1)) b)) = _
  simp only [Expression.eval]
  ring

set_option maxHeartbeats 64000000 in
/-- **Var↔value transport for the own-assert tail.** Mapping `Expression.eval` over the
carrier-generic `ownAsserts` chain at `R = Expression (ZMod p)` yields the same chain at
`R = ZMod p`, given the per-field evaluation pins (exactly the components of a
`circuit_proof_start` `h_input`). This is the one lemma that lets `CoreSpec`'s raw
`OwnAssertsHold` bundle be stated over the evaluated row while both `FormalAssertion`
directions stay pure repackaging. -/
theorem ownAsserts_map_eval (env : Environment (ZMod p)) (colsV : Var DivRemCols (ZMod p))
    (cols : DivRemCols (ZMod p))
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
  have vBpv0 : Expression.eval env colsV.adapter.op_b_memory.prev_value[0] = cols.adapter.op_b_memory.prev_value[0] := by
    rw [← vBpv, Vector.getElem_map]
  have vBpv1 : Expression.eval env colsV.adapter.op_b_memory.prev_value[1] = cols.adapter.op_b_memory.prev_value[1] := by
    rw [← vBpv, Vector.getElem_map]
  have vBpv2 : Expression.eval env colsV.adapter.op_b_memory.prev_value[2] = cols.adapter.op_b_memory.prev_value[2] := by
    rw [← vBpv, Vector.getElem_map]
  have vBpv3 : Expression.eval env colsV.adapter.op_b_memory.prev_value[3] = cols.adapter.op_b_memory.prev_value[3] := by
    rw [← vBpv, Vector.getElem_map]
  have vCpv0 : Expression.eval env colsV.adapter.op_c_memory.prev_value[0] = cols.adapter.op_c_memory.prev_value[0] := by
    rw [← vCpv, Vector.getElem_map]
  have vCpv1 : Expression.eval env colsV.adapter.op_c_memory.prev_value[1] = cols.adapter.op_c_memory.prev_value[1] := by
    rw [← vCpv, Vector.getElem_map]
  have vCpv2 : Expression.eval env colsV.adapter.op_c_memory.prev_value[2] = cols.adapter.op_c_memory.prev_value[2] := by
    rw [← vCpv, Vector.getElem_map]
  have vCpv3 : Expression.eval env colsV.adapter.op_c_memory.prev_value[3] = cols.adapter.op_c_memory.prev_value[3] := by
    rw [← vCpv, Vector.getElem_map]
  have vA0 : Expression.eval env colsV.a[0] = cols.a[0] := by
    rw [← vA, Vector.getElem_map]
  have vA1 : Expression.eval env colsV.a[1] = cols.a[1] := by
    rw [← vA, Vector.getElem_map]
  have vA2 : Expression.eval env colsV.a[2] = cols.a[2] := by
    rw [← vA, Vector.getElem_map]
  have vA3 : Expression.eval env colsV.a[3] = cols.a[3] := by
    rw [← vA, Vector.getElem_map]
  have vB0 : Expression.eval env colsV.b[0] = cols.b[0] := by
    rw [← vB, Vector.getElem_map]
  have vB1 : Expression.eval env colsV.b[1] = cols.b[1] := by
    rw [← vB, Vector.getElem_map]
  have vB2 : Expression.eval env colsV.b[2] = cols.b[2] := by
    rw [← vB, Vector.getElem_map]
  have vB3 : Expression.eval env colsV.b[3] = cols.b[3] := by
    rw [← vB, Vector.getElem_map]
  have vC0 : Expression.eval env colsV.c[0] = cols.c[0] := by
    rw [← vC, Vector.getElem_map]
  have vC1 : Expression.eval env colsV.c[1] = cols.c[1] := by
    rw [← vC, Vector.getElem_map]
  have vC2 : Expression.eval env colsV.c[2] = cols.c[2] := by
    rw [← vC, Vector.getElem_map]
  have vC3 : Expression.eval env colsV.c[3] = cols.c[3] := by
    rw [← vC, Vector.getElem_map]
  have vQ0 : Expression.eval env colsV.quotient[0] = cols.quotient[0] := by
    rw [← vQ, Vector.getElem_map]
  have vQ1 : Expression.eval env colsV.quotient[1] = cols.quotient[1] := by
    rw [← vQ, Vector.getElem_map]
  have vQ2 : Expression.eval env colsV.quotient[2] = cols.quotient[2] := by
    rw [← vQ, Vector.getElem_map]
  have vQ3 : Expression.eval env colsV.quotient[3] = cols.quotient[3] := by
    rw [← vQ, Vector.getElem_map]
  have vQC0 : Expression.eval env colsV.quotient_comp[0] = cols.quotient_comp[0] := by
    rw [← vQC, Vector.getElem_map]
  have vQC1 : Expression.eval env colsV.quotient_comp[1] = cols.quotient_comp[1] := by
    rw [← vQC, Vector.getElem_map]
  have vQC2 : Expression.eval env colsV.quotient_comp[2] = cols.quotient_comp[2] := by
    rw [← vQC, Vector.getElem_map]
  have vQC3 : Expression.eval env colsV.quotient_comp[3] = cols.quotient_comp[3] := by
    rw [← vQC, Vector.getElem_map]
  have vR0 : Expression.eval env colsV.remainder[0] = cols.remainder[0] := by
    rw [← vR, Vector.getElem_map]
  have vR1 : Expression.eval env colsV.remainder[1] = cols.remainder[1] := by
    rw [← vR, Vector.getElem_map]
  have vR2 : Expression.eval env colsV.remainder[2] = cols.remainder[2] := by
    rw [← vR, Vector.getElem_map]
  have vR3 : Expression.eval env colsV.remainder[3] = cols.remainder[3] := by
    rw [← vR, Vector.getElem_map]
  have vRC0 : Expression.eval env colsV.remainder_comp[0] = cols.remainder_comp[0] := by
    rw [← vRC, Vector.getElem_map]
  have vRC1 : Expression.eval env colsV.remainder_comp[1] = cols.remainder_comp[1] := by
    rw [← vRC, Vector.getElem_map]
  have vRC2 : Expression.eval env colsV.remainder_comp[2] = cols.remainder_comp[2] := by
    rw [← vRC, Vector.getElem_map]
  have vRC3 : Expression.eval env colsV.remainder_comp[3] = cols.remainder_comp[3] := by
    rw [← vRC, Vector.getElem_map]
  have vAR0 : Expression.eval env colsV.abs_remainder[0] = cols.abs_remainder[0] := by
    rw [← vAR, Vector.getElem_map]
  have vAR1 : Expression.eval env colsV.abs_remainder[1] = cols.abs_remainder[1] := by
    rw [← vAR, Vector.getElem_map]
  have vAR2 : Expression.eval env colsV.abs_remainder[2] = cols.abs_remainder[2] := by
    rw [← vAR, Vector.getElem_map]
  have vAR3 : Expression.eval env colsV.abs_remainder[3] = cols.abs_remainder[3] := by
    rw [← vAR, Vector.getElem_map]
  have vAC0 : Expression.eval env colsV.abs_c[0] = cols.abs_c[0] := by
    rw [← vAC, Vector.getElem_map]
  have vAC1 : Expression.eval env colsV.abs_c[1] = cols.abs_c[1] := by
    rw [← vAC, Vector.getElem_map]
  have vAC2 : Expression.eval env colsV.abs_c[2] = cols.abs_c[2] := by
    rw [← vAC, Vector.getElem_map]
  have vAC3 : Expression.eval env colsV.abs_c[3] = cols.abs_c[3] := by
    rw [← vAC, Vector.getElem_map]
  have vMax0 : Expression.eval env colsV.max_abs_c_or_1[0] = cols.max_abs_c_or_1[0] := by
    rw [← vMax, Vector.getElem_map]
  have vMax1 : Expression.eval env colsV.max_abs_c_or_1[1] = cols.max_abs_c_or_1[1] := by
    rw [← vMax, Vector.getElem_map]
  have vMax2 : Expression.eval env colsV.max_abs_c_or_1[2] = cols.max_abs_c_or_1[2] := by
    rw [← vMax, Vector.getElem_map]
  have vMax3 : Expression.eval env colsV.max_abs_c_or_1[3] = cols.max_abs_c_or_1[3] := by
    rw [← vMax, Vector.getElem_map]
  have vCnegV0 : Expression.eval env colsV.c_neg_operation.value[0] = cols.c_neg_operation.value[0] := by
    rw [← vCnegV, Vector.getElem_map]
  have vCnegV1 : Expression.eval env colsV.c_neg_operation.value[1] = cols.c_neg_operation.value[1] := by
    rw [← vCnegV, Vector.getElem_map]
  have vCnegV2 : Expression.eval env colsV.c_neg_operation.value[2] = cols.c_neg_operation.value[2] := by
    rw [← vCnegV, Vector.getElem_map]
  have vCnegV3 : Expression.eval env colsV.c_neg_operation.value[3] = cols.c_neg_operation.value[3] := by
    rw [← vCnegV, Vector.getElem_map]
  have vRnegV0 : Expression.eval env colsV.rem_neg_operation.value[0] = cols.rem_neg_operation.value[0] := by
    rw [← vRnegV, Vector.getElem_map]
  have vRnegV1 : Expression.eval env colsV.rem_neg_operation.value[1] = cols.rem_neg_operation.value[1] := by
    rw [← vRnegV, Vector.getElem_map]
  have vRnegV2 : Expression.eval env colsV.rem_neg_operation.value[2] = cols.rem_neg_operation.value[2] := by
    rw [← vRnegV, Vector.getElem_map]
  have vRnegV3 : Expression.eval env colsV.rem_neg_operation.value[3] = cols.rem_neg_operation.value[3] := by
    rw [← vRnegV, Vector.getElem_map]
  have vCtq0 : Expression.eval env colsV.c_times_quotient[0] = cols.c_times_quotient[0] := by
    rw [← vCtq, Vector.getElem_map]
  have vCtq1 : Expression.eval env colsV.c_times_quotient[1] = cols.c_times_quotient[1] := by
    rw [← vCtq, Vector.getElem_map]
  have vCtq2 : Expression.eval env colsV.c_times_quotient[2] = cols.c_times_quotient[2] := by
    rw [← vCtq, Vector.getElem_map]
  have vCtq3 : Expression.eval env colsV.c_times_quotient[3] = cols.c_times_quotient[3] := by
    rw [← vCtq, Vector.getElem_map]
  have vCtq4 : Expression.eval env colsV.c_times_quotient[4] = cols.c_times_quotient[4] := by
    rw [← vCtq, Vector.getElem_map]
  have vCtq5 : Expression.eval env colsV.c_times_quotient[5] = cols.c_times_quotient[5] := by
    rw [← vCtq, Vector.getElem_map]
  have vCtq6 : Expression.eval env colsV.c_times_quotient[6] = cols.c_times_quotient[6] := by
    rw [← vCtq, Vector.getElem_map]
  have vCtq7 : Expression.eval env colsV.c_times_quotient[7] = cols.c_times_quotient[7] := by
    rw [← vCtq, Vector.getElem_map]
  have vCarry0 : Expression.eval env colsV.carry[0] = cols.carry[0] := by
    rw [← vCarry, Vector.getElem_map]
  have vCarry1 : Expression.eval env colsV.carry[1] = cols.carry[1] := by
    rw [← vCarry, Vector.getElem_map]
  have vCarry2 : Expression.eval env colsV.carry[2] = cols.carry[2] := by
    rw [← vCarry, Vector.getElem_map]
  have vCarry3 : Expression.eval env colsV.carry[3] = cols.carry[3] := by
    rw [← vCarry, Vector.getElem_map]
  have vCarry4 : Expression.eval env colsV.carry[4] = cols.carry[4] := by
    rw [← vCarry, Vector.getElem_map]
  have vCarry5 : Expression.eval env colsV.carry[5] = cols.carry[5] := by
    rw [← vCarry, Vector.getElem_map]
  have vCarry6 : Expression.eval env colsV.carry[6] = cols.carry[6] := by
    rw [← vCarry, Vector.getElem_map]
  have vCarry7 : Expression.eval env colsV.carry[7] = cols.carry[7] := by
    rw [← vCarry, Vector.getElem_map]
  simp only [DivRemChip.ownAsserts, List.map_cons,
    List.map_nil, evalSub, Expression.eval,
    pDiv, pDivu, pRem, pRemu, pDivw, pRemw, pDivuw, pRemuw,
    pIr, pIrnw, pOv, pBn, pBnno, pBnnno, pRn, pCn,
    pAce, pAre, pRcm, pBm, pRm, pCm, pQm, pOvb,
    pOvc, pIsc0, pLtb, pOpa0, vBpv0, vBpv1, vBpv2, vBpv3,
    vCpv0, vCpv1, vCpv2, vCpv3, vA0, vA1, vA2, vA3,
    vB0, vB1, vB2, vB3, vC0, vC1, vC2, vC3,
    vQ0, vQ1, vQ2, vQ3, vQC0, vQC1, vQC2, vQC3,
    vR0, vR1, vR2, vR3, vRC0, vRC1, vRC2, vRC3,
    vAR0, vAR1, vAR2, vAR3, vAC0, vAC1, vAC2, vAC3,
    vMax0, vMax1, vMax2, vMax3, vCnegV0, vCnegV1, vCnegV2, vCnegV3,
    vRnegV0, vRnegV1, vRnegV2, vRnegV3, vCtq0, vCtq1, vCtq2, vCtq3,
    vCtq4, vCtq5, vCtq6, vCtq7, vCarry0, vCarry1, vCarry2, vCarry3,
    vCarry4, vCarry5, vCarry6, vCarry7]

/-- Soundness-direction transport: the var-level own-assert equations (the `assertZeros
(ownAsserts cols)` block's `h_holds` content) give the evaluated-row `OwnAssertsHold` bundle.
`colsV`/`cols` are implicit so both solve structurally from `h` and the goal — the pins then
land on fully-instantiated fields. -/
theorem ownAssertsHold_of_forall (env : Environment (ZMod p)) {colsV : Var DivRemCols (ZMod p)}
    {cols : DivRemCols (ZMod p)}
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
theorem forall_of_ownAssertsHold (env : Environment (ZMod p)) {colsV : Var DivRemCols (ZMod p)}
    {cols : DivRemCols (ZMod p)}
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
theorem selection_of_flags {cols : DivRemCols (ZMod p)}
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
    have z1 : cols.is_divu = 0 := hval0 _ (by omega)
    have z2 : cols.is_rem = 0 := hval0 _ (by omega)
    have z3 : cols.is_remu = 0 := hval0 _ (by omega)
    have z4 : cols.is_divw = 0 := hval0 _ (by omega)
    have z5 : cols.is_remw = 0 := hval0 _ (by omega)
    have z6 : cols.is_divuw = 0 := hval0 _ (by omega)
    have z7 : cols.is_remuw = 0 := hval0 _ (by omega)
    cases other <;> first | exact absurd rfl hne | assumption
  · refine ⟨.divu, hval1 _ b1 h, fun other hne => ?_⟩
    have z1 : cols.is_div = 0 := hval0 _ (by omega)
    have z2 : cols.is_rem = 0 := hval0 _ (by omega)
    have z3 : cols.is_remu = 0 := hval0 _ (by omega)
    have z4 : cols.is_divw = 0 := hval0 _ (by omega)
    have z5 : cols.is_remw = 0 := hval0 _ (by omega)
    have z6 : cols.is_divuw = 0 := hval0 _ (by omega)
    have z7 : cols.is_remuw = 0 := hval0 _ (by omega)
    cases other <;> first | exact absurd rfl hne | assumption
  · refine ⟨.rem, hval1 _ b2 h, fun other hne => ?_⟩
    have z1 : cols.is_div = 0 := hval0 _ (by omega)
    have z2 : cols.is_divu = 0 := hval0 _ (by omega)
    have z3 : cols.is_remu = 0 := hval0 _ (by omega)
    have z4 : cols.is_divw = 0 := hval0 _ (by omega)
    have z5 : cols.is_remw = 0 := hval0 _ (by omega)
    have z6 : cols.is_divuw = 0 := hval0 _ (by omega)
    have z7 : cols.is_remuw = 0 := hval0 _ (by omega)
    cases other <;> first | exact absurd rfl hne | assumption
  · refine ⟨.remu, hval1 _ b3 h, fun other hne => ?_⟩
    have z1 : cols.is_div = 0 := hval0 _ (by omega)
    have z2 : cols.is_divu = 0 := hval0 _ (by omega)
    have z3 : cols.is_rem = 0 := hval0 _ (by omega)
    have z4 : cols.is_divw = 0 := hval0 _ (by omega)
    have z5 : cols.is_remw = 0 := hval0 _ (by omega)
    have z6 : cols.is_divuw = 0 := hval0 _ (by omega)
    have z7 : cols.is_remuw = 0 := hval0 _ (by omega)
    cases other <;> first | exact absurd rfl hne | assumption
  · refine ⟨.divw, hval1 _ b4 h, fun other hne => ?_⟩
    have z1 : cols.is_div = 0 := hval0 _ (by omega)
    have z2 : cols.is_divu = 0 := hval0 _ (by omega)
    have z3 : cols.is_rem = 0 := hval0 _ (by omega)
    have z4 : cols.is_remu = 0 := hval0 _ (by omega)
    have z5 : cols.is_remw = 0 := hval0 _ (by omega)
    have z6 : cols.is_divuw = 0 := hval0 _ (by omega)
    have z7 : cols.is_remuw = 0 := hval0 _ (by omega)
    cases other <;> first | exact absurd rfl hne | assumption
  · refine ⟨.remw, hval1 _ b5 h, fun other hne => ?_⟩
    have z1 : cols.is_div = 0 := hval0 _ (by omega)
    have z2 : cols.is_divu = 0 := hval0 _ (by omega)
    have z3 : cols.is_rem = 0 := hval0 _ (by omega)
    have z4 : cols.is_remu = 0 := hval0 _ (by omega)
    have z5 : cols.is_divw = 0 := hval0 _ (by omega)
    have z6 : cols.is_divuw = 0 := hval0 _ (by omega)
    have z7 : cols.is_remuw = 0 := hval0 _ (by omega)
    cases other <;> first | exact absurd rfl hne | assumption
  · refine ⟨.divuw, hval1 _ b6 h, fun other hne => ?_⟩
    have z1 : cols.is_div = 0 := hval0 _ (by omega)
    have z2 : cols.is_divu = 0 := hval0 _ (by omega)
    have z3 : cols.is_rem = 0 := hval0 _ (by omega)
    have z4 : cols.is_remu = 0 := hval0 _ (by omega)
    have z5 : cols.is_divw = 0 := hval0 _ (by omega)
    have z6 : cols.is_remw = 0 := hval0 _ (by omega)
    have z7 : cols.is_remuw = 0 := hval0 _ (by omega)
    cases other <;> first | exact absurd rfl hne | assumption
  · refine ⟨.remuw, hval1 _ b7 h, fun other hne => ?_⟩
    have z1 : cols.is_div = 0 := hval0 _ (by omega)
    have z2 : cols.is_divu = 0 := hval0 _ (by omega)
    have z3 : cols.is_rem = 0 := hval0 _ (by omega)
    have z4 : cols.is_remu = 0 := hval0 _ (by omega)
    have z5 : cols.is_divw = 0 := hval0 _ (by omega)
    have z6 : cols.is_remw = 0 := hval0 _ (by omega)
    have z7 : cols.is_divuw = 0 := hval0 _ (by omega)
    cases other <;> first | exact absurd rfl hne | assumption

/-- The core cluster is self-contained. Its composed multiplications recover operand limb bounds
from their own safe byte-decomposition pulls, while the gate/flag facts come from the core's
own-assert tail. No range fact has to be assumed by the parent chip. -/
def Assumptions (_cols : DivRemCols (ZMod p)) : Prop := True

set_option maxHeartbeats 16000000 in
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
  have eCtq0 : Expression.eval env input_var_c_times_quotient[0] = input_c_times_quotient[0] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq1 : Expression.eval env input_var_c_times_quotient[1] = input_c_times_quotient[1] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq2 : Expression.eval env input_var_c_times_quotient[2] = input_c_times_quotient[2] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq3 : Expression.eval env input_var_c_times_quotient[3] = input_c_times_quotient[3] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq4 : Expression.eval env input_var_c_times_quotient[4] = input_c_times_quotient[4] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq5 : Expression.eval env input_var_c_times_quotient[5] = input_c_times_quotient[5] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq6 : Expression.eval env input_var_c_times_quotient[6] = input_c_times_quotient[6] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq7 : Expression.eval env input_var_c_times_quotient[7] = input_c_times_quotient[7] := by
    rw [← hctq, Vector.getElem_map]
  have eCar0 : Expression.eval env input_var_carry[0] = input_carry[0] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar1 : Expression.eval env input_var_carry[1] = input_carry[1] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar2 : Expression.eval env input_var_carry[2] = input_carry[2] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar3 : Expression.eval env input_var_carry[3] = input_carry[3] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar4 : Expression.eval env input_var_carry[4] = input_carry[4] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar5 : Expression.eval env input_var_carry[5] = input_carry[5] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar6 : Expression.eval env input_var_carry[6] = input_carry[6] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar7 : Expression.eval env input_var_carry[7] = input_carry[7] := by
    rw [← hcarry, Vector.getElem_map]
  have eRc0 : Expression.eval env input_var_remainder_comp[0] = input_remainder_comp[0] := by
    rw [← hrc, Vector.getElem_map]
  have eRc1 : Expression.eval env input_var_remainder_comp[1] = input_remainder_comp[1] := by
    rw [← hrc, Vector.getElem_map]
  have eRc2 : Expression.eval env input_var_remainder_comp[2] = input_remainder_comp[2] := by
    rw [← hrc, Vector.getElem_map]
  have eRc3 : Expression.eval env input_var_remainder_comp[3] = input_remainder_comp[3] := by
    rw [← hrc, Vector.getElem_map]
  have eAc0 : Expression.eval env input_var_abs_c[0] = input_abs_c[0] := by
    rw [← hac, Vector.getElem_map]
  have eAc1 : Expression.eval env input_var_abs_c[1] = input_abs_c[1] := by
    rw [← hac, Vector.getElem_map]
  have eAc2 : Expression.eval env input_var_abs_c[2] = input_abs_c[2] := by
    rw [← hac, Vector.getElem_map]
  have eAc3 : Expression.eval env input_var_abs_c[3] = input_abs_c[3] := by
    rw [← hac, Vector.getElem_map]
  have eAr0 : Expression.eval env input_var_abs_remainder[0] = input_abs_remainder[0] := by
    rw [← har, Vector.getElem_map]
  have eAr1 : Expression.eval env input_var_abs_remainder[1] = input_abs_remainder[1] := by
    rw [← har, Vector.getElem_map]
  have eAr2 : Expression.eval env input_var_abs_remainder[2] = input_abs_remainder[2] := by
    rw [← har, Vector.getElem_map]
  have eAr3 : Expression.eval env input_var_abs_remainder[3] = input_abs_remainder[3] := by
    rw [← har, Vector.getElem_map]
  have eQ0 : Expression.eval env input_var_quotient[0] = input_quotient[0] := by
    rw [← hq, Vector.getElem_map]
  have eQ1 : Expression.eval env input_var_quotient[1] = input_quotient[1] := by
    rw [← hq, Vector.getElem_map]
  have eQ2 : Expression.eval env input_var_quotient[2] = input_quotient[2] := by
    rw [← hq, Vector.getElem_map]
  have eQ3 : Expression.eval env input_var_quotient[3] = input_quotient[3] := by
    rw [← hq, Vector.getElem_map]
  have eR0 : Expression.eval env input_var_remainder[0] = input_remainder[0] := by
    rw [← hr, Vector.getElem_map]
  have eR1 : Expression.eval env input_var_remainder[1] = input_remainder[1] := by
    rw [← hr, Vector.getElem_map]
  have eR2 : Expression.eval env input_var_remainder[2] = input_remainder[2] := by
    rw [← hr, Vector.getElem_map]
  have eR3 : Expression.eval env input_var_remainder[3] = input_remainder[3] := by
    rw [← hr, Vector.getElem_map]
  have eLoP0 : Expression.eval env input_var_c_times_quotient_lower_product[0] = input_c_times_quotient_lower_product[0] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP1 : Expression.eval env input_var_c_times_quotient_lower_product[1] = input_c_times_quotient_lower_product[1] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP2 : Expression.eval env input_var_c_times_quotient_lower_product[2] = input_c_times_quotient_lower_product[2] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP3 : Expression.eval env input_var_c_times_quotient_lower_product[3] = input_c_times_quotient_lower_product[3] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP4 : Expression.eval env input_var_c_times_quotient_lower_product[4] = input_c_times_quotient_lower_product[4] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP5 : Expression.eval env input_var_c_times_quotient_lower_product[5] = input_c_times_quotient_lower_product[5] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP6 : Expression.eval env input_var_c_times_quotient_lower_product[6] = input_c_times_quotient_lower_product[6] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP7 : Expression.eval env input_var_c_times_quotient_lower_product[7] = input_c_times_quotient_lower_product[7] := by
    rw [← hloProd, Vector.getElem_map]
  have eUpP8 : Expression.eval env input_var_c_times_quotient_upper_product[8] = input_c_times_quotient_upper_product[8] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP9 : Expression.eval env input_var_c_times_quotient_upper_product[9] = input_c_times_quotient_upper_product[9] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP10 : Expression.eval env input_var_c_times_quotient_upper_product[10] = input_c_times_quotient_upper_product[10] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP11 : Expression.eval env input_var_c_times_quotient_upper_product[11] = input_c_times_quotient_upper_product[11] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP12 : Expression.eval env input_var_c_times_quotient_upper_product[12] = input_c_times_quotient_upper_product[12] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP13 : Expression.eval env input_var_c_times_quotient_upper_product[13] = input_c_times_quotient_upper_product[13] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP14 : Expression.eval env input_var_c_times_quotient_upper_product[14] = input_c_times_quotient_upper_product[14] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP15 : Expression.eval env input_var_c_times_quotient_upper_product[15] = input_c_times_quotient_upper_product[15] := by
    rw [← hupProd, Vector.getElem_map]
  simp only [eCtq0, eCtq1, eCtq2, eCtq3, eCtq4, eCtq5, eCtq6, eCtq7, eLoP0, eLoP1, eLoP2, eLoP3,
    eLoP4, eLoP5, eLoP6, eLoP7, eUpP8, eUpP9, eUpP10, eUpP11, eUpP12, eUpP13, eUpP14,
    eUpP15] at hg0 hg1 hg2 hg3 hg4 hg5 hg6 hg7
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
    have hneg : - input_is_real = -1 := by rw [hr1]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [eCtq0, eRc0, eCar0] using DivRemChip.isU16_of_byteRowSpec (hp0 hneg)
    · simpa only [eCtq1, eRc1, eCar1, eCar0] using DivRemChip.isU16_of_byteRowSpec (hp1 hneg)
    · simpa only [eCtq2, eRc2, eCar2, eCar1] using DivRemChip.isU16_of_byteRowSpec (hp2 hneg)
    · simpa only [eCtq3, eRc3, eCar3, eCar2] using DivRemChip.isU16_of_byteRowSpec (hp3 hneg)
    · simpa only [eCtq4, eCar4, eCar3] using DivRemChip.isU16_of_byteRowSpec (hp4 hneg)
    · simpa only [eCtq5, eCar5, eCar4] using DivRemChip.isU16_of_byteRowSpec (hp5 hneg)
    · simpa only [eCtq6, eCar6, eCar5] using DivRemChip.isU16_of_byteRowSpec (hp6 hneg)
    · simpa only [eCtq7, eCar7, eCar6] using DivRemChip.isU16_of_byteRowSpec (hp7 hneg)
    · intro i hi
      interval_cases i
      · simpa only [eAc0] using DivRemChip.isU16_of_byteRowSpec (hp8 hneg)
      · simpa only [eAc1] using DivRemChip.isU16_of_byteRowSpec (hp9 hneg)
      · simpa only [eAc2] using DivRemChip.isU16_of_byteRowSpec (hp10 hneg)
      · simpa only [eAc3] using DivRemChip.isU16_of_byteRowSpec (hp11 hneg)
    · intro i hi
      interval_cases i
      · simpa only [eAr0] using DivRemChip.isU16_of_byteRowSpec (hp12 hneg)
      · simpa only [eAr1] using DivRemChip.isU16_of_byteRowSpec (hp13 hneg)
      · simpa only [eAr2] using DivRemChip.isU16_of_byteRowSpec (hp14 hneg)
      · simpa only [eAr3] using DivRemChip.isU16_of_byteRowSpec (hp15 hneg)
    · intro i hi
      interval_cases i
      · simpa only [eQ0] using DivRemChip.isU16_of_byteRowSpec (hp16 hneg)
      · simpa only [eQ1] using DivRemChip.isU16_of_byteRowSpec (hp17 hneg)
      · simpa only [eQ2] using DivRemChip.isU16_of_byteRowSpec (hp18 hneg)
      · simpa only [eQ3] using DivRemChip.isU16_of_byteRowSpec (hp19 hneg)
    · intro i hi
      interval_cases i
      · simpa only [eR0] using DivRemChip.isU16_of_byteRowSpec (hp20 hneg)
      · simpa only [eR1] using DivRemChip.isU16_of_byteRowSpec (hp21 hneg)
      · simpa only [eR2] using DivRemChip.isU16_of_byteRowSpec (hp22 hneg)
      · simpa only [eR3] using DivRemChip.isU16_of_byteRowSpec (hp23 hneg)
    · intro i hi
      interval_cases i
      · simpa only [eCtq0] using DivRemChip.isU16_of_byteRowSpec (hp24 hneg)
      · simpa only [eCtq1] using DivRemChip.isU16_of_byteRowSpec (hp25 hneg)
      · simpa only [eCtq2] using DivRemChip.isU16_of_byteRowSpec (hp26 hneg)
      · simpa only [eCtq3] using DivRemChip.isU16_of_byteRowSpec (hp27 hneg)
      · simpa only [eCtq4] using DivRemChip.isU16_of_byteRowSpec (hp28 hneg)
      · simpa only [eCtq5] using DivRemChip.isU16_of_byteRowSpec (hp29 hneg)
      · simpa only [eCtq6] using DivRemChip.isU16_of_byteRowSpec (hp30 hneg)
      · simpa only [eCtq7] using DivRemChip.isU16_of_byteRowSpec (hp31 hneg)
  · -- the requirements tail: subcircuits owe nothing; the pulls' off-gate cases are vacuous
    and_intros <;>
      first
        | exact Or.inl rfl
        | trivial
        | (intro h1 h0
           first
             | exact off_gate_vacuous bIr h1 h0)

set_option maxHeartbeats 16000000 in
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
  obtain ⟨hSpecLo, hProduct⟩ := hProduct
  obtain ⟨hSpecUp, hProduct⟩ := hProduct
  obtain ⟨hglLo, hglUp⟩ := hProduct
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
  have eCtq0 : Expression.eval env.toEnvironment input_var_c_times_quotient[0] = input_c_times_quotient[0] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq1 : Expression.eval env.toEnvironment input_var_c_times_quotient[1] = input_c_times_quotient[1] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq2 : Expression.eval env.toEnvironment input_var_c_times_quotient[2] = input_c_times_quotient[2] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq3 : Expression.eval env.toEnvironment input_var_c_times_quotient[3] = input_c_times_quotient[3] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq4 : Expression.eval env.toEnvironment input_var_c_times_quotient[4] = input_c_times_quotient[4] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq5 : Expression.eval env.toEnvironment input_var_c_times_quotient[5] = input_c_times_quotient[5] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq6 : Expression.eval env.toEnvironment input_var_c_times_quotient[6] = input_c_times_quotient[6] := by
    rw [← hctq, Vector.getElem_map]
  have eCtq7 : Expression.eval env.toEnvironment input_var_c_times_quotient[7] = input_c_times_quotient[7] := by
    rw [← hctq, Vector.getElem_map]
  have eCar0 : Expression.eval env.toEnvironment input_var_carry[0] = input_carry[0] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar1 : Expression.eval env.toEnvironment input_var_carry[1] = input_carry[1] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar2 : Expression.eval env.toEnvironment input_var_carry[2] = input_carry[2] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar3 : Expression.eval env.toEnvironment input_var_carry[3] = input_carry[3] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar4 : Expression.eval env.toEnvironment input_var_carry[4] = input_carry[4] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar5 : Expression.eval env.toEnvironment input_var_carry[5] = input_carry[5] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar6 : Expression.eval env.toEnvironment input_var_carry[6] = input_carry[6] := by
    rw [← hcarry, Vector.getElem_map]
  have eCar7 : Expression.eval env.toEnvironment input_var_carry[7] = input_carry[7] := by
    rw [← hcarry, Vector.getElem_map]
  have eRc0 : Expression.eval env.toEnvironment input_var_remainder_comp[0] = input_remainder_comp[0] := by
    rw [← hrc, Vector.getElem_map]
  have eRc1 : Expression.eval env.toEnvironment input_var_remainder_comp[1] = input_remainder_comp[1] := by
    rw [← hrc, Vector.getElem_map]
  have eRc2 : Expression.eval env.toEnvironment input_var_remainder_comp[2] = input_remainder_comp[2] := by
    rw [← hrc, Vector.getElem_map]
  have eRc3 : Expression.eval env.toEnvironment input_var_remainder_comp[3] = input_remainder_comp[3] := by
    rw [← hrc, Vector.getElem_map]
  have eAc0 : Expression.eval env.toEnvironment input_var_abs_c[0] = input_abs_c[0] := by
    rw [← hac, Vector.getElem_map]
  have eAc1 : Expression.eval env.toEnvironment input_var_abs_c[1] = input_abs_c[1] := by
    rw [← hac, Vector.getElem_map]
  have eAc2 : Expression.eval env.toEnvironment input_var_abs_c[2] = input_abs_c[2] := by
    rw [← hac, Vector.getElem_map]
  have eAc3 : Expression.eval env.toEnvironment input_var_abs_c[3] = input_abs_c[3] := by
    rw [← hac, Vector.getElem_map]
  have eAr0 : Expression.eval env.toEnvironment input_var_abs_remainder[0] = input_abs_remainder[0] := by
    rw [← har, Vector.getElem_map]
  have eAr1 : Expression.eval env.toEnvironment input_var_abs_remainder[1] = input_abs_remainder[1] := by
    rw [← har, Vector.getElem_map]
  have eAr2 : Expression.eval env.toEnvironment input_var_abs_remainder[2] = input_abs_remainder[2] := by
    rw [← har, Vector.getElem_map]
  have eAr3 : Expression.eval env.toEnvironment input_var_abs_remainder[3] = input_abs_remainder[3] := by
    rw [← har, Vector.getElem_map]
  have eQ0 : Expression.eval env.toEnvironment input_var_quotient[0] = input_quotient[0] := by
    rw [← hq, Vector.getElem_map]
  have eQ1 : Expression.eval env.toEnvironment input_var_quotient[1] = input_quotient[1] := by
    rw [← hq, Vector.getElem_map]
  have eQ2 : Expression.eval env.toEnvironment input_var_quotient[2] = input_quotient[2] := by
    rw [← hq, Vector.getElem_map]
  have eQ3 : Expression.eval env.toEnvironment input_var_quotient[3] = input_quotient[3] := by
    rw [← hq, Vector.getElem_map]
  have eR0 : Expression.eval env.toEnvironment input_var_remainder[0] = input_remainder[0] := by
    rw [← hr, Vector.getElem_map]
  have eR1 : Expression.eval env.toEnvironment input_var_remainder[1] = input_remainder[1] := by
    rw [← hr, Vector.getElem_map]
  have eR2 : Expression.eval env.toEnvironment input_var_remainder[2] = input_remainder[2] := by
    rw [← hr, Vector.getElem_map]
  have eR3 : Expression.eval env.toEnvironment input_var_remainder[3] = input_remainder[3] := by
    rw [← hr, Vector.getElem_map]
  have eLoP0 : Expression.eval env.toEnvironment input_var_c_times_quotient_lower_product[0] = input_c_times_quotient_lower_product[0] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP1 : Expression.eval env.toEnvironment input_var_c_times_quotient_lower_product[1] = input_c_times_quotient_lower_product[1] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP2 : Expression.eval env.toEnvironment input_var_c_times_quotient_lower_product[2] = input_c_times_quotient_lower_product[2] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP3 : Expression.eval env.toEnvironment input_var_c_times_quotient_lower_product[3] = input_c_times_quotient_lower_product[3] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP4 : Expression.eval env.toEnvironment input_var_c_times_quotient_lower_product[4] = input_c_times_quotient_lower_product[4] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP5 : Expression.eval env.toEnvironment input_var_c_times_quotient_lower_product[5] = input_c_times_quotient_lower_product[5] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP6 : Expression.eval env.toEnvironment input_var_c_times_quotient_lower_product[6] = input_c_times_quotient_lower_product[6] := by
    rw [← hloProd, Vector.getElem_map]
  have eLoP7 : Expression.eval env.toEnvironment input_var_c_times_quotient_lower_product[7] = input_c_times_quotient_lower_product[7] := by
    rw [← hloProd, Vector.getElem_map]
  have eUpP8 : Expression.eval env.toEnvironment input_var_c_times_quotient_upper_product[8] = input_c_times_quotient_upper_product[8] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP9 : Expression.eval env.toEnvironment input_var_c_times_quotient_upper_product[9] = input_c_times_quotient_upper_product[9] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP10 : Expression.eval env.toEnvironment input_var_c_times_quotient_upper_product[10] = input_c_times_quotient_upper_product[10] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP11 : Expression.eval env.toEnvironment input_var_c_times_quotient_upper_product[11] = input_c_times_quotient_upper_product[11] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP12 : Expression.eval env.toEnvironment input_var_c_times_quotient_upper_product[12] = input_c_times_quotient_upper_product[12] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP13 : Expression.eval env.toEnvironment input_var_c_times_quotient_upper_product[13] = input_c_times_quotient_upper_product[13] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP14 : Expression.eval env.toEnvironment input_var_c_times_quotient_upper_product[14] = input_c_times_quotient_upper_product[14] := by
    rw [← hupProd, Vector.getElem_map]
  have eUpP15 : Expression.eval env.toEnvironment input_var_c_times_quotient_upper_product[15] = input_c_times_quotient_upper_product[15] := by
    rw [← hupProd, Vector.getElem_map]
  refine ⟨⟨⟨bIr, fun h => absurd h zero_ne_one, bIr, Or.inl rfl, Or.inl rfl,
      Or.inl rfl, Or.inl rfl, by simpa using bIr⟩, hSpecLo⟩,
    ⟨⟨bIrnw, fun h => absurd h zero_ne_one, Or.inl rfl, bDR, bDRu, Or.inl rfl,
      Or.inl rfl, by
        rcases DivRemChip.group_binary4 bDiv bRem bDivu bRemu (by omega) with h | h
        · left; linear_combination h
        · right; linear_combination h⟩, hSpecUp⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [eCtq0, eLoP0, eLoP1]
    rcases bIr with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglLo h).1, sub_self]
  · simp only [eCtq1, eLoP2, eLoP3]
    rcases bIr with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglLo h).2.1, sub_self]
  · simp only [eCtq2, eLoP4, eLoP5]
    rcases bIr with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglLo h).2.2.1, sub_self]
  · simp only [eCtq3, eLoP6, eLoP7]
    rcases bIr with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglLo h).2.2.2, sub_self]
  · simp only [eCtq4, eUpP8, eUpP9]
    rcases DivRemChip.group_binary4 bDiv bDivu bRem bRemu (by omega) with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglUp h).1, sub_self]
  · simp only [eCtq5, eUpP10, eUpP11]
    rcases DivRemChip.group_binary4 bDiv bDivu bRem bRemu (by omega) with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglUp h).2.1, sub_self]
  · simp only [eCtq6, eUpP12, eUpP13]
    rcases DivRemChip.group_binary4 bDiv bDivu bRem bRemu (by omega) with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglUp h).2.2.1, sub_self]
  · simp only [eCtq7, eUpP14, eUpP15]
    rcases DivRemChip.group_binary4 bDiv bDivu bRem bRemu (by omega) with h | h
    · rw [h, zero_mul]
    · rw [h, one_mul, (hglUp h).2.2.2, sub_self]
  · simp only [DivRemChip.assertZeros, DivRemChip.forAllNoOffset_map_assert]
    exact forall_of_ownAssertsHold env.toEnvironment hOwnH hdiv hdivu hrem hremu hdivw hremw
      hdivuw hremuw hir hirnw hov hbn hbnno hbnnno hrn hcn hace hare hrcm hbm hrm hcm hqm hovbres
      hovcres hisc0res hltbit hopa0 hbpv hcpv ha hb hc hq hqc hr hrc har hac hmax hcnegv hrnegv
      hctq hcarry
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq0, eRc0, eCar0] using c0)
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq1, eRc1, eCar1, eCar0] using c1)
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq2, eRc2, eCar2, eCar1] using c2)
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq3, eRc3, eCar3, eCar2] using c3)
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq4, eCar4, eCar3] using c4)
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq5, eCar5, eCar4] using c5)
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq6, eCar6, eCar5] using c6)
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq7, eCar7, eCar6] using c7)
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eAc0] using fAc 0 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eAc1] using fAc 1 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eAc2] using fAc 2 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eAc3] using fAc 3 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eAr0] using fAr 0 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eAr1] using fAr 1 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eAr2] using fAr 2 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eAr3] using fAr 3 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eQ0] using fQ 0 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eQ1] using fQ 1 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eQ2] using fQ 2 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eQ3] using fQ 3 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eR0] using fR 0 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eR1] using fR 1 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eR2] using fR 2 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eR3] using fR 3 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq0] using fCtq 0 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq1] using fCtq 1 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq2] using fCtq 2 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq3] using fCtq 3 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq4] using fCtq 4 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq5] using fCtq 5 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq6] using fCtq 6 (by norm_num))
  · intro hneg
    obtain ⟨c0, c1, c2, c3, c4, c5, c6, c7, fAc, fAr, fQ, fR, fCtq⟩ :=
      hByte (by linear_combination - hneg)
    exact byteRowSpec_of_isU16 (by simpa only [eCtq7] using fCtq 7 (by norm_num))
set_option maxHeartbeats 16000000 in
private theorem main_requirementsChannelsLawful (input_var : Var DivRemCols (ZMod p)) (i₀ : ℕ) :
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
def circuit : FormalAssertion (ZMod p) DivRemCols :=
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
@[circuit_norm] lemma circuit_localLength (x : Var DivRemCols (ZMod p)) :
    circuit.localLength x = 0 := rfl

end SP1Clean.DivRemCore
