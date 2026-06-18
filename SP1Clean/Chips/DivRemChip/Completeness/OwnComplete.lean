import SP1Clean.Chips.DivRemChip.Defs
import SP1Clean.Chips.DivRemChip.OwnAsserts
import SP1Clean.Chips.DivRemChip.Populate.Abs
import SP1Clean.Chips.DivRemChip.Populate.Bounds
import SP1Clean.Chips.DivRemChip.Populate.Euclid
import SP1Clean.Chips.DivRemChip.Populate.Glue
import SP1Clean.Chips.DivRemChip.Populate.Shapes
import SP1Clean.Chips.DivRemChip.Populate.Signs

/-! # `DivRemChip` — the own-asserts completeness lemma (factored for parallel compilation)

The honest `Populate` witnesses satisfy every one of the chip's ~121 own `assertZero` constraints
(`ownAsserts`, the `[E13…E367, op_a_0]` list). This is the substance of the `case own` hole in
`Formal.lean`'s `completeness`; it is split out here (mirroring the `Soundness/<Op>.lean` split) so the
heavy arithmetic compiles in its own file under its own heartbeat budget, off the 256M-heartbeat
`completeness` theorem.

The lemma is stated env-parametrically over an abstract column var-struct `colsV`, taking the
per-column **eval pins** (`Expression.eval env colsV.<field> = <populate value>`) as hypotheses — the
`case own` glue supplies them from the completeness proof's own pins (`h_env_*`/`h_input`). Each of the
121 conjuncts is dispatched to its already-proven value lemma in `Populate/{Abs,Bounds,Shapes,Signs,
Glue,Euclid}.lean`. -/

namespace SP1Clean.DivRemChip

open Circuit
open Extracted (DivRemCols)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private instance : Fact (2 ^ 17 < p) :=
  ⟨lt_trans (by norm_num) (Fact.out (p := 2 ^ 24 < p))⟩

/-! ## Forward-overflow lemmas (for the `case eN` Euclid gate `(is_overflow − 1)`)

`euclid_limbs_s64/sW` need `hnotmin`; in the non-overflow branch we get it by contradiction from this
forward implication: on a signed class the overflow operand pair forces `is_overflow = 1`. -/

private lemma s64_intMin_limbs {B : Word (ZMod p)} (hB : B.isU64)
    (hBm : Word.toBitVec64 B = BitVec.intMin 64) :
    B[0] = 0 ∧ B[1] = 0 ∧ B[2] = 0 ∧ B[3] = 32768 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hB
  have htn : B.toNat = 2 ^ 63 := by
    have h := Word.toBitVec64_toNat hB
    rw [hBm, BitVec.toNat_intMin_of_pos (by norm_num)] at h
    omega
  rw [Word.toNat_def] at htn
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply ZMod.val_injective; rw [ZMod.val_zero]; omega
  · apply ZMod.val_injective; rw [ZMod.val_zero]; omega
  · apply ZMod.val_injective; rw [ZMod.val_zero]; omega
  · apply ZMod.val_injective; rw [val_32768_zmod_p]; omega

private lemma s64_allOnes_limbs {C : Word (ZMod p)} (hC : C.isU64)
    (hCm : Word.toBitVec64 C = BitVec.allOnes 64) :
    C[0] = 65535 ∧ C[1] = 65535 ∧ C[2] = 65535 ∧ C[3] = 65535 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hC
  have htn : C.toNat = 2 ^ 64 - 1 := by
    have h := Word.toBitVec64_toNat hC
    rw [hCm, BitVec.toNat_allOnes] at h
    omega
  rw [Word.toNat_def] at htn
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ZMod.val_injective <;> rw [val_65535_zmod_p] <;> omega

private lemma sW_intMin_limbs {B : Word (ZMod p)} (hB : B.isU64)
    (hBm : (Word.toBitVec64 B).setWidth 32 = BitVec.intMin 32) :
    B[0] = 0 ∧ B[1] = 32768 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hB
  have htn : B.toNat % 2 ^ 32 = 2 ^ 31 := by
    have h := congrArg BitVec.toNat hBm
    rw [BitVec.toNat_setWidth, Word.toBitVec64_toNat hB, BitVec.toNat_intMin_of_pos (by norm_num)] at h
    omega
  rw [Word.toNat_def] at htn
  refine ⟨?_, ?_⟩
  · apply ZMod.val_injective; rw [ZMod.val_zero]; omega
  · apply ZMod.val_injective; rw [val_32768_zmod_p]; omega

private lemma sW_allOnes_limbs {C : Word (ZMod p)} (hC : C.isU64)
    (hCm : (Word.toBitVec64 C).setWidth 32 = BitVec.allOnes 32) :
    C[0] = 65535 ∧ C[1] = 65535 := by
  obtain ⟨h0, h1, h2, h3⟩ := Word.lt_cases_of_isU64 hC
  have htn : C.toNat % 2 ^ 32 = 2 ^ 32 - 1 := by
    have h := congrArg BitVec.toNat hCm
    rw [BitVec.toNat_setWidth, Word.toBitVec64_toNat hC, BitVec.toNat_allOnes] at h
    omega
  rw [Word.toNat_def] at htn
  refine ⟨?_, ?_⟩ <;> apply ZMod.val_injective <;> rw [val_65535_zmod_p] <;> omega

private lemma overflow_one_of_s64 {B C : Word (ZMod p)} (hB : B.isU64) (hC : C.isU64)
    {f : Vector (ZMod p) 8} (hw : f[4] + f[5] + f[6] + f[7] = 0)
    (hsig : f[0] + f[2] + f[4] + f[5] = 1)
    (hBm : Word.toBitVec64 B = BitVec.intMin 64) (hCm : Word.toBitVec64 C = BitVec.allOnes 64) :
    populateIsOverflow 1 B C f = 1 := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := s64_intMin_limbs hB hBm
  obtain ⟨hc0, hc1, hc2, hc3⟩ := s64_allOnes_limbs hC hCm
  have hwne : ¬(f[4] + f[5] + f[6] + f[7] = 1) := by rw [hw]; exact zero_ne_one
  have hovb : (ovbWitness 1 B f).is_diff_zero.result = 1 := by
    unfold ovbWitness
    rw [if_pos rfl, if_neg hwne, isEqualWord_populate_result, if_pos ⟨hb0, hb1, hb2, hb3⟩]
  have hovc : (ovcWitness 1 C f).is_diff_zero.result = 1 := by
    unfold ovcWitness
    rw [if_pos rfl, if_neg hwne, isEqualWord_populate_result, if_pos ⟨hc0, hc1, hc2, hc3⟩]
  unfold populateIsOverflow
  rw [hovb, hovc, hsig]; ring

private lemma overflow_one_of_sW {B C : Word (ZMod p)} (hB : B.isU64) (hC : C.isU64)
    {f : Vector (ZMod p) 8} (hW : f[4] + f[5] + f[6] + f[7] = 1)
    (hsig : f[0] + f[2] + f[4] + f[5] = 1)
    (hBm : (Word.toBitVec64 B).setWidth 32 = BitVec.intMin 32)
    (hCm : (Word.toBitVec64 C).setWidth 32 = BitVec.allOnes 32) :
    populateIsOverflow 1 B C f = 1 := by
  obtain ⟨hb0, hb1⟩ := sW_intMin_limbs hB hBm
  obtain ⟨hc0, hc1⟩ := sW_allOnes_limbs hC hCm
  have hovb : (ovbWitness 1 B f).is_diff_zero.result = 1 := by
    unfold ovbWitness
    rw [if_pos rfl, if_pos hW, isEqualWord_populate_result, if_pos ⟨hb0, hb1, rfl, rfl⟩]
  have hovc : (ovcWitness 1 C f).is_diff_zero.result = 1 := by
    unfold ovcWitness
    rw [if_pos rfl, if_pos hW, isEqualWord_populate_result, if_pos ⟨hc0, hc1, rfl, rfl⟩]
  unfold populateIsOverflow
  rw [hovb, hovc, hsig]; ring

set_option maxHeartbeats 64000000 in
set_option linter.unusedVariables false in
/-- Every own-assert (`ownAsserts colsV`) evaluates to `0` at the honest populate witnesses, given the
per-column eval pins. -/
theorem ownAsserts_complete (env : Environment (ZMod p)) (colsV : Var DivRemCols (ZMod p))
    (ir : ZMod p) (B C : Word (ZMod p)) (F : Vector (ZMod p) 8)
    (hbU : B.isU64) (hcU : C.isU64) (hbin : ir = 0 ∨ ir = 1)
    (hf0 : F[0] = 0 ∨ F[0] = 1) (hf1 : F[1] = 0 ∨ F[1] = 1) (hf2 : F[2] = 0 ∨ F[2] = 1)
    (hf3 : F[3] = 0 ∨ F[3] = 1) (hf4 : F[4] = 0 ∨ F[4] = 1) (hf5 : F[5] = 0 ∨ F[5] = 1)
    (hf6 : F[6] = 0 ∨ F[6] = 1) (hf7 : F[7] = 0 ∨ F[7] = 1)
    (hsum : F[0] + F[1] + F[2] + F[3] + F[4] + F[5] + F[6] + F[7] = 1)
    -- a signed-class row is real (the divu padding template has the signed sum `0`); needed only by
    -- the Euclid bullets to rule out the `ir=0 ∧ signed ∧ B=intMin` non-row. Wiring supplies it.
    (hsr : F[0] + F[2] + F[4] + F[5] = 1 → ir = 1)
    -- flag eval pins
    (eF0 : Expression.eval env colsV.is_div = F[0]) (eF1 : Expression.eval env colsV.is_divu = F[1])
    (eF2 : Expression.eval env colsV.is_rem = F[2]) (eF3 : Expression.eval env colsV.is_remu = F[3])
    (eF4 : Expression.eval env colsV.is_divw = F[4]) (eF5 : Expression.eval env colsV.is_remw = F[5])
    (eF6 : Expression.eval env colsV.is_divuw = F[6]) (eF7 : Expression.eval env colsV.is_remuw = F[7])
    (eIR : Expression.eval env colsV.is_real = ir)
    -- scalar eval pins
    (eIRNW : Expression.eval env colsV.is_real_not_word = ir * (1 - (F[4] + F[5] + F[6] + F[7])))
    (eOV : Expression.eval env colsV.is_overflow = populateIsOverflow ir B C F)
    (eBN : Expression.eval env colsV.b_neg = populateBNeg B F)
    (eBNNO : Expression.eval env colsV.b_neg_not_overflow
      = populateBNeg B F * (1 - populateIsOverflow ir B C F))
    (eBNNNO : Expression.eval env colsV.b_not_neg_not_overflow
      = (1 - populateBNeg B F) * (1 - populateIsOverflow ir B C F))
    (eRN : Expression.eval env colsV.rem_neg = populateRemNeg B C F)
    (eCN : Expression.eval env colsV.c_neg = populateCNeg C F)
    (eACE : Expression.eval env colsV.abs_c_alu_event = populateCNeg C F * ir)
    (eARE : Expression.eval env colsV.abs_rem_alu_event = populateRemNeg B C F * ir)
    (eRCM : Expression.eval env colsV.remainder_check_multiplicity = ltGate ir C F)
    -- msb eval pins
    (eBM : Expression.eval env colsV.b_msb.msb = bMsbCell B F)
    (eCM : Expression.eval env colsV.c_msb.msb = cMsbCell C F)
    (eRM : Expression.eval env colsV.rem_msb.msb = remMsbCell B C F)
    (eQM : Expression.eval env colsV.quot_msb.msb = quotMsbCell B C F)
    -- word/vector eval pins, stated WHOLE-VECTOR so the kernel never reduces the heavy `populate*`
    -- (a per-element `(populate… B C F)[i]'hi` in the signature forces a `GetElem`-size whnf of e.g.
    -- `populateAbsRem`'s `remBits`/sdiv core → kernel deep recursion). The per-element forms the
    -- bullets use are recovered cheaply in the proof body via `Vector.getElem_map`.
    (eBvec : Vector.map (Expression.eval env) colsV.b = bComp B F)
    (eCvec : Vector.map (Expression.eval env) colsV.c = cComp C F)
    (eQvec : Vector.map (Expression.eval env) colsV.quotient = populateQuotient B C F)
    (eQCvec : Vector.map (Expression.eval env) colsV.quotient_comp = populateQuotComp B C F)
    (eRvec : Vector.map (Expression.eval env) colsV.remainder = populateRemainder B C F)
    (eRCvec : Vector.map (Expression.eval env) colsV.remainder_comp = populateRemComp B C F)
    (eAvec : Vector.map (Expression.eval env) colsV.a = populateA B C F)
    (eABSCvec : Vector.map (Expression.eval env) colsV.abs_c = populateAbsC C F)
    (eABSRvec : Vector.map (Expression.eval env) colsV.abs_remainder = populateAbsRem B C F)
    (eMAXvec : Vector.map (Expression.eval env) colsV.max_abs_c_or_1 = populateMaxAbsCOr1 C F)
    (eCTQvec : Vector.map (Expression.eval env) colsV.c_times_quotient = populateCtq B C F)
    (eCARRYvec : Vector.map (Expression.eval env) colsV.carry = populateCarry B C F)
    (eCNEGVvec :
      Vector.map (Expression.eval env) colsV.c_neg_operation.value = wCnegWitness ir C F)
    (eRNEGVvec :
      Vector.map (Expression.eval env) colsV.rem_neg_operation.value = wRnegWitness ir B C F)
    (eBPVvec : Vector.map (Expression.eval env) colsV.adapter.op_b_memory.prev_value = B)
    (eCPVvec : Vector.map (Expression.eval env) colsV.adapter.op_c_memory.prev_value = C)
    -- struct-result eval pins (scalar; no `GetElem`-size whnf, so safe in the signature)
    (eOVBR : Expression.eval env colsV.is_overflow_b.is_diff_zero.result
      = (ovbWitness ir B F).is_diff_zero.result)
    (eOVCR : Expression.eval env colsV.is_overflow_c.is_diff_zero.result
      = (ovcWitness ir C F).is_diff_zero.result)
    (eISC0 : Expression.eval env colsV.is_c_0.result = (isC0Witness C F).result)
    (eLTBIT : Expression.eval env colsV.remainder_lt_operation.u16_compare_operation.bit
      = (ltBitWitness ir B C F)[0])
    (eOPA0 : Expression.eval env colsV.adapter.op_a_0 = 0) :
    ∀ e ∈ ownAsserts colsV, Expression.eval env e = 0 := by
  -- recover the per-element eval pins (cheap here: each is checked incrementally in the body, not as
  -- part of the lemma's Pi-type) from the whole-vector signature pins.
  have eB : ∀ i (hi : i < 4), Expression.eval env (colsV.b[i]'hi) = (bComp B F)[i]'hi :=
    fun i hi => by rw [← eBvec, Vector.getElem_map]
  have eC : ∀ i (hi : i < 4), Expression.eval env (colsV.c[i]'hi) = (cComp C F)[i]'hi :=
    fun i hi => by rw [← eCvec, Vector.getElem_map]
  have eQ : ∀ i (hi : i < 4),
      Expression.eval env (colsV.quotient[i]'hi) = (populateQuotient B C F)[i]'hi :=
    fun i hi => by rw [← eQvec, Vector.getElem_map]
  have eQC : ∀ i (hi : i < 4),
      Expression.eval env (colsV.quotient_comp[i]'hi) = (populateQuotComp B C F)[i]'hi :=
    fun i hi => by rw [← eQCvec, Vector.getElem_map]
  have eR : ∀ i (hi : i < 4),
      Expression.eval env (colsV.remainder[i]'hi) = (populateRemainder B C F)[i]'hi :=
    fun i hi => by rw [← eRvec, Vector.getElem_map]
  have eRC : ∀ i (hi : i < 4),
      Expression.eval env (colsV.remainder_comp[i]'hi) = (populateRemComp B C F)[i]'hi :=
    fun i hi => by rw [← eRCvec, Vector.getElem_map]
  have eA : ∀ i (hi : i < 4), Expression.eval env (colsV.a[i]'hi) = (populateA B C F)[i]'hi :=
    fun i hi => by rw [← eAvec, Vector.getElem_map]
  have eABSC : ∀ i (hi : i < 4),
      Expression.eval env (colsV.abs_c[i]'hi) = (populateAbsC C F)[i]'hi :=
    fun i hi => by rw [← eABSCvec, Vector.getElem_map]
  have eABSR : ∀ i (hi : i < 4),
      Expression.eval env (colsV.abs_remainder[i]'hi) = (populateAbsRem B C F)[i]'hi :=
    fun i hi => by rw [← eABSRvec, Vector.getElem_map]
  have eMAX : ∀ i (hi : i < 4),
      Expression.eval env (colsV.max_abs_c_or_1[i]'hi) = (populateMaxAbsCOr1 C F)[i]'hi :=
    fun i hi => by rw [← eMAXvec, Vector.getElem_map]
  have eCTQ : ∀ i (hi : i < 8),
      Expression.eval env (colsV.c_times_quotient[i]'hi) = (populateCtq B C F)[i]'hi :=
    fun i hi => by rw [← eCTQvec, Vector.getElem_map]
  have eCARRY : ∀ i (hi : i < 8),
      Expression.eval env (colsV.carry[i]'hi) = (populateCarry B C F)[i]'hi :=
    fun i hi => by rw [← eCARRYvec, Vector.getElem_map]
  have eCNEGV : ∀ i (hi : i < 4),
      Expression.eval env (colsV.c_neg_operation.value[i]'hi) = (wCnegWitness ir C F)[i]'hi :=
    fun i hi => by rw [← eCNEGVvec, Vector.getElem_map]
  have eRNEGV : ∀ i (hi : i < 4),
      Expression.eval env (colsV.rem_neg_operation.value[i]'hi) = (wRnegWitness ir B C F)[i]'hi :=
    fun i hi => by rw [← eRNEGVvec, Vector.getElem_map]
  have eBPV : ∀ i (hi : i < 4),
      Expression.eval env (colsV.adapter.op_b_memory.prev_value[i]'hi) = B[i]'hi :=
    fun i hi => by rw [← eBPVvec, Vector.getElem_map]
  have eCPV : ∀ i (hi : i < 4),
      Expression.eval env (colsV.adapter.op_c_memory.prev_value[i]'hi) = C[i]'hi :=
    fun i hi => by rw [← eCPVvec, Vector.getElem_map]
  have hclass := flagClassTrichotomy hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
  have hsig := sig_bool_of_class hclass
  have hword : F[4] + F[5] + F[6] + F[7] = 0 ∨ F[4] + F[5] + F[6] + F[7] = 1 := by
    rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with
      ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ |
      ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ |
      ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ |
      ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ <;>
      rw [g4, g5, g6, g7] <;> norm_num
  have hltgate : ltGate ir C F = 0 ∨ ltGate ir C F = 1 := by
    rcases hbin with h | h <;> rcases isC0_result_bool C F with h' | h' <;>
      simp only [ltGate, h, h'] <;> norm_num
  have hgates : (F[6] + F[7] = 0 ∨ F[6] + F[7] = 1)
      ∧ (F[4] + F[5] = 0 ∨ F[4] + F[5] = 1)
      ∧ (F[1] + F[3] + F[0] + F[2] = 0 ∨ F[1] + F[3] + F[0] + F[2] = 1)
      ∧ (F[1] + F[0] + F[4] + F[6] = 0 ∨ F[1] + F[0] + F[4] + F[6] = 1)
      ∧ (F[3] + F[2] + F[5] + F[7] = 0 ∨ F[3] + F[2] + F[5] + F[7] = 1) := by
    rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with
      ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ |
      ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ |
      ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ |
      ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ | ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ <;>
      simp only [g0, g1, g2, g3, g4, g5, g6, g7] <;> norm_num
  obtain ⟨he67, he45, he64bit, hdivgate, hremgate⟩ := hgates
  have hOvWB : populateIsOverflow ir B C F = 1 →
      populateQuotient B C F = bComp B F ∧ populateRemainder B C F = #v[0, 0, 0, 0] := by
    intro hov
    have hir : ir = 1 := by
      by_contra hne
      rw [populateIsOverflow_zero_of_not_real B C F hne] at hov
      exact zero_ne_one hov
    subst hir
    rcases hclass with ⟨hcl, h4, h5, h6, h7⟩ | ⟨hcl, h0, h2, h6, h7⟩ | hcl
    · exact overflow_quotient_64 hbU hcU hcl h4 h5 h6 h7 hov
    · exact overflow_quotient_word hbU hcU h0 h2 h6 h7 hcl hov
    · exfalso
      simp only [populateIsOverflow, hcl, mul_zero] at hov
      exact zero_ne_one hov
  -- the carry-chain Euclidean identity holds OFF the overflow row; the bullets' `(is_overflow−1)`
  -- gate covers the overflow row. On a signed class the `hnotmin` side-condition is discharged by
  -- the forward-overflow lemmas (an overflow operand pair would force `is_overflow = 1`).
  have hEU : populateIsOverflow ir B C F = 1 ∨ EuclidLimbEqs B C F := by
    by_cases hov : populateIsOverflow ir B C F = 1
    · exact Or.inl hov
    · refine Or.inr ?_
      rcases hclass with ⟨hcl, h4, h5, h6, h7⟩ | ⟨hcl, h0, h2, h6, h7⟩ | hcl
      · refine euclid_limbs_s64 hbU hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hcl ?_
        rintro ⟨hBm, hCm⟩
        apply hov
        rw [hsr (by rw [h4, h5]; linear_combination hcl)]
        exact overflow_one_of_s64 hbU hcU (by rw [h4, h5, h6, h7]; ring)
          (by rw [h4, h5]; linear_combination hcl) hBm hCm
      · refine euclid_limbs_sW hbU hcU hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hcl ?_
        rintro ⟨hBm, hCm⟩
        apply hov
        rw [hsr (by rw [h0, h2]; linear_combination hcl)]
        exact overflow_one_of_sW hbU hcU (by rw [h6, h7]; linear_combination hcl)
          (by rw [h0, h2]; linear_combination hcl) hBm hCm
      · rcases he67 with hg | hg
        · exact euclid_limbs_u64 hbU hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
            (by linear_combination hsum - hcl - hg)
        · exact euclid_limbs_uW hbU hcU hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum hg
  simp only [ownAsserts, List.forall_mem_cons]
  refine ⟨?e13, ?e15, ?e17, ?e19, ?e20, ?e21, ?e22, ?e23, ?e29, ?e35, ?e41, ?e47, ?e48, ?e49,
    ?e51, ?e54, ?e57, ?e59, ?e61, ?e64, ?e67, ?e69, ?e70, ?e71, ?e73, ?e76, ?e79, ?e81, ?e83,
    ?e86, ?e89, ?e91, ?e96, ?e99, ?e103, ?e105, ?e107, ?e109, ?e111, ?e113, ?e115, ?e117, ?e119,
    ?e154, ?e157, ?e160, ?e163, ?e167, ?e171, ?e175, ?e179, ?e184, ?e189, ?e194, ?e199, ?e204,
    ?e209, ?e214, ?e219, ?e225, ?e228, ?e230, ?e232, ?e234, ?e236, ?e238, ?e240, ?e242, ?e244,
    ?e247, ?e250, ?e253, ?e256, ?e259, ?e262, ?e265, ?e268, ?e270, ?e272, ?e274, ?e276, ?e278,
    ?e280, ?e282, ?e284, ?e286, ?e288, ?e299, ?e300, ?e301, ?e302, ?e305, ?e307, ?e309, ?e311,
    ?e313, ?e315, ?e317, ?e319, ?e321, ?e323, ?e325, ?e327, ?e329, ?e331, ?e333, ?e335, ?e337,
    ?e339, ?e341, ?e343, ?e345, ?e347, ?e349, ?e351, ?e353, ?e355, ?e357, ?e359, ?e367, ?eopa0⟩
  -- == representative milestone-0 bullets (one per mechanism); rest stubbed ==
  case e13 =>
    simp only [circuit_norm, eIRNW, eIR, eF4, eF5, eF6, eF7]; ring
  case e96 =>
    simp only [circuit_norm, eOV, eOVBR, eOVCR, eF0, eF2, eF4, eF5, populateIsOverflow]; ring
  case e20 =>
    simp only [circuit_norm, eBPV 0 (by norm_num), eB 0 (by norm_num), bComp_limb0]; ring
  case e309 =>
    simp only [circuit_norm, eCARRY 0 (by norm_num)]
    rcases populateCarry_bool B C hsig 0 (by norm_num) with h | h <;> rw [h] <;> ring
  case e325 =>
    simp only [circuit_norm, eF0]; rcases hf0 with h | h <;> rw [h] <;> ring
  case e367 =>
    simp only [circuit_norm, eF0, eF1, eF2, eF3, eF4, eF5, eF6, eF7]; linear_combination -hsum
  case eopa0 =>
    simp only [circuit_norm, eOPA0]
  -- == remaining bullets (to fill) ==
  case e15 =>
    simp only [circuit_norm, eBM, eBN, eF0, eF2, eF4, eF5, populateBNeg_def]; ring
  case e17 =>
    simp only [circuit_norm, eRM, eRN, eF0, eF2, eF4, eF5, populateRemNeg_def]; ring
  case e19 =>
    simp only [circuit_norm, eCM, eCN, eF0, eF2, eF4, eF5, populateCNeg_def]; ring
  case e21 =>
    simp only [circuit_norm, eCPV 0 (by norm_num), eC 0 (by norm_num), cComp_limb0]; ring
  case e22 =>
    simp only [circuit_norm, eBPV 1 (by norm_num), eB 1 (by norm_num), bComp_limb1]; ring
  case e23 =>
    simp only [circuit_norm, eCPV 1 (by norm_num), eC 1 (by norm_num), cComp_limb1]; ring
  case e29 =>
    simp only [circuit_norm, eB 2 (by norm_num), eBPV 2 (by norm_num), eBN, eF4, eF5, eF6, eF7,
      bComp_limb2 B hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum]; ring
  case e35 =>
    simp only [circuit_norm, eC 2 (by norm_num), eCPV 2 (by norm_num), eCN, eF4, eF5, eF6, eF7,
      cComp_limb2 C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum]; ring
  case e41 =>
    simp only [circuit_norm, eB 3 (by norm_num), eBPV 3 (by norm_num), eBN, eF4, eF5, eF6, eF7,
      bComp_limb3 B hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum]; ring
  case e47 =>
    simp only [circuit_norm, eC 3 (by norm_num), eCPV 3 (by norm_num), eCN, eF4, eF5, eF6, eF7,
      cComp_limb3 C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum]; ring
  case e48 =>
    simp only [circuit_norm, eQC 0 (by norm_num), eQ 0 (by norm_num), quotComp_limb0]; ring
  case e49 =>
    simp only [circuit_norm, eQC 1 (by norm_num), eQ 1 (by norm_num), quotComp_limb1]; ring
  case e51 =>
    simp only [circuit_norm, eF6, eF7, eQC 2 (by norm_num)]
    rcases he67 with h | h
    · rw [h]; ring
    · rw [(quotComp_hi_unsignedW B C h).1]; ring
  case e54 =>
    simp only [circuit_norm, eF4, eF5, eQC 2 (by norm_num), eQM]
    rcases he45 with h | h
    · rw [h]; ring
    · rw [(quotComp_hi_signedW B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h).1]; ring
  case e57 =>
    simp only [circuit_norm, eF4, eF5, eF6, eF7, eQ 2 (by norm_num), eQM]
    rcases hword with h | h
    · rw [h]; ring
    · rw [(quotient_hi_word B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h).1]; ring
  case e59 =>
    simp only [circuit_norm, eF0, eF1, eF2, eF3, eQC 2 (by norm_num), eQ 2 (by norm_num)]
    rcases he64bit with h | h
    · rw [h]; ring
    · rw [(quotComp_hi_64 B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum (by linear_combination h)).1]
      ring
  case e61 =>
    simp only [circuit_norm, eF6, eF7, eQC 3 (by norm_num)]
    rcases he67 with h | h
    · rw [h]; ring
    · rw [(quotComp_hi_unsignedW B C h).2]; ring
  case e64 =>
    simp only [circuit_norm, eF4, eF5, eQC 3 (by norm_num), eQM]
    rcases he45 with h | h
    · rw [h]; ring
    · rw [(quotComp_hi_signedW B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h).2]; ring
  case e67 =>
    simp only [circuit_norm, eF4, eF5, eF6, eF7, eQ 3 (by norm_num), eQM]
    rcases hword with h | h
    · rw [h]; ring
    · rw [(quotient_hi_word B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h).2]; ring
  case e69 =>
    simp only [circuit_norm, eF0, eF1, eF2, eF3, eQC 3 (by norm_num), eQ 3 (by norm_num)]
    rcases he64bit with h | h
    · rw [h]; ring
    · rw [(quotComp_hi_64 B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum (by linear_combination h)).2]
      ring
  case e70 =>
    simp only [circuit_norm, eRC 0 (by norm_num), eR 0 (by norm_num), remComp_limb0]; ring
  case e71 =>
    simp only [circuit_norm, eRC 1 (by norm_num), eR 1 (by norm_num), remComp_limb1]; ring
  case e73 =>
    simp only [circuit_norm, eF6, eF7, eRC 2 (by norm_num)]
    rcases he67 with h | h
    · rw [h]; ring
    · rw [(remComp_hi_unsignedW B C h).1]; ring
  case e76 =>
    simp only [circuit_norm, eF4, eF5, eRC 2 (by norm_num), eRM]
    rcases he45 with h | h
    · rw [h]; ring
    · rw [(remComp_hi_signedW B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h).1]; ring
  case e79 =>
    simp only [circuit_norm, eF4, eF5, eF6, eF7, eR 2 (by norm_num), eRM]
    rcases hword with h | h
    · rw [h]; ring
    · rw [(remainder_hi_word B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h).1]; ring
  case e81 =>
    simp only [circuit_norm, eF0, eF1, eF2, eF3, eRC 2 (by norm_num), eR 2 (by norm_num)]
    rcases he64bit with h | h
    · rw [h]; ring
    · rw [(remComp_hi_64 B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum (by linear_combination h)).1]
      ring
  case e83 =>
    simp only [circuit_norm, eF6, eF7, eRC 3 (by norm_num)]
    rcases he67 with h | h
    · rw [h]; ring
    · rw [(remComp_hi_unsignedW B C h).2]; ring
  case e86 =>
    simp only [circuit_norm, eF4, eF5, eRC 3 (by norm_num), eRM]
    rcases he45 with h | h
    · rw [h]; ring
    · rw [(remComp_hi_signedW B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h).2]; ring
  case e89 =>
    simp only [circuit_norm, eF4, eF5, eF6, eF7, eR 3 (by norm_num), eRM]
    rcases hword with h | h
    · rw [h]; ring
    · rw [(remainder_hi_word B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h).2]; ring
  case e91 =>
    simp only [circuit_norm, eF0, eF1, eF2, eF3, eRC 3 (by norm_num), eR 3 (by norm_num)]
    rcases he64bit with h | h
    · rw [h]; ring
    · rw [(remComp_hi_64 B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum (by linear_combination h)).2]
      ring
  case e99 =>
    simp only [circuit_norm, eBNNO, eBN, eOV]; ring
  case e103 =>
    simp only [circuit_norm, eBNNNO, eBN, eOV]; ring
  case e105 =>
    simp only [circuit_norm, eOV, eQ 0 (by norm_num), eB 0 (by norm_num)]
    by_cases hov : populateIsOverflow ir B C F = 1
    · rw [(hOvWB hov).1]; ring
    · rcases populateIsOverflow_bool ir B C hsig with h | h
      · rw [h]; ring
      · exact absurd h hov
  case e107 =>
    simp only [circuit_norm, eOV, eR 0 (by norm_num)]
    by_cases hov : populateIsOverflow ir B C F = 1
    · rw [(hOvWB hov).2]; simp
    · rcases populateIsOverflow_bool ir B C hsig with h | h
      · rw [h]; ring
      · exact absurd h hov
  case e109 =>
    simp only [circuit_norm, eOV, eQ 1 (by norm_num), eB 1 (by norm_num)]
    by_cases hov : populateIsOverflow ir B C F = 1
    · rw [(hOvWB hov).1]; ring
    · rcases populateIsOverflow_bool ir B C hsig with h | h
      · rw [h]; ring
      · exact absurd h hov
  case e111 =>
    simp only [circuit_norm, eOV, eR 1 (by norm_num)]
    by_cases hov : populateIsOverflow ir B C F = 1
    · rw [(hOvWB hov).2]; simp
    · rcases populateIsOverflow_bool ir B C hsig with h | h
      · rw [h]; ring
      · exact absurd h hov
  case e113 =>
    simp only [circuit_norm, eOV, eQ 2 (by norm_num), eB 2 (by norm_num)]
    by_cases hov : populateIsOverflow ir B C F = 1
    · rw [(hOvWB hov).1]; ring
    · rcases populateIsOverflow_bool ir B C hsig with h | h
      · rw [h]; ring
      · exact absurd h hov
  case e115 =>
    simp only [circuit_norm, eOV, eR 2 (by norm_num)]
    by_cases hov : populateIsOverflow ir B C F = 1
    · rw [(hOvWB hov).2]; simp
    · rcases populateIsOverflow_bool ir B C hsig with h | h
      · rw [h]; ring
      · exact absurd h hov
  case e117 =>
    simp only [circuit_norm, eOV, eQ 3 (by norm_num), eB 3 (by norm_num)]
    by_cases hov : populateIsOverflow ir B C F = 1
    · rw [(hOvWB hov).1]; ring
    · rcases populateIsOverflow_bool ir B C hsig with h | h
      · rw [h]; ring
      · exact absurd h hov
  case e119 =>
    simp only [circuit_norm, eOV, eR 3 (by norm_num)]
    by_cases hov : populateIsOverflow ir B C F = 1
    · rw [(hOvWB hov).2]; simp
    · rcases populateIsOverflow_bool ir B C hsig with h | h
      · rw [h]; ring
      · exact absurd h hov
  case e154 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨c1, _, _, _, _, _, _, _⟩ := heu
      simp only [circuit_norm, eB 0 (by norm_num), eCTQ 0 (by norm_num), eRC 0 (by norm_num),
        eCARRY 0 (by norm_num)]
      rw [c1]; ring
  case e157 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, c2, _, _, _, _, _, _⟩ := heu
      simp only [circuit_norm, eB 1 (by norm_num), eCTQ 1 (by norm_num), eRC 1 (by norm_num),
        eCARRY 1 (by norm_num), eCARRY 0 (by norm_num)]
      rw [c2]; ring
  case e160 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, _, c3, _, _, _, _, _⟩ := heu
      simp only [circuit_norm, eB 2 (by norm_num), eCTQ 2 (by norm_num), eRC 2 (by norm_num),
        eCARRY 2 (by norm_num), eCARRY 1 (by norm_num)]
      rw [c3]; ring
  case e163 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, _, _, c4, _, _, _, _⟩ := heu
      simp only [circuit_norm, eB 3 (by norm_num), eCTQ 3 (by norm_num), eRC 3 (by norm_num),
        eCARRY 3 (by norm_num), eCARRY 2 (by norm_num)]
      rw [c4]; ring
  case e167 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, _, _, _, c5, _, _, _⟩ := heu
      simp only [circuit_norm, eBN, eRN, eCTQ 4 (by norm_num), eCARRY 4 (by norm_num),
        eCARRY 3 (by norm_num)]
      push_cast at c5; rw [c5]; ring
  case e171 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, _, _, _, _, c6, _, _⟩ := heu
      simp only [circuit_norm, eBN, eRN, eCTQ 5 (by norm_num), eCARRY 5 (by norm_num),
        eCARRY 4 (by norm_num)]
      push_cast at c6; rw [c6]; ring
  case e175 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, _, _, _, _, _, c7, _⟩ := heu
      simp only [circuit_norm, eBN, eRN, eCTQ 6 (by norm_num), eCARRY 6 (by norm_num),
        eCARRY 5 (by norm_num)]
      push_cast at c7; rw [c7]; ring
  case e179 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, _, _, _, _, _, _, c8⟩ := heu
      simp only [circuit_norm, eBN, eRN, eCTQ 7 (by norm_num), eCARRY 7 (by norm_num),
        eCARRY 6 (by norm_num)]
      push_cast at c8; rw [c8]; ring
  case e184 =>
    simp only [circuit_norm, eF0, eF1, eF4, eF6, eQ 0 (by norm_num), eA 0 (by norm_num)]
    rcases hdivgate with h | h
    · rw [h]; ring
    · rw [populateA_div B C (by linear_combination h)]; ring
  case e189 =>
    simp only [circuit_norm, eF2, eF3, eF5, eF7, eR 0 (by norm_num), eA 0 (by norm_num)]
    rcases hremgate with h | h
    · rw [h]; ring
    · rw [populateA_rem B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum (by linear_combination h)]; ring
  case e194 =>
    simp only [circuit_norm, eF0, eF1, eF4, eF6, eQ 1 (by norm_num), eA 1 (by norm_num)]
    rcases hdivgate with h | h
    · rw [h]; ring
    · rw [populateA_div B C (by linear_combination h)]; ring
  case e199 =>
    simp only [circuit_norm, eF2, eF3, eF5, eF7, eR 1 (by norm_num), eA 1 (by norm_num)]
    rcases hremgate with h | h
    · rw [h]; ring
    · rw [populateA_rem B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum (by linear_combination h)]; ring
  case e204 =>
    simp only [circuit_norm, eF0, eF1, eF4, eF6, eQ 2 (by norm_num), eA 2 (by norm_num)]
    rcases hdivgate with h | h
    · rw [h]; ring
    · rw [populateA_div B C (by linear_combination h)]; ring
  case e209 =>
    simp only [circuit_norm, eF2, eF3, eF5, eF7, eR 2 (by norm_num), eA 2 (by norm_num)]
    rcases hremgate with h | h
    · rw [h]; ring
    · rw [populateA_rem B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum (by linear_combination h)]; ring
  case e214 =>
    simp only [circuit_norm, eF0, eF1, eF4, eF6, eQ 3 (by norm_num), eA 3 (by norm_num)]
    rcases hdivgate with h | h
    · rw [h]; ring
    · rw [populateA_div B C (by linear_combination h)]; ring
  case e219 =>
    simp only [circuit_norm, eF2, eF3, eF5, eF7, eR 3 (by norm_num), eA 3 (by norm_num)]
    rcases hremgate with h | h
    · rw [h]; ring
    · rw [populateA_rem B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum (by linear_combination h)]; ring
  case e225 =>
    simp only [circuit_norm, eRN, eBN]
    linear_combination remNeg_mul_bNeg_sub_one (C := C) hbU hclass
  case e228 =>
    simp only [circuit_norm, eR 0 (by norm_num), eR 1 (by norm_num), eR 2 (by norm_num),
      eR 3 (by norm_num), eRN, eBN]
    linear_combination rem_nonzero_nonneg_imp_bNonneg hbU hclass
  case e230 =>
    simp only [circuit_norm, eISC0, eQ 0 (by norm_num)]
    rcases isC0_result_bool C F with h | h
    · rw [h]; ring
    · rw [h, isC0_one_quotient hcU h 0 (by norm_num)]; ring
  case e232 =>
    simp only [circuit_norm, eISC0, eQ 1 (by norm_num)]
    rcases isC0_result_bool C F with h | h
    · rw [h]; ring
    · rw [h, isC0_one_quotient hcU h 1 (by norm_num)]; ring
  case e234 =>
    simp only [circuit_norm, eISC0, eQ 2 (by norm_num)]
    rcases isC0_result_bool C F with h | h
    · rw [h]; ring
    · rw [h, isC0_one_quotient hcU h 2 (by norm_num)]; ring
  case e236 =>
    simp only [circuit_norm, eISC0, eQ 3 (by norm_num)]
    rcases isC0_result_bool C F with h | h
    · rw [h]; ring
    · rw [h, isC0_one_quotient hcU h 3 (by norm_num)]; ring
  case e238 =>
    simp only [circuit_norm, eISC0, eRC 0 (by norm_num), eB 0 (by norm_num)]
    rcases isC0_result_bool C F with h | h
    · rw [h]; ring
    · rw [h, isC0_one_remComp hbU hcU hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h]; ring
  case e240 =>
    simp only [circuit_norm, eISC0, eRC 1 (by norm_num), eB 1 (by norm_num)]
    rcases isC0_result_bool C F with h | h
    · rw [h]; ring
    · rw [h, isC0_one_remComp hbU hcU hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h]; ring
  case e242 =>
    simp only [circuit_norm, eISC0, eRC 2 (by norm_num), eB 2 (by norm_num)]
    rcases isC0_result_bool C F with h | h
    · rw [h]; ring
    · rw [h, isC0_one_remComp hbU hcU hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h]; ring
  case e244 =>
    simp only [circuit_norm, eISC0, eRC 3 (by norm_num), eB 3 (by norm_num)]
    rcases isC0_result_bool C F with h | h
    · rw [h]; ring
    · rw [h, isC0_one_remComp hbU hcU hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h]; ring
  case e247 =>
    simp only [circuit_norm, eCN, eC 0 (by norm_num), eABSC 0 (by norm_num)]
    rcases populateCNeg_bool hcU hsig with h | h
    · rw [absC_eq_of_not_neg hcU hclass h, h]; ring
    · rw [h]; ring
  case e250 =>
    simp only [circuit_norm, eRN, eRC 0 (by norm_num), eABSR 0 (by norm_num)]
    rcases populateRemNeg_bool B C hsig with h | h
    · rw [absRem_eq_of_not_neg hclass h, h]; ring
    · rw [h]; ring
  case e253 =>
    simp only [circuit_norm, eCN, eC 1 (by norm_num), eABSC 1 (by norm_num)]
    rcases populateCNeg_bool hcU hsig with h | h
    · rw [absC_eq_of_not_neg hcU hclass h, h]; ring
    · rw [h]; ring
  case e256 =>
    simp only [circuit_norm, eRN, eRC 1 (by norm_num), eABSR 1 (by norm_num)]
    rcases populateRemNeg_bool B C hsig with h | h
    · rw [absRem_eq_of_not_neg hclass h, h]; ring
    · rw [h]; ring
  case e259 =>
    simp only [circuit_norm, eCN, eC 2 (by norm_num), eABSC 2 (by norm_num)]
    rcases populateCNeg_bool hcU hsig with h | h
    · rw [absC_eq_of_not_neg hcU hclass h, h]; ring
    · rw [h]; ring
  case e262 =>
    simp only [circuit_norm, eRN, eRC 2 (by norm_num), eABSR 2 (by norm_num)]
    rcases populateRemNeg_bool B C hsig with h | h
    · rw [absRem_eq_of_not_neg hclass h, h]; ring
    · rw [h]; ring
  case e265 =>
    simp only [circuit_norm, eCN, eC 3 (by norm_num), eABSC 3 (by norm_num)]
    rcases populateCNeg_bool hcU hsig with h | h
    · rw [absC_eq_of_not_neg hcU hclass h, h]; ring
    · rw [h]; ring
  case e268 =>
    simp only [circuit_norm, eRN, eRC 3 (by norm_num), eABSR 3 (by norm_num)]
    rcases populateRemNeg_bool B C hsig with h | h
    · rw [absRem_eq_of_not_neg hclass h, h]; ring
    · rw [h]; ring
  case e270 =>
    simp only [circuit_norm, eACE, eCNEGV 0 (by norm_num), wCnegWitness]
    split_ifs with h
    · simp [wCneg_value_zero hcU hclass h]
    · simp
  case e272 =>
    simp only [circuit_norm, eACE, eCNEGV 1 (by norm_num), wCnegWitness]
    split_ifs with h
    · simp [wCneg_value_zero hcU hclass h]
    · simp
  case e274 =>
    simp only [circuit_norm, eACE, eCNEGV 2 (by norm_num), wCnegWitness]
    split_ifs with h
    · simp [wCneg_value_zero hcU hclass h]
    · simp
  case e276 =>
    simp only [circuit_norm, eACE, eCNEGV 3 (by norm_num), wCnegWitness]
    split_ifs with h
    · simp [wCneg_value_zero hcU hclass h]
    · simp
  case e278 =>
    simp only [circuit_norm, eARE, eRNEGV 0 (by norm_num), wRnegWitness]
    split_ifs with h
    · simp [wRneg_value_zero hclass h]
    · simp
  case e280 =>
    simp only [circuit_norm, eARE, eRNEGV 1 (by norm_num), wRnegWitness]
    split_ifs with h
    · simp [wRneg_value_zero hclass h]
    · simp
  case e282 =>
    simp only [circuit_norm, eARE, eRNEGV 2 (by norm_num), wRnegWitness]
    split_ifs with h
    · simp [wRneg_value_zero hclass h]
    · simp
  case e284 =>
    simp only [circuit_norm, eARE, eRNEGV 3 (by norm_num), wRnegWitness]
    split_ifs with h
    · simp [wRneg_value_zero hclass h]
    · simp
  case e286 =>
    simp only [circuit_norm, eACE, eCN, eIR]; ring
  case e288 =>
    simp only [circuit_norm, eARE, eRN, eIR]; ring
  case e299 =>
    simp only [circuit_norm, eMAX 0 (by norm_num), eISC0, eABSC 0 (by norm_num)]
    rw [maxAbs_limb0 hcU F]; ring
  case e300 =>
    simp only [circuit_norm, eMAX 1 (by norm_num), eISC0, eABSC 1 (by norm_num)]
    rw [maxAbs_limbk hcU F 1 (by norm_num) (by norm_num)]; ring
  case e301 =>
    simp only [circuit_norm, eMAX 2 (by norm_num), eISC0, eABSC 2 (by norm_num)]
    rw [maxAbs_limbk hcU F 2 (by norm_num) (by norm_num)]; ring
  case e302 =>
    simp only [circuit_norm, eMAX 3 (by norm_num), eISC0, eABSC 3 (by norm_num)]
    rw [maxAbs_limbk hcU F 3 (by norm_num) (by norm_num)]; ring
  case e305 =>
    simp only [circuit_norm, eISC0, eIR, eRCM, ltGate]; ring
  case e307 =>
    simp only [circuit_norm, eRCM, eLTBIT]
    rcases hltgate with h | h
    · rw [h]; ring
    · rw [h, ltBit_one_of_gate hcU hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h]; ring
  case e311 =>
    simp only [circuit_norm, eCARRY 1 (by norm_num)]
    rcases populateCarry_bool B C hsig 1 (by norm_num) with h | h <;> rw [h] <;> ring
  case e313 =>
    simp only [circuit_norm, eCARRY 2 (by norm_num)]
    rcases populateCarry_bool B C hsig 2 (by norm_num) with h | h <;> rw [h] <;> ring
  case e315 =>
    simp only [circuit_norm, eCARRY 3 (by norm_num)]
    rcases populateCarry_bool B C hsig 3 (by norm_num) with h | h <;> rw [h] <;> ring
  case e317 =>
    simp only [circuit_norm, eCARRY 4 (by norm_num)]
    rcases populateCarry_bool B C hsig 4 (by norm_num) with h | h <;> rw [h] <;> ring
  case e319 =>
    simp only [circuit_norm, eCARRY 5 (by norm_num)]
    rcases populateCarry_bool B C hsig 5 (by norm_num) with h | h <;> rw [h] <;> ring
  case e321 =>
    simp only [circuit_norm, eCARRY 6 (by norm_num)]
    rcases populateCarry_bool B C hsig 6 (by norm_num) with h | h <;> rw [h] <;> ring
  case e323 =>
    simp only [circuit_norm, eCARRY 7 (by norm_num)]
    rcases populateCarry_bool B C hsig 7 (by norm_num) with h | h <;> rw [h] <;> ring
  case e327 =>
    simp only [circuit_norm, eF1]; rcases hf1 with h | h <;> rw [h] <;> ring
  case e329 =>
    simp only [circuit_norm, eF2]; rcases hf2 with h | h <;> rw [h] <;> ring
  case e331 =>
    simp only [circuit_norm, eF3]; rcases hf3 with h | h <;> rw [h] <;> ring
  case e333 =>
    simp only [circuit_norm, eF4]; rcases hf4 with h | h <;> rw [h] <;> ring
  case e335 =>
    simp only [circuit_norm, eF5]; rcases hf5 with h | h <;> rw [h] <;> ring
  case e337 =>
    simp only [circuit_norm, eF6]; rcases hf6 with h | h <;> rw [h] <;> ring
  case e339 =>
    simp only [circuit_norm, eF7]; rcases hf7 with h | h <;> rw [h] <;> ring
  case e341 =>
    simp only [circuit_norm, eOV]
    rcases populateIsOverflow_bool ir B C hsig with h | h <;> rw [h] <;> ring
  case e343 =>
    simp only [circuit_norm, eIRNW]
    rcases hbin with h | h <;> rcases hword with hw | hw <;> rw [h, hw] <;> ring
  case e345 =>
    simp only [circuit_norm, eBN]
    rcases populateBNeg_bool hbU hsig with h | h <;> rw [h] <;> ring
  case e347 =>
    simp only [circuit_norm, eBNNO]
    rcases populateBNeg_bool hbU hsig with h | h <;>
      rcases populateIsOverflow_bool ir B C hsig with h' | h' <;> rw [h, h'] <;> ring
  case e349 =>
    simp only [circuit_norm, eBNNNO]
    rcases populateBNeg_bool hbU hsig with h | h <;>
      rcases populateIsOverflow_bool ir B C hsig with h' | h' <;> rw [h, h'] <;> ring
  case e351 =>
    simp only [circuit_norm, eRN]
    rcases populateRemNeg_bool B C hsig with h | h <;> rw [h] <;> ring
  case e353 =>
    simp only [circuit_norm, eCN]
    rcases populateCNeg_bool hcU hsig with h | h <;> rw [h] <;> ring
  case e355 =>
    simp only [circuit_norm, eIR]; rcases hbin with h | h <;> rw [h] <;> ring
  case e357 =>
    simp only [circuit_norm, eACE]
    rcases populateCNeg_bool hcU hsig with h | h <;> rcases hbin with h' | h' <;>
      rw [h, h'] <;> ring
  case e359 =>
    simp only [circuit_norm, eARE]
    rcases populateRemNeg_bool B C hsig with h | h <;> rcases hbin with h' | h' <;>
      rw [h, h'] <;> ring

end SP1Clean.DivRemChip
