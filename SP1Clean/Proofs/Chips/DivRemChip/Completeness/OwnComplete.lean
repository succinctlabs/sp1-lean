import SP1Clean.Proofs.Chips.DivRemChip.Defs
import SP1Clean.Native.Operations.DivRemOperation.OwnAsserts
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Abs
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Bounds
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Euclid
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Glue
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Shapes
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Signs

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

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


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
  refine ⟨?_, ?_, ?_, ?_⟩ <;> apply ZMod.val_injective <;>
    simp only [ZMod.val_zero, val_32768_zmod_p] <;> omega

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
  refine ⟨?_, ?_⟩ <;> apply ZMod.val_injective <;>
    simp only [ZMod.val_zero, val_32768_zmod_p] <;> omega

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

omit [Fact (2 ^ 24 < p)] in
/-- Per-element eval pin from a whole-vector one. The whole-vector form is what the caller may state
in a *signature* without forcing a `GetElem`-size whnf of the heavy `populate*` witnesses; this
recovers the element form cheaply inside a proof body. -/
private lemma eval_getElem {n : ℕ} {env : Environment (ZMod p)}
    {v : Vector (Expression (ZMod p)) n} {w : Vector (ZMod p) n}
    (h : Vector.map (Expression.eval env) v = w) (i : ℕ) (hi : i < n) :
    Expression.eval env (v[i]'hi) = w[i]'hi := by
  rw [← h, Vector.getElem_map]

set_option linter.unusedVariables false in
/-- Every own-assert (`ownAsserts colsV`) evaluates to `0` at the honest populate witnesses, given the
per-column eval pins. -/
theorem ownAsserts_complete (env : Environment (ZMod p)) (colsV : Var Columns (ZMod p))
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
    -- bullets use are recovered cheaply in the proof body via `eval_getElem`.
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
  -- part of the lemma's Pi-type) from the whole-vector signature pins. Their bound is the vector's
  -- own length, so each is usable as an unapplied quantified `simp only` rule.
  have eB := eval_getElem eBvec
  have eC := eval_getElem eCvec
  have eQ := eval_getElem eQvec
  have eQC := eval_getElem eQCvec
  have eR := eval_getElem eRvec
  have eRC := eval_getElem eRCvec
  have eA := eval_getElem eAvec
  have eABSC := eval_getElem eABSCvec
  have eABSR := eval_getElem eABSRvec
  have eMAX := eval_getElem eMAXvec
  have eCTQ := eval_getElem eCTQvec
  have eCARRY := eval_getElem eCARRYvec
  have eCNEGV := eval_getElem eCNEGVvec
  have eRNEGV := eval_getElem eRNEGVvec
  have eBPV := eval_getElem eBPVvec
  have eCPV := eval_getElem eCPVvec
  have hclass := flagClassTrichotomy hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
  have hsig := sig_bool_of_class hclass
  have hcb := populateCarry_bool B C hsig
  have hbn := populateBNeg_bool hbU hsig
  have hcn := populateCNeg_bool hcU hsig
  have hrn := populateRemNeg_bool B C hsig
  have hovb := populateIsOverflow_bool ir B C hsig
  have hisc0 := isC0_result_bool C F
  have hltgate := ltGate_bool C F hbin
  have hgates : (F[4] + F[5] + F[6] + F[7] = 0 ∨ F[4] + F[5] + F[6] + F[7] = 1)
      ∧ (F[6] + F[7] = 0 ∨ F[6] + F[7] = 1)
      ∧ (F[4] + F[5] = 0 ∨ F[4] + F[5] = 1)
      ∧ (F[1] + F[3] + F[0] + F[2] = 0 ∨ F[1] + F[3] + F[0] + F[2] = 1)
      ∧ (F[1] + F[0] + F[4] + F[6] = 0 ∨ F[1] + F[0] + F[4] + F[6] = 1)
      ∧ (F[3] + F[2] + F[5] + F[7] = 0 ∨ F[3] + F[2] + F[5] + F[7] = 1) := by
    rcases flags_cases hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum with
      g | g | g | g | g | g | g | g <;> obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7⟩ := g <;>
      simp only [g0, g1, g2, g3, g4, g5, g6, g7] <;> norm_num
  obtain ⟨hword, he67, he45, he64bit, hdivgate, hremgate⟩ := hgates
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
  case e13 => simp only [circuit_norm, eIRNW, eIR, eF4, eF5, eF6, eF7]; ring
  case e15 | e17 | e19 =>
    simp only [circuit_norm, eBM, eRM, eCM, eBN, eRN, eCN, eF0, eF2, eF4, eF5, populateBNeg_def,
      populateRemNeg_def, populateCNeg_def]; ring
  case e20 | e21 | e22 | e23 =>
    simp only [circuit_norm, eBPV, eCPV, eB, eC, bComp_limb0, bComp_limb1, cComp_limb0,
      cComp_limb1]; ring
  case e29 | e35 | e41 | e47 =>
    simp only [circuit_norm, eB, eC, eBPV, eCPV, eBN, eCN, eF4, eF5, eF6, eF7,
      bComp_limb2 B hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum,
      bComp_limb3 B hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum,
      cComp_limb2 C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum,
      cComp_limb3 C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum]; ring
  case e48 | e49 | e70 | e71 =>
    simp only [circuit_norm, eQC, eQ, eRC, eR, quotComp_limb0, quotComp_limb1, remComp_limb0,
      remComp_limb1]; ring
  case e51 | e61 | e73 | e83 =>
    simp only [circuit_norm, eF6, eF7, eQC, eRC]
    rcases he67 with h | h
    · rw [h]; ring
    · obtain ⟨q2, q3⟩ := quotComp_hi_unsignedW B C h
      obtain ⟨r2, r3⟩ := remComp_hi_unsignedW B C h
      simp only [q2, q3, r2, r3]; ring
  case e54 | e64 | e76 | e86 =>
    simp only [circuit_norm, eF4, eF5, eQC, eRC, eQM, eRM]
    rcases he45 with h | h
    · rw [h]; ring
    · obtain ⟨q2, q3⟩ := quotComp_hi_signedW B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h
      obtain ⟨r2, r3⟩ := remComp_hi_signedW B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h
      simp only [q2, q3, r2, r3]; ring
  case e57 | e67 | e79 | e89 =>
    simp only [circuit_norm, eF4, eF5, eF6, eF7, eQ, eR, eQM, eRM]
    rcases hword with h | h
    · rw [h]; ring
    · obtain ⟨q2, q3⟩ := quotient_hi_word B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h
      obtain ⟨r2, r3⟩ := remainder_hi_word B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h
      simp only [q2, q3, r2, r3]; ring
  case e59 | e69 | e81 | e91 =>
    simp only [circuit_norm, eF0, eF1, eF2, eF3, eQC, eQ, eRC, eR]
    rcases he64bit with h | h
    · rw [h]; ring
    · obtain ⟨q2, q3⟩ := quotComp_hi_64 B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
        (by linear_combination h)
      obtain ⟨r2, r3⟩ := remComp_hi_64 B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum
        (by linear_combination h)
      simp only [q2, q3, r2, r3]; ring
  case e96 =>
    simp only [circuit_norm, eOV, eOVBR, eOVCR, eF0, eF2, eF4, eF5, populateIsOverflow]; ring
  case e99 | e103 => simp only [circuit_norm, eBNNO, eBNNNO, eBN, eOV]; ring
  case e105 | e109 | e113 | e117 =>
    simp only [circuit_norm, eOV, eQ, eB]
    rcases hovb with h | h
    · rw [h]; ring
    · rw [(hOvWB h).1]; ring
  case e107 | e111 | e115 | e119 =>
    simp only [circuit_norm, eOV, eR]
    rcases hovb with h | h
    · rw [h]; ring
    · rw [(hOvWB h).2]; simp
  case e154 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨c1, _, _, _, _, _, _, _⟩ := heu
      simp only [circuit_norm, eB, eCTQ, eRC, eCARRY, c1]; ring
  case e157 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, c2, _, _, _, _, _, _⟩ := heu
      simp only [circuit_norm, eB, eCTQ, eRC, eCARRY, c2]; ring
  case e160 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, _, c3, _, _, _, _, _⟩ := heu
      simp only [circuit_norm, eB, eCTQ, eRC, eCARRY, c3]; ring
  case e163 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, _, _, c4, _, _, _, _⟩ := heu
      simp only [circuit_norm, eB, eCTQ, eRC, eCARRY, c4]; ring
  case e167 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, _, _, _, c5, _, _, _⟩ := heu
      simp only [circuit_norm, eBN, eRN, eCTQ, eCARRY]
      push_cast at c5; rw [c5]; ring
  case e171 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, _, _, _, _, c6, _, _⟩ := heu
      simp only [circuit_norm, eBN, eRN, eCTQ, eCARRY]
      push_cast at c6; rw [c6]; ring
  case e175 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, _, _, _, _, _, c7, _⟩ := heu
      simp only [circuit_norm, eBN, eRN, eCTQ, eCARRY]
      push_cast at c7; rw [c7]; ring
  case e179 =>
    rcases hEU with hov | heu
    · simp only [circuit_norm, eOV, hov]; ring
    · obtain ⟨_, _, _, _, _, _, _, c8⟩ := heu
      simp only [circuit_norm, eBN, eRN, eCTQ, eCARRY]
      push_cast at c8; rw [c8]; ring
  case e184 | e194 | e204 | e214 =>
    simp only [circuit_norm, eF0, eF1, eF4, eF6, eQ, eA]
    rcases hdivgate with h | h
    · rw [h]; ring
    · rw [populateA_div B C (by linear_combination h)]; ring
  case e189 | e199 | e209 | e219 =>
    simp only [circuit_norm, eF2, eF3, eF5, eF7, eR, eA]
    rcases hremgate with h | h
    · rw [h]; ring
    · rw [populateA_rem B C hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum (by linear_combination h)]; ring
  case e225 =>
    simp only [circuit_norm, eRN, eBN]
    linear_combination remNeg_mul_bNeg_sub_one (C := C) hbU hclass
  case e228 =>
    simp only [circuit_norm, eR, eRN, eBN]
    linear_combination rem_nonzero_nonneg_imp_bNonneg hbU hclass
  case e230 | e232 | e234 | e236 =>
    simp only [circuit_norm, eISC0, eQ]
    rcases hisc0 with h | h
    · rw [h]; ring
    · simp only [h, isC0_one_quotient (B := B) hcU h]; ring
  case e238 | e240 | e242 | e244 =>
    simp only [circuit_norm, eISC0, eRC, eB]
    rcases hisc0 with h | h
    · rw [h]; ring
    · rw [h, isC0_one_remComp hbU hcU hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h]; ring
  case e247 | e253 | e259 | e265 =>
    simp only [circuit_norm, eCN, eC, eABSC]
    rcases hcn with h | h
    · rw [absC_eq_of_not_neg hcU hclass h, h]; ring
    · rw [h]; ring
  case e250 | e256 | e262 | e268 =>
    simp only [circuit_norm, eRN, eRC, eABSR]
    rcases hrn with h | h
    · rw [absRem_eq_of_not_neg hclass h, h]; ring
    · rw [h]; ring
  case e270 | e272 | e274 | e276 =>
    simp only [circuit_norm, eACE, eCNEGV, wCnegWitness]
    split_ifs with h
    · simp [wCneg_value_zero hcU hclass h]
    · simp
  case e278 | e280 | e282 | e284 =>
    simp only [circuit_norm, eARE, eRNEGV, wRnegWitness]
    split_ifs with h
    · simp [wRneg_value_zero hclass h]
    · simp
  case e286 | e288 => simp only [circuit_norm, eACE, eARE, eCN, eRN, eIR]; ring
  case e299 =>
    simp only [circuit_norm, eMAX, eISC0, eABSC]
    rw [maxAbs_limb0 hcU F]; ring
  case e300 =>
    simp only [circuit_norm, eMAX, eISC0, eABSC]
    rw [maxAbs_limbk hcU F 1 (by norm_num) (by norm_num)]; ring
  case e301 =>
    simp only [circuit_norm, eMAX, eISC0, eABSC]
    rw [maxAbs_limbk hcU F 2 (by norm_num) (by norm_num)]; ring
  case e302 =>
    simp only [circuit_norm, eMAX, eISC0, eABSC]
    rw [maxAbs_limbk hcU F 3 (by norm_num) (by norm_num)]; ring
  case e305 => simp only [circuit_norm, eISC0, eIR, eRCM, ltGate]; ring
  case e307 =>
    simp only [circuit_norm, eRCM, eLTBIT]
    rcases hltgate with h | h
    · rw [h]; ring
    · rw [h, ltBit_one_of_gate hcU hf0 hf1 hf2 hf3 hf4 hf5 hf6 hf7 hsum h]; ring
  case e309 =>
    simp only [circuit_norm, eCARRY]; rcases hcb 0 (by norm_num) with h | h <;> rw [h] <;> ring
  case e311 =>
    simp only [circuit_norm, eCARRY]; rcases hcb 1 (by norm_num) with h | h <;> rw [h] <;> ring
  case e313 =>
    simp only [circuit_norm, eCARRY]; rcases hcb 2 (by norm_num) with h | h <;> rw [h] <;> ring
  case e315 =>
    simp only [circuit_norm, eCARRY]; rcases hcb 3 (by norm_num) with h | h <;> rw [h] <;> ring
  case e317 =>
    simp only [circuit_norm, eCARRY]; rcases hcb 4 (by norm_num) with h | h <;> rw [h] <;> ring
  case e319 =>
    simp only [circuit_norm, eCARRY]; rcases hcb 5 (by norm_num) with h | h <;> rw [h] <;> ring
  case e321 =>
    simp only [circuit_norm, eCARRY]; rcases hcb 6 (by norm_num) with h | h <;> rw [h] <;> ring
  case e323 =>
    simp only [circuit_norm, eCARRY]; rcases hcb 7 (by norm_num) with h | h <;> rw [h] <;> ring
  case e325 => simp only [circuit_norm, eF0]; rcases hf0 with h | h <;> rw [h] <;> ring
  case e327 => simp only [circuit_norm, eF1]; rcases hf1 with h | h <;> rw [h] <;> ring
  case e329 => simp only [circuit_norm, eF2]; rcases hf2 with h | h <;> rw [h] <;> ring
  case e331 => simp only [circuit_norm, eF3]; rcases hf3 with h | h <;> rw [h] <;> ring
  case e333 => simp only [circuit_norm, eF4]; rcases hf4 with h | h <;> rw [h] <;> ring
  case e335 => simp only [circuit_norm, eF5]; rcases hf5 with h | h <;> rw [h] <;> ring
  case e337 => simp only [circuit_norm, eF6]; rcases hf6 with h | h <;> rw [h] <;> ring
  case e339 => simp only [circuit_norm, eF7]; rcases hf7 with h | h <;> rw [h] <;> ring
  case e341 => simp only [circuit_norm, eOV]; rcases hovb with h | h <;> rw [h] <;> ring
  case e343 =>
    simp only [circuit_norm, eIRNW]
    rcases hbin with h | h <;> rcases hword with hw | hw <;> rw [h, hw] <;> ring
  case e345 => simp only [circuit_norm, eBN]; rcases hbn with h | h <;> rw [h] <;> ring
  case e347 | e349 =>
    simp only [circuit_norm, eBNNO, eBNNNO]
    rcases hbn with h | h <;> rcases hovb with h' | h' <;> rw [h, h'] <;> ring
  case e351 => simp only [circuit_norm, eRN]; rcases hrn with h | h <;> rw [h] <;> ring
  case e353 => simp only [circuit_norm, eCN]; rcases hcn with h | h <;> rw [h] <;> ring
  case e355 => simp only [circuit_norm, eIR]; rcases hbin with h | h <;> rw [h] <;> ring
  case e357 =>
    simp only [circuit_norm, eACE]
    rcases hcn with h | h <;> rcases hbin with h' | h' <;> rw [h, h'] <;> ring
  case e359 =>
    simp only [circuit_norm, eARE]
    rcases hrn with h | h <;> rcases hbin with h' | h' <;> rw [h, h'] <;> ring
  case e367 =>
    simp only [circuit_norm, eF0, eF1, eF2, eF3, eF4, eF5, eF6, eF7]; linear_combination -hsum
  case eopa0 => simp only [circuit_norm, eOPA0]

end SP1Clean.DivRemChip
