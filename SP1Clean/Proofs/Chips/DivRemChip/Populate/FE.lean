import SP1Clean.Proofs.Chips.DivRemChip.Populate.IRCtq

/-! # `DivRemChip` — the per-site witness-IR payloads (A7c)

One exportable payload per `populateRow` witness site, each a pure function of the raw operand
read expressions (`B`/`C` — `adapter.op_b/c_memory.prev_value`) and, where SP1 gates the populate,
the `is_real` input expression. Every payload carries one eval lemma equating its cells to the
corresponding value-layer populate at the evaluated words — under the flag binarities that
`ProverAssumptions` provides (dishonest hints may put arbitrary field elements in the seven
hinted slots; the completeness seam only ever evaluates these payloads under the contract).

The dispatch calculus is `Populate/IR.lean`, the word bridges `Populate/IRWord.lean`, the
128-bit product block `Populate/IRCtq.lean`; the sub-operation struct twins live beside their
operations (`MulOperation.populateFEW`, `AddOperation.populateFW`,
`IsZeroWordOperation.populateFE`, `IsEqualWordOperation.populateFE`). -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

/-! ## Shared flag sums and result words -/

section Payloads

/-- The signed-class selector `is_div + is_rem + is_divw + is_remw`. -/
def signedSumF : Witgen.FExpr (ZMod p) := flagF 0 + flagF 2 + flagF 4 + flagF 5

/-- The W-class selector `is_divw + is_remw + is_divuw + is_remuw`. -/
def wSumF : Witgen.FExpr (ZMod p) := flagF 4 + flagF 5 + flagF 6 + flagF 7

/-- The 64-bit-class selector `is_div + is_divu + is_rem + is_remu`. -/
def longSumF : Witgen.FExpr (ZMod p) := flagF 0 + flagF 1 + flagF 2 + flagF 3

/-- The flags site (8 cells; `flagF` derives `is_divu`). -/
def flagsFE : Vector (Witgen.FExpr (ZMod p)) 8 :=
  #v[flagF 0, flagF 1, flagF 2, flagF 3, flagF 4, flagF 5, flagF 6, flagF 7]

/-- The `quotient` word site. -/
def quotFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  wordFOfU64 (quotBitsU (wordU B) (wordU C))

/-- The `remainder` word site. -/
def remFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  wordFOfU64 (remBitsU (wordU B) (wordU C))

/-- The `quotient_comp` word site. -/
def quotCompFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  wordFOfU64 (quotCompBitsU (wordU B) (wordU C))

/-- The `remainder_comp` word site. -/
def remCompFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  wordFOfU64 (remCompBitsU (wordU B) (wordU C))

/-- The result word `a` site (quotient on the div classes, remainder on the rem classes). -/
def aFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  Vector.ofFn fun i =>
    .ite (((flagF 0 : Witgen.FExpr (ZMod p)) + flagF 1 + flagF 4 + flagF 6) =? (1 : ZMod p))
      (quotFE B C)[i]
      (.ite (((flagF 2 : Witgen.FExpr (ZMod p)) + flagF 3 + flagF 5 + flagF 7) =? (1 : ZMod p))
        (remFE B C)[i] 0)

end Payloads

/-! ## Eval lemmas (word/result sites) -/

section PayloadEval

variable (env : ProverEnvironment (ZMod p))

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating the flags site is `hintFlags`. -/
theorem flagsFE_eval (i : ℕ) (hi : i < 8) :
    ((flagsFE (p := p))[i]).eval { env := env } = (hintFlags env.hint)[i] := by
  interval_cases i <;>
    simpa only [flagsFE, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ] using flagF_eval env _ (by omega)

variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)

include hWB hWC hUB hUC

/-- Evaluating the `quotient` site is `populateQuotient`. -/
theorem quotFE_eval (i : ℕ) (hi : i < 4) :
    ((quotFE B C)[i]).eval { env := env }
      = (populateQuotient vB vC (hintFlags env.hint))[i] :=
  wordFOfU64_eval env _ (quotBitsU_toNat env B C vB vC hWB hWC hUB hUC) i hi

/-- Evaluating the `remainder` site is `populateRemainder`. -/
theorem remFE_eval (i : ℕ) (hi : i < 4) :
    ((remFE B C)[i]).eval { env := env }
      = (populateRemainder vB vC (hintFlags env.hint))[i] :=
  wordFOfU64_eval env _ (remBitsU_toNat env B C vB vC hWB hWC hUB hUC) i hi

/-- Evaluating the `quotient_comp` site is `populateQuotComp`. -/
theorem quotCompFE_eval (i : ℕ) (hi : i < 4) :
    ((quotCompFE B C)[i]).eval { env := env }
      = (populateQuotComp vB vC (hintFlags env.hint))[i] :=
  wordFOfU64_eval env _ (quotCompBitsU_toNat env B C vB vC hWB hWC hUB hUC) i hi

/-- Evaluating the `remainder_comp` site is `populateRemComp`. -/
theorem remCompFE_eval (i : ℕ) (hi : i < 4) :
    ((remCompFE B C)[i]).eval { env := env }
      = (populateRemComp vB vC (hintFlags env.hint))[i] :=
  wordFOfU64_eval env _ (remCompBitsU_toNat env B C vB vC hWB hWC hUB hUC) i hi

/-- Evaluating the result-word site is `populateA`. -/
theorem aFE_eval (i : ℕ) (hi : i < 4) :
    ((aFE B C)[i]).eval { env := env } = (populateA vB vC (hintFlags env.hint))[i] := by
  have hf0 := flagF_eval env 0 (by omega)
  have hf1 := flagF_eval env 1 (by omega)
  have hf2 := flagF_eval env 2 (by omega)
  have hf3 := flagF_eval env 3 (by omega)
  have hf4 := flagF_eval env 4 (by omega)
  have hf5 := flagF_eval env 5 (by omega)
  have hf6 := flagF_eval env 6 (by omega)
  have hf7 := flagF_eval env 7 (by omega)
  have hq := quotFE_eval env B C vB vC hWB hWC hUB hUC i hi
  have hr := remFE_eval env B C vB vC hWB hWC hUB hUC i hi
  simp only [aFE, populateA, circuit_norm, Vector.getElem_ofFn,
    hf0, hf1, hf2, hf3, hf4, hf5, hf6, hf7]
  split_ifs
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans hq
  · contradiction
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans hr
  · contradiction
  · contradiction
  · interval_cases i <;> simp

end PayloadEval

/-! ## MSB cells, sign scalars, absolute-value words -/

section MsbSign

/-- The shared `b_msb` cell site (raw-read limb 1 on the W classes, limb 3 otherwise). -/
def bMsbFE (B : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  .ite ((wSumF (p := p)) =? (1 : ZMod p))
    (U16MSBOperation.populate_msbF (.expr B[1])) (U16MSBOperation.populate_msbF (.expr B[3]))

/-- The shared `c_msb` cell site. -/
def cMsbFE (C : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  .ite ((wSumF (p := p)) =? (1 : ZMod p))
    (U16MSBOperation.populate_msbF (.expr C[1])) (U16MSBOperation.populate_msbF (.expr C[3]))

/-- The shared `rem_msb` cell site (on the populated remainder). -/
def remMsbFE (B C : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  .ite ((wSumF (p := p)) =? (1 : ZMod p))
    (U16MSBOperation.populate_msbF (remFE B C)[1]) (U16MSBOperation.populate_msbF (remFE B C)[3])

/-- The `quot_msb` cell site (W classes only; zero elsewhere). -/
def quotMsbFE (B C : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  .ite ((wSumF (p := p)) =? (1 : ZMod p))
    (U16MSBOperation.populate_msbF (quotFE B C)[1]) 0

/-- `b_neg = is_signed_type · b_msb`. -/
def bNegFE (B : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  signedSumF * bMsbFE B

/-- `c_neg = is_signed_type · c_msb`. -/
def cNegFE (C : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  signedSumF * cMsbFE C

/-- `rem_neg = is_signed_type · rem_msb`. -/
def remNegFE (B C : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  signedSumF * remMsbFE B C

end MsbSign

section MsbSignEval

variable (env : ProverEnvironment (ZMod p))

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating the W-class selector is the flag sum. -/
theorem wSumF_eval :
    (wSumF (p := p)).eval { env := env }
      = (hintFlags env.hint)[4] + (hintFlags env.hint)[5]
        + (hintFlags env.hint)[6] + (hintFlags env.hint)[7] := by
  simp only [wSumF, circuit_norm, flagF_eval env 4 (by omega), flagF_eval env 5 (by omega),
    flagF_eval env 6 (by omega), flagF_eval env 7 (by omega)]

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating the signed-class selector is the flag sum. -/
theorem signedSumF_eval :
    (signedSumF (p := p)).eval { env := env }
      = (hintFlags env.hint)[0] + (hintFlags env.hint)[2]
        + (hintFlags env.hint)[4] + (hintFlags env.hint)[5] := by
  simp only [signedSumF, circuit_norm, flagF_eval env 0 (by omega), flagF_eval env 2 (by omega),
    flagF_eval env 4 (by omega), flagF_eval env 5 (by omega)]

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating the 64-bit-class selector is the flag sum. -/
theorem longSumF_eval :
    (longSumF (p := p)).eval { env := env }
      = (hintFlags env.hint)[0] + (hintFlags env.hint)[1]
        + (hintFlags env.hint)[2] + (hintFlags env.hint)[3] := by
  simp only [longSumF, circuit_norm, flagF_eval env 0 (by omega), flagF_eval env 1 (by omega),
    flagF_eval env 2 (by omega), flagF_eval env 3 (by omega)]

variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)


omit [Fact (2 ^ 24 < p)] in
include hWB hUB in
/-- Evaluating the `b_msb` site is `bMsbCell`. -/
theorem bMsbFE_eval :
    (bMsbFE B).eval { env := env } = bMsbCell vB (hintFlags env.hint) := by
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hUB
  have h1 := hWB 1 (by omega)
  have h3 := hWB 3 (by omega)
  have hm1 := U16MSBOperation.populate_msbF_eval { env := env } (.expr B[1])
    (by simp only [circuit_norm, h1]; exact u1)
  have hm3 := U16MSBOperation.populate_msbF_eval { env := env } (.expr B[3])
    (by simp only [circuit_norm, h3]; exact u3)
  simp only [circuit_norm, h1, h3] at hm1 hm3
  simp only [bMsbFE, bMsbCell, circuit_norm, wSumF_eval env]
  split_ifs
  · exact hm1
  · exact hm3

omit [Fact (2 ^ 24 < p)] in
include hWC hUC in
/-- Evaluating the `c_msb` site is `cMsbCell`. -/
theorem cMsbFE_eval :
    (cMsbFE C).eval { env := env } = cMsbCell vC (hintFlags env.hint) := by
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hUC
  have h1 := hWC 1 (by omega)
  have h3 := hWC 3 (by omega)
  have hm1 := U16MSBOperation.populate_msbF_eval { env := env } (.expr C[1])
    (by simp only [circuit_norm, h1]; exact u1)
  have hm3 := U16MSBOperation.populate_msbF_eval { env := env } (.expr C[3])
    (by simp only [circuit_norm, h3]; exact u3)
  simp only [circuit_norm, h1, h3] at hm1 hm3
  simp only [cMsbFE, cMsbCell, circuit_norm, wSumF_eval env]
  split_ifs
  · exact hm1
  · exact hm3

include hWB hWC hUB hUC in
/-- Evaluating the `rem_msb` site is `remMsbCell`. -/
theorem remMsbFE_eval :
    (remMsbFE B C).eval { env := env } = remMsbCell vB vC (hintFlags env.hint) := by
  obtain ⟨w0, w1, w2, w3⟩ :=
    Word.lt_cases_of_isU64 (wordOfBits_isU64 (p := p) (remBits vB vC (hintFlags env.hint)))
  have hr1 := remFE_eval env B C vB vC hWB hWC hUB hUC 1 (by omega)
  have hr3 := remFE_eval env B C vB vC hWB hWC hUB hUC 3 (by omega)
  have hm1 := U16MSBOperation.populate_msbF_eval { env := env } (remFE B C)[1]
    (by rw [hr1]; exact w1)
  have hm3 := U16MSBOperation.populate_msbF_eval { env := env } (remFE B C)[3]
    (by rw [hr3]; exact w3)
  rw [hr1] at hm1
  rw [hr3] at hm3
  simp only [remMsbFE, remMsbCell, circuit_norm, wSumF_eval env]
  split_ifs
  · exact hm1
  · exact hm3

include hWB hWC hUB hUC in
/-- Evaluating the `quot_msb` site is `quotMsbCell`. -/
theorem quotMsbFE_eval :
    (quotMsbFE B C).eval { env := env } = quotMsbCell vB vC (hintFlags env.hint) := by
  obtain ⟨w0, w1, w2, w3⟩ :=
    Word.lt_cases_of_isU64 (wordOfBits_isU64 (p := p) (quotBits vB vC (hintFlags env.hint)))
  have hq1 := quotFE_eval env B C vB vC hWB hWC hUB hUC 1 (by omega)
  have hm1 := U16MSBOperation.populate_msbF_eval { env := env } (quotFE B C)[1]
    (by rw [hq1]; exact w1)
  rw [hq1] at hm1
  simp only [quotMsbFE, quotMsbCell, circuit_norm, wSumF_eval env]
  split_ifs
  · exact hm1
  · rfl

omit [Fact (2 ^ 24 < p)] in
include hWB hUB in
/-- Evaluating `b_neg` is `populateBNeg`. -/
theorem bNegFE_eval :
    (bNegFE B).eval { env := env } = populateBNeg vB (hintFlags env.hint) := by
  simp only [bNegFE, populateBNeg, circuit_norm, signedSumF_eval env,
    bMsbFE_eval env B vB hWB hUB]

omit [Fact (2 ^ 24 < p)] in
include hWC hUC in
/-- Evaluating `c_neg` is `populateCNeg`. -/
theorem cNegFE_eval :
    (cNegFE C).eval { env := env } = populateCNeg vC (hintFlags env.hint) := by
  simp only [cNegFE, populateCNeg, circuit_norm, signedSumF_eval env,
    cMsbFE_eval env C vC hWC hUC]

include hWB hWC hUB hUC in
/-- Evaluating `rem_neg` is `populateRemNeg`. -/
theorem remNegFE_eval :
    (remNegFE B C).eval { env := env } = populateRemNeg vB vC (hintFlags env.hint) := by
  simp only [remNegFE, populateRemNeg, circuit_norm, signedSumF_eval env,
    remMsbFE_eval env B C vB vC hWB hWC hUB hUC]

end MsbSignEval

/-! ## Absolute values and `max(|c|, 1)` -/

section AbsPayloads

/-- The `abs_c` word site. -/
def absCFE (C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  Vector.ofFn fun i =>
    .ite ((signedSumF (p := p)) =? (1 : ZMod p))
      (wordFOfU64 (absU (compU (wordU C))))[i] (compF C)[i]

/-- The `abs_remainder` word site. -/
def absRemFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  Vector.ofFn fun i =>
    .ite ((signedSumF (p := p)) =? (1 : ZMod p))
      (wordFOfU64 (absU (remBitsU (wordU B) (wordU C))))[i] (remCompFE B C)[i]

/-- The `abs_c` u64 value (for the `max_abs_c_or_1` zero test). -/
def absCU (C : Word (Expression (ZMod p))) : Witgen.U64Expr (ZMod p) :=
  .ite ((signedSumF (p := p)) =? (1 : ZMod p))
    (absU (compU (wordU C))) (compU (wordU C))

/-- The `max_abs_c_or_1` word site (`Word(1)` exactly on `abs_c = 0`). -/
def maxAbsFE (C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  #v[.ite (absCU C =? (0 : ℕ)) 1 (absCFE C)[0],
     .ite (absCU C =? (0 : ℕ)) 0 (absCFE C)[1],
     .ite (absCU C =? (0 : ℕ)) 0 (absCFE C)[2],
     .ite (absCU C =? (0 : ℕ)) 0 (absCFE C)[3]]

end AbsPayloads

section AbsEval

variable (env : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)


include hWC hUC in
/-- Evaluating the `abs_c` site is `populateAbsC`. -/
theorem absCFE_eval (i : ℕ) (hi : i < 4) :
    ((absCFE C)[i]).eval { env := env } = (populateAbsC vC (hintFlags env.hint))[i] := by
  have hcomp := compU_toNat env (wordU C) (hx := wordU_toNat env C vC hWC hUC) hUC
  have habs := absU_toNat env (compU (wordU C)) hcomp
  simp only [absCFE, populateAbsC, circuit_norm, Vector.getElem_ofFn, signedSumF_eval env]
  split_ifs
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans
      (wordFOfU64_eval env _ habs i hi)
  · contradiction
  · contradiction
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans
      (compF_eval env C vC hWC hUC i hi)

include hWB hWC hUB hUC in
/-- Evaluating the `abs_remainder` site is `populateAbsRem`. -/
theorem absRemFE_eval (i : ℕ) (hi : i < 4) :
    ((absRemFE B C)[i]).eval { env := env }
      = (populateAbsRem vB vC (hintFlags env.hint))[i] := by
  have habs := absU_toNat env (remBitsU (wordU B) (wordU C))
    (remBitsU_toNat env B C vB vC hWB hWC hUB hUC)
  simp only [absRemFE, populateAbsRem, circuit_norm, Vector.getElem_ofFn, signedSumF_eval env]
  split_ifs
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans
      (wordFOfU64_eval env _ habs i hi)
  · contradiction
  · contradiction
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans
      (remCompFE_eval env B C vB vC hWB hWC hUB hUC i hi)

include hWC hUC in
/-- Evaluating the `abs_c` u64 value is `Word.toNat (populateAbsC …)`. -/
theorem absCU_toNat :
    ((absCU C).eval { env := env }).toNat = Word.toNat (populateAbsC vC (hintFlags env.hint)) := by
  have hcomp := compU_toNat env (wordU C) (hx := wordU_toNat env C vC hWC hUC) hUC
  have habs := absU_toNat env (compU (wordU C)) hcomp
  have htn : ∀ x : BitVec 64, (Word.toBitVec64 (wordOfBits (p := p) x)).toNat = x.toNat :=
    fun x => by rw [wordOfBits_toBitVec64]
  simp only [absCU, populateAbsC, circuit_norm, signedSumF_eval env]
  split_ifs
  · rw [habs, ← Word.toBitVec64_toNat (wordOfBits_isU64 _), wordOfBits_toBitVec64]
  · rw [hcomp, Word.toBitVec64_toNat (cComp_isU64 hUC _)]

include hWC hUC in
/-- Evaluating the `max_abs_c_or_1` site is `populateMaxAbsCOr1`. -/
theorem maxAbsFE_eval (i : ℕ) (hi : i < 4) :
    ((maxAbsFE C)[i]).eval { env := env }
      = (populateMaxAbsCOr1 vC (hintFlags env.hint))[i] := by
  have hz := absCU_toNat env C vC hWC hUC
  interval_cases i <;>
    (simp only [maxAbsFE, populateMaxAbsCOr1, circuit_norm, Vector.getElem_mk,
       List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
     split_ifs <;>
       first
         | omega
         | exact (Witgen.FExpr.eval_getElem { env := env } _ 0 (by omega)).symm.trans
             (absCFE_eval env C vC hWC hUC 0 (by omega))
         | exact (Witgen.FExpr.eval_getElem { env := env } _ 1 (by omega)).symm.trans
             (absCFE_eval env C vC hWC hUC 1 (by omega))
         | exact (Witgen.FExpr.eval_getElem { env := env } _ 2 (by omega)).symm.trans
             (absCFE_eval env C vC hWC hUC 2 (by omega))
         | exact (Witgen.FExpr.eval_getElem { env := env } _ 3 (by omega)).symm.trans
             (absCFE_eval env C vC hWC hUC 3 (by omega))
         | simp [circuit_norm])

end AbsEval

end SP1Clean.DivRemChip
