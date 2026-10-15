import SP1Clean.Proofs.Chips.DivRemChip.Populate.IRCtq
import ToClean.Circuit.WitgenEval

/-! # `DivRemChip` — the per-site witness-IR payloads (A7c)

One exportable payload per `populateRow` witness site, each a pure function of the raw operand
read expressions (`B`/`C` — `adapter.op_b/c_memory.prev_value`) and, where SP1 gates the populate,
the `is_real` input expression. Every payload carries one eval lemma equating its cells to the
corresponding value-layer populate at the evaluated words — under the flag binarities that
`ProverAssumptions` provides. The seven explicit selectors may be arbitrary field elements;
the completeness seam evaluates these payloads under its Boolean-selector contract.

The dispatch calculus is `Populate/IR.lean`, the word bridges `Populate/IRWord.lean`, the
128-bit product block `Populate/IRCtq.lean`; the sub-operation struct twins live beside their
operations (`MulOperation.populateFEW`, `AddOperation.populateFW`,
`IsZeroWordOperation.populateFE`, `IsEqualWordOperation.populateFE`). -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
variable (selectors : Vector (Expression (ZMod p)) 7)

omit [Fact (2 ^ 24 < p)] in
/-- A field-equality condition holds when the operand evaluates to the constant
(`BExpr.eval_feq_iff` with the constant's evaluation folded). -/
private lemma feq_true (env : ProverEnvironment (ZMod p)) (x : Witgen.FExpr (ZMod p))
    (v c : ZMod p) (hx : x.eval { env := env } = v) (h : v = c) :
    (x =? c).eval { env := env } = true :=
  (Witgen.BExpr.eval_feq_iff _ _ _).mpr (by
    rw [hx, show Witgen.FExpr.eval { env := env } (Witgen.FExpr.const c) = c from rfl, h])

omit [Fact (2 ^ 24 < p)] in
/-- A field-equality condition fails when the operand's value differs from the constant. -/
private lemma feq_false (env : ProverEnvironment (ZMod p)) (x : Witgen.FExpr (ZMod p))
    (v c : ZMod p) (hx : x.eval { env := env } = v) (h : ¬ v = c) :
    ¬ (x =? c).eval { env := env } = true := fun hb => h (by
  have hx' := (Witgen.BExpr.eval_feq_iff _ _ _).mp hb
  rwa [hx, show Witgen.FExpr.eval { env := env } (Witgen.FExpr.const c) = c from rfl] at hx')

/-! ## Shared flag sums and result words -/

section Payloads

/-- The signed-class selector `is_div + is_rem + is_divw + is_remw`. -/
def signedSumF : Witgen.FExpr (ZMod p) := flagF selectors 0 + flagF selectors 2 + flagF selectors 4 + flagF selectors 5

/-- The W-class selector `is_divw + is_remw + is_divuw + is_remuw`. -/
def wSumF : Witgen.FExpr (ZMod p) := flagF selectors 4 + flagF selectors 5 + flagF selectors 6 + flagF selectors 7

/-- The 64-bit-class selector `is_div + is_divu + is_rem + is_remu`. -/
def longSumF : Witgen.FExpr (ZMod p) := flagF selectors 0 + flagF selectors 1 + flagF selectors 2 + flagF selectors 3

/-- The `quotient` word site. -/
def quotFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  wordFOfU64 (quotBitsU selectors (wordU B) (wordU C))

/-- The `remainder` word site. -/
def remFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  wordFOfU64 (remBitsU selectors (wordU B) (wordU C))

/-- The `quotient_comp` word site. -/
def quotCompFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  wordFOfU64 (quotCompBitsU selectors (wordU B) (wordU C))

/-- The `remainder_comp` word site. -/
def remCompFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  wordFOfU64 (remCompBitsU selectors (wordU B) (wordU C))

/-- The result word `a` site (quotient on the div classes, remainder on the rem classes). -/
def aFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  Vector.ofFn fun i =>
    .ite (((flagF selectors 0 : Witgen.FExpr (ZMod p)) + flagF selectors 1 + flagF selectors 4 + flagF selectors 6) =? (1 : ZMod p))
      (quotFE selectors B C)[i]
      (.ite (((flagF selectors 2 : Witgen.FExpr (ZMod p)) + flagF selectors 3 + flagF selectors 5 + flagF selectors 7) =? (1 : ZMod p))
        (remFE selectors B C)[i] 0)

end Payloads

/-! ## Eval lemmas (word/result sites) -/

section PayloadEval

variable (env : ProverEnvironment (ZMod p))

variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)

include hWB hWC hUB hUC

/-- Evaluating the `quotient` site is `populateQuotient`. -/
theorem quotFE_eval (i : ℕ) (hi : i < 4) :
    ((quotFE selectors B C)[i]).eval { env := env }
      = (populateQuotient vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] :=
  wordFOfU64_eval env _ (quotBitsU_toNat selectors env B C vB vC hWB hWC hUB hUC) i hi

/-- Evaluating the `remainder` site is `populateRemainder`. -/
theorem remFE_eval (i : ℕ) (hi : i < 4) :
    ((remFE selectors B C)[i]).eval { env := env }
      = (populateRemainder vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] :=
  wordFOfU64_eval env _ (remBitsU_toNat selectors env B C vB vC hWB hWC hUB hUC) i hi

/-- Evaluating the `quotient_comp` site is `populateQuotComp`. -/
theorem quotCompFE_eval (i : ℕ) (hi : i < 4) :
    ((quotCompFE selectors B C)[i]).eval { env := env }
      = (populateQuotComp vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] :=
  wordFOfU64_eval env _ (quotCompBitsU_toNat selectors env B C vB vC hWB hWC hUB hUC) i hi

/-- Evaluating the `remainder_comp` site is `populateRemComp`. -/
theorem remCompFE_eval (i : ℕ) (hi : i < 4) :
    ((remCompFE selectors B C)[i]).eval { env := env }
      = (populateRemComp vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] :=
  wordFOfU64_eval env _ (remCompBitsU_toNat selectors env B C vB vC hWB hWC hUB hUC) i hi

/-- Evaluating the result-word site is `populateA`. -/
theorem aFE_eval (i : ℕ) (hi : i < 4) :
    ((aFE selectors B C)[i]).eval { env := env } = (populateA vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] := by
  have hf0 := flagF_eval selectors env 0 (by omega)
  have hf1 := flagF_eval selectors env 1 (by omega)
  have hf2 := flagF_eval selectors env 2 (by omega)
  have hf3 := flagF_eval selectors env 3 (by omega)
  have hf4 := flagF_eval selectors env 4 (by omega)
  have hf5 := flagF_eval selectors env 5 (by omega)
  have hf6 := flagF_eval selectors env 6 (by omega)
  have hf7 := flagF_eval selectors env 7 (by omega)
  have hq := quotFE_eval selectors env B C vB vC hWB hWC hUB hUC i hi
  have hr := remFE_eval selectors env B C vB vC hWB hWC hUB hUC i hi
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
  .ite (((wSumF selectors)) =? (1 : ZMod p))
    (U16MSBOperation.populate_msbF (.expr B[1])) (U16MSBOperation.populate_msbF (.expr B[3]))

/-- The shared `c_msb` cell site. -/
def cMsbFE (C : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  .ite (((wSumF selectors)) =? (1 : ZMod p))
    (U16MSBOperation.populate_msbF (.expr C[1])) (U16MSBOperation.populate_msbF (.expr C[3]))

/-- The shared `rem_msb` cell site (on the populated remainder). -/
def remMsbFE (B C : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  .ite (((wSumF selectors)) =? (1 : ZMod p))
    (U16MSBOperation.populate_msbF (remFE selectors B C)[1]) (U16MSBOperation.populate_msbF (remFE selectors B C)[3])

/-- The `quot_msb` cell site (W classes only; zero elsewhere). -/
def quotMsbFE (B C : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  .ite (((wSumF selectors)) =? (1 : ZMod p))
    (U16MSBOperation.populate_msbF (quotFE selectors B C)[1]) 0

/-- `b_neg = is_signed_type · b_msb`. -/
def bNegFE (B : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  (signedSumF selectors) * bMsbFE selectors B

/-- `c_neg = is_signed_type · c_msb`. -/
def cNegFE (C : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  (signedSumF selectors) * cMsbFE selectors C

/-- `rem_neg = is_signed_type · rem_msb`. -/
def remNegFE (B C : Word (Expression (ZMod p))) : Witgen.FExpr (ZMod p) :=
  (signedSumF selectors) * remMsbFE selectors B C

end MsbSign

section MsbSignEval

variable (env : ProverEnvironment (ZMod p))

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating the W-class selector is the flag sum. -/
theorem wSumF_eval :
    ((wSumF selectors)).eval { env := env }
      = (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[4] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[5]
        + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[6] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[7] := by
  simp only [wSumF, circuit_norm, flagF_eval selectors env 4 (by omega), flagF_eval selectors env 5 (by omega),
    flagF_eval selectors env 6 (by omega), flagF_eval selectors env 7 (by omega)]

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating the signed-class selector is the flag sum. -/
theorem signedSumF_eval :
    ((signedSumF selectors)).eval { env := env }
      = (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2]
        + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[4] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[5] := by
  simp only [signedSumF, circuit_norm, flagF_eval selectors env 0 (by omega), flagF_eval selectors env 2 (by omega),
    flagF_eval selectors env 4 (by omega), flagF_eval selectors env 5 (by omega)]

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating the 64-bit-class selector is the flag sum. -/
theorem longSumF_eval :
    ((longSumF selectors)).eval { env := env }
      = (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[1]
        + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[3] := by
  simp only [longSumF, circuit_norm, flagF_eval selectors env 0 (by omega), flagF_eval selectors env 1 (by omega),
    flagF_eval selectors env 2 (by omega), flagF_eval selectors env 3 (by omega)]

variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)


omit [Fact (2 ^ 24 < p)] in
include hWB hUB in
/-- Evaluating the `b_msb` site is `bMsbCell`. -/
theorem bMsbFE_eval :
    (bMsbFE selectors B).eval { env := env } = bMsbCell vB (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hUB
  have h1 := hWB 1 (by omega)
  have h3 := hWB 3 (by omega)
  have hm1 := U16MSBOperation.populate_msbF_eval { env := env } (.expr B[1])
    (by simp only [circuit_norm, h1]; exact u1)
  have hm3 := U16MSBOperation.populate_msbF_eval { env := env } (.expr B[3])
    (by simp only [circuit_norm, h3]; exact u3)
  simp only [circuit_norm, h1, h3] at hm1 hm3
  simp only [bMsbFE, bMsbCell, circuit_norm, wSumF_eval selectors env]
  split_ifs
  · exact hm1
  · exact hm3

omit [Fact (2 ^ 24 < p)] in
include hWC hUC in
/-- Evaluating the `c_msb` site is `cMsbCell`. -/
theorem cMsbFE_eval :
    (cMsbFE selectors C).eval { env := env } = cMsbCell vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hUC
  have h1 := hWC 1 (by omega)
  have h3 := hWC 3 (by omega)
  have hm1 := U16MSBOperation.populate_msbF_eval { env := env } (.expr C[1])
    (by simp only [circuit_norm, h1]; exact u1)
  have hm3 := U16MSBOperation.populate_msbF_eval { env := env } (.expr C[3])
    (by simp only [circuit_norm, h3]; exact u3)
  simp only [circuit_norm, h1, h3] at hm1 hm3
  simp only [cMsbFE, cMsbCell, circuit_norm, wSumF_eval selectors env]
  split_ifs
  · exact hm1
  · exact hm3

include hWB hWC hUB hUC in
/-- Evaluating the `rem_msb` site is `remMsbCell`. -/
theorem remMsbFE_eval :
    (remMsbFE selectors B C).eval { env := env } = remMsbCell vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  obtain ⟨w0, w1, w2, w3⟩ :=
    Word.lt_cases_of_isU64 (wordOfBits_isU64 (p := p) (remBits vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))))
  have hr1 := remFE_eval selectors env B C vB vC hWB hWC hUB hUC 1 (by omega)
  have hr3 := remFE_eval selectors env B C vB vC hWB hWC hUB hUC 3 (by omega)
  have hm1 := U16MSBOperation.populate_msbF_eval { env := env } (remFE selectors B C)[1]
    (by rw [hr1]; exact w1)
  have hm3 := U16MSBOperation.populate_msbF_eval { env := env } (remFE selectors B C)[3]
    (by rw [hr3]; exact w3)
  rw [hr1] at hm1
  rw [hr3] at hm3
  simp only [remMsbFE, remMsbCell, circuit_norm, wSumF_eval selectors env]
  split_ifs
  · exact hm1
  · exact hm3

include hWB hWC hUB hUC in
/-- Evaluating the `quot_msb` site is `quotMsbCell`. -/
theorem quotMsbFE_eval :
    (quotMsbFE selectors B C).eval { env := env } = quotMsbCell vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  obtain ⟨w0, w1, w2, w3⟩ :=
    Word.lt_cases_of_isU64 (wordOfBits_isU64 (p := p) (quotBits vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))))
  have hq1 := quotFE_eval selectors env B C vB vC hWB hWC hUB hUC 1 (by omega)
  have hm1 := U16MSBOperation.populate_msbF_eval { env := env } (quotFE selectors B C)[1]
    (by rw [hq1]; exact w1)
  rw [hq1] at hm1
  simp only [quotMsbFE, quotMsbCell, circuit_norm, wSumF_eval selectors env]
  split_ifs
  · exact hm1
  · rfl

omit [Fact (2 ^ 24 < p)] in
include hWB hUB in
/-- Evaluating `b_neg` is `populateBNeg`. -/
theorem bNegFE_eval :
    (bNegFE selectors B).eval { env := env } = populateBNeg vB (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  simp only [bNegFE, populateBNeg, circuit_norm, signedSumF_eval selectors env,
    bMsbFE_eval selectors env B vB hWB hUB]

omit [Fact (2 ^ 24 < p)] in
include hWC hUC in
/-- Evaluating `c_neg` is `populateCNeg`. -/
theorem cNegFE_eval :
    (cNegFE selectors C).eval { env := env } = populateCNeg vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  simp only [cNegFE, populateCNeg, circuit_norm, signedSumF_eval selectors env,
    cMsbFE_eval selectors env C vC hWC hUC]

include hWB hWC hUB hUC in
/-- Evaluating `rem_neg` is `populateRemNeg`. -/
theorem remNegFE_eval :
    (remNegFE selectors B C).eval { env := env } = populateRemNeg vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  simp only [remNegFE, populateRemNeg, circuit_norm, signedSumF_eval selectors env,
    remMsbFE_eval selectors env B C vB vC hWB hWC hUB hUC]

end MsbSignEval

/-! ## Absolute values and `max(|c|, 1)` -/

section AbsPayloads

/-- The `abs_c` word site. -/
def absCFE (C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  Vector.ofFn fun i =>
    .ite (((signedSumF selectors)) =? (1 : ZMod p))
      (wordFOfU64 (absU (compU selectors (wordU C))))[i] (compF selectors C)[i]

/-- The `abs_remainder` word site. -/
def absRemFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  Vector.ofFn fun i =>
    .ite (((signedSumF selectors)) =? (1 : ZMod p))
      (wordFOfU64 (absU (remBitsU selectors (wordU B) (wordU C))))[i] (remCompFE selectors B C)[i]

/-- The `abs_c` u64 value (for the `max_abs_c_or_1` zero test). -/
def absCU (C : Word (Expression (ZMod p))) : Witgen.U64Expr (ZMod p) :=
  .ite (((signedSumF selectors)) =? (1 : ZMod p))
    (absU (compU selectors (wordU C))) (compU selectors (wordU C))

/-- The `max_abs_c_or_1` word site (`Word(1)` exactly on `abs_c = 0`). -/
def maxAbsFE (C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  #v[.ite (absCU selectors C =? (0 : ℕ)) 1 (absCFE selectors C)[0],
     .ite (absCU selectors C =? (0 : ℕ)) 0 (absCFE selectors C)[1],
     .ite (absCU selectors C =? (0 : ℕ)) 0 (absCFE selectors C)[2],
     .ite (absCU selectors C =? (0 : ℕ)) 0 (absCFE selectors C)[3]]

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
    ((absCFE selectors C)[i]).eval { env := env } = (populateAbsC vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] := by
  have hcomp := compU_toNat selectors env (wordU C) (hx := wordU_toNat env C vC hWC hUC) hUC
  have habs := absU_toNat env (compU selectors (wordU C)) hcomp
  simp only [absCFE, populateAbsC, circuit_norm, Vector.getElem_ofFn, signedSumF_eval selectors env]
  split_ifs
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans
      (wordFOfU64_eval env _ habs i hi)
  · contradiction
  · contradiction
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans
      (compF_eval selectors env C vC hWC hUC i hi)

include hWB hWC hUB hUC in
/-- Evaluating the `abs_remainder` site is `populateAbsRem`. -/
theorem absRemFE_eval (i : ℕ) (hi : i < 4) :
    ((absRemFE selectors B C)[i]).eval { env := env }
      = (populateAbsRem vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] := by
  have habs := absU_toNat env (remBitsU selectors (wordU B) (wordU C))
    (remBitsU_toNat selectors env B C vB vC hWB hWC hUB hUC)
  simp only [absRemFE, populateAbsRem, circuit_norm, Vector.getElem_ofFn, signedSumF_eval selectors env]
  split_ifs
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans
      (wordFOfU64_eval env _ habs i hi)
  · contradiction
  · contradiction
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans
      (remCompFE_eval selectors env B C vB vC hWB hWC hUB hUC i hi)

include hWC hUC in
/-- Evaluating the `abs_c` u64 value is `Word.toNat (populateAbsC …)`. -/
theorem absCU_toNat :
    ((absCU selectors C).eval { env := env }).toNat = Word.toNat (populateAbsC vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))) := by
  have hcomp := compU_toNat selectors env (wordU C) (hx := wordU_toNat env C vC hWC hUC) hUC
  have habs := absU_toNat env (compU selectors (wordU C)) hcomp
  have htn : ∀ x : BitVec 64, (Word.toBitVec64 (wordOfBits (p := p) x)).toNat = x.toNat :=
    fun x => by rw [wordOfBits_toBitVec64]
  simp only [absCU, populateAbsC, circuit_norm, signedSumF_eval selectors env]
  split_ifs
  · rw [habs, ← Word.toBitVec64_toNat (wordOfBits_isU64 _), wordOfBits_toBitVec64]
  · rw [hcomp, Word.toBitVec64_toNat (cComp_isU64 hUC _)]

include hWC hUC in
/-- Evaluating the `max_abs_c_or_1` site is `populateMaxAbsCOr1`. -/
theorem maxAbsFE_eval (i : ℕ) (hi : i < 4) :
    ((maxAbsFE selectors C)[i]).eval { env := env }
      = (populateMaxAbsCOr1 vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] := by
  have hz := absCU_toNat selectors env C vC hWC hUC
  interval_cases i <;>
    (simp only [maxAbsFE, populateMaxAbsCOr1, circuit_norm, Vector.getElem_mk,
       List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
     split_ifs <;>
       first
         | omega
         | exact (Witgen.FExpr.eval_getElem { env := env } _ 0 (by omega)).symm.trans
             (absCFE_eval selectors env C vC hWC hUC 0 (by omega))
         | exact (Witgen.FExpr.eval_getElem { env := env } _ 1 (by omega)).symm.trans
             (absCFE_eval selectors env C vC hWC hUC 1 (by omega))
         | exact (Witgen.FExpr.eval_getElem { env := env } _ 2 (by omega)).symm.trans
             (absCFE_eval selectors env C vC hWC hUC 2 (by omega))
         | exact (Witgen.FExpr.eval_getElem { env := env } _ 3 (by omega)).symm.trans
             (absCFE_eval selectors env C vC hWC hUC 3 (by omega))
         | simp [circuit_norm])

end AbsEval

/-! ## The overflow result cells and the `scal` site -/

section ScalPayloads

/-- The `is_overflow_b` result cell (the gated `IsEqualWordOperation` result, recomputed —
`populateIsOverflow` reads it off the witnessed struct, which SP1 populates per-event). -/
def ovbResFE (ir : Expression (ZMod p)) (B : Word (Expression (ZMod p))) :
    Witgen.FExpr (ZMod p) :=
  .ite ((Witgen.FExpr.expr ir) =? (1 : ZMod p))
    (.ite (((wSumF selectors)) =? (1 : ZMod p))
      ((toElements (IsEqualWordOperation.populateFE
          #v[.expr B[0], .expr B[1], 0, 0] #v[0, .const 32768, 0, 0]))[10]'(by
        have h : size Circuits.Types.IsEqualWordOperation = 11 := rfl
        omega))
      ((toElements (IsEqualWordOperation.populateFE
          #v[.expr B[0], .expr B[1], .expr B[2], .expr B[3]]
          #v[0, 0, 0, .const 32768]))[10]'(by
        have h : size Circuits.Types.IsEqualWordOperation = 11 := rfl
        omega)))
    0

/-- The `is_overflow_c` result cell. -/
def ovcResFE (ir : Expression (ZMod p)) (C : Word (Expression (ZMod p))) :
    Witgen.FExpr (ZMod p) :=
  .ite ((Witgen.FExpr.expr ir) =? (1 : ZMod p))
    (.ite (((wSumF selectors)) =? (1 : ZMod p))
      ((toElements (IsEqualWordOperation.populateFE
          #v[.expr C[0], .expr C[1], 0, 0]
          #v[.const 65535, .const 65535, 0, 0]))[10]'(by
        have h : size Circuits.Types.IsEqualWordOperation = 11 := rfl
        omega))
      ((toElements (IsEqualWordOperation.populateFE
          #v[.expr C[0], .expr C[1], .expr C[2], .expr C[3]]
          #v[.const 65535, .const 65535, .const 65535, .const 65535]))[10]'(by
        have h : size Circuits.Types.IsEqualWordOperation = 11 := rfl
        omega)))
    0

/-- `is_overflow = ovb.result · ovc.result · is_signed_type`. -/
def isOverflowFE (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Witgen.FExpr (ZMod p) :=
  ovbResFE selectors ir B * ovcResFE selectors ir C * (signedSumF selectors)

/-- The seven scalar gate/sign cells site. -/
def scalFE (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Vector (Witgen.FExpr (ZMod p)) 7 :=
  #v[isOverflowFE selectors ir B C, bNegFE selectors B,
     bNegFE selectors B * (1 - isOverflowFE selectors ir B C),
     (1 - bNegFE selectors B) * (1 - isOverflowFE selectors ir B C),
     Witgen.FExpr.expr ir * (1 - (wSumF selectors)), remNegFE selectors B C, cNegFE selectors C]

end ScalPayloads

section ScalEval

variable (env : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)

omit [Fact (2 ^ 24 < p)] in
include hWB in
/-- Evaluating the `is_overflow_b` result cell is the witnessed struct's result. -/
theorem ovbResFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) :
    (ovbResFE selectors ir B).eval { env := env }
      = (ovbWitness vir vB (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))).is_diff_zero.result := by
  have htrunc := IsEqualWordOperation.populateFE_eval env
    (#v[.expr B[0], .expr B[1], 0, 0]) (#v[0, .const 32768, 0, 0])
    (va := #v[vB[0], vB[1], 0, 0]) (vb := #v[0, 32768, 0, 0])
    (by intro k hk; interval_cases k <;>
          simp [circuit_norm, hWB 0 (by omega), hWB 1 (by omega)])
    (by intro k hk; interval_cases k <;> simp [circuit_norm])
  have hfull := IsEqualWordOperation.populateFE_eval env
    (#v[.expr B[0], .expr B[1], .expr B[2], .expr B[3]]) (#v[0, 0, 0, .const 32768])
    (va := vB) (vb := #v[0, 0, 0, 32768])
    (by intro k hk; interval_cases k <;>
          simp [circuit_norm, hWB 0 (by omega), hWB 1 (by omega), hWB 2 (by omega),
            hWB 3 (by omega)])
    (by intro k hk; interval_cases k <;> simp [circuit_norm])
  -- fully manual: unfold the two ites by `rfl`, resolve the conditions, rewrite the leaves
  -- (the mixed simp route loops in the `fields (size M)` projection machinery)
  have h11 : (10 : ℕ) < size Circuits.Types.IsEqualWordOperation := by
    have h : size Circuits.Types.IsEqualWordOperation = 11 := rfl
    omega
  have hl1 : Witgen.FExpr.eval { env := env }
      ((toElements (IsEqualWordOperation.populateFE
        (#v[.expr B[0], .expr B[1], 0, 0]) (#v[0, .const 32768, 0, 0])))[10]'h11)
      = (toElements (IsEqualWordOperation.populate
          (#v[vB[0], vB[1], 0, 0]) (#v[0, 32768, 0, 0])))[10]'h11 := by
    rw [Witgen.getElem_eval_toElements, htrunc]
  have hl2 : Witgen.FExpr.eval { env := env }
      ((toElements (IsEqualWordOperation.populateFE
        (#v[.expr B[0], .expr B[1], .expr B[2], .expr B[3]]) (#v[0, 0, 0, .const 32768])))[10]'h11)
      = (toElements (IsEqualWordOperation.populate vB (#v[0, 0, 0, 32768])))[10]'h11 := by
    rw [Witgen.getElem_eval_toElements, hfull]
  have e1 : (ovbResFE selectors ir B).eval { env := env }
      = if ((Witgen.FExpr.expr ir) =? (1 : ZMod p)).eval { env := env }
        then (if (((wSumF selectors)) =? (1 : ZMod p)).eval { env := env }
              then Witgen.FExpr.eval { env := env }
                ((toElements (IsEqualWordOperation.populateFE
                  (#v[.expr B[0], .expr B[1], 0, 0]) (#v[0, .const 32768, 0, 0])))[10]'h11)
              else Witgen.FExpr.eval { env := env }
                ((toElements (IsEqualWordOperation.populateFE
                  (#v[.expr B[0], .expr B[1], .expr B[2], .expr B[3]])
                  (#v[0, 0, 0, .const 32768])))[10]'h11))
        else 0 := rfl
  rw [e1, hl1, hl2]
  simp only [ovbWitness]
  by_cases h1 : vir = 1
  · rw [if_pos (feq_true env _ _ _ hir h1), if_pos h1]
    by_cases h2 : (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[4] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[5]
        + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[6] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[7] = 1
    · rw [if_pos (feq_true env _ _ _ (wSumF_eval selectors env) h2), if_pos h2,
        IsEqualWordOperation.result_eq_toElements]
    · rw [if_neg (feq_false env _ _ _ (wSumF_eval selectors env) h2), if_neg h2,
        IsEqualWordOperation.result_eq_toElements]
  · rw [if_neg (feq_false env _ _ _ hir h1), if_neg h1]
    rfl

omit [Fact (2 ^ 24 < p)] in
include hWC in
/-- Evaluating the `is_overflow_c` result cell is the witnessed struct's result. -/
theorem ovcResFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) :
    (ovcResFE selectors ir C).eval { env := env }
      = (ovcWitness vir vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))).is_diff_zero.result := by
  have htrunc := IsEqualWordOperation.populateFE_eval env
    (#v[.expr C[0], .expr C[1], 0, 0]) (#v[.const 65535, .const 65535, 0, 0])
    (va := #v[vC[0], vC[1], 0, 0]) (vb := #v[65535, 65535, 0, 0])
    (by intro k hk; interval_cases k <;>
          simp [circuit_norm, hWC 0 (by omega), hWC 1 (by omega)])
    (by intro k hk; interval_cases k <;> simp [circuit_norm])
  have hfull := IsEqualWordOperation.populateFE_eval env
    (#v[.expr C[0], .expr C[1], .expr C[2], .expr C[3]])
    (#v[.const 65535, .const 65535, .const 65535, .const 65535])
    (va := vC) (vb := #v[65535, 65535, 65535, 65535])
    (by intro k hk; interval_cases k <;>
          simp [circuit_norm, hWC 0 (by omega), hWC 1 (by omega), hWC 2 (by omega),
            hWC 3 (by omega)])
    (by intro k hk; interval_cases k <;> simp [circuit_norm])
  have h11 : (10 : ℕ) < size Circuits.Types.IsEqualWordOperation := by
    have h : size Circuits.Types.IsEqualWordOperation = 11 := rfl
    omega
  have hl1 : Witgen.FExpr.eval { env := env }
      ((toElements (IsEqualWordOperation.populateFE
        (#v[.expr C[0], .expr C[1], 0, 0]) (#v[.const 65535, .const 65535, 0, 0])))[10]'h11)
      = (toElements (IsEqualWordOperation.populate
          (#v[vC[0], vC[1], 0, 0]) (#v[65535, 65535, 0, 0])))[10]'h11 := by
    rw [Witgen.getElem_eval_toElements, htrunc]
  have hl2 : Witgen.FExpr.eval { env := env }
      ((toElements (IsEqualWordOperation.populateFE
        (#v[.expr C[0], .expr C[1], .expr C[2], .expr C[3]])
        (#v[.const 65535, .const 65535, .const 65535, .const 65535])))[10]'h11)
      = (toElements (IsEqualWordOperation.populate vC
          (#v[65535, 65535, 65535, 65535])))[10]'h11 := by
    rw [Witgen.getElem_eval_toElements, hfull]
  have e1 : (ovcResFE selectors ir C).eval { env := env }
      = if ((Witgen.FExpr.expr ir) =? (1 : ZMod p)).eval { env := env }
        then (if (((wSumF selectors)) =? (1 : ZMod p)).eval { env := env }
              then Witgen.FExpr.eval { env := env }
                ((toElements (IsEqualWordOperation.populateFE
                  (#v[.expr C[0], .expr C[1], 0, 0])
                  (#v[.const 65535, .const 65535, 0, 0])))[10]'h11)
              else Witgen.FExpr.eval { env := env }
                ((toElements (IsEqualWordOperation.populateFE
                  (#v[.expr C[0], .expr C[1], .expr C[2], .expr C[3]])
                  (#v[.const 65535, .const 65535, .const 65535, .const 65535])))[10]'h11))
        else 0 := rfl
  rw [e1, hl1, hl2]
  simp only [ovcWitness]
  by_cases h1 : vir = 1
  · rw [if_pos (feq_true env _ _ _ hir h1), if_pos h1]
    by_cases h2 : (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[4] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[5]
        + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[6] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[7] = 1
    · rw [if_pos (feq_true env _ _ _ (wSumF_eval selectors env) h2), if_pos h2,
        IsEqualWordOperation.result_eq_toElements]
    · rw [if_neg (feq_false env _ _ _ (wSumF_eval selectors env) h2), if_neg h2,
        IsEqualWordOperation.result_eq_toElements]
  · rw [if_neg (feq_false env _ _ _ hir h1), if_neg h1]
    rfl

omit [Fact (2 ^ 24 < p)] in
include hWB hWC in
/-- Evaluating `is_overflow` is `populateIsOverflow`. -/
theorem isOverflowFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) :
    (isOverflowFE selectors ir B C).eval { env := env }
      = populateIsOverflow vir vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  simp only [isOverflowFE, populateIsOverflow, circuit_norm,
    ovbResFE_eval selectors env B vB hWB ir vir hir, ovcResFE_eval selectors env C vC hWC ir vir hir,
    signedSumF_eval selectors env]

include hWB hWC hUB hUC in
/-- Evaluating a `scal` cell is the corresponding `populateScal` cell. -/
theorem scalFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 7) :
    ((scalFE selectors ir B C)[i]).eval { env := env }
      = (populateScal vir vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] := by
  have hov := isOverflowFE_eval selectors env B C vB vC hWB hWC ir vir hir
  have hbn := bNegFE_eval selectors env B vB hWB hUB
  have hcn := cNegFE_eval selectors env C vC hWC hUC
  have hrn := remNegFE_eval selectors env B C vB vC hWB hWC hUB hUC
  interval_cases i <;>
    simp only [scalFE, populateScal, circuit_norm, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, hov, hbn, hcn, hrn, hir, wSumF_eval selectors env]

end ScalEval

/-! ## The `c_times_quotient` site -/

section CtqSite

/-- The eight committed product limbs share their computational quotient and divisor. -/
def ctqProgram (B C : Word (Expression (ZMod p))) :
    Witgen.M (ZMod p) (Vector (Witgen.FExpr (ZMod p)) 8) := do
  let q ← quotCompBitsU selectors (wordU B) (wordU C)
  let c ← compU selectors (wordU C)
  return Vector.ofFn fun k => ctqLimbF selectors q c k.val

omit [Fact (2 ^ 24 < p)] in
/-- Shared product limbs preserve the expression semantics for arbitrary operand and selector values. -/
theorem ctqProgram_eval_limb (env : ProverEnvironment (ZMod p))
    (B C : Word (Expression (ZMod p))) (k : ℕ) (hk : k < 8) :
    ((ctqProgram selectors B C).eval (value := fields 8) env)[k] =
      (ctqLimbF selectors (quotCompBitsU selectors (wordU B) (wordU C)) (compU selectors (wordU C)) k).eval
        { env := env } := by
  simp only [ctqProgram, Witgen.M.eval, Witgen.M.bind_def, Witgen.M.pure_def,
    Witgen.letU_def, Array.size_empty,
    List.cons_append, List.nil_append, Witgen.evalSteps,
    Witgen.eval, explicit_provable_type, circuit_norm, Vector.getElem_ofFn, ctqLimbF]
  apply congrArg (fun u : UInt64 => (u.toNat : ZMod p))
  apply (ctqLimbU_congr selectors)
  · simp [circuit_norm, -Witgen.u64Wrap]
  · simp [compU, low32U, sext32U, wordU, flagF, selectorF,
      circuit_norm, -Witgen.u64Wrap]
  · intro i hi
    rfl

variable (env : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)

include hWB hWC hUB hUC in
/-- Evaluating a product limb is the corresponding `populateCtq` cell. -/
theorem ctqProgram_eval (k : ℕ) (hk : k < 8) :
    ((ctqProgram selectors B C).eval (value := fields 8) env)[k] = (populateCtq vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[k] := by
  have hq : ((Witgen.U64Expr.eval { env := env }
      (quotCompBitsU selectors (wordU B) (wordU C))).toNat)
      = (Word.toBitVec64 (populateQuotComp vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))).toNat := by
    rw [quotCompBitsU_toNat selectors env B C vB vC hWB hWC hUB hUC, populateQuotComp,
      wordOfBits_toBitVec64]
  have hc : ((Witgen.U64Expr.eval { env := env } (compU selectors (wordU C))).toNat)
      = (Word.toBitVec64 (cComp vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))).toNat :=
    compU_toNat selectors env (wordU C) (wordU_toNat env C vC hWC hUC) hUC
  rw [ctqProgram_eval_limb]
  exact ctqLimbF_eval selectors env _ _ vB vC hq hc k hk

end CtqSite

/-! ## The `is_c_0` site and the remainder-check gate -/

section IsC0Site

/-- The `is_c_0` struct site (ungated, flat 11 cells). -/
def isC0FE (C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 11 :=
  (toElements (IsZeroWordOperation.populateFE (compF selectors C))).cast
    (show size Circuits.Types.IsZeroWordOperation = 11 from rfl)

/-- The remainder-check gate cell `is_real · (1 − is_c_0.result)`. -/
def ltGateFE (ir : Expression (ZMod p)) (C : Word (Expression (ZMod p))) :
    Witgen.FExpr (ZMod p) :=
  Witgen.FExpr.expr ir * (1 - (IsZeroWordOperation.populateFE (compF selectors C)).result)

variable (env : ProverEnvironment (ZMod p))
variable (C : Word (Expression (ZMod p))) (vC : Word (ZMod p))
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUC : vC.isU64)

omit [Fact (2 ^ 24 < p)] in
include hWC hUC in
/-- Evaluating an `is_c_0` cell is the corresponding flattened `isC0Witness` cell. -/
theorem isC0FE_eval (i : ℕ) (hi : i < 11) :
    ((isC0FE selectors C)[i]).eval { env := env }
      = ((toElements (isC0Witness vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))).cast
          (show size Circuits.Types.IsZeroWordOperation = 11 from rfl))[i] := by
  have h := IsZeroWordOperation.populateFE_eval env (compF selectors C)
    (va := cComp vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))) (compF_eval selectors env C vC hWC hUC)
  rw [isC0FE, Vector.getElem_cast, Vector.getElem_cast,
    Witgen.getElem_eval_toElements, h]
  rfl

omit [Fact (2 ^ 24 < p)] in
include hWC hUC in
/-- Evaluating the gate cell is `ltGate`. -/
theorem ltGateFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) :
    (ltGateFE selectors ir C).eval { env := env } = ltGate vir vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  have h := IsZeroWordOperation.populateFE_eval env (compF selectors C)
    (va := cComp vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))) (compF_eval selectors env C vC hWC hUC)
  have hres : ((IsZeroWordOperation.populateFE (compF selectors C)).result).eval { env := env }
      = (isC0Witness vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))).result := by
    simp only [circuit_norm]
    rw [h]
    rfl
  simp only [ltGateFE, ltGate, circuit_norm, hir, hres]

end IsC0Site

/-! ## The negation words and the `misc` site -/

section NegWordSites

/-- The `c_neg_operation` value-word site (gated on `c_neg · is_real = 1`). -/
def wCnegFE (ir : Expression (ZMod p)) (C : Word (Expression (ZMod p))) :
    Vector (Witgen.FExpr (ZMod p)) 4 :=
  Vector.ofFn fun i =>
    .ite ((cNegFE selectors C * Witgen.FExpr.expr ir) =? (1 : ZMod p))
      ((AddOperation.populateFW (compF selectors C) (absCFE selectors C))[i.val]) 0

/-- Build magnitude limbs from an already computed remainder. The unsigned W case still
truncates to 32 bits, including for selector inputs outside the honest one-hot domain. -/
private def absRemFromU (r : Witgen.U64Expr (ZMod p)) :
    Vector (Witgen.FExpr (ZMod p)) 4 :=
  Vector.ofFn fun i =>
    .ite (signedSumF selectors =? (1 : ZMod p))
      (wordFOfU64 (absU r))[i]
      (wordFOfU64 (.ite ((flagF selectors 6 + flagF selectors 7) =? (1 : ZMod p))
        (low32U r) r))[i]

/-- The remainder-negation word shares the raw remainder before forming its magnitude limbs. -/
def wRnegProgram (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Witgen.M (ZMod p) (Vector (Witgen.FExpr (ZMod p)) 4) := do
  let r ← remBitsU selectors (wordU B) (wordU C)
  let a0 ← (absRemFromU selectors r)[0]
  let a1 ← (absRemFromU selectors r)[1]
  let a2 ← (absRemFromU selectors r)[2]
  let a3 ← (absRemFromU selectors r)[3]
  return Witgen.gateFE (M := fields 4)
    ((remNegFE selectors B C * Witgen.FExpr.expr ir) =? (1 : ZMod p))
    (AddOperation.populateFW (wordFOfU64 r) #v[a0, a1, a2, a3])

omit [Fact (2 ^ 24 < p)] in
/-- Sharing preserves the negation word without range or honest-selector assumptions. -/
theorem wRnegProgram_eval_value (env : ProverEnvironment (ZMod p))
    (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    (wRnegProgram selectors ir B C).eval (value := fields 4) env =
      if (remNegFE selectors B C).eval { env := env } * ir.eval env.toEnvironment = 1 then
        Witgen.eval (M := fields 4) { env := env } (AddOperation.populateFW (remFE selectors B C) (absRemFE selectors B C))
      else Vector.replicate 4 0 := by
  simp only [wRnegProgram, Witgen.M.eval, Witgen.M.bind_def, Witgen.M.pure_def,
    Witgen.letU_def, Witgen.letF_def, Array.size_empty, Array.size_push, Array.toList_push,
    List.cons_append, List.nil_append, Witgen.evalSteps]
  rw [Witgen.eval_gateFE]
  have hgate (ctx : Witgen.Ctx (ZMod p)) :
      (remNegFE selectors B C).eval ctx = (remNegFE selectors B C).eval { env := ctx.env } := by rfl
  simp only [circuit_norm, hgate]
  refine if_congr Iff.rfl ?_ rfl
  apply Vector.ext
  intro i hi
  simp only [Witgen.eval_fields', Vector.getElem_map]
  apply AddOperation.populateFW_congr
  · intro j hj
    interval_cases j <;> simp only [remFE, wordFOfU64, circuit_norm, -Witgen.u64Wrap] <;> rfl
  · intro j hj
    interval_cases j <;> simp only [absRemFromU, absRemFE, remCompFE, remCompBitsU, wordFOfU64,
      absU, negU, low32U, circuit_norm, -Witgen.u64Wrap] <;> rfl

omit [Fact (2 ^ 24 < p)] in
/-- Cellwise reading of the shared negation program. -/
theorem wRnegProgram_eval_limb (env : ProverEnvironment (ZMod p))
    (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) (i : ℕ) (hi : i < 4) :
    ((wRnegProgram selectors ir B C).eval (value := fields 4) env)[i] =
      if (remNegFE selectors B C).eval { env := env } * ir.eval env.toEnvironment = 1 then
        ((AddOperation.populateFW (remFE selectors B C) (absRemFE selectors B C))[i]).eval { env := env }
      else 0 := by
  rw [wRnegProgram_eval_value]
  split_ifs <;> simp only [Witgen.eval_fields', Vector.getElem_map, Vector.getElem_replicate]

/-- The three event/multiplicity cells. -/
def miscFE (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Vector (Witgen.FExpr (ZMod p)) 3 :=
  #v[cNegFE selectors C * Witgen.FExpr.expr ir, remNegFE selectors B C * Witgen.FExpr.expr ir, ltGateFE selectors ir C]

variable (env : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)

include hWC hUC in
/-- Evaluating a `c_neg_operation` cell is the corresponding `wCnegWitness` cell. -/
theorem wCnegFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 4) :
    ((wCnegFE selectors ir C)[i]).eval { env := env }
      = (wCnegWitness vir vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] := by
  have hcn := cNegFE_eval selectors env C vC hWC hUC
  have hadd := AddOperation.populateFW_eval env (compF selectors C) (absCFE selectors C)
    (cComp vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))) (populateAbsC vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))
    (compF_eval selectors env C vC hWC hUC) (absCFE_eval selectors env C vC hWC hUC)
    (cComp_isU64 hUC _) (populateAbsC_isU64 hUC _) i hi
  simp only [wCnegFE, wCnegWitness, circuit_norm, Vector.getElem_ofFn, hcn, hir]
  split_ifs
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans hadd
  · contradiction
  · contradiction
  · interval_cases i <;> simp

include hWB hWC hUB hUC in
/-- Evaluating a `rem_neg_operation` cell is the corresponding `wRnegWitness` cell. -/
theorem wRnegProgram_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 4) :
    ((wRnegProgram selectors ir B C).eval (value := fields 4) env)[i]
      = (wRnegWitness vir vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] := by
  have hrn := remNegFE_eval selectors env B C vB vC hWB hWC hUB hUC
  have hadd := AddOperation.populateFW_eval env (remFE selectors B C) (absRemFE selectors B C)
    (populateRemainder vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))) (populateAbsRem vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))
    (remFE_eval selectors env B C vB vC hWB hWC hUB hUC) (absRemFE_eval selectors env B C vB vC hWB hWC hUB hUC)
    (populateRemainder_isU64 vB vC _) (populateAbsRem_isU64 vB vC _) i hi
  rw [wRnegProgram_eval_limb]
  simp only [wRnegWitness, hrn, hir]
  split_ifs
  · exact hadd
  · interval_cases i <;> simp

include hWB hWC hUB hUC in
/-- Evaluating a `misc` cell is the corresponding `populateMisc` cell. -/
theorem miscFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 3) :
    ((miscFE selectors ir B C)[i]).eval { env := env }
      = (populateMisc vir vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] := by
  have hcn := cNegFE_eval selectors env C vC hWC hUC
  have hrn := remNegFE_eval selectors env B C vB vC hWB hWC hUB hUC
  have hlg := ltGateFE_eval selectors env C vC hWC hUC ir vir hir
  interval_cases i <;>
    simp only [miscFE, populateMisc, circuit_norm, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, hcn, hrn, hlg, hir]

end NegWordSites

/-! ## The remainder-check comparison sites -/

section LtSites

/-- The comparison families share their eight operand limbs before selecting output cells.
The output function is ordinary witness authoring; Clean owns the program and its lowering. -/
private def comparisonProgram {n : ℕ} (ir : Expression (ZMod p))
    (B C : Word (Expression (ZMod p)))
    (cell : Word (Witgen.FExpr (ZMod p)) → Word (Witgen.FExpr (ZMod p)) → Fin n → Witgen.FExpr (ZMod p)) :
    Witgen.M (ZMod p) (Vector (Witgen.FExpr (ZMod p)) n) := do
  let r ← remBitsU selectors (wordU B) (wordU C)
  let a0 ← (absRemFromU selectors r)[0]
  let a1 ← (absRemFromU selectors r)[1]
  let a2 ← (absRemFromU selectors r)[2]
  let a3 ← (absRemFromU selectors r)[3]
  let c0 ← (maxAbsFE selectors C)[0]
  let c1 ← (maxAbsFE selectors C)[1]
  let c2 ← (maxAbsFE selectors C)[2]
  let c3 ← (maxAbsFE selectors C)[3]
  return Witgen.gateFE (M := fields n) ((ltGateFE selectors ir C) =? (1 : ZMod p))
    (Vector.ofFn (cell #v[a0, a1, a2, a3] #v[c0, c1, c2, c3]))

omit [Fact (2 ^ 24 < p)] in
/-- Maximum-divisor limbs do not read local witness-program values. -/
private theorem maxAbsFE_eval_ctx (ctx : Witgen.Ctx (ZMod p))
    (C : Word (Expression (ZMod p))) (i : ℕ) (hi : i < 4) :
    (maxAbsFE selectors C)[i].eval ctx = (maxAbsFE selectors C)[i].eval { env := ctx.env } := by
  interval_cases i <;> rfl

omit [Fact (2 ^ 24 < p)] in
/-- Operand sharing preserves any comparison cell that depends only on its operand values. -/
private theorem comparisonProgram_eval_limb {n : ℕ} (env : ProverEnvironment (ZMod p))
    (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p)))
    (cell : Word (Witgen.FExpr (ZMod p)) → Word (Witgen.FExpr (ZMod p)) → Fin n → Witgen.FExpr (ZMod p))
    (hcell : ∀ (ctx ctx' : Witgen.Ctx (ZMod p)) (a c a' c' : Word (Witgen.FExpr (ZMod p))),
      (∀ (j : ℕ) (_ : j < 4), a[j].eval ctx = a'[j].eval ctx') →
      (∀ (j : ℕ) (_ : j < 4), c[j].eval ctx = c'[j].eval ctx') →
      ∀ k, (cell a c k).eval ctx = (cell a' c' k).eval ctx')
    (i : ℕ) (hi : i < n) :
    ((comparisonProgram selectors ir B C cell).eval (value := fields n) env)[i] =
      if (ltGateFE selectors ir C).eval { env := env } = 1 then
        (cell (absRemFE selectors B C) (maxAbsFE selectors C) ⟨i, hi⟩).eval { env := env } else 0 := by
  have heval : (comparisonProgram selectors ir B C cell).eval (value := fields n) env =
      if (ltGateFE selectors ir C).eval { env := env } = 1 then
        Witgen.eval (M := fields n) { env := env } (Vector.ofFn (cell (absRemFE selectors B C) (maxAbsFE selectors C)))
      else Vector.replicate n 0 := by
    simp only [comparisonProgram, Witgen.M.eval, Witgen.M.bind_def, Witgen.M.pure_def,
      Witgen.letU_def, Witgen.letF_def, Array.size_empty, Array.size_push, Array.toList_push,
      List.cons_append, List.nil_append, Witgen.evalSteps, maxAbsFE_eval_ctx]
    rw [Witgen.eval_gateFE]
    have hgate (ctx : Witgen.Ctx (ZMod p)) :
        (ltGateFE selectors ir C).eval ctx = (ltGateFE selectors ir C).eval { env := ctx.env } := by rfl
    simp only [circuit_norm, hgate]
    refine if_congr Iff.rfl ?_ rfl
    apply Vector.ext
    intro k hk
    simp only [Witgen.eval_fields', Vector.getElem_map, Vector.getElem_ofFn]
    apply hcell
    · intro j hj
      interval_cases j <;> simp only [absRemFromU, absRemFE, remCompFE, remCompBitsU, wordFOfU64,
        absU, negU, low32U, circuit_norm, -Witgen.u64Wrap] <;> rfl
    · intro j hj
      interval_cases j <;> simp only [circuit_norm, -Witgen.u64Wrap] <;> rfl
  rw [heval]
  split_ifs <;> simp only [Witgen.eval_fields', Vector.getElem_map,
    Vector.getElem_ofFn, Vector.getElem_replicate]

/-- The gated comparison-limb site. -/
def clProgram (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Witgen.M (ZMod p) (Vector (Witgen.FExpr (ZMod p)) 2) :=
  comparisonProgram selectors ir B C LtOperationUnsigned.comparisonLimbsF

omit [Fact (2 ^ 24 < p)] in
/-- Shared operands preserve this comparison cell for arbitrary inputs and selectors. -/
theorem clProgram_eval_limb (env : ProverEnvironment (ZMod p))
    (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) (i : ℕ) (hi : i < 2) :
    ((clProgram selectors ir B C).eval (value := fields 2) env)[i] =
      if (ltGateFE selectors ir C).eval { env := env } = 1 then
        (LtOperationUnsigned.comparisonLimbsF (absRemFE selectors B C) (maxAbsFE selectors C) ⟨i, hi⟩).eval { env := env } else 0 := by
  apply (comparisonProgram_eval_limb selectors)
  intro ctx ctx' a c a' c' ha hc k
  exact (LtOperationUnsigned.scanF_congr ctx ctx' a c ha hc).1 k

/-- The gated `u16_flags` site. -/
def ltfProgram (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Witgen.M (ZMod p) (Vector (Witgen.FExpr (ZMod p)) 4) :=
  comparisonProgram selectors ir B C LtOperationUnsigned.flagsF

omit [Fact (2 ^ 24 < p)] in
/-- Shared operands preserve this comparison cell for arbitrary inputs and selectors. -/
theorem ltfProgram_eval_limb (env : ProverEnvironment (ZMod p))
    (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) (i : ℕ) (hi : i < 4) :
    ((ltfProgram selectors ir B C).eval (value := fields 4) env)[i] =
      if (ltGateFE selectors ir C).eval { env := env } = 1 then
        (LtOperationUnsigned.flagsF (absRemFE selectors B C) (maxAbsFE selectors C) ⟨i, hi⟩).eval { env := env } else 0 := by
  apply (comparisonProgram_eval_limb selectors)
  intro ctx ctx' a c a' c' ha hc k
  exact (LtOperationUnsigned.scanF_congr ctx ctx' a c ha hc).2.1 k

/-- The gated `not_eq_inv` site. -/
def neiProgram (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Witgen.M (ZMod p) (Vector (Witgen.FExpr (ZMod p)) 1) :=
  comparisonProgram selectors ir B C (fun a c _ => LtOperationUnsigned.notEqInvF a c)

omit [Fact (2 ^ 24 < p)] in
/-- Shared operands preserve this comparison cell for arbitrary inputs and selectors. -/
theorem neiProgram_eval_limb (env : ProverEnvironment (ZMod p))
    (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) (i : ℕ) (hi : i < 1) :
    ((neiProgram selectors ir B C).eval (value := fields 1) env)[i] =
      if (ltGateFE selectors ir C).eval { env := env } = 1 then
        (LtOperationUnsigned.notEqInvF (absRemFE selectors B C) (maxAbsFE selectors C)).eval { env := env } else 0 := by
  apply (comparisonProgram_eval_limb selectors)
  intro ctx ctx' a c a' c' ha hc k
  exact (LtOperationUnsigned.scanF_congr ctx ctx' a c ha hc).2.2.1

/-- The gated compare-bit site. -/
def bitProgram (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Witgen.M (ZMod p) (Vector (Witgen.FExpr (ZMod p)) 1) :=
  comparisonProgram selectors ir B C (fun a c _ => LtOperationUnsigned.compareBitF a c)

omit [Fact (2 ^ 24 < p)] in
/-- Shared operands preserve this comparison cell for arbitrary inputs and selectors. -/
theorem bitProgram_eval_limb (env : ProverEnvironment (ZMod p))
    (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) (i : ℕ) (hi : i < 1) :
    ((bitProgram selectors ir B C).eval (value := fields 1) env)[i] =
      if (ltGateFE selectors ir C).eval { env := env } = 1 then
        (LtOperationUnsigned.compareBitF (absRemFE selectors B C) (maxAbsFE selectors C)).eval { env := env } else 0 := by
  apply (comparisonProgram_eval_limb selectors)
  intro ctx ctx' a c a' c' ha hc k
  exact (LtOperationUnsigned.scanF_congr ctx ctx' a c ha hc).2.2.2


variable (env : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)

-- the shared scan facts over the evaluated (abs_remainder, max_abs_c_or_1) pair
include hWB hWC hUB hUC in
private theorem ltScan :
    (∀ k : Fin 2, (LtOperationUnsigned.comparisonLimbsF (absRemFE selectors B C) (maxAbsFE selectors C) k).eval
        { env := env }
      = (LtOperationUnsigned.comparisonLimbsWitness
          (populateAbsRem vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))
          (populateMaxAbsCOr1 vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))))[(k : ℕ)]) ∧
    (∀ k : Fin 4, (LtOperationUnsigned.flagsF (absRemFE selectors B C) (maxAbsFE selectors C) k).eval { env := env }
      = (LtOperationUnsigned.flagsWitness
          (populateAbsRem vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))
          (populateMaxAbsCOr1 vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))))[(k : ℕ)]) ∧
    (LtOperationUnsigned.notEqInvF (absRemFE selectors B C) (maxAbsFE selectors C)).eval { env := env }
      = (LtOperationUnsigned.notEqInvWitness
          (populateAbsRem vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))
          (populateMaxAbsCOr1 vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))))[0] ∧
    (LtOperationUnsigned.compareBitF (absRemFE selectors B C) (maxAbsFE selectors C)).eval { env := env }
      = U16CompareOperation.populate_bit
          (LtOperationUnsigned.comparisonLimbsWitness
            (populateAbsRem vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))
            (populateMaxAbsCOr1 vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))))[0]
          (LtOperationUnsigned.comparisonLimbsWitness
            (populateAbsRem vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))
            (populateMaxAbsCOr1 vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))))[1] :=
  LtOperationUnsigned.scanF_eval { env := env } _ _ _ _
    (absRemFE_eval selectors env B C vB vC hWB hWC hUB hUC)
    (maxAbsFE_eval selectors env C vC hWC hUC)

include hWB hWC hUB hUC in
/-- Evaluating a comparison-limb cell is the corresponding `ltClWitness` cell. -/
theorem clProgram_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 2) :
    ((clProgram selectors ir B C).eval (value := fields 2) env)[i]
      = (ltClWitness vir vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] := by
  have hlg := ltGateFE_eval selectors env C vC hWC hUC ir vir hir
  have hscan := (ltScan selectors env B C vB vC hWB hWC hUB hUC).1 ⟨i, hi⟩
  rw [clProgram_eval_limb]
  simp only [ltClWitness, circuit_norm, hlg]
  split_ifs
  · exact hscan
  · interval_cases i <;> rfl

include hWB hWC hUB hUC in
/-- Evaluating a `u16_flags` cell is the corresponding `ltFlagsWitness` cell. -/
theorem ltfProgram_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 4) :
    ((ltfProgram selectors ir B C).eval (value := fields 4) env)[i]
      = (ltFlagsWitness vir vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] := by
  have hlg := ltGateFE_eval selectors env C vC hWC hUC ir vir hir
  have hscan := (ltScan selectors env B C vB vC hWB hWC hUB hUC).2.1 ⟨i, hi⟩
  rw [ltfProgram_eval_limb]
  simp only [ltFlagsWitness, circuit_norm, hlg]
  split_ifs
  · exact hscan
  · interval_cases i <;> rfl

include hWB hWC hUB hUC in
/-- Evaluating the `not_eq_inv` cell is the `ltNotEqInvWitness` cell. -/
theorem neiProgram_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 1) :
    ((neiProgram selectors ir B C).eval (value := fields 1) env)[i]
      = (ltNotEqInvWitness vir vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] := by
  have hlg := ltGateFE_eval selectors env C vC hWC hUC ir vir hir
  have hscan := (ltScan selectors env B C vB vC hWB hWC hUB hUC).2.2.1
  interval_cases i
  rw [neiProgram_eval_limb]
  simp only [ltNotEqInvWitness, circuit_norm, hlg]
  split_ifs
  · exact hscan
  · rfl

include hWB hWC hUB hUC in
/-- Evaluating the compare-bit cell is the `ltBitWitness` cell. -/
theorem bitProgram_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 1) :
    ((bitProgram selectors ir B C).eval (value := fields 1) env)[i]
      = (ltBitWitness vir vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[i] := by
  have hlg := ltGateFE_eval selectors env C vC hWC hUC ir vir hir
  have hscan := (ltScan selectors env B C vB vC hWB hWC hUB hUC).2.2.2
  interval_cases i
  rw [bitProgram_eval_limb]
  simp only [ltBitWitness, ltClWitness, circuit_norm, hlg]
  split_ifs with h
  · rw [hscan]
    congr 1
  · rfl

end LtSites

/-! ## The gated `MulOperation` product structs -/

section MulSites

/-- The two gated multiplication blocks use Clean's shared witness programs. The computational
quotient is evaluated once, and the divisor limbs are bound before the schoolbook product reuses
them. `upper` selects the existing 64-bit/signed gate without changing the 45-cell layout. -/
def mulProgram (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p)))
    (upper : Bool) : Witgen.M (ZMod p) (Circuits.Types.MulOperation (Witgen.FExpr (ZMod p))) := do
  let q ← quotCompBitsU selectors (wordU B) (wordU C)
  let c0 ← (compF selectors C)[0]
  let c1 ← (compF selectors C)[1]
  let c2 ← (compF selectors C)[2]
  let c3 ← (compF selectors C)[3]
  let gate := if upper then
    ((Witgen.FExpr.expr ir) =? (1 : ZMod p)).and (((longSumF selectors)) =? (1 : ZMod p))
    else (Witgen.FExpr.expr ir) =? (1 : ZMod p)
  return Witgen.gateFE gate
    (MulOperation.populateFEW (wordFOfU64 q) #v[c0, c1, c2, c3]
      (if upper then flagF selectors 0 + flagF selectors 2 else 0) 0 0)

omit [Fact (2 ^ 24 < p)] in
/-- Computational operand cells read only the environment, independently of local IR steps. -/
private theorem compF_eval_ctx (ctx : Witgen.Ctx (ZMod p))
    (C : Word (Expression (ZMod p))) (i : ℕ) (hi : i < 4) :
    (compF selectors C)[i].eval ctx = (compF selectors C)[i].eval { env := ctx.env } := by
  interval_cases i <;>
    simp only [compF, flagF, selectorF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap]

omit [Fact (2 ^ 24 < p)] in
/-- Explicit sharing preserves the original payload for every environment, including dishonest
selectors. This is an authoring proof over Clean's evaluator, not an additional IR transformation. -/
theorem mulProgram_eval (env : ProverEnvironment (ZMod p))
    (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) (upper : Bool) :
    (mulProgram selectors ir B C upper).eval env =
      Witgen.eval { env := env }
        (Witgen.gateFE
          (if upper then ((Witgen.FExpr.expr ir) =? (1 : ZMod p)).and
            (((longSumF selectors)) =? (1 : ZMod p)) else (Witgen.FExpr.expr ir) =? (1 : ZMod p))
          (MulOperation.populateFEW (quotCompFE selectors B C) (compF selectors C)
            (if upper then flagF selectors 0 + flagF selectors 2 else 0) 0 0)) := by
  simp only [mulProgram, Witgen.M.eval, Witgen.M.bind_def, Witgen.M.pure_def,
    Witgen.letU_def, Witgen.letF_def, Array.size_push, Array.size_empty,
    Array.toList_push, List.cons_append, List.nil_append, Witgen.evalSteps, compF_eval_ctx]
  rw [Witgen.eval_gateFE, Witgen.eval_gateFE]
  have hgate (ctx : Witgen.Ctx (ZMod p)) :
      (if upper then ((Witgen.FExpr.expr ir) =? (1 : ZMod p)).and
        (((longSumF selectors)) =? (1 : ZMod p)) else (Witgen.FExpr.expr ir) =? (1 : ZMod p)).eval ctx
      = (if upper then ((Witgen.FExpr.expr ir) =? (1 : ZMod p)).and
        (((longSumF selectors)) =? (1 : ZMod p)) else (Witgen.FExpr.expr ir) =? (1 : ZMod p)).eval
          { env := ctx.env } := by
    cases upper <;> simp only [Bool.false_eq_true,
      longSumF, flagF, selectorF, circuit_norm, -Witgen.u64Wrap]
    · exact decide_eq_decide.mpr Iff.rfl
    · congr 1
  rw [hgate]
  refine if_congr Iff.rfl ?_ rfl
  apply MulOperation.populateFEW_congr
  · intro i hi
    interval_cases i <;>
      simp [wordFOfU64, quotCompFE, circuit_norm, -Witgen.u64Wrap]
  · intro i hi
    interval_cases i <;> simp [circuit_norm, -Witgen.u64Wrap]
  · cases upper <;> simp only [Bool.false_eq_true, flagF, selectorF, circuit_norm, -Witgen.u64Wrap]
  · rfl
  · rfl


variable (env : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)

include hWB hWC hUB hUC in
/-- The evaluated operand words of the product payloads, in `populateFEW_eval`'s shape. -/
private theorem mulOperandEvals :
    (#v[Witgen.FExpr.eval { env := env } (quotCompFE selectors B C)[0],
        Witgen.FExpr.eval { env := env } (quotCompFE selectors B C)[1],
        Witgen.FExpr.eval { env := env } (quotCompFE selectors B C)[2],
        Witgen.FExpr.eval { env := env } (quotCompFE selectors B C)[3]]
      = populateQuotComp vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))) ∧
    (#v[Witgen.FExpr.eval { env := env } (compF selectors C)[0],
        Witgen.FExpr.eval { env := env } (compF selectors C)[1],
        Witgen.FExpr.eval { env := env } (compF selectors C)[2],
        Witgen.FExpr.eval { env := env } (compF selectors C)[3]]
      = cComp vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))) := by
  constructor <;>
    (apply Vector.ext
     intro k hk
     interval_cases k) <;>
    first
      | exact quotCompFE_eval selectors env B C vB vC hWB hWC hUB hUC 0 (by omega)
      | exact quotCompFE_eval selectors env B C vB vC hWB hWC hUB hUC 1 (by omega)
      | exact quotCompFE_eval selectors env B C vB vC hWB hWC hUB hUC 2 (by omega)
      | exact quotCompFE_eval selectors env B C vB vC hWB hWC hUB hUC 3 (by omega)
      | exact compF_eval selectors env C vC hWC hUC 0 (by omega)
      | exact compF_eval selectors env C vC hWC hUC 1 (by omega)
      | exact compF_eval selectors env C vC hWC hUC 2 (by omega)
      | exact compF_eval selectors env C vC hWC hUC 3 (by omega)

include hWB hWC hUB hUC in
/-- Evaluating the lower product payload is `populateMulLower`. -/
theorem mulLowerProgram_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) :
    (mulProgram selectors ir B C false).eval env
      = populateMulLower vir vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  obtain ⟨hqw, hcw⟩ := mulOperandEvals selectors env B C vB vC hWB hWC hUB hUC
  have hinner := MulOperation.populateFEWW_eval env (quotCompFE selectors B C) (compF selectors C) 0 0 0
    (populateQuotComp vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))) (cComp vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))) 0 0 0
    hqw hcw rfl rfl rfl (populateQuotComp_isU64 vB vC _) (cComp_isU64 hUC _)
    (Or.inl rfl) (Or.inl rfl) (by simp)
  rw [mulProgram_eval]
  simp only [Bool.false_eq_true, ↓reduceIte, Witgen.eval_gateFE, populateMulLower]
  by_cases h1 : vir = 1
  · rw [if_pos (feq_true env _ _ _ hir h1), if_pos h1, hinner]
  · rw [if_neg (feq_false env _ _ _ hir h1), if_neg h1, MulOperation.fromElements_zero]

include hWB hWC hUB hUC in
/-- Evaluating the upper product payload is `populateMulUpper` (under the flag binarities the
contract provides — the signed selector `f[0] + f[2]` must be binary). -/
theorem mulUpperProgram_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir)
    (hf02 : (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2] = 0
      ∨ (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2] = 1) :
    (mulProgram selectors ir B C true).eval env
      = populateMulUpper vir vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  obtain ⟨hqw, hcw⟩ := mulOperandEvals selectors env B C vB vC hWB hWC hUB hUC
  have hh : Witgen.FExpr.eval { env := env }
      ((flagF selectors 0 : Witgen.FExpr (ZMod p)) + flagF selectors 2)
      = (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2] := by
    simp only [circuit_norm, flagF_eval selectors env 0 (by omega), flagF_eval selectors env 2 (by omega)]
  have hsumv : ((selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2]).val + (0 : ZMod p).val ≤ 1 := by
    rcases hf02 with h | h
    · simp [h]
    · simp [h, ZMod.val_one]
  have hinner := MulOperation.populateFEWW_eval env (quotCompFE selectors B C) (compF selectors C)
    ((flagF selectors 0 : Witgen.FExpr (ZMod p)) + flagF selectors 2) 0 0
    (populateQuotComp vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))) (cComp vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))
    ((selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2]) 0 0
    hqw hcw hh rfl rfl (populateQuotComp_isU64 vB vC _) (cComp_isU64 hUC _)
    hf02 (Or.inl rfl) hsumv
  have hband : ((Witgen.BExpr.and ((Witgen.FExpr.expr ir) =? (1 : ZMod p))
      (((longSumF selectors)) =? (1 : ZMod p))).eval { env := env })
      = ((((Witgen.FExpr.expr ir) =? (1 : ZMod p)).eval { env := env })
        && ((((longSumF selectors)) =? (1 : ZMod p)).eval { env := env })) := rfl
  rw [mulProgram_eval]
  simp only [↓reduceIte, Witgen.eval_gateFE, populateMulUpper]
  by_cases h1 : vir = 1
  · by_cases h2 : (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[1]
        + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[3] = 1
    · rw [if_pos (by
          rw [hband, feq_true env _ _ _ hir h1, feq_true env _ _ _ (longSumF_eval selectors env) h2]
          rfl),
        if_pos ⟨h1, h2⟩, hinner]
    · rw [if_neg (by
          rw [hband]
          intro hb
          simp only [Bool.and_eq_true] at hb
          exact feq_false env _ _ _ (longSumF_eval selectors env) h2 hb.2),
        if_neg (by intro h; exact h2 h.2), MulOperation.fromElements_zero]
  · rw [if_neg (by
        rw [hband]
        intro hb
        simp only [Bool.and_eq_true] at hb
        exact feq_false env _ _ _ hir h1 hb.1),
      if_neg (by intro h; exact h1 h.1), MulOperation.fromElements_zero]

end MulSites

/-! ## The gated overflow struct payloads -/

section OvSites

/-- The `is_overflow_b` struct payload (real rows; word-truncated on the W classes). -/
def ovbFE (ir : Expression (ZMod p)) (B : Word (Expression (ZMod p))) :
    Circuits.Types.IsEqualWordOperation (Witgen.FExpr (ZMod p)) :=
  Witgen.gateFE ((Witgen.FExpr.expr ir) =? (1 : ZMod p))
    (Witgen.iteFE (((wSumF selectors)) =? (1 : ZMod p))
      (IsEqualWordOperation.populateFE
        (#v[.expr B[0], .expr B[1], 0, 0]) (#v[0, .const 32768, 0, 0]))
      (IsEqualWordOperation.populateFE
        (#v[.expr B[0], .expr B[1], .expr B[2], .expr B[3]]) (#v[0, 0, 0, .const 32768])))

/-- The `is_overflow_c` struct payload. -/
def ovcFE (ir : Expression (ZMod p)) (C : Word (Expression (ZMod p))) :
    Circuits.Types.IsEqualWordOperation (Witgen.FExpr (ZMod p)) :=
  Witgen.gateFE ((Witgen.FExpr.expr ir) =? (1 : ZMod p))
    (Witgen.iteFE (((wSumF selectors)) =? (1 : ZMod p))
      (IsEqualWordOperation.populateFE
        (#v[.expr C[0], .expr C[1], 0, 0]) (#v[.const 65535, .const 65535, 0, 0]))
      (IsEqualWordOperation.populateFE
        (#v[.expr C[0], .expr C[1], .expr C[2], .expr C[3]])
        (#v[.const 65535, .const 65535, .const 65535, .const 65535])))

variable (env : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])

omit [Fact (2 ^ 24 < p)] in
include hWB in
/-- Evaluating the `is_overflow_b` payload is `ovbWitness`. -/
theorem ovbFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) :
    Witgen.eval { env := env } (ovbFE selectors ir B) = ovbWitness vir vB (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  have htrunc := IsEqualWordOperation.populateFE_eval env
    (#v[.expr B[0], .expr B[1], 0, 0]) (#v[0, .const 32768, 0, 0])
    (va := #v[vB[0], vB[1], 0, 0]) (vb := #v[0, 32768, 0, 0])
    (by intro k hk; interval_cases k <;>
          simp [circuit_norm, hWB 0 (by omega), hWB 1 (by omega)])
    (by intro k hk; interval_cases k <;> simp [circuit_norm])
  have hfull := IsEqualWordOperation.populateFE_eval env
    (#v[.expr B[0], .expr B[1], .expr B[2], .expr B[3]]) (#v[0, 0, 0, .const 32768])
    (va := vB) (vb := #v[0, 0, 0, 32768])
    (by intro k hk; interval_cases k <;>
          simp [circuit_norm, hWB 0 (by omega), hWB 1 (by omega), hWB 2 (by omega),
            hWB 3 (by omega)])
    (by intro k hk; interval_cases k <;> simp [circuit_norm])
  rw [ovbFE, Witgen.eval_gateFE, Witgen.eval_iteFE]
  simp only [ovbWitness]
  by_cases h1 : vir = 1
  · rw [if_pos (feq_true env _ _ _ hir h1), if_pos h1]
    by_cases h2 : (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[4] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[5]
        + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[6] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[7] = 1
    · rw [if_pos (feq_true env _ _ _ (wSumF_eval selectors env) h2), if_pos h2, htrunc]
    · rw [if_neg (feq_false env _ _ _ (wSumF_eval selectors env) h2), if_neg h2, hfull]
  · rw [if_neg (feq_false env _ _ _ hir h1), if_neg h1,
      IsEqualWordOperation.fromElements_zero]

omit [Fact (2 ^ 24 < p)] in
include hWC in
/-- Evaluating the `is_overflow_c` payload is `ovcWitness`. -/
theorem ovcFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) :
    Witgen.eval { env := env } (ovcFE selectors ir C) = ovcWitness vir vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) := by
  have htrunc := IsEqualWordOperation.populateFE_eval env
    (#v[.expr C[0], .expr C[1], 0, 0]) (#v[.const 65535, .const 65535, 0, 0])
    (va := #v[vC[0], vC[1], 0, 0]) (vb := #v[65535, 65535, 0, 0])
    (by intro k hk; interval_cases k <;>
          simp [circuit_norm, hWC 0 (by omega), hWC 1 (by omega)])
    (by intro k hk; interval_cases k <;> simp [circuit_norm])
  have hfull := IsEqualWordOperation.populateFE_eval env
    (#v[.expr C[0], .expr C[1], .expr C[2], .expr C[3]])
    (#v[.const 65535, .const 65535, .const 65535, .const 65535])
    (va := vC) (vb := #v[65535, 65535, 65535, 65535])
    (by intro k hk; interval_cases k <;>
          simp [circuit_norm, hWC 0 (by omega), hWC 1 (by omega), hWC 2 (by omega),
            hWC 3 (by omega)])
    (by intro k hk; interval_cases k <;> simp [circuit_norm])
  rw [ovcFE, Witgen.eval_gateFE, Witgen.eval_iteFE]
  simp only [ovcWitness]
  by_cases h1 : vir = 1
  · rw [if_pos (feq_true env _ _ _ hir h1), if_pos h1]
    by_cases h2 : (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[4] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[5]
        + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[6] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[7] = 1
    · rw [if_pos (feq_true env _ _ _ (wSumF_eval selectors env) h2), if_pos h2, htrunc]
    · rw [if_neg (feq_false env _ _ _ (wSumF_eval selectors env) h2), if_neg h2, hfull]
  · rw [if_neg (feq_false env _ _ _ hir h1), if_neg h1,
      IsEqualWordOperation.fromElements_zero]

end OvSites

/-! ## The carry chain -/

section CarrySite

/-- Remainder addend: the committed limb below the word, the sign fill above it. -/
def remAddendU (r : Word (Witgen.FExpr (ZMod p))) (sign : Witgen.FExpr (ZMod p))
    (k : ℕ) : Witgen.U64Expr (ZMod p) :=
  if h : k < 4 then Witgen.U64Expr.val (r[k]'h)
  else Witgen.U64Expr.val sign * 65535

/-- Carry recursion for the product plus remainder. Its expression operands may name shared steps. -/
def carryChainU (q c : Witgen.U64Expr (ZMod p))
    (r : Word (Witgen.FExpr (ZMod p))) (sign : Witgen.FExpr (ZMod p)) :
    ℕ → Witgen.U64Expr (ZMod p)
  | 0 => (ctqLimbU selectors q c 0 + remAddendU r sign 0) / 65536
  | n + 1 => (ctqLimbU selectors q c (n + 1) + remAddendU r sign (n + 1)
      + carryChainU q c r sign n) / 65536

omit [Fact (2 ^ 24 < p)] in
/-- Carry evaluation depends only on operand values and selectors, without range assumptions. -/
theorem carryChainU_congr (ctx ctx' : Witgen.Ctx (ZMod p))
    (q c q' c' : Witgen.U64Expr (ZMod p))
    (r r' : Word (Witgen.FExpr (ZMod p))) (sign sign' : Witgen.FExpr (ZMod p))
    (hq : q.eval ctx = q'.eval ctx') (hc : c.eval ctx = c'.eval ctx')
    (hr : ∀ (i : ℕ) (_ : i < 4), r[i].eval ctx = r'[i].eval ctx')
    (hs : sign.eval ctx = sign'.eval ctx') (hselectors : ∀ i (hi : i < 7), Expression.eval ctx.env.toEnvironment selectors[i] =
      Expression.eval ctx'.env.toEnvironment selectors[i]) :
    ∀ n, (carryChainU selectors q c r sign n).eval ctx = (carryChainU selectors q' c' r' sign' n).eval ctx' := by
  have hlimb := ctqLimbU_congr selectors ctx ctx' q c q' c' hq hc hselectors
  have haddend (k : ℕ) : (remAddendU r sign k).eval ctx
      = (remAddendU r' sign' k).eval ctx' := by
    unfold remAddendU
    split_ifs with h <;> simp only [circuit_norm, -Witgen.u64Wrap, hr, hs]
  intro n
  induction n with
  | zero => simp only [carryChainU, circuit_norm, -Witgen.u64Wrap, hlimb 0, haddend 0]
  | succ n ih =>
    simp only [carryChainU, circuit_norm, -Witgen.u64Wrap, hlimb (n + 1), haddend (n + 1), ih]

/-- The eight carries share the quotient, divisor, remainder and sign calculation. -/
def carryProgram (B C : Word (Expression (ZMod p))) :
    Witgen.M (ZMod p) (Vector (Witgen.FExpr (ZMod p)) 8) := do
  let q ← quotCompBitsU selectors (wordU B) (wordU C)
  let c ← compU selectors (wordU C)
  let r ← remCompBitsU selectors (wordU B) (wordU C)
  let sign ← remNegFE selectors B C
  return Vector.ofFn fun k => (carryChainU selectors q c (wordFOfU64 r) sign k.val).toField

omit [Fact (2 ^ 24 < p)] in
/-- Authored sharing preserves each carry for every environment, including malformed selectors. -/
theorem carryProgram_eval_limb (env : ProverEnvironment (ZMod p))
    (B C : Word (Expression (ZMod p))) (k : ℕ) (hk : k < 8) :
    ((carryProgram selectors B C).eval (value := fields 8) env)[k] =
      ((carryChainU selectors (quotCompBitsU selectors (wordU B) (wordU C)) (compU selectors (wordU C))
        (remCompFE selectors B C) (remNegFE selectors B C) k).eval { env := env }).toNat := by
  simp only [carryProgram, Witgen.M.eval, Witgen.M.bind_def, Witgen.M.pure_def,
    Witgen.letU_def, Witgen.letF_def, Array.size_empty,
    List.cons_append, List.nil_append, Witgen.evalSteps,
    Witgen.eval, explicit_provable_type, circuit_norm, Vector.getElem_ofFn]
  apply congrArg (fun u : UInt64 => (u.toNat : ZMod p))
  apply (carryChainU_congr selectors)
  · simp [circuit_norm, -Witgen.u64Wrap]
  · simp only [circuit_norm, -Witgen.u64Wrap]
    rfl
  · intro i hi
    interval_cases i <;> simp only [remCompFE, wordFOfU64, circuit_norm, -Witgen.u64Wrap] <;> rfl
  · simp only [circuit_norm, -Witgen.u64Wrap]
    rfl
  · intro i hi
    rfl

variable (env : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)

include hWB hWC hUB hUC in
/-- Evaluating an addend limb is `remAddendNat` — under the flag binarities the contract
provides (a dishonest non-binary flag could push the sign fill past the u64 `val`
truncation), with the ≤ `2^18` bound for the chain's wrap-freeness. -/
private theorem remAddendU_toNat
    (hf : ∀ (k : ℕ) (_ : k < 8), (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[k] = 0 ∨ (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[k] = 1)
    (k : ℕ) (hk : k < 8) :
    ((remAddendU (remCompFE selectors B C) (remNegFE selectors B C) k).eval { env := env }).toNat
      = remAddendNat vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) k
      ∧ remAddendNat vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) k < 2 ^ 18 := by
  have hrn := remNegFE_eval selectors env B C vB vC hWB hWC hUB hUC
  have hval_add : ∀ a b : ZMod p, (a + b).val ≤ a.val + b.val := fun a b =>
    (ZMod.val_add a b) ▸ Nat.mod_le _ _
  have hval_mul : ∀ a b : ZMod p, (a * b).val ≤ a.val * b.val := fun a b =>
    (ZMod.val_mul a b) ▸ Nat.mod_le _ _
  have hbin1 : ∀ x : ZMod p, x = 0 ∨ x = 1 → x.val ≤ 1 := by
    rintro x (rfl | rfl)
    · simp
    · rw [ZMod.val_one]
  have hrnval : (populateRemNeg vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))).val ≤ 4 := by
    have hmsb := hbin1 _ (remMsbCell_bool vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))
    have h0 := hbin1 _ (hf 0 (by omega)); have h2 := hbin1 _ (hf 2 (by omega))
    have h4 := hbin1 _ (hf 4 (by omega)); have h5 := hbin1 _ (hf 5 (by omega))
    rw [populateRemNeg]
    calc ((((selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[4]
            + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[5])) * remMsbCell vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))).val
        ≤ ((selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[4]
            + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[5]).val * (remMsbCell vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))).val :=
          hval_mul _ _
      _ ≤ 4 := by
          have hs1 := hval_add ((selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2]
            + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[4]) (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[5]
          have hs2 := hval_add ((selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2])
            (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[4]
          have hs3 := hval_add (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2]
          have := Nat.mul_le_mul (show ((selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[0] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[2]
            + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[4] + (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[5]).val ≤ 4 from by omega) hmsb
          omega
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  · obtain ⟨w0, w1, w2, w3⟩ :=
      Word.lt_cases_of_isU64 (populateRemComp_isU64 vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))
    have hrc0 := remCompFE_eval selectors env B C vB vC hWB hWC hUB hUC 0 (by omega)
    have hrc1 := remCompFE_eval selectors env B C vB vC hWB hWC hUB hUC 1 (by omega)
    have hrc2 := remCompFE_eval selectors env B C vB vC hWB hWC hUB hUC 2 (by omega)
    have hrc3 := remCompFE_eval selectors env B C vB vC hWB hWC hUB hUC 3 (by omega)
    rw [remAddendU, dif_pos hk4, remAddendNat, dif_pos hk4]
    refine ⟨?_, by interval_cases k <;> omega⟩
    interval_cases k <;>
      simp only [circuit_norm, hrc0, hrc1, hrc2, hrc3]
  · rw [remAddendU, dif_neg (by omega), remAddendNat, dif_neg (by omega)]
    refine ⟨?_, by
      have := Nat.mul_le_mul hrnval (le_refl 65535)
      omega⟩
    simp only [circuit_norm, hrn]

include hWB hWC hUB hUC in
/-- Evaluating the carry recursion is `carryNat`, with the ≤ `5` bound riding in the motive so
the u64 wrap never trips (each step is `(< 2^16) + (< 2^18) + (≤ 5)` over `2^16`). -/
private theorem carryChainU_toNat
    (hf : ∀ (k : ℕ) (_ : k < 8), (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[k] = 0 ∨ (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[k] = 1) :
    ∀ n, n < 8 → (((carryChainU selectors (quotCompBitsU selectors (wordU B) (wordU C)) (compU selectors (wordU C))
        (remCompFE selectors B C) (remNegFE selectors B C) n).eval { env := env }).toNat
        = carryNat vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) n
      ∧ carryNat vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) n ≤ 5) := by
  have hq : ((Witgen.U64Expr.eval { env := env }
      (quotCompBitsU selectors (wordU B) (wordU C))).toNat)
      = (Word.toBitVec64 (populateQuotComp vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))).toNat := by
    rw [quotCompBitsU_toNat selectors env B C vB vC hWB hWC hUB hUC, populateQuotComp,
      wordOfBits_toBitVec64]
  have hc : ((Witgen.U64Expr.eval { env := env } (compU selectors (wordU C))).toNat)
      = (Word.toBitVec64 (cComp vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))).toNat :=
    compU_toNat selectors env (wordU C) (wordU_toNat env C vC hWC hUC) hUC
  have hctqlt : ∀ k, ctqLimbNat vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))) k < 2 ^ 16 := fun k =>
    Nat.mod_lt _ (by norm_num)
  intro n
  induction n with
  | zero =>
    intro _
    have hl := ctqLimbU_toNat selectors env _ _ vB vC hq hc 0 (by omega)
    obtain ⟨hra, hrab⟩ := remAddendU_toNat selectors env B C vB vC hWB hWC hUB hUC hf 0 (by omega)
    have hb1 := hctqlt 0
    constructor
    · simp only [carryChainU, carryNat, circuit_norm, hl, hra]
      omega
    · rw [carryNat]
      omega
  | succ n ih =>
    intro hn
    obtain ⟨ih1, ih2⟩ := ih (by omega)
    have hl := ctqLimbU_toNat selectors env _ _ vB vC hq hc (n + 1) (by omega)
    obtain ⟨hra, hrab⟩ := remAddendU_toNat selectors env B C vB vC hWB hWC hUB hUC hf (n + 1) (by omega)
    have hb1 := hctqlt (n + 1)
    constructor
    · simp only [carryChainU, carryNat, circuit_norm, hl, hra, ih1]
      omega
    · rw [carryNat]
      omega

include hWB hWC hUB hUC in
/-- Evaluating a carry cell is the corresponding `populateCarry` cell. -/
theorem carryProgram_eval
    (hf : ∀ (k : ℕ) (_ : k < 8), (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[k] = 0 ∨ (selectorFlags (selectors.map (Expression.eval env.toEnvironment)))[k] = 1)
    (k : ℕ) (hk : k < 8) :
    ((carryProgram selectors B C).eval (value := fields 8) env)[k]
      = (populateCarry vB vC (selectorFlags (selectors.map (Expression.eval env.toEnvironment))))[k] := by
  have h := (carryChainU_toNat selectors env B C vB vC hWB hWC hUB hUC hf k hk).1
  rw [carryProgram_eval_limb]
  simp only [populateCarry, Vector.getElem_ofFn, h]

end CarrySite

end SP1Clean.DivRemChip
