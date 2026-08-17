import SP1Clean.Proofs.Chips.DivRemChip.Populate.IRCtq
import ToClean.Circuit.WitgenEval

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

/-! ## The overflow result cells and the `scal` site -/

section ScalPayloads

/-- The `is_overflow_b` result cell (the gated `IsEqualWordOperation` result, recomputed —
`populateIsOverflow` reads it off the witnessed struct, which SP1 populates per-event). -/
def ovbResFE (ir : Expression (ZMod p)) (B : Word (Expression (ZMod p))) :
    Witgen.FExpr (ZMod p) :=
  .ite ((Witgen.FExpr.expr ir) =? (1 : ZMod p))
    (.ite ((wSumF (p := p)) =? (1 : ZMod p))
      ((toElements (IsEqualWordOperation.populateFE
          #v[.expr B[0], .expr B[1], 0, 0] #v[0, .const 32768, 0, 0]))[10]'(by
        have h : size Extracted.IsEqualWordOperation = 11 := rfl
        omega))
      ((toElements (IsEqualWordOperation.populateFE
          #v[.expr B[0], .expr B[1], .expr B[2], .expr B[3]]
          #v[0, 0, 0, .const 32768]))[10]'(by
        have h : size Extracted.IsEqualWordOperation = 11 := rfl
        omega)))
    0

/-- The `is_overflow_c` result cell. -/
def ovcResFE (ir : Expression (ZMod p)) (C : Word (Expression (ZMod p))) :
    Witgen.FExpr (ZMod p) :=
  .ite ((Witgen.FExpr.expr ir) =? (1 : ZMod p))
    (.ite ((wSumF (p := p)) =? (1 : ZMod p))
      ((toElements (IsEqualWordOperation.populateFE
          #v[.expr C[0], .expr C[1], 0, 0]
          #v[.const 65535, .const 65535, 0, 0]))[10]'(by
        have h : size Extracted.IsEqualWordOperation = 11 := rfl
        omega))
      ((toElements (IsEqualWordOperation.populateFE
          #v[.expr C[0], .expr C[1], .expr C[2], .expr C[3]]
          #v[.const 65535, .const 65535, .const 65535, .const 65535]))[10]'(by
        have h : size Extracted.IsEqualWordOperation = 11 := rfl
        omega)))
    0

/-- `is_overflow = ovb.result · ovc.result · is_signed_type`. -/
def isOverflowFE (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Witgen.FExpr (ZMod p) :=
  ovbResFE ir B * ovcResFE ir C * signedSumF

/-- The seven scalar gate/sign cells site. -/
def scalFE (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Vector (Witgen.FExpr (ZMod p)) 7 :=
  #v[isOverflowFE ir B C, bNegFE B,
     bNegFE B * (1 - isOverflowFE ir B C),
     (1 - bNegFE B) * (1 - isOverflowFE ir B C),
     Witgen.FExpr.expr ir * (1 - wSumF), remNegFE B C, cNegFE C]

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
    (ovbResFE ir B).eval { env := env }
      = (ovbWitness vir vB (hintFlags env.hint)).is_diff_zero.result := by
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
  have h11 : (10 : ℕ) < size Extracted.IsEqualWordOperation := by
    have h : size Extracted.IsEqualWordOperation = 11 := rfl
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
  have e1 : (ovbResFE ir B).eval { env := env }
      = if ((Witgen.FExpr.expr ir) =? (1 : ZMod p)).eval { env := env }
        then (if ((wSumF (p := p)) =? (1 : ZMod p)).eval { env := env }
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
    by_cases h2 : (hintFlags env.hint)[4] + (hintFlags env.hint)[5]
        + (hintFlags env.hint)[6] + (hintFlags env.hint)[7] = 1
    · rw [if_pos (feq_true env _ _ _ (wSumF_eval env) h2), if_pos h2,
        IsEqualWordOperation.result_eq_toElements]
    · rw [if_neg (feq_false env _ _ _ (wSumF_eval env) h2), if_neg h2,
        IsEqualWordOperation.result_eq_toElements]
  · rw [if_neg (feq_false env _ _ _ hir h1), if_neg h1]
    rfl

omit [Fact (2 ^ 24 < p)] in
include hWC in
/-- Evaluating the `is_overflow_c` result cell is the witnessed struct's result. -/
theorem ovcResFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) :
    (ovcResFE ir C).eval { env := env }
      = (ovcWitness vir vC (hintFlags env.hint)).is_diff_zero.result := by
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
  have h11 : (10 : ℕ) < size Extracted.IsEqualWordOperation := by
    have h : size Extracted.IsEqualWordOperation = 11 := rfl
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
  have e1 : (ovcResFE ir C).eval { env := env }
      = if ((Witgen.FExpr.expr ir) =? (1 : ZMod p)).eval { env := env }
        then (if ((wSumF (p := p)) =? (1 : ZMod p)).eval { env := env }
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
    by_cases h2 : (hintFlags env.hint)[4] + (hintFlags env.hint)[5]
        + (hintFlags env.hint)[6] + (hintFlags env.hint)[7] = 1
    · rw [if_pos (feq_true env _ _ _ (wSumF_eval env) h2), if_pos h2,
        IsEqualWordOperation.result_eq_toElements]
    · rw [if_neg (feq_false env _ _ _ (wSumF_eval env) h2), if_neg h2,
        IsEqualWordOperation.result_eq_toElements]
  · rw [if_neg (feq_false env _ _ _ hir h1), if_neg h1]
    rfl

omit [Fact (2 ^ 24 < p)] in
include hWB hWC in
/-- Evaluating `is_overflow` is `populateIsOverflow`. -/
theorem isOverflowFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) :
    (isOverflowFE ir B C).eval { env := env }
      = populateIsOverflow vir vB vC (hintFlags env.hint) := by
  simp only [isOverflowFE, populateIsOverflow, circuit_norm,
    ovbResFE_eval env B vB hWB ir vir hir, ovcResFE_eval env C vC hWC ir vir hir,
    signedSumF_eval env]

include hWB hWC hUB hUC in
/-- Evaluating a `scal` cell is the corresponding `populateScal` cell. -/
theorem scalFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 7) :
    ((scalFE ir B C)[i]).eval { env := env }
      = (populateScal vir vB vC (hintFlags env.hint))[i] := by
  have hov := isOverflowFE_eval env B C vB vC hWB hWC ir vir hir
  have hbn := bNegFE_eval env B vB hWB hUB
  have hcn := cNegFE_eval env C vC hWC hUC
  have hrn := remNegFE_eval env B C vB vC hWB hWC hUB hUC
  interval_cases i <;>
    simp only [scalFE, populateScal, circuit_norm, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, hov, hbn, hcn, hrn, hir, wSumF_eval env]

end ScalEval

/-! ## The `c_times_quotient` site -/

section CtqSite

/-- The eight committed product limbs. -/
def ctqFE (B C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 8 :=
  Vector.ofFn fun k =>
    ctqLimbF (quotCompBitsU (wordU B) (wordU C)) (compU (wordU C)) k.val

variable (env : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)

include hWB hWC hUB hUC in
/-- Evaluating a product limb is the corresponding `populateCtq` cell. -/
theorem ctqFE_eval (k : ℕ) (hk : k < 8) :
    ((ctqFE B C)[k]).eval { env := env } = (populateCtq vB vC (hintFlags env.hint))[k] := by
  have hq : ((Witgen.U64Expr.eval { env := env }
      (quotCompBitsU (wordU B) (wordU C))).toNat)
      = (Word.toBitVec64 (populateQuotComp vB vC (hintFlags env.hint))).toNat := by
    rw [quotCompBitsU_toNat env B C vB vC hWB hWC hUB hUC, populateQuotComp,
      wordOfBits_toBitVec64]
  have hc : ((Witgen.U64Expr.eval { env := env } (compU (wordU C))).toNat)
      = (Word.toBitVec64 (cComp vC (hintFlags env.hint))).toNat :=
    compU_toNat env (wordU C) (wordU_toNat env C vC hWC hUC) hUC
  simpa only [ctqFE, Vector.getElem_ofFn] using
    ctqLimbF_eval env _ _ vB vC hq hc k hk

end CtqSite

/-! ## The `is_c_0` site and the remainder-check gate -/

section IsC0Site

/-- The `is_c_0` struct site (ungated, flat 11 cells). -/
def isC0FE (C : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 11 :=
  (toElements (IsZeroWordOperation.populateFE (compF C))).cast
    (show size Extracted.IsZeroWordOperation = 11 from rfl)

/-- The remainder-check gate cell `is_real · (1 − is_c_0.result)`. -/
def ltGateFE (ir : Expression (ZMod p)) (C : Word (Expression (ZMod p))) :
    Witgen.FExpr (ZMod p) :=
  Witgen.FExpr.expr ir * (1 - (IsZeroWordOperation.populateFE (compF C)).result)

variable (env : ProverEnvironment (ZMod p))
variable (C : Word (Expression (ZMod p))) (vC : Word (ZMod p))
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUC : vC.isU64)

omit [Fact (2 ^ 24 < p)] in
include hWC hUC in
/-- Evaluating an `is_c_0` cell is the corresponding flattened `isC0Witness` cell. -/
theorem isC0FE_eval (i : ℕ) (hi : i < 11) :
    ((isC0FE C)[i]).eval { env := env }
      = ((toElements (isC0Witness vC (hintFlags env.hint))).cast
          (show size Extracted.IsZeroWordOperation = 11 from rfl))[i] := by
  have h := IsZeroWordOperation.populateFE_eval env (compF C)
    (va := cComp vC (hintFlags env.hint)) (compF_eval env C vC hWC hUC)
  rw [isC0FE, Vector.getElem_cast, Vector.getElem_cast,
    Witgen.getElem_eval_toElements, h]
  rfl

omit [Fact (2 ^ 24 < p)] in
include hWC hUC in
/-- Evaluating the gate cell is `ltGate`. -/
theorem ltGateFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) :
    (ltGateFE ir C).eval { env := env } = ltGate vir vC (hintFlags env.hint) := by
  have h := IsZeroWordOperation.populateFE_eval env (compF C)
    (va := cComp vC (hintFlags env.hint)) (compF_eval env C vC hWC hUC)
  have hres : ((IsZeroWordOperation.populateFE (compF C)).result).eval { env := env }
      = (isC0Witness vC (hintFlags env.hint)).result := by
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
    .ite ((cNegFE C * Witgen.FExpr.expr ir) =? (1 : ZMod p))
      ((AddOperation.populateFW (compF C) (absCFE C))[i.val]) 0

/-- The `rem_neg_operation` value-word site (gated on `rem_neg · is_real = 1`). -/
def wRnegFE (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Vector (Witgen.FExpr (ZMod p)) 4 :=
  Vector.ofFn fun i =>
    .ite ((remNegFE B C * Witgen.FExpr.expr ir) =? (1 : ZMod p))
      ((AddOperation.populateFW (remFE B C) (absRemFE B C))[i.val]) 0

/-- The three event/multiplicity cells. -/
def miscFE (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Vector (Witgen.FExpr (ZMod p)) 3 :=
  #v[cNegFE C * Witgen.FExpr.expr ir, remNegFE B C * Witgen.FExpr.expr ir, ltGateFE ir C]

variable (env : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)

include hWC hUC in
/-- Evaluating a `c_neg_operation` cell is the corresponding `wCnegWitness` cell. -/
theorem wCnegFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 4) :
    ((wCnegFE ir C)[i]).eval { env := env }
      = (wCnegWitness vir vC (hintFlags env.hint))[i] := by
  have hcn := cNegFE_eval env C vC hWC hUC
  have hadd := AddOperation.populateFW_eval env (compF C) (absCFE C)
    (cComp vC (hintFlags env.hint)) (populateAbsC vC (hintFlags env.hint))
    (compF_eval env C vC hWC hUC) (absCFE_eval env C vC hWC hUC)
    (cComp_isU64 hUC _) (populateAbsC_isU64 hUC _) i hi
  simp only [wCnegFE, wCnegWitness, circuit_norm, Vector.getElem_ofFn, hcn, hir]
  split_ifs
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans hadd
  · contradiction
  · contradiction
  · interval_cases i <;> simp

include hWB hWC hUB hUC in
/-- Evaluating a `rem_neg_operation` cell is the corresponding `wRnegWitness` cell. -/
theorem wRnegFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 4) :
    ((wRnegFE ir B C)[i]).eval { env := env }
      = (wRnegWitness vir vB vC (hintFlags env.hint))[i] := by
  have hrn := remNegFE_eval env B C vB vC hWB hWC hUB hUC
  have hadd := AddOperation.populateFW_eval env (remFE B C) (absRemFE B C)
    (populateRemainder vB vC (hintFlags env.hint)) (populateAbsRem vB vC (hintFlags env.hint))
    (remFE_eval env B C vB vC hWB hWC hUB hUC) (absRemFE_eval env B C vB vC hWB hWC hUB hUC)
    (populateRemainder_isU64 vB vC _) (populateAbsRem_isU64 vB vC _) i hi
  simp only [wRnegFE, wRnegWitness, circuit_norm, Vector.getElem_ofFn, hrn, hir]
  split_ifs
  · exact (Witgen.FExpr.eval_getElem { env := env } _ i hi).symm.trans hadd
  · contradiction
  · contradiction
  · interval_cases i <;> simp

include hWB hWC hUB hUC in
/-- Evaluating a `misc` cell is the corresponding `populateMisc` cell. -/
theorem miscFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 3) :
    ((miscFE ir B C)[i]).eval { env := env }
      = (populateMisc vir vB vC (hintFlags env.hint))[i] := by
  have hcn := cNegFE_eval env C vC hWC hUC
  have hrn := remNegFE_eval env B C vB vC hWB hWC hUB hUC
  have hlg := ltGateFE_eval env C vC hWC hUC ir vir hir
  interval_cases i <;>
    simp only [miscFE, populateMisc, circuit_norm, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, hcn, hrn, hlg, hir]

end NegWordSites

/-! ## The remainder-check comparison sites -/

section LtSites

/-- The gated comparison-limb site. -/
def clFE (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Vector (Witgen.FExpr (ZMod p)) 2 :=
  Vector.ofFn fun k =>
    .ite ((ltGateFE ir C) =? (1 : ZMod p))
      (LtOperationUnsigned.comparisonLimbsF (absRemFE B C) (maxAbsFE C) k) 0

/-- The gated `u16_flags` site. -/
def ltfFE (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Vector (Witgen.FExpr (ZMod p)) 4 :=
  Vector.ofFn fun k =>
    .ite ((ltGateFE ir C) =? (1 : ZMod p))
      (LtOperationUnsigned.flagsF (absRemFE B C) (maxAbsFE C) k) 0

/-- The gated `not_eq_inv` site. -/
def neiFE (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Vector (Witgen.FExpr (ZMod p)) 1 :=
  #v[.ite ((ltGateFE ir C) =? (1 : ZMod p))
      (LtOperationUnsigned.notEqInvF (absRemFE B C) (maxAbsFE C)) 0]

/-- The gated compare-bit site. -/
def bitFE (ir : Expression (ZMod p)) (B C : Word (Expression (ZMod p))) :
    Vector (Witgen.FExpr (ZMod p)) 1 :=
  #v[.ite ((ltGateFE ir C) =? (1 : ZMod p))
      (LtOperationUnsigned.compareBitF (absRemFE B C) (maxAbsFE C)) 0]

variable (env : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
  (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
  (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
  (hUB : vB.isU64) (hUC : vC.isU64)

-- the shared scan facts over the evaluated (abs_remainder, max_abs_c_or_1) pair
include hWB hWC hUB hUC in
private theorem ltScan :
    (∀ k : Fin 2, (LtOperationUnsigned.comparisonLimbsF (absRemFE B C) (maxAbsFE C) k).eval
        { env := env }
      = (LtOperationUnsigned.comparisonLimbsWitness
          (populateAbsRem vB vC (hintFlags env.hint))
          (populateMaxAbsCOr1 vC (hintFlags env.hint)))[(k : ℕ)]) ∧
    (∀ k : Fin 4, (LtOperationUnsigned.flagsF (absRemFE B C) (maxAbsFE C) k).eval { env := env }
      = (LtOperationUnsigned.flagsWitness
          (populateAbsRem vB vC (hintFlags env.hint))
          (populateMaxAbsCOr1 vC (hintFlags env.hint)))[(k : ℕ)]) ∧
    (LtOperationUnsigned.notEqInvF (absRemFE B C) (maxAbsFE C)).eval { env := env }
      = (LtOperationUnsigned.notEqInvWitness
          (populateAbsRem vB vC (hintFlags env.hint))
          (populateMaxAbsCOr1 vC (hintFlags env.hint)))[0] ∧
    (LtOperationUnsigned.compareBitF (absRemFE B C) (maxAbsFE C)).eval { env := env }
      = U16CompareOperation.populate_bit
          (LtOperationUnsigned.comparisonLimbsWitness
            (populateAbsRem vB vC (hintFlags env.hint))
            (populateMaxAbsCOr1 vC (hintFlags env.hint)))[0]
          (LtOperationUnsigned.comparisonLimbsWitness
            (populateAbsRem vB vC (hintFlags env.hint))
            (populateMaxAbsCOr1 vC (hintFlags env.hint)))[1] :=
  LtOperationUnsigned.scanF_eval { env := env } _ _ _ _
    (absRemFE_eval env B C vB vC hWB hWC hUB hUC)
    (maxAbsFE_eval env C vC hWC hUC)

include hWB hWC hUB hUC in
/-- Evaluating a comparison-limb cell is the corresponding `ltClWitness` cell. -/
theorem clFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 2) :
    ((clFE ir B C)[i]).eval { env := env }
      = (ltClWitness vir vB vC (hintFlags env.hint))[i] := by
  have hlg := ltGateFE_eval env C vC hWC hUC ir vir hir
  have hscan := (ltScan env B C vB vC hWB hWC hUB hUC).1 ⟨i, hi⟩
  simp only [clFE, ltClWitness, circuit_norm, Vector.getElem_ofFn, hlg]
  split_ifs
  · exact hscan
  · interval_cases i <;> rfl

include hWB hWC hUB hUC in
/-- Evaluating a `u16_flags` cell is the corresponding `ltFlagsWitness` cell. -/
theorem ltfFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 4) :
    ((ltfFE ir B C)[i]).eval { env := env }
      = (ltFlagsWitness vir vB vC (hintFlags env.hint))[i] := by
  have hlg := ltGateFE_eval env C vC hWC hUC ir vir hir
  have hscan := (ltScan env B C vB vC hWB hWC hUB hUC).2.1 ⟨i, hi⟩
  simp only [ltfFE, ltFlagsWitness, circuit_norm, Vector.getElem_ofFn, hlg]
  split_ifs
  · exact hscan
  · interval_cases i <;> rfl

include hWB hWC hUB hUC in
/-- Evaluating the `not_eq_inv` cell is the `ltNotEqInvWitness` cell. -/
theorem neiFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 1) :
    ((neiFE ir B C)[i]).eval { env := env }
      = (ltNotEqInvWitness vir vB vC (hintFlags env.hint))[i] := by
  have hlg := ltGateFE_eval env C vC hWC hUC ir vir hir
  have hscan := (ltScan env B C vB vC hWB hWC hUB hUC).2.2.1
  interval_cases i
  simp only [neiFE, ltNotEqInvWitness, circuit_norm, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, hlg]
  split_ifs
  · exact hscan
  · rfl

include hWB hWC hUB hUC in
/-- Evaluating the compare-bit cell is the `ltBitWitness` cell. -/
theorem bitFE_eval (ir : Expression (ZMod p)) (vir : ZMod p)
    (hir : Expression.eval env.toEnvironment ir = vir) (i : ℕ) (hi : i < 1) :
    ((bitFE ir B C)[i]).eval { env := env }
      = (ltBitWitness vir vB vC (hintFlags env.hint))[i] := by
  have hlg := ltGateFE_eval env C vC hWC hUC ir vir hir
  have hscan := (ltScan env B C vB vC hWB hWC hUB hUC).2.2.2
  interval_cases i
  simp only [bitFE, ltBitWitness, ltClWitness, circuit_norm, Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_zero, hlg]
  split_ifs with h
  · rw [hscan]
    congr 1
  · rfl

end LtSites

end SP1Clean.DivRemChip
