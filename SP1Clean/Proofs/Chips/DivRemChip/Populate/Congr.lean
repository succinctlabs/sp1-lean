import SP1Clean.Proofs.Chips.DivRemChip.Populate.FE

/-! # `DivRemChip` — witness-payload environment-locality (A7f)

The `ComputableWitnesses` counterparts of the `Populate/{IR,IRWord,IRCtq,FE}` eval lemmas:
every payload reads its environment only through the operand-read expressions, `is_real`, and
the `"div_rem_flags"` hint, so two environments agreeing there produce identical witnesses.
All congruences, no bounds. Two proof shapes:

* **Flat same-tree simp** (most sites): unfold to the leaves, rewrite the operand and hint
  reads in the same pass — the leaf must rewrite *in the simp that forms the dispatch
  condition*, or it lands under a baked `Decidable` instance no later pass can reach.
* **Compositional** (`srwMsbIR_congr`'s discipline, for the struct-read and scan sites):
  instantiate the sub-payload congruence as a `have` (`IsEqualWordOperation.populateFE_congr`,
  `LtOperationUnsigned.scanF_congr`, the carry addend/limb helpers) and keep the sub-payload
  folded in the final simp. The `is_overflow_*` cells route the folded struct read through
  `Witgen.getElem_eval_toElements` instantiated explicitly (its `size` side-condition is not
  simp-dischargeable) and close by `if_congr` + `exact`, since the struct-eval terms match
  only up to instance paths. -/

namespace SP1Clean.DivRemChip

open Circuit

-- The site congruences below share one hypothesis template (`hB`/`hC`/`hir`/`hhint`) and a
-- small family of unfold lists, so the `ComputableWitnesses` slots consume them uniformly;
-- per-site minimisation of the lists (and of the included hypotheses) would trade that
-- uniformity for noise. Both linters are on the repo's sanctioned-suppression list.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

section CalculusCongr

variable (env env' : ProverEnvironment (ZMod p))

omit [Fact (2 ^ 24 < p)] in
/-- The derived flags agree whenever the hints do. -/
theorem flagF_congr (hhint : env.hint = env'.hint) (k : ℕ) (hk : k < 8) :
    (flagF (p := p) k).eval { env := env } = (flagF k).eval { env := env' } := by
  rw [flagF_eval env k hk, flagF_eval env' k hk, hhint]

omit [Fact (2 ^ 24 < p)] in
/-- The remainder dispatch, one same-tree simp (the template every payload congruence below
follows: unfold to the leaves, rewrite the operand and hint reads, both sides coincide). -/
theorem remBitsU_congr (hhint : env.hint = env'.hint) (b c : Witgen.U64Expr (ZMod p))
    (hb : b.eval { env := env } = b.eval { env := env' })
    (hc : c.eval { env := env } = c.eval { env := env' }) :
    (remBitsU b c).eval { env := env } = (remBitsU b c).eval { env := env' } := by
  simp only [remBitsU, negU, neg32U, low32U, sext32U, srem32U, sremU, flagF, hintF,
    circuit_norm, -Witgen.u64Wrap, hb, hc, hhint]

end CalculusCongr

section SiteCongr

variable (env env' : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (ir : Expression (ZMod p))
  (hB : ∀ (i : ℕ) (_ : i < 4),
    Expression.eval env.toEnvironment B[i] = Expression.eval env'.toEnvironment B[i])
  (hC : ∀ (i : ℕ) (_ : i < 4),
    Expression.eval env.toEnvironment C[i] = Expression.eval env'.toEnvironment C[i])
  (hir : Expression.eval env.toEnvironment ir = Expression.eval env'.toEnvironment ir)
  (hhint : env.hint = env'.hint)


omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the flags site. -/
theorem flagsCongr :
    (Witgen.WitgenIR.ofFExprs (flagsFE (p := p))).eval env
      = (Witgen.WitgenIR.ofFExprs (flagsFE (p := p))).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [flagsFE, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `quotient_comp` site. -/
theorem quotCompCongr :
    (Witgen.WitgenIR.ofFExprs (quotCompFE B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (quotCompFE B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [quotCompFE, wordFOfU64, quotCompBitsU, quotBitsU, allOnesU, compU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the result-word site. -/
theorem aCongr :
    (Witgen.WitgenIR.ofFExprs (aFE B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (aFE B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [aFE, quotFE, remFE, wordFOfU64, quotBitsU, remBitsU, allOnesU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the committed `b` operand site. -/
theorem bCongr :
    (Witgen.WitgenIR.ofFExprs (compF B)).eval env
      = (Witgen.WitgenIR.ofFExprs (compF B)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [compF, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the committed `c` operand site. -/
theorem cCongr :
    (Witgen.WitgenIR.ofFExprs (compF C)).eval env
      = (Witgen.WitgenIR.ofFExprs (compF C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [compF, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hir hhint in
/-- Environment-locality of the `is_overflow_b` result cell (the two `IsEqualWordOperation`
struct reads stay folded; `Witgen.getElem_eval_toElements` + the struct-level congruence
close them — the `srwMsbIR_congr` discipline). -/
private theorem ovbResCongr :
    Witgen.FExpr.eval { env := env } (ovbResFE ir B)
      = Witgen.FExpr.eval { env := env' } (ovbResFE ir B) := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have h1 := IsEqualWordOperation.populateFE_congr env env'
      #v[.expr B[0], .expr B[1], 0, 0] #v[0, .const 32768, 0, 0]
      (by intro i hi; interval_cases i <;>
        simp only [circuit_norm, -Witgen.u64Wrap, hB0, hB1])
      (by intro i hi; interval_cases i <;>
        simp only [circuit_norm, -Witgen.u64Wrap])
  have h2 := IsEqualWordOperation.populateFE_congr env env'
      #v[.expr B[0], .expr B[1], .expr B[2], .expr B[3]] #v[0, 0, 0, .const 32768]
      (by intro i hi; interval_cases i <;>
        simp only [circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3])
      (by intro i hi; interval_cases i <;>
        simp only [circuit_norm, -Witgen.u64Wrap])
  have hsz : (10 : ℕ) < size Extracted.IsEqualWordOperation := by
    have h : size Extracted.IsEqualWordOperation = 11 := rfl
    omega
  have hc1 := Witgen.getElem_eval_toElements { env := env }
      (IsEqualWordOperation.populateFE #v[.expr B[0], .expr B[1], 0, 0]
        #v[0, .const 32768, 0, 0]) 10 hsz
  have hc1' := Witgen.getElem_eval_toElements { env := env' }
      (IsEqualWordOperation.populateFE #v[.expr B[0], .expr B[1], 0, 0]
        #v[0, .const 32768, 0, 0]) 10 hsz
  have hc2 := Witgen.getElem_eval_toElements { env := env }
      (IsEqualWordOperation.populateFE
        #v[.expr B[0], .expr B[1], .expr B[2], .expr B[3]] #v[0, 0, 0, .const 32768]) 10 hsz
  have hc2' := Witgen.getElem_eval_toElements { env := env' }
      (IsEqualWordOperation.populateFE
        #v[.expr B[0], .expr B[1], .expr B[2], .expr B[3]] #v[0, 0, 0, .const 32768]) 10 hsz
  simp only [ovbResFE, wSumF, flagF, hintF, circuit_norm, -Witgen.u64Wrap, hir, hhint]
  refine if_congr Iff.rfl (if_congr Iff.rfl ?_ ?_) rfl
  · exact hc1.trans (((congrArg (fun s => (toElements s)[10]'hsz) h1)).trans hc1'.symm)
  · exact hc2.trans (((congrArg (fun s => (toElements s)[10]'hsz) h2)).trans hc2'.symm)

omit [Fact (2 ^ 24 < p)] in
include hC hir hhint in
/-- Environment-locality of the `is_overflow_c` result cell. -/
private theorem ovcResCongr :
    Witgen.FExpr.eval { env := env } (ovcResFE ir C)
      = Witgen.FExpr.eval { env := env' } (ovcResFE ir C) := by
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  have h1 := IsEqualWordOperation.populateFE_congr env env'
      #v[.expr C[0], .expr C[1], 0, 0] #v[.const 65535, .const 65535, 0, 0]
      (by intro i hi; interval_cases i <;>
        simp only [circuit_norm, -Witgen.u64Wrap, hC0, hC1])
      (by intro i hi; interval_cases i <;>
        simp only [circuit_norm, -Witgen.u64Wrap])
  have h2 := IsEqualWordOperation.populateFE_congr env env'
      #v[.expr C[0], .expr C[1], .expr C[2], .expr C[3]]
      #v[.const 65535, .const 65535, .const 65535, .const 65535]
      (by intro i hi; interval_cases i <;>
        simp only [circuit_norm, -Witgen.u64Wrap, hC0, hC1, hC2, hC3])
      (by intro i hi; interval_cases i <;>
        simp only [circuit_norm, -Witgen.u64Wrap])
  have hsz : (10 : ℕ) < size Extracted.IsEqualWordOperation := by
    have h : size Extracted.IsEqualWordOperation = 11 := rfl
    omega
  have hc1 := Witgen.getElem_eval_toElements { env := env }
      (IsEqualWordOperation.populateFE #v[.expr C[0], .expr C[1], 0, 0]
        #v[.const 65535, .const 65535, 0, 0]) 10 hsz
  have hc1' := Witgen.getElem_eval_toElements { env := env' }
      (IsEqualWordOperation.populateFE #v[.expr C[0], .expr C[1], 0, 0]
        #v[.const 65535, .const 65535, 0, 0]) 10 hsz
  have hc2 := Witgen.getElem_eval_toElements { env := env }
      (IsEqualWordOperation.populateFE
        #v[.expr C[0], .expr C[1], .expr C[2], .expr C[3]]
        #v[.const 65535, .const 65535, .const 65535, .const 65535]) 10 hsz
  have hc2' := Witgen.getElem_eval_toElements { env := env' }
      (IsEqualWordOperation.populateFE
        #v[.expr C[0], .expr C[1], .expr C[2], .expr C[3]]
        #v[.const 65535, .const 65535, .const 65535, .const 65535]) 10 hsz
  simp only [ovcResFE, wSumF, flagF, hintF, circuit_norm, -Witgen.u64Wrap, hir, hhint]
  refine if_congr Iff.rfl (if_congr Iff.rfl ?_ ?_) rfl
  · exact hc1.trans (((congrArg (fun s => (toElements s)[10]'hsz) h1)).trans hc1'.symm)
  · exact hc2.trans (((congrArg (fun s => (toElements s)[10]'hsz) h2)).trans hc2'.symm)

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `scal` site. -/
theorem scalCongr :
    (Witgen.WitgenIR.ofFExprs (scalFE ir B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (scalFE ir B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  have hovb := ovbResCongr env env' B ir hB hir hhint
  have hovc := ovcResCongr env env' C ir hC hir hhint
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [scalFE, isOverflowFE, bNegFE, cNegFE, remNegFE, bMsbFE, cMsbFE, remMsbFE, signedSumF, wSumF, remFE, wordFOfU64, remBitsU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hovb, hovc, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `c_times_quotient` site. -/
theorem ctqCongr :
    (Witgen.WitgenIR.ofFExprs (ctqFE B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (ctqFE B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only  [reduceIte, reduceDIte, Nat.reduceLT, Nat.reduceSub, Nat.reduceMul, ctqFE, ctqLimbF, ctqLimbU, ctqHiU, umulhU, quotCompBitsU, quotBitsU, allOnesU, compU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `is_c_0` site. -/
theorem isC0Congr :
    (Witgen.WitgenIR.ofFExprs (isC0FE C)).eval env
      = (Witgen.WitgenIR.ofFExprs (isC0FE C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  have hcells : ∀ (j : ℕ) (_ : j < 4),
      Witgen.FExpr.eval { env := env } (compF C)[j]
        = Witgen.FExpr.eval { env := env' } (compF C)[j] := by
    intro j hj
    interval_cases j <;>
    simp only [compF, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF,
        circuit_norm, -Witgen.u64Wrap, hC0, hC1, hC2, hC3, hhint]
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs, isC0FE, Vector.getElem_cast,
    Witgen.getElem_eval_toElements,
    IsZeroWordOperation.populateFE_congr env env' (compF C) hcells]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `abs_c` site. -/
theorem absCCongr :
    (Witgen.WitgenIR.ofFExprs (absCFE C)).eval env
      = (Witgen.WitgenIR.ofFExprs (absCFE C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [absCFE, compU, compF, wSumF, signedSumF, wordFOfU64, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `abs_remainder` site. -/
theorem absRemCongr :
    (Witgen.WitgenIR.ofFExprs (absRemFE B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (absRemFE B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [absRemFE, remCompFE, wordFOfU64, remCompBitsU, remBitsU, compU, signedSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `remainder_comp` site. -/
theorem remCompCongr :
    (Witgen.WitgenIR.ofFExprs (remCompFE B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (remCompFE B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [remCompFE, wordFOfU64, remCompBitsU, remBitsU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `max_abs_c_or_1` site. -/
theorem maxAbsCongr :
    (Witgen.WitgenIR.ofFExprs (maxAbsFE C)).eval env
      = (Witgen.WitgenIR.ofFExprs (maxAbsFE C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [maxAbsFE, absCU, absCFE, compU, compF, wSumF, signedSumF, wordFOfU64, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `c_neg_operation` site. -/
theorem wCnegCongr :
    (Witgen.WitgenIR.ofFExprs (wCnegFE ir C)).eval env
      = (Witgen.WitgenIR.ofFExprs (wCnegFE ir C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [wCnegFE, cNegFE, cMsbFE, absCFE, compU, compF, wSumF, signedSumF, wordFOfU64, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF, AddOperation.populateFW,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `rem_neg_operation` site. -/
theorem wRnegCongr :
    (Witgen.WitgenIR.ofFExprs (wRnegFE ir B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (wRnegFE ir B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [wRnegFE, remNegFE, remMsbFE, remFE, absRemFE, remCompFE, wordFOfU64, remCompBitsU, remBitsU, wSumF, signedSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF, AddOperation.populateFW,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `misc` site. -/
theorem miscCongr :
    (Witgen.WitgenIR.ofFExprs (miscFE ir B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (miscFE ir B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [miscFE, cNegFE, remNegFE, cMsbFE, remMsbFE, remFE, ltGateFE, compF, wordFOfU64, remBitsU, wSumF, signedSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF, IsZeroWordOperation.populateFE, IsZeroOperation.populateFE,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hhint in
/-- Cell-level environment-locality of `abs_remainder` (feeds `scanF_congr`). -/
private theorem absRemCellCongr :
    ∀ (j : ℕ) (_ : j < 4),
      Witgen.FExpr.eval { env := env } (absRemFE B C)[j]
        = Witgen.FExpr.eval { env := env' } (absRemFE B C)[j] := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  intro j hj
  interval_cases j <;>
  simp only [absRemFE, remCompFE, wordFOfU64, remCompBitsU, remBitsU, compU, signedSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hhint]

omit [Fact (2 ^ 24 < p)] in
include hC hhint in
/-- Cell-level environment-locality of `max_abs_c_or_1` (feeds `scanF_congr`). -/
private theorem maxAbsCellCongr :
    ∀ (j : ℕ) (_ : j < 4),
      Witgen.FExpr.eval { env := env } (maxAbsFE C)[j]
        = Witgen.FExpr.eval { env := env' } (maxAbsFE C)[j] := by
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  intro j hj
  interval_cases j <;>
  simp only [maxAbsFE, absCU, absCFE, compU, compF, wSumF, signedSumF, wordFOfU64, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hC0, hC1, hC2, hC3, hhint]

omit [Fact (2 ^ 24 < p)] in
include hC hir hhint in
/-- Environment-locality of the remainder-check gate cell. -/
private theorem ltGateCongr :
    Witgen.FExpr.eval { env := env } (ltGateFE ir C)
      = Witgen.FExpr.eval { env := env' } (ltGateFE ir C) := by
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  simp only [ltGateFE, compF, wSumF, signedSumF, wordFOfU64, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF, IsZeroWordOperation.populateFE, IsZeroOperation.populateFE,
      circuit_norm, -Witgen.u64Wrap, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the comparison-limb site (compositional: the gate cell plus
`LtOperationUnsigned.scanF_congr` over the folded operand payloads). -/
theorem clCongr :
    (Witgen.WitgenIR.ofFExprs (clFE ir B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (clFE ir B C)).eval env' := by
  have hgate := ltGateCongr env env' C ir hC hir hhint
  have hscan := LtOperationUnsigned.scanF_congr { env := env } { env := env' }
      (absRemFE B C) (maxAbsFE C)
      (absRemCellCongr env env' B C hB hC hhint)
      (maxAbsCellCongr env env' C hC hhint)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [clFE, circuit_norm, -Witgen.u64Wrap, hgate,
    hscan.1 ⟨0, by omega⟩, hscan.1 ⟨1, by omega⟩]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `u16_flags` site (compositional, like `clCongr`). -/
theorem ltfCongr :
    (Witgen.WitgenIR.ofFExprs (ltfFE ir B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (ltfFE ir B C)).eval env' := by
  have hgate := ltGateCongr env env' C ir hC hir hhint
  have hscan := LtOperationUnsigned.scanF_congr { env := env } { env := env' }
      (absRemFE B C) (maxAbsFE C)
      (absRemCellCongr env env' B C hB hC hhint)
      (maxAbsCellCongr env env' C hC hhint)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [ltfFE, circuit_norm, -Witgen.u64Wrap, hgate,
    hscan.2.1 ⟨0, by omega⟩, hscan.2.1 ⟨1, by omega⟩,
    hscan.2.1 ⟨2, by omega⟩, hscan.2.1 ⟨3, by omega⟩]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `not_eq_inv` site. -/
theorem neiCongr :
    (Witgen.WitgenIR.ofFExprs (neiFE ir B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (neiFE ir B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  obtain rfl : i = 0 := by omega
  simp only [neiFE, ltGateFE, absRemFE, maxAbsFE, absCU, absCFE, remCompFE, compU, compF, wordFOfU64, remCompBitsU, remBitsU, wSumF, signedSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF, IsZeroWordOperation.populateFE, IsZeroOperation.populateFE, LtOperationUnsigned.comparisonLimbsF, LtOperationUnsigned.flagsF, LtOperationUnsigned.notEqInvF, LtOperationUnsigned.compareBitF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the compare-bit site. -/
theorem bitCongr :
    (Witgen.WitgenIR.ofFExprs (bitFE ir B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (bitFE ir B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  obtain rfl : i = 0 := by omega
  simp only [bitFE, ltGateFE, absRemFE, maxAbsFE, absCU, absCFE, remCompFE, compU, compF, wordFOfU64, remCompBitsU, remBitsU, wSumF, signedSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF, IsZeroWordOperation.populateFE, IsZeroOperation.populateFE, LtOperationUnsigned.comparisonLimbsF, LtOperationUnsigned.flagsF, LtOperationUnsigned.notEqInvF, LtOperationUnsigned.compareBitF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `remainder` site. -/
theorem remCongr :
    (Witgen.WitgenIR.ofFExprs (remFE B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (remFE B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [remFE, wordFOfU64, remBitsU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `quotient` site. -/
theorem quotCongr :
    (Witgen.WitgenIR.ofFExprs (quotFE B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (quotFE B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [quotFE, wordFOfU64, quotBitsU, allOnesU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `b_msb` cell site. -/
theorem bMsbCongr :
    (Witgen.WitgenIR.ofFExprs (#v[bMsbFE B])).eval env
      = (Witgen.WitgenIR.ofFExprs (#v[bMsbFE B])).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  obtain rfl : i = 0 := by omega
  simp only [bMsbFE, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `c_msb` cell site. -/
theorem cMsbCongr :
    (Witgen.WitgenIR.ofFExprs (#v[cMsbFE C])).eval env
      = (Witgen.WitgenIR.ofFExprs (#v[cMsbFE C])).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  obtain rfl : i = 0 := by omega
  simp only [cMsbFE, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `rem_msb` cell site. -/
theorem remMsbCongr :
    (Witgen.WitgenIR.ofFExprs (#v[remMsbFE B C])).eval env
      = (Witgen.WitgenIR.ofFExprs (#v[remMsbFE B C])).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  obtain rfl : i = 0 := by omega
  simp only [remMsbFE, remFE, wordFOfU64, remBitsU, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hhint in
/-- Environment-locality of the `quot_msb` cell site. -/
theorem quotMsbCongr :
    (Witgen.WitgenIR.ofFExprs (#v[quotMsbFE B C])).eval env
      = (Witgen.WitgenIR.ofFExprs (#v[quotMsbFE B C])).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  obtain rfl : i = 0 := by omega
  simp only [quotMsbFE, quotFE, wordFOfU64, quotBitsU, allOnesU, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hhint in
/-- Environment-locality of the committed-operand product arguments (the `carry` chain's two
`u64` inputs, congruence-instantiated once). -/
private theorem carryArgsCongr :
    (quotCompBitsU (wordU B) (wordU C)).eval { env := env }
        = (quotCompBitsU (wordU B) (wordU C)).eval { env := env' }
      ∧ (compU (wordU C)).eval { env := env } = (compU (wordU C)).eval { env := env' } := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  constructor <;>
  simp only [quotCompBitsU, quotBitsU, allOnesU, compU, negU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, hintF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hhint]

omit [Fact (2 ^ 24 < p)] in
include hhint in
/-- Environment-locality of a product limb over abstract argument congruences. -/
private theorem ctqLimbCongr (q c : Witgen.U64Expr (ZMod p))
    (hq : q.eval { env := env } = q.eval { env := env' })
    (hc : c.eval { env := env } = c.eval { env := env' }) :
    ∀ k, (ctqLimbU q c k).eval { env := env } = (ctqLimbU q c k).eval { env := env' } := by
  intro k
  unfold ctqLimbU
  split_ifs <;>
  simp only [ctqHiU, umulhU, negU, flagF, hintF,
    circuit_norm, -Witgen.u64Wrap, hq, hc, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hhint in
/-- Environment-locality of the remainder addend at every limb (the `k < 4` dispatch splits;
each branch is one same-tree simp). -/
private theorem remAddendCongr :
    ∀ k, (remAddendU B C k).eval { env := env } = (remAddendU B C k).eval { env := env' } := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  intro k
  by_cases h : k < 4
  · interval_cases k <;>
    simp only [remAddendU, reduceDIte, Nat.reduceLT, remCompFE, wordFOfU64, remCompBitsU, remBitsU, negU, sremU, srem32U, neg32U, low32U, sext32U, wordU, flagF, hintF,
        circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hhint]
  · simp only [remAddendU, dif_neg h, remNegFE, remMsbFE, remFE, wordFOfU64, remBitsU, wSumF, signedSumF, negU, sremU, srem32U, neg32U, low32U, sext32U, wordU, flagF, hintF, U16MSBOperation.populate_msbF,
        circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hhint]

omit [Fact (2 ^ 24 < p)] in
include hB hC hhint in
/-- Environment-locality of the carry recursion, by induction with the addend and limb
congruences folded (unfolding the whole eight-deep chain at once is over budget). -/
private theorem carryChainU_congr :
    ∀ n, (carryChainU B C n).eval { env := env } = (carryChainU B C n).eval { env := env' } := by
  have hargs := carryArgsCongr env env' B C hB hC hhint
  have hlimb := ctqLimbCongr env env' hhint _ _ hargs.1 hargs.2
  have haddend := remAddendCongr env env' B C hB hC hhint
  intro n
  induction n with
  | zero =>
    simp only [carryChainU, circuit_norm, -Witgen.u64Wrap, hlimb 0, haddend 0]
  | succ n ih =>
    simp only [carryChainU, circuit_norm, -Witgen.u64Wrap, hlimb (n + 1), haddend (n + 1), ih]

omit [Fact (2 ^ 24 < p)] in
include hB hC hhint in
/-- Environment-locality of the `carry` site. -/
theorem carryCongr :
    (Witgen.WitgenIR.ofFExprs (carryFE B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (carryFE B C)).eval env' := by
  have hch := carryChainU_congr env env' B C hB hC hhint
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs, carryFE, Vector.getElem_ofFn,
    circuit_norm, hch]

end SiteCongr

end SP1Clean.DivRemChip
