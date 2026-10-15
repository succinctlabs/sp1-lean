import SP1Clean.Proofs.Chips.DivRemChip.Populate.FE

/-! # `DivRemChip` — witness-payload environment-locality (A7f)

The `ComputableWitnesses` counterparts of the `Populate/{IR,IRWord,IRCtq,FE}` eval lemmas:
every payload reads its environment only through the operand-read expressions, `is_real`, and
the seven supplied selectors, so two environments agreeing there produce identical witnesses.
All congruences, no bounds. Two proof shapes:

* **Flat same-tree simp** (most sites): unfold to the leaves, rewrite the operand and selector
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

-- The site congruences below share one hypothesis template (`hB`/`hC`/`hir`/`hselectors`) and a
-- small family of unfold lists, so the `ComputableWitnesses` slots consume them uniformly;
-- per-site minimisation of the lists (and of the included hypotheses) would trade that
-- uniformity for noise. Both linters are on the repo's sanctioned-suppression list.
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
variable (selectors : Vector (Expression (ZMod p)) 7)

section CalculusCongr

variable (env env' : ProverEnvironment (ZMod p))

omit [Fact (2 ^ 24 < p)] in
/-- The derived flags agree whenever the selector inputs do. -/
theorem flagF_congr (hselectors : ∀ i (hi : i < 7), Expression.eval env.toEnvironment selectors[i] =
      Expression.eval env'.toEnvironment selectors[i]) (k : ℕ) (hk : k < 8) :
    (flagF selectors k).eval { env := env } = (flagF selectors k).eval { env := env' } := by
  interval_cases k <;> simp only [flagF, selectorF, circuit_norm, hselectors]

omit [Fact (2 ^ 24 < p)] in
/-- The remainder dispatch, one same-tree simp (the template every payload congruence below
follows: unfold to the leaves, rewrite the operand and selector reads, both sides coincide). -/
theorem remBitsU_congr (hselectors : ∀ i (hi : i < 7), Expression.eval env.toEnvironment selectors[i] =
      Expression.eval env'.toEnvironment selectors[i]) (b c : Witgen.U64Expr (ZMod p))
    (hb : b.eval { env := env } = b.eval { env := env' })
    (hc : c.eval { env := env } = c.eval { env := env' }) :
    (remBitsU selectors b c).eval { env := env } = (remBitsU selectors b c).eval { env := env' } := by
  simp only [remBitsU, negU, neg32U, low32U, sext32U, srem32U, sremU, flagF, selectorF,
    circuit_norm, -Witgen.u64Wrap, hb, hc, hselectors]

end CalculusCongr

section SiteCongr

variable (env env' : ProverEnvironment (ZMod p))
variable (B C : Word (Expression (ZMod p))) (ir : Expression (ZMod p))
  (hB : ∀ (i : ℕ) (_ : i < 4),
    Expression.eval env.toEnvironment B[i] = Expression.eval env'.toEnvironment B[i])
  (hC : ∀ (i : ℕ) (_ : i < 4),
    Expression.eval env.toEnvironment C[i] = Expression.eval env'.toEnvironment C[i])
  (hir : Expression.eval env.toEnvironment ir = Expression.eval env'.toEnvironment ir)
  (hselectors : ∀ i (hi : i < 7), Expression.eval env.toEnvironment selectors[i] =
      Expression.eval env'.toEnvironment selectors[i])


omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `quotient_comp` site. -/
theorem quotCompCongr :
    (Witgen.WitgenIR.ofFExprs (quotCompFE selectors B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (quotCompFE selectors B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [quotCompFE, wordFOfU64, quotCompBitsU, quotBitsU, allOnesU, compU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the result-word site. -/
theorem aCongr :
    (Witgen.WitgenIR.ofFExprs (aFE selectors B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (aFE selectors B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [aFE, quotFE, remFE, wordFOfU64, quotBitsU, remBitsU, allOnesU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the committed `b` operand site. -/
theorem bCongr :
    (Witgen.WitgenIR.ofFExprs (compF selectors B)).eval env
      = (Witgen.WitgenIR.ofFExprs (compF selectors B)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [compF, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the committed `c` operand site. -/
theorem cCongr :
    (Witgen.WitgenIR.ofFExprs (compF selectors C)).eval env
      = (Witgen.WitgenIR.ofFExprs (compF selectors C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [compF, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hir hselectors in
/-- Environment-locality of the `is_overflow_b` result cell (the two `IsEqualWordOperation`
struct reads stay folded; `Witgen.getElem_eval_toElements` + the struct-level congruence
close them — the `srwMsbIR_congr` discipline). -/
private theorem ovbResCongr :
    Witgen.FExpr.eval { env := env } (ovbResFE selectors ir B)
      = Witgen.FExpr.eval { env := env' } (ovbResFE selectors ir B) := by
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
  have hsz : (10 : ℕ) < size Circuits.Types.IsEqualWordOperation := by
    have h : size Circuits.Types.IsEqualWordOperation = 11 := rfl
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
  simp only [ovbResFE, wSumF, flagF, selectorF, circuit_norm, -Witgen.u64Wrap, hir, hselectors]
  refine if_congr Iff.rfl (if_congr Iff.rfl ?_ ?_) rfl
  · rw [← Witgen.FExpr.eval_getElem, ← Witgen.FExpr.eval_getElem]
    exact hc1.trans (((congrArg (fun s => (toElements s)[10]'hsz) h1)).trans hc1'.symm)
  · rw [← Witgen.FExpr.eval_getElem, ← Witgen.FExpr.eval_getElem]
    exact hc2.trans (((congrArg (fun s => (toElements s)[10]'hsz) h2)).trans hc2'.symm)

omit [Fact (2 ^ 24 < p)] in
include hC hir hselectors in
/-- Environment-locality of the `is_overflow_c` result cell. -/
private theorem ovcResCongr :
    Witgen.FExpr.eval { env := env } (ovcResFE selectors ir C)
      = Witgen.FExpr.eval { env := env' } (ovcResFE selectors ir C) := by
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
  have hsz : (10 : ℕ) < size Circuits.Types.IsEqualWordOperation := by
    have h : size Circuits.Types.IsEqualWordOperation = 11 := rfl
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
  simp only [ovcResFE, wSumF, flagF, selectorF, circuit_norm, -Witgen.u64Wrap, hir, hselectors]
  refine if_congr Iff.rfl (if_congr Iff.rfl ?_ ?_) rfl
  · rw [← Witgen.FExpr.eval_getElem, ← Witgen.FExpr.eval_getElem]
    exact hc1.trans (((congrArg (fun s => (toElements s)[10]'hsz) h1)).trans hc1'.symm)
  · rw [← Witgen.FExpr.eval_getElem, ← Witgen.FExpr.eval_getElem]
    exact hc2.trans (((congrArg (fun s => (toElements s)[10]'hsz) h2)).trans hc2'.symm)

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `scal` site. -/
theorem scalCongr :
    (Witgen.WitgenIR.ofFExprs (scalFE selectors ir B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (scalFE selectors ir B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  have hovb := ovbResCongr selectors env env' B ir hB hir hselectors
  have hovc := ovcResCongr selectors env env' C ir hC hir hselectors
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [scalFE, isOverflowFE, bNegFE, cNegFE, remNegFE, bMsbFE, cMsbFE, remMsbFE, signedSumF, wSumF, remFE, wordFOfU64, remBitsU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hovb, hovc, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hselectors in
/-- Environment-locality of the committed-operand product arguments (the product and carry programs' two
`u64` inputs, congruence-instantiated once). -/
private theorem productArgsCongr :
    (quotCompBitsU selectors (wordU B) (wordU C)).eval { env := env }
        = (quotCompBitsU selectors (wordU B) (wordU C)).eval { env := env' }
      ∧ (compU selectors (wordU C)).eval { env := env } = (compU selectors (wordU C)).eval { env := env' } := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  constructor <;>
  simp only [quotCompBitsU, quotBitsU, allOnesU, compU, negU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the shared product-limb program. -/
theorem ctqCongr :
    ((ctqProgram selectors B C).toIRLiteral (value := fields 8)).eval env
      = ((ctqProgram selectors B C).toIRLiteral (value := fields 8)).eval env' := by
  have hargs := productArgsCongr selectors env env' B C hB hC hselectors
  rw [Witgen.M.eval_toIRLiteral, Witgen.M.eval_toIRLiteral]
  apply congrArg (toElements (M := fields 8))
  apply Vector.ext
  intro i hi
  rw [ctqProgram_eval_limb, (ctqProgram_eval_limb selectors)]
  simp only [ctqLimbF, circuit_norm, -Witgen.u64Wrap]
  exact congrArg (fun u : UInt64 => (u.toNat : ZMod p))
    ((ctqLimbU_congr selectors) { env := env } { env := env' } _ _ _ _ hargs.1 hargs.2 hselectors i)

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `is_c_0` site. -/
theorem isC0Congr :
    (Witgen.WitgenIR.ofFExprs (isC0FE selectors C)).eval env
      = (Witgen.WitgenIR.ofFExprs (isC0FE selectors C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  have hcells : ∀ (j : ℕ) (_ : j < 4),
      Witgen.FExpr.eval { env := env } (compF selectors C)[j]
        = Witgen.FExpr.eval { env := env' } (compF selectors C)[j] := by
    intro j hj
    interval_cases j <;>
    simp only [compF, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF,
        circuit_norm, -Witgen.u64Wrap, hC0, hC1, hC2, hC3, hselectors]
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs, isC0FE, Vector.getElem_cast,
    Witgen.getElem_eval_toElements,
    IsZeroWordOperation.populateFE_congr env env' (compF selectors C) hcells]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `abs_c` site. -/
theorem absCCongr :
    (Witgen.WitgenIR.ofFExprs (absCFE selectors C)).eval env
      = (Witgen.WitgenIR.ofFExprs (absCFE selectors C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [absCFE, compU, compF, wSumF, signedSumF, wordFOfU64, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `abs_remainder` site. -/
theorem absRemCongr :
    (Witgen.WitgenIR.ofFExprs (absRemFE selectors B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (absRemFE selectors B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [absRemFE, remCompFE, wordFOfU64, remCompBitsU, remBitsU, compU, signedSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `remainder_comp` site. -/
theorem remCompCongr :
    (Witgen.WitgenIR.ofFExprs (remCompFE selectors B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (remCompFE selectors B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [remCompFE, wordFOfU64, remCompBitsU, remBitsU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `max_abs_c_or_1` site. -/
theorem maxAbsCongr :
    (Witgen.WitgenIR.ofFExprs (maxAbsFE selectors C)).eval env
      = (Witgen.WitgenIR.ofFExprs (maxAbsFE selectors C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [maxAbsFE, absCU, absCFE, compU, compF, wSumF, signedSumF, wordFOfU64, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `c_neg_operation` site. -/
theorem wCnegCongr :
    (Witgen.WitgenIR.ofFExprs (wCnegFE selectors ir C)).eval env
      = (Witgen.WitgenIR.ofFExprs (wCnegFE selectors ir C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [wCnegFE, cNegFE, cMsbFE, absCFE, compU, compF, wSumF, signedSumF, wordFOfU64, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF, AddOperation.populateFW,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `misc` site. -/
theorem miscCongr :
    (Witgen.WitgenIR.ofFExprs (miscFE selectors ir B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (miscFE selectors ir B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [miscFE, cNegFE, remNegFE, cMsbFE, remMsbFE, remFE, ltGateFE, compF, wordFOfU64, remBitsU, wSumF, signedSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF, IsZeroWordOperation.populateFE, IsZeroOperation.populateFE,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hselectors in
/-- Cell-level environment-locality of `abs_remainder` (feeds `scanF_congr`). -/
private theorem absRemCellCongr :
    ∀ (j : ℕ) (_ : j < 4),
      Witgen.FExpr.eval { env := env } (absRemFE selectors B C)[j]
        = Witgen.FExpr.eval { env := env' } (absRemFE selectors B C)[j] := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  intro j hj
  interval_cases j <;>
  simp only [absRemFE, remCompFE, wordFOfU64, remCompBitsU, remBitsU, compU, signedSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hC hselectors in
/-- Cell-level environment-locality of `max_abs_c_or_1` (feeds `scanF_congr`). -/
private theorem maxAbsCellCongr :
    ∀ (j : ℕ) (_ : j < 4),
      Witgen.FExpr.eval { env := env } (maxAbsFE selectors C)[j]
        = Witgen.FExpr.eval { env := env' } (maxAbsFE selectors C)[j] := by
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  intro j hj
  interval_cases j <;>
  simp only [maxAbsFE, absCU, absCFE, compU, compF, wSumF, signedSumF, wordFOfU64, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hC0, hC1, hC2, hC3, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hC hir hselectors in
/-- Environment-locality of the remainder-check gate cell. -/
private theorem ltGateCongr :
    Witgen.FExpr.eval { env := env } (ltGateFE selectors ir C)
      = Witgen.FExpr.eval { env := env' } (ltGateFE selectors ir C) := by
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  simp only [ltGateFE, compF, wSumF, signedSumF, wordFOfU64, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF, IsZeroWordOperation.populateFE, IsZeroOperation.populateFE,
      circuit_norm, -Witgen.u64Wrap, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the shared `clProgram` witness site. -/
theorem clCongr :
    ((clProgram selectors ir B C).toIRLiteral (value := fields 2)).eval env
      = ((clProgram selectors ir B C).toIRLiteral (value := fields 2)).eval env' := by
  have hgate := ltGateCongr selectors env env' C ir hC hir hselectors
  have hscan := LtOperationUnsigned.scanF_congr { env := env } { env := env' }
    (absRemFE selectors B C) (maxAbsFE selectors C)
    (absRemCellCongr selectors env env' B C hB hC hselectors)
    (maxAbsCellCongr selectors env env' C hC hselectors)
  rw [Witgen.M.eval_toIRLiteral, Witgen.M.eval_toIRLiteral]
  apply congrArg (toElements (M := fields 2))
  apply Vector.ext
  intro i hi
  rw [clProgram_eval_limb, (clProgram_eval_limb selectors), hgate, hscan.1 ⟨i, hi⟩]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the shared `ltfProgram` witness site. -/
theorem ltfCongr :
    ((ltfProgram selectors ir B C).toIRLiteral (value := fields 4)).eval env
      = ((ltfProgram selectors ir B C).toIRLiteral (value := fields 4)).eval env' := by
  have hgate := ltGateCongr selectors env env' C ir hC hir hselectors
  have hscan := LtOperationUnsigned.scanF_congr { env := env } { env := env' }
    (absRemFE selectors B C) (maxAbsFE selectors C)
    (absRemCellCongr selectors env env' B C hB hC hselectors)
    (maxAbsCellCongr selectors env env' C hC hselectors)
  rw [Witgen.M.eval_toIRLiteral, Witgen.M.eval_toIRLiteral]
  apply congrArg (toElements (M := fields 4))
  apply Vector.ext
  intro i hi
  rw [ltfProgram_eval_limb, (ltfProgram_eval_limb selectors), hgate, hscan.2.1 ⟨i, hi⟩]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the shared `neiProgram` witness site. -/
theorem neiCongr :
    ((neiProgram selectors ir B C).toIRLiteral (value := fields 1)).eval env
      = ((neiProgram selectors ir B C).toIRLiteral (value := fields 1)).eval env' := by
  have hgate := ltGateCongr selectors env env' C ir hC hir hselectors
  have hscan := LtOperationUnsigned.scanF_congr { env := env } { env := env' }
    (absRemFE selectors B C) (maxAbsFE selectors C)
    (absRemCellCongr selectors env env' B C hB hC hselectors)
    (maxAbsCellCongr selectors env env' C hC hselectors)
  rw [Witgen.M.eval_toIRLiteral, Witgen.M.eval_toIRLiteral]
  apply congrArg (toElements (M := fields 1))
  apply Vector.ext
  intro i hi
  rw [neiProgram_eval_limb, (neiProgram_eval_limb selectors), hgate, hscan.2.2.1]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the shared `bitProgram` witness site. -/
theorem bitCongr :
    ((bitProgram selectors ir B C).toIRLiteral (value := fields 1)).eval env
      = ((bitProgram selectors ir B C).toIRLiteral (value := fields 1)).eval env' := by
  have hgate := ltGateCongr selectors env env' C ir hC hir hselectors
  have hscan := LtOperationUnsigned.scanF_congr { env := env } { env := env' }
    (absRemFE selectors B C) (maxAbsFE selectors C)
    (absRemCellCongr selectors env env' B C hB hC hselectors)
    (maxAbsCellCongr selectors env env' C hC hselectors)
  rw [Witgen.M.eval_toIRLiteral, Witgen.M.eval_toIRLiteral]
  apply congrArg (toElements (M := fields 1))
  apply Vector.ext
  intro i hi
  rw [bitProgram_eval_limb, (bitProgram_eval_limb selectors), hgate, hscan.2.2.2]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `remainder` site. -/
theorem remCongr :
    (Witgen.WitgenIR.ofFExprs (remFE selectors B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (remFE selectors B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [remFE, wordFOfU64, remBitsU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- The shared negation word reads only its input operands, gate and selectors. -/
theorem wRnegCongr :
    ((wRnegProgram selectors ir B C).toIRLiteral (value := fields 4)).eval env
      = ((wRnegProgram selectors ir B C).toIRLiteral (value := fields 4)).eval env' := by
  have hgate : (remNegFE selectors B C).eval { env := env } * ir.eval env.toEnvironment =
      (remNegFE selectors B C).eval { env := env' } * ir.eval env'.toEnvironment := by
    have h := Witgen.cell_congr_of_ofFExprs_congr
      (miscCongr selectors env env' B C ir hB hC hir hselectors) 1 (by omega)
    simpa only [miscFE, circuit_norm] using h
  rw [Witgen.M.eval_toIRLiteral, Witgen.M.eval_toIRLiteral]
  apply congrArg (toElements (M := fields 4))
  apply Vector.ext
  intro i hi
  have hadd := AddOperation.populateFW_congr { env := env } { env := env' }
    (remFE selectors B C) (absRemFE selectors B C)
    (Witgen.cell_congr_of_ofFExprs_congr (remCongr selectors env env' B C ir hB hC hir hselectors))
    (absRemCellCongr selectors env env' B C hB hC hselectors) i hi
  rw [wRnegProgram_eval_limb, (wRnegProgram_eval_limb selectors), hgate, hadd]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `quotient` site. -/
theorem quotCongr :
    (Witgen.WitgenIR.ofFExprs (quotFE selectors B C)).eval env
      = (Witgen.WitgenIR.ofFExprs (quotFE selectors B C)).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  interval_cases i <;>
  simp only [quotFE, wordFOfU64, quotBitsU, allOnesU, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `b_msb` cell site. -/
theorem bMsbCongr :
    (Witgen.WitgenIR.ofFExprs (#v[bMsbFE selectors B])).eval env
      = (Witgen.WitgenIR.ofFExprs (#v[bMsbFE selectors B])).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  obtain rfl : i = 0 := by omega
  simp only [bMsbFE, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `c_msb` cell site. -/
theorem cMsbCongr :
    (Witgen.WitgenIR.ofFExprs (#v[cMsbFE selectors C])).eval env
      = (Witgen.WitgenIR.ofFExprs (#v[cMsbFE selectors C])).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  obtain rfl : i = 0 := by omega
  simp only [cMsbFE, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `rem_msb` cell site. -/
theorem remMsbCongr :
    (Witgen.WitgenIR.ofFExprs (#v[remMsbFE selectors B C])).eval env
      = (Witgen.WitgenIR.ofFExprs (#v[remMsbFE selectors B C])).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  obtain rfl : i = 0 := by omega
  simp only [remMsbFE, remFE, wordFOfU64, remBitsU, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the `quot_msb` cell site. -/
theorem quotMsbCongr :
    (Witgen.WitgenIR.ofFExprs (#v[quotMsbFE selectors B C])).eval env
      = (Witgen.WitgenIR.ofFExprs (#v[quotMsbFE selectors B C])).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  apply Vector.ext
  intro i hi
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs]
  obtain rfl : i = 0 := by omega
  simp only [quotMsbFE, quotFE, wordFOfU64, quotBitsU, allOnesU, wSumF, negU, absU, sdivU, sremU, neg32U, sdiv32U, srem32U, low32U, sext32U, wordU, flagF, selectorF, U16MSBOperation.populate_msbF,
      circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3, hC0, hC1, hC2, hC3, hir, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Both shared multiplication programs depend only on the input operands, gate and selectors. -/
theorem mulProgramCongr (upper : Bool) :
    (mulProgram selectors ir B C upper).toIRLiteral.eval env
      = (mulProgram selectors ir B C upper).toIRLiteral.eval env' := by
  rw [Witgen.M.eval_toIRLiteral, Witgen.M.eval_toIRLiteral]
  apply congrArg toElements
  rw [mulProgram_eval, (mulProgram_eval selectors)]
  have hq := Witgen.cell_congr_of_ofFExprs_congr
    (quotCompCongr selectors env env' B C ir hB hC hir hselectors)
  have hc := Witgen.cell_congr_of_ofFExprs_congr (cCongr selectors env env' B C ir hB hC hir hselectors)
  refine Witgen.gateFE_congr _ _ _ _ ?_
    (MulOperation.populateFEW_congr { env := env } { env := env' }
      _ _ _ _ _ hq hc ?_ rfl rfl)
  · cases upper <;>
      simp only [longSumF, flagF, selectorF, circuit_norm, -Witgen.u64Wrap, hir, hselectors]
    · exact decide_eq_decide.mpr Iff.rfl
    · congr 1
      exact decide_eq_decide.mpr Iff.rfl
  · cases upper <;> simp only [flagF, selectorF, circuit_norm, -Witgen.u64Wrap, hselectors]

omit [Fact (2 ^ 24 < p)] in
include hB hir hselectors in
/-- Environment-locality of the flattened `is_overflow_b` struct site. -/
theorem ovbCongr :
    (Witgen.WitgenIR.ofFExprs ((toElements (ovbFE selectors ir B)).cast
        (show size Circuits.Types.IsEqualWordOperation = 11 from rfl))).eval env
      = (Witgen.WitgenIR.ofFExprs ((toElements (ovbFE selectors ir B)).cast
        (show size Circuits.Types.IsEqualWordOperation = 11 from rfl))).eval env' := by
  have hB0 := hB 0 (by omega); have hB1 := hB 1 (by omega)
  have hB2 := hB 2 (by omega); have hB3 := hB 3 (by omega)
  have hstruct : Witgen.eval { env := env } (ovbFE selectors ir B)
      = Witgen.eval { env := env' } (ovbFE selectors ir B) := by
    refine Witgen.gateFE_congr _ _ _ _ ?_ (Witgen.iteFE_congr _ _ _ _ _ ?_
      (IsEqualWordOperation.populateFE_congr env env' _ _
        (by intro i hi; interval_cases i <;>
          simp only [circuit_norm, -Witgen.u64Wrap, hB0, hB1])
        (by intro i hi; interval_cases i <;>
          simp only [circuit_norm, -Witgen.u64Wrap]))
      (IsEqualWordOperation.populateFE_congr env env' _ _
        (by intro i hi; interval_cases i <;>
          simp only [circuit_norm, -Witgen.u64Wrap, hB0, hB1, hB2, hB3])
        (by intro i hi; interval_cases i <;>
          simp only [circuit_norm, -Witgen.u64Wrap]))) <;>
    (simp only [wSumF, flagF, selectorF, circuit_norm, -Witgen.u64Wrap, hir, hselectors]; all_goals exact decide_eq_decide.mpr Iff.rfl)
  apply Vector.ext
  intro i hi
  have hsz : i < size Circuits.Types.IsEqualWordOperation := by
    have h : size Circuits.Types.IsEqualWordOperation = 11 := rfl
    omega
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs, Vector.getElem_cast]
  exact (Witgen.getElem_eval_toElements _ _ i hsz).trans
    ((congrArg (fun s => (toElements s)[i]'hsz) hstruct).trans
      (Witgen.getElem_eval_toElements _ _ i hsz).symm)

omit [Fact (2 ^ 24 < p)] in
include hC hir hselectors in
/-- Environment-locality of the flattened `is_overflow_c` struct site. -/
theorem ovcCongr :
    (Witgen.WitgenIR.ofFExprs ((toElements (ovcFE selectors ir C)).cast
        (show size Circuits.Types.IsEqualWordOperation = 11 from rfl))).eval env
      = (Witgen.WitgenIR.ofFExprs ((toElements (ovcFE selectors ir C)).cast
        (show size Circuits.Types.IsEqualWordOperation = 11 from rfl))).eval env' := by
  have hC0 := hC 0 (by omega); have hC1 := hC 1 (by omega)
  have hC2 := hC 2 (by omega); have hC3 := hC 3 (by omega)
  have hstruct : Witgen.eval { env := env } (ovcFE selectors ir C)
      = Witgen.eval { env := env' } (ovcFE selectors ir C) := by
    refine Witgen.gateFE_congr _ _ _ _ ?_ (Witgen.iteFE_congr _ _ _ _ _ ?_
      (IsEqualWordOperation.populateFE_congr env env' _ _
        (by intro i hi; interval_cases i <;>
          simp only [circuit_norm, -Witgen.u64Wrap, hC0, hC1])
        (by intro i hi; interval_cases i <;>
          simp only [circuit_norm, -Witgen.u64Wrap]))
      (IsEqualWordOperation.populateFE_congr env env' _ _
        (by intro i hi; interval_cases i <;>
          simp only [circuit_norm, -Witgen.u64Wrap, hC0, hC1, hC2, hC3])
        (by intro i hi; interval_cases i <;>
          simp only [circuit_norm, -Witgen.u64Wrap]))) <;>
    (simp only [wSumF, flagF, selectorF, circuit_norm, -Witgen.u64Wrap, hir, hselectors]; all_goals exact decide_eq_decide.mpr Iff.rfl)
  apply Vector.ext
  intro i hi
  have hsz : i < size Circuits.Types.IsEqualWordOperation := by
    have h : size Circuits.Types.IsEqualWordOperation = 11 := rfl
    omega
  simp only [Witgen.WitgenIR.getElem_eval_ofFExprs, Vector.getElem_cast]
  exact (Witgen.getElem_eval_toElements _ _ i hsz).trans
    ((congrArg (fun s => (toElements s)[i]'hsz) hstruct).trans
      (Witgen.getElem_eval_toElements _ _ i hsz).symm)

omit [Fact (2 ^ 24 < p)] in
include hB hC hir hselectors in
/-- Environment-locality of the shared carry program. -/
theorem carryCongr :
    ((carryProgram selectors B C).toIRLiteral (value := fields 8)).eval env
      = ((carryProgram selectors B C).toIRLiteral (value := fields 8)).eval env' := by
  have hargs := productArgsCongr selectors env env' B C hB hC hselectors
  have hr := Witgen.cell_congr_of_ofFExprs_congr
    (remCompCongr selectors env env' B C ir hB hC hir hselectors)
  have hmsb : (remMsbFE selectors B C).eval { env := env } = (remMsbFE selectors B C).eval { env := env' } :=
    Witgen.cell_congr_of_ofFExprs_congr
      (remMsbCongr selectors env env' B C ir hB hC hir hselectors) 0 (by decide)
  have hs : (remNegFE selectors B C).eval { env := env } = (remNegFE selectors B C).eval { env := env' } := by
    simp only [remNegFE, signedSumF, flagF, selectorF, circuit_norm, -Witgen.u64Wrap, hmsb, hselectors]
  have hch := (carryChainU_congr selectors) { env := env } { env := env' } _ _ _ _ _ _ _ _
    hargs.1 hargs.2 hr hs hselectors
  rw [Witgen.M.eval_toIRLiteral, Witgen.M.eval_toIRLiteral]
  apply congrArg (toElements (M := fields 8))
  apply Vector.ext
  intro i hi
  rw [carryProgram_eval_limb, (carryProgram_eval_limb selectors), hch]

end SiteCongr

end SP1Clean.DivRemChip
