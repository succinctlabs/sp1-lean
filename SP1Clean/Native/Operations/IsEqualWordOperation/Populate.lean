import SP1Clean.Math.Word
import SP1Clean.Native.Operations.IsZeroWordOperation.Populate
import SP1Clean.Extracted.IsEqualWordOperation

/-! # `IsEqualWordOperation` — `populate` (the witness generator)

SP1's `IsEqualWordOperation::populate` ported natively: runs `IsZeroWordOperation.populate` on the
limb-wise difference `a - b` and packages the `IsEqualWordOperation` column struct (a single
`is_diff_zero` field). The composing chip witnesses the columns with this. `spec_populate` lives in
`Formal` (it references `Spec`, which also lives there to avoid an import cycle). -/

namespace SP1Clean.IsEqualWordOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The witnessed column struct: `IsZeroWordOperation.populate` on the limb-wise difference `a - b`. -/
def populate (a b : Word (ZMod p)) : Extracted.IsEqualWordOperation (ZMod p) :=
  ⟨IsZeroWordOperation.populate #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]⟩

section FE

/-- The witness-IR twin of `populate`: `IsZeroWordOperation.populateFE` on the limb-wise
difference (the IR's derived `sub` sugar). -/
def populateFE (a b : Vector (Witgen.FExpr (ZMod p)) 4) :
    Extracted.IsEqualWordOperation (Witgen.FExpr (ZMod p)) :=
  ⟨IsZeroWordOperation.populateFE #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]⟩

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the twin is `populate` on the evaluated words. -/
theorem populateFE_eval (env : ProverEnvironment (ZMod p))
    (a b : Vector (Witgen.FExpr (ZMod p)) 4) (va vb : Word (ZMod p))
    (hA : ∀ (i : ℕ) (_ : i < 4), Witgen.FExpr.eval { env := env } a[i] = va[i])
    (hB : ∀ (i : ℕ) (_ : i < 4), Witgen.FExpr.eval { env := env } b[i] = vb[i]) :
    Witgen.eval { env := env } (populateFE a b) = populate va vb := by
  have hdiff : ∀ (i : ℕ) (_ : i < 4), Witgen.FExpr.eval { env := env }
      (#v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]] :
        Vector (Witgen.FExpr (ZMod p)) 4)[i]
      = (#v[va[0] - vb[0], va[1] - vb[1], va[2] - vb[2], va[3] - vb[3]] : Word (ZMod p))[i] := by
    intro i hi
    interval_cases i <;>
      (simp only [circuit_norm, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ,
        hA 0 (by omega), hA 1 (by omega), hA 2 (by omega), hA 3 (by omega),
        hB 0 (by omega), hB 1 (by omega), hB 2 (by omega), hB 3 (by omega)]
       try ring)
  have h := IsZeroWordOperation.populateFE_eval env
    (#v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]])
    (#v[va[0] - vb[0], va[1] - vb[1], va[2] - vb[2], va[3] - vb[3]]) hdiff
  rw [Witgen.StructEval.eval_eq_eval]
  show (⟨Witgen.eval { env := env }
      (IsZeroWordOperation.populateFE #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]])⟩ :
    Extracted.IsEqualWordOperation (ZMod p)) = populate va vb
  rw [h]
  rfl

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the twin. -/
theorem populateFE_congr (env env' : ProverEnvironment (ZMod p))
    (a b : Vector (Witgen.FExpr (ZMod p)) 4)
    (hA : ∀ (i : ℕ) (_ : i < 4),
      Witgen.FExpr.eval { env := env } a[i] = Witgen.FExpr.eval { env := env' } a[i])
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Witgen.FExpr.eval { env := env } b[i] = Witgen.FExpr.eval { env := env' } b[i]) :
    Witgen.eval { env := env } (populateFE a b) = Witgen.eval { env := env' } (populateFE a b) := by
  have hdiff : ∀ (i : ℕ) (_ : i < 4), Witgen.FExpr.eval { env := env }
      (#v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]] :
        Vector (Witgen.FExpr (ZMod p)) 4)[i]
      = Witgen.FExpr.eval { env := env' }
        (#v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]] :
          Vector (Witgen.FExpr (ZMod p)) 4)[i] := by
    intro i hi
    interval_cases i <;>
      simp only [circuit_norm, -Witgen.u64Wrap, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ,
        hA 0 (by omega), hA 1 (by omega), hA 2 (by omega), hA 3 (by omega),
        hB 0 (by omega), hB 1 (by omega), hB 2 (by omega), hB 3 (by omega)]
  have h := IsZeroWordOperation.populateFE_congr env env'
    (#v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]]) hdiff
  rw [Witgen.StructEval.eval_eq_eval, Witgen.StructEval.eval_eq_eval]
  show (⟨Witgen.eval { env := env }
      (IsZeroWordOperation.populateFE #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]])⟩ :
    Extracted.IsEqualWordOperation (ZMod p))
    = ⟨Witgen.eval { env := env' }
        (IsZeroWordOperation.populateFE #v[a[0] - b[0], a[1] - b[1], a[2] - b[2], a[3] - b[3]])⟩
  rw [h]

end FE

section Flatten

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The single-field wrapper flattens to its field's flattening (kills the nested `toElements`
tower: one rewrite lands in `IsZeroWordOperation`, whose navigators finish). -/
lemma toElements_mk (s : Extracted.IsZeroWordOperation (ZMod p)) :
    toElements (⟨s⟩ : Extracted.IsEqualWordOperation (ZMod p))
      = (toElements s).cast (by rfl) := by
  ext i hi
  simp only [circuit_norm, explicit_provable_type]
  exact (Vector.getElem_append_left hi).trans (Vector.getElem_cast _)

omit [Fact (2 ^ 17 < p)] in
/-- Every flattened cell of the zero struct is zero. -/
lemma zc_cell (i : ℕ) (hi : i < size Extracted.IsEqualWordOperation) :
    (toElements (⟨IsZeroWordOperation.zeroCols⟩ :
        Extracted.IsEqualWordOperation (ZMod p)))[i] = 0 := by
  rw [toElements_mk, Vector.getElem_cast, IsZeroWordOperation.zc_cell]

omit [Fact (2 ^ 17 < p)] in
/-- The flattened zero struct, as a `fromElements` of zeros (the shape `Witgen.eval_gateFE`'s
else branch produces). -/
lemma fromElements_zero :
    (fromElements (Vector.replicate (size Extracted.IsEqualWordOperation) 0)
      : Extracted.IsEqualWordOperation (ZMod p)) = ⟨IsZeroWordOperation.zeroCols⟩ := by
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.toElements_fromElements, Vector.getElem_replicate]
  exact (zc_cell i hi).symm

end Flatten


end SP1Clean.IsEqualWordOperation
