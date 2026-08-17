import SP1Clean.Math.Word
import SP1Clean.Native.Operations.IsZeroOperation.Populate
import SP1Clean.Extracted.IsZeroWordOperation

/-! # `IsZeroWordOperation` — `populate` (the witness generator)

SP1's `IsZeroWordOperation::populate` ported natively. `isZeroWordWitness` (vector form) is retained for
the conformance check in `WitnessTests/IsZeroWordOperationWitness.lean`. `spec_populate` lives in
`Formal` to avoid an import cycle. -/

namespace SP1Clean.IsZeroWordOperation

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The witnessed column struct: per-limb `IsZeroOperation.populate`, the two half-products, and
`result = first_half * second_half`. -/
def populate (a : Word (ZMod p)) : Extracted.IsZeroWordOperation (ZMod p) :=
  let l0 := IsZeroOperation.populate a[0]
  let l1 := IsZeroOperation.populate a[1]
  let l2 := IsZeroOperation.populate a[2]
  let l3 := IsZeroOperation.populate a[3]
  let fh := l0.result * l1.result
  let sh := l2.result * l3.result
  ⟨l0, l1, l2, l3, fh, sh, fh * sh⟩

/-- The all-zero column struct — the witness on rows where the gadget is inactive and SP1 leaves
the struct unpopulated (gated `IsZeroWord`/`IsEqualWord` composition on padding rows). `spec_zero`
(in `Formal`) discharges the composed assertion's obligation at this value. -/
def zeroCols : Extracted.IsZeroWordOperation (ZMod p) :=
  ⟨⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, 0, 0, 0⟩

/-- Vector form of the witness, used only for the conformance check in
`WitnessTests/IsZeroWordOperationWitness.lean`. Returns
`(limb inverses, limb results, first_half, second_half, result)`. -/
def isZeroWordWitness (a : Word (ZMod p)) :
    Vector (ZMod p) 4 × Vector (ZMod p) 4 × ZMod p × ZMod p × ZMod p :=
  let z0 := IsZeroOperation.isZeroWitness a[0]
  let z1 := IsZeroOperation.isZeroWitness a[1]
  let z2 := IsZeroOperation.isZeroWitness a[2]
  let z3 := IsZeroOperation.isZeroWitness a[3]
  let inv := #v[z0[0], z1[0], z2[0], z3[0]]
  let res := #v[z0[1], z1[1], z2[1], z3[1]]
  let fh := res[0] * res[1]
  let sh := res[2] * res[3]
  (inv, res, fh, sh, fh * sh)

section FE

/-- The witness-IR twin of `populate`: per-limb `IsZeroOperation.populateFE`, the two half
products, and the result product — over computed word cells. -/
def populateFE (a : Vector (Witgen.FExpr (ZMod p)) 4) :
    Extracted.IsZeroWordOperation (Witgen.FExpr (ZMod p)) :=
  let l0 := IsZeroOperation.populateFE a[0]
  let l1 := IsZeroOperation.populateFE a[1]
  let l2 := IsZeroOperation.populateFE a[2]
  let l3 := IsZeroOperation.populateFE a[3]
  let fh := l0.result * l1.result
  let sh := l2.result * l3.result
  ⟨l0, l1, l2, l3, fh, sh, fh * sh⟩

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the twin is `populate` on the evaluated word. -/
theorem populateFE_eval (env : ProverEnvironment (ZMod p))
    (a : Vector (Witgen.FExpr (ZMod p)) 4) (va : Word (ZMod p))
    (hA : ∀ (i : ℕ) (_ : i < 4), Witgen.FExpr.eval { env := env } a[i] = va[i]) :
    Witgen.eval { env := env } (populateFE a) = populate va := by
  have h0 := hA 0 (by omega); have h1 := hA 1 (by omega)
  have h2 := hA 2 (by omega); have h3 := hA 3 (by omega)
  by_cases hv0 : va[0] = 0 <;> by_cases hv1 : va[1] = 0 <;>
    by_cases hv2 : va[2] = 0 <;> by_cases hv3 : va[3] = 0 <;>
    (simp [populateFE, populate, IsZeroOperation.populateFE, IsZeroOperation.populate,
       circuit_norm, explicit_provable_type, h0, h1, h2, h3, hv0, hv1, hv2, hv3,
       Witgen.StructEval.eval.go, ProvableStruct.toComponents, ProvableStruct.fromComponents]
     rfl)

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the twin. -/
theorem populateFE_congr (env env' : ProverEnvironment (ZMod p))
    (a : Vector (Witgen.FExpr (ZMod p)) 4)
    (hA : ∀ (i : ℕ) (_ : i < 4),
      Witgen.FExpr.eval { env := env } a[i] = Witgen.FExpr.eval { env := env' } a[i]) :
    Witgen.eval { env := env } (populateFE a) = Witgen.eval { env := env' } (populateFE a) := by
  simp [populateFE, IsZeroOperation.populateFE, circuit_norm, explicit_provable_type,
    hA 0 (by omega), hA 1 (by omega), hA 2 (by omega), hA 3 (by omega),
    Witgen.StructEval.eval.go, ProvableStruct.toComponents, ProvableStruct.fromComponents]

end FE

section Navigators

/-! Per-cell `toElements` projections over an *opaque* struct (the `MulOperation` navigator
technique): destructure, then literal-index `getElem` append chains — never `whnf` through the
`combinedSize'` tower on a compound literal. Cell order: `is_zero_limb_k ↦ {2k, 2k+1}`
(inverse, result), `is_zero_first_half ↦ 8`, `is_zero_second_half ↦ 9`, `result ↦ 10`.
Their one consumer is the flattened zero-struct fact `zc_cell` below (the gated-composition
else-branch); per-cell *evaluation* facts need no navigators — `Witgen.getElem_eval_toElements`
collapses them generically. -/

set_option linter.unusedSectionVars false in
/-- Cell `0` is `is_zero_limb_0.inverse`. -/
private lemma toElements_cell_0 {F : Type} (s : Extracted.IsZeroWordOperation F) :
    (toElements s)[0]'(by have h : size Extracted.IsZeroWordOperation = 11 := rfl; omega)
      = s.is_zero_limb_0.inverse := by
  obtain ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, fh, sh, r⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  exact Vector.getElem_append_left (by decide)

set_option linter.unusedSectionVars false in
/-- Cell `1` is `is_zero_limb_0.result`. -/
private lemma toElements_cell_1 {F : Type} (s : Extracted.IsZeroWordOperation F) :
    (toElements s)[1]'(by have h : size Extracted.IsZeroWordOperation = 11 := rfl; omega)
      = s.is_zero_limb_0.result := by
  obtain ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, fh, sh, r⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  exact Vector.getElem_append_left (by decide)

set_option linter.unusedSectionVars false in
/-- Cell `2` is `is_zero_limb_1.inverse`. -/
private lemma toElements_cell_2 {F : Type} (s : Extracted.IsZeroWordOperation F) :
    (toElements s)[2]'(by have h : size Extracted.IsZeroWordOperation = 11 := rfl; omega)
      = s.is_zero_limb_1.inverse := by
  obtain ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, fh, sh, r⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans (Vector.getElem_append_left ?_) <;> decide

set_option linter.unusedSectionVars false in
/-- Cell `3` is `is_zero_limb_1.result`. -/
private lemma toElements_cell_3 {F : Type} (s : Extracted.IsZeroWordOperation F) :
    (toElements s)[3]'(by have h : size Extracted.IsZeroWordOperation = 11 := rfl; omega)
      = s.is_zero_limb_1.result := by
  obtain ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, fh, sh, r⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans (Vector.getElem_append_left ?_) <;> decide

set_option linter.unusedSectionVars false in
/-- Cell `4` is `is_zero_limb_2.inverse`. -/
private lemma toElements_cell_4 {F : Type} (s : Extracted.IsZeroWordOperation F) :
    (toElements s)[4]'(by have h : size Extracted.IsZeroWordOperation = 11 := rfl; omega)
      = s.is_zero_limb_2.inverse := by
  obtain ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, fh, sh, r⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans (Vector.getElem_append_left ?_)) <;> decide

set_option linter.unusedSectionVars false in
/-- Cell `5` is `is_zero_limb_2.result`. -/
private lemma toElements_cell_5 {F : Type} (s : Extracted.IsZeroWordOperation F) :
    (toElements s)[5]'(by have h : size Extracted.IsZeroWordOperation = 11 := rfl; omega)
      = s.is_zero_limb_2.result := by
  obtain ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, fh, sh, r⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans (Vector.getElem_append_left ?_)) <;> decide

set_option linter.unusedSectionVars false in
/-- Cell `6` is `is_zero_limb_3.inverse`. -/
private lemma toElements_cell_6 {F : Type} (s : Extracted.IsZeroWordOperation F) :
    (toElements s)[6]'(by have h : size Extracted.IsZeroWordOperation = 11 := rfl; omega)
      = s.is_zero_limb_3.inverse := by
  obtain ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, fh, sh, r⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_right ?_ ?_).trans (Vector.getElem_append_left ?_))) <;> decide

set_option linter.unusedSectionVars false in
/-- Cell `7` is `is_zero_limb_3.result`. -/
private lemma toElements_cell_7 {F : Type} (s : Extracted.IsZeroWordOperation F) :
    (toElements s)[7]'(by have h : size Extracted.IsZeroWordOperation = 11 := rfl; omega)
      = s.is_zero_limb_3.result := by
  obtain ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, fh, sh, r⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_right ?_ ?_).trans (Vector.getElem_append_left ?_))) <;> decide

set_option linter.unusedSectionVars false in
/-- Cell `8` is `is_zero_first_half`. -/
private lemma toElements_cell_8 {F : Type} (s : Extracted.IsZeroWordOperation F) :
    (toElements s)[8]'(by have h : size Extracted.IsZeroWordOperation = 11 := rfl; omega)
      = s.is_zero_first_half := by
  obtain ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, fh, sh, r⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_right ?_ ?_).trans
        ((Vector.getElem_append_right ?_ ?_).trans (Vector.getElem_append_left ?_)))) <;> decide

set_option linter.unusedSectionVars false in
/-- Cell `9` is `is_zero_second_half`. -/
private lemma toElements_cell_9 {F : Type} (s : Extracted.IsZeroWordOperation F) :
    (toElements s)[9]'(by have h : size Extracted.IsZeroWordOperation = 11 := rfl; omega)
      = s.is_zero_second_half := by
  obtain ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, fh, sh, r⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_right ?_ ?_).trans
        ((Vector.getElem_append_right ?_ ?_).trans
          ((Vector.getElem_append_right ?_ ?_).trans (Vector.getElem_append_left ?_))))) <;> decide

set_option linter.unusedSectionVars false in
/-- Cell `10` is `result`. -/
private lemma toElements_cell_10 {F : Type} (s : Extracted.IsZeroWordOperation F) :
    (toElements s)[10]'(by have h : size Extracted.IsZeroWordOperation = 11 := rfl; omega)
      = s.result := by
  obtain ⟨⟨i0, r0⟩, ⟨i1, r1⟩, ⟨i2, r2⟩, ⟨i3, r3⟩, fh, sh, r⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_right ?_ ?_).trans
        ((Vector.getElem_append_right ?_ ?_).trans
          ((Vector.getElem_append_right ?_ ?_).trans
            ((Vector.getElem_append_right ?_ ?_).trans (Vector.getElem_append_left ?_)))))) <;> decide

set_option linter.unusedSectionVars false in
/-- The result field is flattened cell `10` (the public face of the navigator family, for
composing chips that read the result cell of a struct payload). -/
lemma result_eq_toElements {F : Type} (s : Extracted.IsZeroWordOperation F) :
    s.result = (toElements s)[10]'(by
      have h : size Extracted.IsZeroWordOperation = 11 := rfl
      omega) :=
  (toElements_cell_10 s).symm

omit [Fact (2 ^ 17 < p)] in
/-- Every flattened cell of the zero struct is zero (the gated-composition else-branch fact). -/
lemma zc_cell (i : ℕ) (hi : i < size Extracted.IsZeroWordOperation) :
    (toElements (zeroCols : Extracted.IsZeroWordOperation (ZMod p)))[i] = 0 := by
  have hi' : i < 11 := hi
  interval_cases i
  · rw [toElements_cell_0]; rfl
  · rw [toElements_cell_1]; rfl
  · rw [toElements_cell_2]; rfl
  · rw [toElements_cell_3]; rfl
  · rw [toElements_cell_4]; rfl
  · rw [toElements_cell_5]; rfl
  · rw [toElements_cell_6]; rfl
  · rw [toElements_cell_7]; rfl
  · rw [toElements_cell_8]; rfl
  · rw [toElements_cell_9]; rfl
  · rw [toElements_cell_10]; rfl

omit [Fact (2 ^ 17 < p)] in
/-- The flattened zero struct, as a `fromElements` of zeros (the shape `Witgen.eval_gateFE`'s
else branch produces). -/
lemma fromElements_zero :
    (fromElements (Vector.replicate (size Extracted.IsZeroWordOperation) 0)
      : Extracted.IsZeroWordOperation (ZMod p)) = zeroCols := by
  rw [ProvableType.ext_iff]
  intro i hi
  rw [ProvableType.toElements_fromElements, Vector.getElem_replicate]
  exact (zc_cell i hi).symm

end Navigators


end SP1Clean.IsZeroWordOperation
