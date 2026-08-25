import SP1Clean.Math.Word
import SP1Clean.Extracted.LtOperationUnsigned
import SP1Clean.Native.Operations.U16CompareOperation.Populate

/-! # `LtOperationUnsigned` — native witness generation

SP1's `LtOperationUnsigned::populate_unsigned` ported to Lean: the one-hot `u16_flags`, the
`comparison_limbs`, and the non-equality inverse `not_eq_inv` at the most-significant differing limb
(all-equal ⇒ zero), plus the composed `U16CompareOperation` bit on the selected limb pair. A composing
circuit (`LtOperationSigned`) witnesses the whole block with `populate`; `spec_populate` (that the
witness satisfies the gadget `Spec`) lives in `Formal.lean`. -/

namespace SP1Clean.LtOperationUnsigned

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Native witness for the `comparison_limbs` column, **field-generic** over `ZMod p`: the
`(bᵢ, ccᵢ)` pair at the most-significant differing limb (all-equal ⇒ `0`). This is SP1's
`LtOperationUnsigned::populate_unsigned` limb-scan ported to Lean. -/
def comparisonLimbsWitness (b cc : Word (ZMod p)) : Vector (ZMod p) 2 :=
  if b[3] ≠ cc[3] then #v[b[3], cc[3]] else if b[2] ≠ cc[2] then #v[b[2], cc[2]]
  else if b[1] ≠ cc[1] then #v[b[1], cc[1]] else if b[0] ≠ cc[0] then #v[b[0], cc[0]]
  else (#v[0, 0] : Vector (ZMod p) 2)

/-- Native witness for the `u16_flags` column: the one-hot flag at the most-significant differing
limb (all-equal ⇒ all zero). -/
def flagsWitness (b cc : Word (ZMod p)) : Vector (ZMod p) 4 :=
  if b[3] ≠ cc[3] then #v[0, 0, 0, 1] else if b[2] ≠ cc[2] then #v[0, 0, 1, 0]
  else if b[1] ≠ cc[1] then #v[0, 1, 0, 0] else if b[0] ≠ cc[0] then #v[1, 0, 0, 0]
  else (#v[0, 0, 0, 0] : Vector (ZMod p) 4)

/-- Native witness for the `not_eq_inv` column: the **field inverse** `(bᵢ - ccᵢ)⁻¹` at the
most-significant differing limb (all-equal ⇒ `0`). This is the column with no ℕ analogue — SP1's
`(b_limb - c_limb).inverse()` — so its conformance can only be checked at SP1's concrete field. -/
def notEqInvWitness (b cc : Word (ZMod p)) : Vector (ZMod p) 1 :=
  if b[3] ≠ cc[3] then #v[(b[3] - cc[3])⁻¹] else if b[2] ≠ cc[2] then #v[(b[2] - cc[2])⁻¹]
  else if b[1] ≠ cc[1] then #v[(b[1] - cc[1])⁻¹] else if b[0] ≠ cc[0] then #v[(b[0] - cc[0])⁻¹]
  else (#v[0] : Vector (ZMod p) 1)

/-- The all-zero column struct — the witness on rows where the gadget is inactive and SP1 leaves
the struct unpopulated (`DivRemChip`'s `remainder_lt_operation` when the remainder-check
multiplicity is `0`). `spec_zero` (in `Formal`) discharges the composed assertion's obligation at
this value. -/
def zeroCols : Extracted.LtOperationUnsigned (ZMod p) :=
  ⟨⟨0⟩, #v[0, 0, 0, 0], 0, #v[0, 0]⟩

/-- Fully witnessed `LtOperationUnsigned` column struct (SP1's `populate_unsigned`): one-hot flags,
comparison limbs, non-equality inverse, and the composed `U16CompareOperation` bit. -/
def populate (b cc : Word (ZMod p)) : Extracted.LtOperationUnsigned (ZMod p) :=
  let cl := comparisonLimbsWitness b cc
  let f := flagsWitness b cc
  let ni := notEqInvWitness b cc
  ⟨⟨U16CompareOperation.populate_bit cl[0] cl[1]⟩, f, ni[0], cl⟩

/-! ### Witness IR

The `FExpr` twins of the limb-scan witnesses, over **abstract** limb expressions (the composing
`LtOperationSigned.populateFE` instantiates them at the sign-adjusted limbs; `DivRemChip` will
instantiate them at its remainder/divisor words). Everything here is field-sort — the scans branch
on limb (dis)equality via `=?` (`BExpr.feq`), the inverse leaf is `FExpr.inv`, the compare bit is
`<?` (`BExpr.flt`, exact field-`val` comparison) — so the eval lemmas are pure `if`-congruences
needing no bounds. Deliberately **not** `@[circuit_norm]` (the opacity doctrine). -/

/-- The `FExpr` twin of `comparisonLimbsWitness`: cell `k` scans most-significant-first for the
first differing limb pair (`if a = b then <continue> else <this pair>` — the value scan's `≠` with
the branches swapped). -/
def comparisonLimbsF (b cc : Vector (Witgen.FExpr (ZMod p)) 4) (k : Fin 2) :
    Witgen.FExpr (ZMod p) :=
  .ite (b[3] =? cc[3])
    (.ite (b[2] =? cc[2])
      (.ite (b[1] =? cc[1])
        (.ite (b[0] =? cc[0]) 0 (if k = 0 then b[0] else cc[0]))
        (if k = 0 then b[1] else cc[1]))
      (if k = 0 then b[2] else cc[2]))
    (if k = 0 then b[3] else cc[3])

/-- The `FExpr` twin of `flagsWitness`: the one-hot flag at the most-significant differing limb. -/
def flagsF (b cc : Vector (Witgen.FExpr (ZMod p)) 4) (k : Fin 4) : Witgen.FExpr (ZMod p) :=
  .ite (b[3] =? cc[3])
    (.ite (b[2] =? cc[2])
      (.ite (b[1] =? cc[1])
        (.ite (b[0] =? cc[0]) 0 (if k = 0 then 1 else 0))
        (if k = 1 then 1 else 0))
      (if k = 2 then 1 else 0))
    (if k = 3 then 1 else 0)

/-- The `FExpr` twin of `notEqInvWitness`: the field inverse of the first differing limb pair. -/
def notEqInvF (b cc : Vector (Witgen.FExpr (ZMod p)) 4) : Witgen.FExpr (ZMod p) :=
  .ite (b[3] =? cc[3])
    (.ite (b[2] =? cc[2])
      (.ite (b[1] =? cc[1])
        (.ite (b[0] =? cc[0]) 0 (b[0] - cc[0])⁻¹)
        (b[1] - cc[1])⁻¹)
      (b[2] - cc[2])⁻¹)
    (b[3] - cc[3])⁻¹

/-- The `FExpr` twin of the composed `U16CompareOperation.populate_bit` at the scanned limb pair. -/
def compareBitF (b cc : Vector (Witgen.FExpr (ZMod p)) 4) : Witgen.FExpr (ZMod p) :=
  (comparisonLimbsF b cc 0 <? comparisonLimbsF b cc 1).toField

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the scan twins is exactly the value-level scans on the evaluated limbs (a pure
`if`-congruence — the four conditions match under `heval`, and every leaf is a mirrored field
expression). Stated for all four cell families at once, over abstract limb evaluations. -/
theorem scanF_eval (ctx : Witgen.Ctx (ZMod p)) (b cc : Vector (Witgen.FExpr (ZMod p)) 4)
    (vb vcc : Word (ZMod p))
    (hb : ∀ (i : ℕ) (_ : i < 4), (b[i]).eval ctx = vb[i])
    (hcc : ∀ (i : ℕ) (_ : i < 4), (cc[i]).eval ctx = vcc[i]) :
    (∀ k : Fin 2, (comparisonLimbsF b cc k).eval ctx = (comparisonLimbsWitness vb vcc)[(k : ℕ)]) ∧
    (∀ k : Fin 4, (flagsF b cc k).eval ctx = (flagsWitness vb vcc)[(k : ℕ)]) ∧
    (notEqInvF b cc).eval ctx = (notEqInvWitness vb vcc)[0] ∧
    (compareBitF b cc).eval ctx
      = U16CompareOperation.populate_bit (comparisonLimbsWitness vb vcc)[0]
          (comparisonLimbsWitness vb vcc)[1] := by
  have hb0 := hb 0 (by omega); have hb1 := hb 1 (by omega)
  have hb2 := hb 2 (by omega); have hb3 := hb 3 (by omega)
  have hc0 := hcc 0 (by omega); have hc1 := hcc 1 (by omega)
  have hc2 := hcc 2 (by omega); have hc3 := hcc 3 (by omega)
  have hscan : ∀ k : Fin 2,
      (comparisonLimbsF b cc k).eval ctx = (comparisonLimbsWitness vb vcc)[(k : ℕ)] := by
    intro k
    fin_cases k <;>
    · simp only [comparisonLimbsF, comparisonLimbsWitness, circuit_norm,
        hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
      split_ifs <;> simp_all [circuit_norm]
  refine ⟨hscan, ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;>
    · simp only [flagsF, flagsWitness, circuit_norm,
        hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
      split_ifs <;> simp_all [circuit_norm]
  · simp only [notEqInvF, notEqInvWitness, circuit_norm,
      hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
    split_ifs <;> simp_all [circuit_norm]
  · simp only [compareBitF, U16CompareOperation.populate_bit, circuit_norm,
      hscan 0, hscan 1]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the scan twins (the `ComputableWitnesses` counterpart of
`scanF_eval` — both sides are the same `ite` tree, so rewriting the limb evaluations closes
every family without a case split). -/
theorem scanF_congr (ctx ctx' : Witgen.Ctx (ZMod p)) (b cc : Vector (Witgen.FExpr (ZMod p)) 4)
    (hb : ∀ (i : ℕ) (_ : i < 4), (b[i]).eval ctx = (b[i]).eval ctx')
    (hcc : ∀ (i : ℕ) (_ : i < 4), (cc[i]).eval ctx = (cc[i]).eval ctx') :
    (∀ k : Fin 2,
      (comparisonLimbsF b cc k).eval ctx = (comparisonLimbsF b cc k).eval ctx') ∧
    (∀ k : Fin 4, (flagsF b cc k).eval ctx = (flagsF b cc k).eval ctx') ∧
    (notEqInvF b cc).eval ctx = (notEqInvF b cc).eval ctx' ∧
    (compareBitF b cc).eval ctx = (compareBitF b cc).eval ctx' := by
  have hb0 := hb 0 (by omega); have hb1 := hb 1 (by omega)
  have hb2 := hb 2 (by omega); have hb3 := hb 3 (by omega)
  have hc0 := hcc 0 (by omega); have hc1 := hcc 1 (by omega)
  have hc2 := hcc 2 (by omega); have hc3 := hcc 3 (by omega)
  have hscan : ∀ k : Fin 2,
      (comparisonLimbsF b cc k).eval ctx = (comparisonLimbsF b cc k).eval ctx' := by
    intro k
    fin_cases k <;>
    · simp only [comparisonLimbsF, circuit_norm, -Witgen.u64Wrap,
        hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
      all_goals split_ifs <;> simp_all [circuit_norm, -Witgen.u64Wrap]
  refine ⟨hscan, ?_, ?_, ?_⟩
  · intro k
    fin_cases k <;>
    · simp only [flagsF, circuit_norm, -Witgen.u64Wrap,
        hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
      all_goals split_ifs <;> simp_all [circuit_norm, -Witgen.u64Wrap]
  · simp only [notEqInvF, circuit_norm, -Witgen.u64Wrap,
      hb0, hb1, hb2, hb3, hc0, hc1, hc2, hc3]
  · simp only [compareBitF, circuit_norm, -Witgen.u64Wrap, hscan 0, hscan 1]

end SP1Clean.LtOperationUnsigned
