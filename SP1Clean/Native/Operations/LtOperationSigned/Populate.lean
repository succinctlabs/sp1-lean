import SP1Clean.Native.Operations.LtOperationUnsigned.Populate
import SP1Clean.Native.Operations.U16MSBOperation.Populate
import SP1Clean.Extracted.LtOperationSigned

/-! # `LtOperationSigned` — native witness generation

SP1's `LtOperationSigned::populate` ported to Lean: the two `is_signed`-gated sign bits (`b_msb`,
`c_msb`, each `is_signed · populate_msb`) and the `LtOperationUnsigned.populate` on the sign-adjusted
words. The op witnesses nothing itself (it is a `FormalAssertion`); a composing chip
(`LtChip`/`BranchChip`) witnesses the whole `LtOperationSigned` column block with `populate`.

The unsigned compare columns are gated on `is_real`: the auto-generated `main` threads the row's
`is_real` to the composed `LtOperationUnsigned.circuit` (faithful to SP1), and the unsigned selectors
`(is_real − Σflags≥i)·(bᵢ − ccᵢ)` are `is_real`-dependent — so on a padding row (`is_real = 0`) the
satisfying witness is the **all-zero** unsigned block (`Σflags = 0` makes every selector vanish), not
the real one-hot. `spec_populate` (that the witness satisfies the gadget `Spec`) lives in `Formal.lean`. -/

namespace SP1Clean.LtOperationSigned

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Fully witnessed `LtOperationSigned` column struct (SP1's `populate`): the two `is_signed`-gated
sign bits and the `LtOperationUnsigned` compare columns on the sign-adjusted words — the latter zeroed
on a padding row (`is_real = 0`), where the threaded unsigned compare contributes nothing. -/
def populate (b cc : Word (ZMod p)) (is_signed is_real : ZMod p) :
    Extracted.LtOperationSigned (ZMod p) :=
  let bm := is_signed * U16MSBOperation.populate_msb b[3]
  let cm := is_signed * U16MSBOperation.populate_msb cc[3]
  let bAdj : Word (ZMod p) := #v[b[0], b[1], b[2], b[3] + is_signed * 32768 - 65536 * bm]
  let cAdj : Word (ZMod p) := #v[cc[0], cc[1], cc[2], cc[3] + is_signed * 32768 - 65536 * cm]
  let result : Extracted.LtOperationUnsigned (ZMod p) :=
    if is_real = 1 then LtOperationUnsigned.populate bAdj cAdj
    else ⟨⟨0⟩, #v[0, 0, 0, 0], 0, #v[0, 0]⟩
  ⟨result, ⟨bm⟩, ⟨cm⟩⟩

/-! ### Witness IR

The struct-shaped `FExpr` twin of `populate` (the `BitwiseU16Operation.populateFE` pattern): the
two `is_signed`-gated sign bits (`populate_msbF`'s first consumers), the sign-adjusted limb
expressions, and the `LtOperationUnsigned` scan twins instantiated at them — each unsigned cell
wrapped in the `is_real` gate that mirrors the value side's `if is_real = 1 … else zeroCols`.
Deliberately **not** `@[circuit_norm]`; only the lemmas below cross the boundary. -/

/-- The sign-adjusted limb expressions (`b[3] + is_signed·2^15 − 2^16·msb`), as witness IR. -/
def adjLimbsF (w : Word (Expression (ZMod p))) (is_signed : Expression (ZMod p)) :
    Vector (Witgen.FExpr (ZMod p)) 4 :=
  #v[.expr w[0], .expr w[1], .expr w[2],
     .expr w[3] + .expr is_signed * (32768 : Witgen.FExpr (ZMod p))
       - (65536 : Witgen.FExpr (ZMod p))
           * (.expr is_signed * U16MSBOperation.populate_msbF (.expr w[3]))]

/-- The witness-IR twin of `populate`, over the chip's input expressions (`is_signed` is the chip's
witnessed flag cell; `is_real` the input selector). -/
def populateFE (b cc : Word (Expression (ZMod p))) (is_signed is_real : Expression (ZMod p)) :
    Extracted.LtOperationSigned (Witgen.FExpr (ZMod p)) :=
  let bAdj := adjLimbsF b is_signed
  let cAdj := adjLimbsF cc is_signed
  let gate : Witgen.FExpr (ZMod p) → Witgen.FExpr (ZMod p) :=
    fun e => .ite (is_real =? (1 : ZMod p)) e 0
  ⟨⟨⟨gate (LtOperationUnsigned.compareBitF bAdj cAdj)⟩,
    #v[gate (LtOperationUnsigned.flagsF bAdj cAdj 0), gate (LtOperationUnsigned.flagsF bAdj cAdj 1),
       gate (LtOperationUnsigned.flagsF bAdj cAdj 2), gate (LtOperationUnsigned.flagsF bAdj cAdj 3)],
    gate (LtOperationUnsigned.notEqInvF bAdj cAdj),
    #v[gate (LtOperationUnsigned.comparisonLimbsF bAdj cAdj 0),
       gate (LtOperationUnsigned.comparisonLimbsF bAdj cAdj 1)]⟩,
   ⟨.expr is_signed * U16MSBOperation.populate_msbF (.expr b[3])⟩,
   ⟨.expr is_signed * U16MSBOperation.populate_msbF (.expr cc[3])⟩⟩

section Navigators

set_option linter.unusedSectionVars false

/-- Cell `0` of a flattened `LtOperationSigned` struct is the compare bit. -/
private lemma toElements_cell_bit {F : Type} (s : Extracted.LtOperationSigned F) :
    (toElements s)[0]'(by have h10 : size Extracted.LtOperationSigned = 10 := rfl; omega)
      = s.result.u16_compare_operation.bit := by
  obtain ⟨⟨⟨a⟩, f, ni, cl⟩, ⟨bm⟩, ⟨cm⟩⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_left ?_).trans
    ((Vector.getElem_cast ?_).trans ((Vector.getElem_append_left ?_).trans
      ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_)))) <;> decide

/-- Cell `1 + k` (`k < 4`) is the `k`-th one-hot flag. -/
private lemma toElements_cell_flag {F : Type} (s : Extracted.LtOperationSigned F)
    (k : ℕ) (hk : k < 4) :
    (toElements s)[1 + k]'(by have h10 : size Extracted.LtOperationSigned = 10 := rfl; omega)
      = s.result.u16_flags[k] := by
  obtain ⟨⟨⟨a⟩, f, ni, cl⟩, ⟨bm⟩, ⟨cm⟩⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type]
     refine (Vector.getElem_append_left ?_).trans
       ((Vector.getElem_cast ?_).trans ((Vector.getElem_append_right ?_ ?_).trans
         (Vector.getElem_append_left ?_))) <;> decide)

/-- Cell `5` is the non-equality inverse. -/
private lemma toElements_cell_notEqInv {F : Type} (s : Extracted.LtOperationSigned F) :
    (toElements s)[5]'(by have h10 : size Extracted.LtOperationSigned = 10 := rfl; omega)
      = s.result.not_eq_inv := by
  obtain ⟨⟨⟨a⟩, f, ni, cl⟩, ⟨bm⟩, ⟨cm⟩⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_left ?_).trans
    ((Vector.getElem_cast ?_).trans ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_right ?_ ?_).trans (Vector.getElem_append_left ?_)))) <;> decide

/-- Cell `6 + k` (`k < 2`) is the `k`-th comparison limb. -/
private lemma toElements_cell_compLimb {F : Type} (s : Extracted.LtOperationSigned F)
    (k : ℕ) (hk : k < 2) :
    (toElements s)[6 + k]'(by have h10 : size Extracted.LtOperationSigned = 10 := rfl; omega)
      = s.result.comparison_limbs[k] := by
  obtain ⟨⟨⟨a⟩, f, ni, cl⟩, ⟨bm⟩, ⟨cm⟩⟩ := s
  interval_cases k <;>
    (simp only [circuit_norm, explicit_provable_type]
     refine (Vector.getElem_append_left ?_).trans
       ((Vector.getElem_cast ?_).trans ((Vector.getElem_append_right ?_ ?_).trans
         ((Vector.getElem_append_right ?_ ?_).trans ((Vector.getElem_append_right ?_ ?_).trans
           (Vector.getElem_append_left ?_))))) <;> decide)

/-- Cell `8` is the gated `b` sign bit. -/
private lemma toElements_cell_bMsb {F : Type} (s : Extracted.LtOperationSigned F) :
    (toElements s)[8]'(by have h10 : size Extracted.LtOperationSigned = 10 := rfl; omega)
      = s.b_msb.msb := by
  obtain ⟨⟨⟨a⟩, f, ni, cl⟩, ⟨bm⟩, ⟨cm⟩⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_left ?_).trans
      ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_))) <;> decide

/-- Cell `9` is the gated `c` sign bit. -/
private lemma toElements_cell_cMsb {F : Type} (s : Extracted.LtOperationSigned F) :
    (toElements s)[9]'(by have h10 : size Extracted.LtOperationSigned = 10 := rfl; omega)
      = s.c_msb.msb := by
  obtain ⟨⟨⟨a⟩, f, ni, cl⟩, ⟨bm⟩, ⟨cm⟩⟩ := s
  simp only [circuit_norm, explicit_provable_type]
  refine (Vector.getElem_append_right ?_ ?_).trans
    ((Vector.getElem_append_right ?_ ?_).trans
      ((Vector.getElem_append_left ?_).trans
        ((Vector.getElem_cast ?_).trans (Vector.getElem_append_left ?_)))) <;> decide

end Navigators

/-- The evaluated sign-adjusted word (the value `populate`'s internal `bAdj`/`cAdj`). -/
private def adjVal (v : Word (ZMod p)) (vs : ZMod p) : Word (ZMod p) :=
  #v[v[0], v[1], v[2],
     v[3] + vs * 32768 - 65536 * (vs * U16MSBOperation.populate_msb v[3])]

omit [Fact (2 ^ 17 < p)] in
private lemma adjLimbsF_eval (env : ProverEnvironment (ZMod p))
    (w : Word (Expression (ZMod p))) (is_signed : Expression (ZMod p)) (v : Word (ZMod p))
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment w[i] = v[i])
    (hv3 : v[3].val < 2 ^ 16) :
    ∀ (i : ℕ) (_ : i < 4), ((adjLimbsF w is_signed)[i]).eval { env := env }
      = (adjVal v (Expression.eval env.toEnvironment is_signed))[i] := by
  have hW0 := hW 0 (by omega); have hW1 := hW 1 (by omega)
  have hW2 := hW 2 (by omega); have hW3 := hW 3 (by omega)
  have hmsb := U16MSBOperation.populate_msbF_eval { env := env } (.expr w[3])
    (by simpa [circuit_norm, hW3] using hv3)
  intro i h
  interval_cases i <;>
    simp only [adjLimbsF, adjVal, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, circuit_norm, hmsb,
      hW0, hW1, hW2, hW3]

omit [Fact (2 ^ 17 < p)] in
private lemma msbF_eval (env : ProverEnvironment (ZMod p))
    (w : Word (Expression (ZMod p))) (is_signed : Expression (ZMod p)) (v : Word (ZMod p))
    (hW3 : Expression.eval env.toEnvironment w[3] = v[3]) (hv3 : v[3].val < 2 ^ 16) :
    (Witgen.FExpr.expr is_signed * U16MSBOperation.populate_msbF (.expr w[3])).eval { env := env }
      = Expression.eval env.toEnvironment is_signed * U16MSBOperation.populate_msb v[3] := by
  have hmsb := U16MSBOperation.populate_msbF_eval { env := env } (.expr w[3])
    (by simpa [circuit_norm, hW3] using hv3)
  simp only [circuit_norm, hmsb, hW3]

omit [Fact (2 ^ 17 < p)] in
/-- Evaluating the witness IR is exactly `populate` on the evaluated operands (the
`BitwiseU16Operation.populateFE_eval` statement shape; the `isU64` bounds feed the sign-bit
divisions, and one `is_real` case split resolves every gate on both sides at once). -/
theorem populateFE_eval (env : ProverEnvironment (ZMod p))
    (b cc : Word (Expression (ZMod p))) (is_signed is_real : Expression (ZMod p))
    (vb vcc : Word (ZMod p))
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (hvcc : #v[Expression.eval env.toEnvironment cc[0], Expression.eval env.toEnvironment cc[1],
               Expression.eval env.toEnvironment cc[2],
               Expression.eval env.toEnvironment cc[3]] = vcc)
    (hb : vb.isU64) (hcc : vcc.isU64) :
    Witgen.eval { env := env } (populateFE b cc is_signed is_real)
      = populate vb vcc (Expression.eval env.toEnvironment is_signed)
          (Expression.eval env.toEnvironment is_real) := by
  obtain ⟨hb0, hb1, hb2, hb3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hc0, hc1, hc2, hc3⟩ := Word.lt_cases_of_isU64 hcc
  have hB : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment b[i] = vb[i] := by
    intro i h; rw [← hvb]; interval_cases i <;> simp
  have hC : ∀ (i : ℕ) (h : i < 4), Expression.eval env.toEnvironment cc[i] = vcc[i] := by
    intro i h; rw [← hvcc]; interval_cases i <;> simp
  have hAdjB := adjLimbsF_eval env b is_signed vb hB hb3
  have hAdjC := adjLimbsF_eval env cc is_signed vcc hC hc3
  obtain ⟨hCL, hFL, hNI, hBit⟩ := LtOperationUnsigned.scanF_eval { env := env }
    (adjLimbsF b is_signed) (adjLimbsF cc is_signed)
    (adjVal vb (Expression.eval env.toEnvironment is_signed))
    (adjVal vcc (Expression.eval env.toEnvironment is_signed)) hAdjB hAdjC
  have hbmF := msbF_eval env b is_signed vb (hB 3 (by omega)) hb3
  have hcmF := msbF_eval env cc is_signed vcc (hC 3 (by omega)) hc3
  have hpop : populate vb vcc (Expression.eval env.toEnvironment is_signed)
        (Expression.eval env.toEnvironment is_real)
      = ⟨if Expression.eval env.toEnvironment is_real = 1 then
           LtOperationUnsigned.populate
             (adjVal vb (Expression.eval env.toEnvironment is_signed))
             (adjVal vcc (Expression.eval env.toEnvironment is_signed))
         else ⟨⟨0⟩, #v[0, 0, 0, 0], 0, #v[0, 0]⟩,
         ⟨Expression.eval env.toEnvironment is_signed * U16MSBOperation.populate_msb vb[3]⟩,
         ⟨Expression.eval env.toEnvironment is_signed * U16MSBOperation.populate_msb vcc[3]⟩⟩ := rfl
  rw [hpop]
  refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
  have hi10 : i < 10 := by
    have hsz : size Extracted.LtOperationSigned = 10 := rfl
    omega
  rw [show (Witgen.eval { env := env } (populateFE b cc is_signed is_real) :
          Extracted.LtOperationSigned (ZMod p))
        = fromElements ((toElements (populateFE b cc is_signed is_real)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements, Vector.getElem_map]
  by_cases hreal : Expression.eval env.toEnvironment is_real = 1 <;>
  · interval_cases i
    · refine ((congrArg _ (toElements_cell_bit _)).trans ?_).trans (toElements_cell_bit _).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hBit]
    · refine ((congrArg _ (toElements_cell_flag _ 0 (by omega))).trans ?_).trans
        (toElements_cell_flag _ 0 (by omega)).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hFL 0]
    · refine ((congrArg _ (toElements_cell_flag _ 1 (by omega))).trans ?_).trans
        (toElements_cell_flag _ 1 (by omega)).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hFL 1]
    · refine ((congrArg _ (toElements_cell_flag _ 2 (by omega))).trans ?_).trans
        (toElements_cell_flag _ 2 (by omega)).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hFL 2]
    · refine ((congrArg _ (toElements_cell_flag _ 3 (by omega))).trans ?_).trans
        (toElements_cell_flag _ 3 (by omega)).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hFL 3]
    · refine ((congrArg _ (toElements_cell_notEqInv _)).trans ?_).trans
        (toElements_cell_notEqInv _).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hNI]
    · refine ((congrArg _ (toElements_cell_compLimb _ 0 (by omega))).trans ?_).trans
        (toElements_cell_compLimb _ 0 (by omega)).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hCL 0]
    · refine ((congrArg _ (toElements_cell_compLimb _ 1 (by omega))).trans ?_).trans
        (toElements_cell_compLimb _ 1 (by omega)).symm
      simp [populateFE, LtOperationUnsigned.populate, circuit_norm, hreal, hCL 1]
    · refine ((congrArg _ (toElements_cell_bMsb _)).trans ?_).trans (toElements_cell_bMsb _).symm
      simpa [populateFE, circuit_norm] using hbmF
    · refine ((congrArg _ (toElements_cell_cMsb _)).trans ?_).trans (toElements_cell_cMsb _).symm
      simpa [populateFE, circuit_norm] using hcmF


omit [Fact (2 ^ 17 < p)] in
/-- Elementwise corollary of `populateFE_eval`, in the exact per-cell shape the chip completeness
seam's witness obligations arrive in. -/
theorem populateFE_eval_cell (env : ProverEnvironment (ZMod p))
    (b cc : Word (Expression (ZMod p))) (is_signed is_real : Expression (ZMod p))
    (vb vcc : Word (ZMod p))
    (hvb : #v[Expression.eval env.toEnvironment b[0], Expression.eval env.toEnvironment b[1],
              Expression.eval env.toEnvironment b[2], Expression.eval env.toEnvironment b[3]] = vb)
    (hvcc : #v[Expression.eval env.toEnvironment cc[0], Expression.eval env.toEnvironment cc[1],
               Expression.eval env.toEnvironment cc[2],
               Expression.eval env.toEnvironment cc[3]] = vcc)
    (hb : vb.isU64) (hcc : vcc.isU64) (j : ℕ) (hj : j < 10) :
    Witgen.FExpr.eval { env := env }
        ((toElements (populateFE b cc is_signed is_real))[j]'(by
          have h10 : size Extracted.LtOperationSigned = 10 := rfl
          omega))
      = (toElements (populate vb vcc (Expression.eval env.toEnvironment is_signed)
          (Expression.eval env.toEnvironment is_real)))[j]'(by
          have h10 : size Extracted.LtOperationSigned = 10 := rfl
          omega) := by
  have h := congrArg
    (fun s : Extracted.LtOperationSigned (ZMod p) => (toElements s)[j]'(by
      have h10 : size Extracted.LtOperationSigned = 10 := rfl
      omega))
    (populateFE_eval env b cc is_signed is_real vb vcc hvb hvcc hb hcc)
  rw [show (Witgen.eval { env := env } (populateFE b cc is_signed is_real) :
          Extracted.LtOperationSigned (ZMod p))
        = fromElements ((toElements (populateFE b cc is_signed is_real)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements] at h
  simpa [Vector.getElem_map] using h

omit [Fact (2 ^ 17 < p)] in
/-- `ofFExprs`-of-`toElements` evaluation is the flattened struct evaluation. -/
private lemma ofFExprs_eval_eq (env : ProverEnvironment (ZMod p))
    (xs : Extracted.LtOperationSigned (Witgen.FExpr (ZMod p))) :
    (Witgen.WitgenIR.ofFExprs (toElements xs)).eval env
      = toElements (Witgen.eval { env := env } xs) := by
  rw [show (Witgen.eval { env := env } xs : Extracted.LtOperationSigned (ZMod p))
        = fromElements ((toElements xs).map (Witgen.FExpr.eval { env := env })) from rfl,
    ProvableType.toElements_fromElements]
  apply Vector.ext
  intro i hi
  simp [circuit_norm, Vector.getElem_map]

omit [Fact (2 ^ 17 < p)] in
/-- Environment-locality of the witness IR, in the raw `ofFExprs` payload form the
`ComputableWitnesses` obligations quantify over (a congruence, so it needs no bounds). -/
theorem populateFE_congr_flat (env env' : ProverEnvironment (ZMod p))
    (b cc : Word (Expression (ZMod p))) (is_signed is_real : Expression (ZMod p))
    (hB : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment b[i] = Expression.eval env'.toEnvironment b[i])
    (hC : ∀ (i : ℕ) (_ : i < 4),
      Expression.eval env.toEnvironment cc[i] = Expression.eval env'.toEnvironment cc[i])
    (hS : Expression.eval env.toEnvironment is_signed
      = Expression.eval env'.toEnvironment is_signed)
    (hR : Expression.eval env.toEnvironment is_real
      = Expression.eval env'.toEnvironment is_real) :
    (Witgen.WitgenIR.ofFExprs (toElements (populateFE b cc is_signed is_real))).eval env
      = (Witgen.WitgenIR.ofFExprs (toElements (populateFE b cc is_signed is_real))).eval env' := by
  have hmsbB := U16MSBOperation.populate_msbF_congr { env := env } { env := env' } (.expr b[3])
    (by simpa [circuit_norm] using hB 3 (by omega))
  have hmsbC := U16MSBOperation.populate_msbF_congr { env := env } { env := env' } (.expr cc[3])
    (by simpa [circuit_norm] using hC 3 (by omega))
  have hAdjB : ∀ (i : ℕ) (_ : i < 4), ((adjLimbsF b is_signed)[i]).eval { env := env }
      = ((adjLimbsF b is_signed)[i]).eval { env := env' } := by
    intro i h
    interval_cases i <;>
      simp only [adjLimbsF, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, circuit_norm, -Witgen.u64Wrap, hmsbB, hS,
        hB 0 (by omega), hB 1 (by omega), hB 2 (by omega), hB 3 (by omega)]
  have hAdjC : ∀ (i : ℕ) (_ : i < 4), ((adjLimbsF cc is_signed)[i]).eval { env := env }
      = ((adjLimbsF cc is_signed)[i]).eval { env := env' } := by
    intro i h
    interval_cases i <;>
      simp only [adjLimbsF, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, circuit_norm, -Witgen.u64Wrap, hmsbC, hS,
        hC 0 (by omega), hC 1 (by omega), hC 2 (by omega), hC 3 (by omega)]
  obtain ⟨hCL, hFL, hNI, hBit⟩ := LtOperationUnsigned.scanF_congr { env := env } { env := env' }
    (adjLimbsF b is_signed) (adjLimbsF cc is_signed) hAdjB hAdjC
  rw [ofFExprs_eval_eq, ofFExprs_eval_eq]
  refine congrArg toElements ?_
  refine (ProvableType.ext_iff _ _).mpr fun i hi => ?_
  have hi10 : i < 10 := by
    have hsz : size Extracted.LtOperationSigned = 10 := rfl
    omega
  rw [show (Witgen.eval { env := env } (populateFE b cc is_signed is_real) :
          Extracted.LtOperationSigned (ZMod p))
        = fromElements ((toElements (populateFE b cc is_signed is_real)).map
            (Witgen.FExpr.eval { env := env })) from rfl,
    show (Witgen.eval { env := env' } (populateFE b cc is_signed is_real) :
          Extracted.LtOperationSigned (ZMod p))
        = fromElements ((toElements (populateFE b cc is_signed is_real)).map
            (Witgen.FExpr.eval { env := env' })) from rfl,
    ProvableType.toElements_fromElements, ProvableType.toElements_fromElements,
    Vector.getElem_map, Vector.getElem_map]
  interval_cases i
  · exact ((congrArg _ (toElements_cell_bit _)).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hBit])).trans
      (congrArg _ (toElements_cell_bit _)).symm
  · exact ((congrArg _ (toElements_cell_flag _ 0 (by omega))).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hFL 0])).trans
      (congrArg _ (toElements_cell_flag _ 0 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_flag _ 1 (by omega))).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hFL 1])).trans
      (congrArg _ (toElements_cell_flag _ 1 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_flag _ 2 (by omega))).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hFL 2])).trans
      (congrArg _ (toElements_cell_flag _ 2 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_flag _ 3 (by omega))).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hFL 3])).trans
      (congrArg _ (toElements_cell_flag _ 3 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_notEqInv _)).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hNI])).trans
      (congrArg _ (toElements_cell_notEqInv _)).symm
  · exact ((congrArg _ (toElements_cell_compLimb _ 0 (by omega))).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hCL 0])).trans
      (congrArg _ (toElements_cell_compLimb _ 0 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_compLimb _ 1 (by omega))).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hR, hCL 1])).trans
      (congrArg _ (toElements_cell_compLimb _ 1 (by omega))).symm
  · exact ((congrArg _ (toElements_cell_bMsb _)).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hmsbB, hS])).trans
      (congrArg _ (toElements_cell_bMsb _)).symm
  · exact ((congrArg _ (toElements_cell_cMsb _)).trans (by
      simp only [populateFE, circuit_norm, -Witgen.u64Wrap, hmsbC, hS])).trans
      (congrArg _ (toElements_cell_cMsb _)).symm

end SP1Clean.LtOperationSigned
