import SP1Clean.Proofs.Chips.DivRemChip.Populate.IR
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Bounds

/-! # `DivRemChip` — witness-IR word bridges (A7b)

The word-level layer between the u64 dispatch calculus (`Populate/IR.lean`) and the per-site
witness payloads: unpacking a u64-sorted value into the four committed u16 limbs (`wordFOfU64`,
the `wordOfBits` twin), the computational-operand dispatches (`bCompU`/`cCompU` in the u64 sort,
`bCompF`/`cCompF` as committed words), and the computational quotient/remainder dispatches
(`quotCompBitsU`/`remCompBitsU`). Each builder carries one eval lemma against its value-layer
twin; the `toBitVec64` characterisations of `bComp`/`cComp` are proved here as the value-side
handles those evals rest on. Deliberately **not** `@[circuit_norm]`. -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

section WordUnpack

/-- The four u16 limbs of a u64-sorted value, as field-sorted cells (`wordOfBits`' IR twin). -/
def wordFOfU64 (x : Witgen.U64Expr (ZMod p)) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  #v[(x % 65536).toField, (x >>> 16 % 65536).toField,
     (x >>> 32 % 65536).toField, (x >>> 48 % 65536).toField]

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating a limb of the unpack is the corresponding `wordOfBits` limb. -/
theorem wordFOfU64_eval (env : ProverEnvironment (ZMod p)) (x : Witgen.U64Expr (ZMod p))
    {bv : BitVec 64} (hx : ((x.eval { env := env })).toNat = bv.toNat)
    (i : ℕ) (hi : i < 4) :
    ((wordFOfU64 x)[i]).eval { env := env } = (wordOfBits (p := p) bv)[i] := by
  have hlt := bv.isLt
  interval_cases i <;>
  · simp only [wordFOfU64, wordOfBits, wordOfNat, circuit_norm, FiniteField.fromNat, hx,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    congr 1
    all_goals simp only [Nat.shiftRight_eq_div_pow]
    all_goals omega

end WordUnpack

section CompValue

omit [Fact (2 ^ 24 < p)] in
/-- `bComp` and `cComp` are literally the same word-extension function. -/
theorem bComp_eq_cComp : (bComp : Word (ZMod p) → Vector (ZMod p) 8 → Word (ZMod p)) = cComp :=
  rfl

/-- The u64 bit pattern of the computational operand `cComp`: the raw value for the 64-bit
variants, its low 32 bits sign-extended (signed W) or zero-extended (unsigned W) otherwise. -/
theorem cComp_toBitVec64 (C : Word (ZMod p)) (f : Vector (ZMod p) 8) (hC : C.isU64) :
    Word.toBitVec64 (cComp C f)
      = if f[4] + f[5] = 1 then (BitVec.setWidth 32 (Word.toBitVec64 C)).signExtend 64
        else if f[6] + f[7] = 1 then BitVec.setWidth 64 (BitVec.setWidth 32 (Word.toBitVec64 C))
        else Word.toBitVec64 C := by
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hC
  have hCn := Word.toBitVec64_toNat hC
  have hlow : (BitVec.setWidth 32 (Word.toBitVec64 C)).toNat = C[0].val + 2 ^ 16 * C[1].val := by
    rw [BitVec.toNat_setWidth, hCn, Word.toNat_def]
    omega
  have hmsb : (BitVec.setWidth 32 (Word.toBitVec64 C)).msb
      = decide (2 ^ 31 ≤ (BitVec.setWidth 32 (Word.toBitVec64 C)).toNat) :=
    BitVec.msb_eq_decide _
  -- the msb fill is decided by the ℕ quotient `C[1].val / 32768 ∈ {0, 1}`
  have hqcase : C[1].val / 32768 = 0 ∨ C[1].val / 32768 = 1 := by omega
  unfold cComp
  split_ifs with h45 h67
  · -- signed W: the msb-filled word is the sign extension of the low 32 bits
    have hp24 : 2 ^ 24 < p := Fact.out
    have hval2 : ((U16MSBOperation.populate_msb C[1]) * (65535 : ZMod p)).val
        = C[1].val / 32768 * 65535 := by
      simp only [U16MSBOperation.populate_msb]
      rcases hqcase with hq | hq
      · simp [hq]
      · simp only [hq, Nat.cast_one, one_mul]
        rw [show ((65535 : ZMod p)) = ((65535 : ℕ) : ZMod p) by norm_cast,
          ZMod.val_natCast_of_lt (by omega)]
    have hml : ((U16MSBOperation.populate_msb C[1]) * (65535 : ZMod p)).val < 2 ^ 16 := by
      rw [hval2]; omega
    have hU : Word.isU64 (#v[C[0], C[1], U16MSBOperation.populate_msb C[1] * 65535,
        U16MSBOperation.populate_msb C[1] * 65535] : Word (ZMod p)) := by
      apply Word.isU64_of_cases <;>
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ]
      exacts [u0, u1, hml, hml]
    show (Word.toBitVec64 (#v[C[0], C[1], U16MSBOperation.populate_msb C[1] * 65535,
        U16MSBOperation.populate_msb C[1] * 65535] : Word (ZMod p)))
      = (BitVec.setWidth 32 C.toBitVec64).signExtend 64
    rw [← BitVec.toNat_inj, BitVec.toNat_signExtend]
    simp only [BitVec.toNat_setWidth, hlow, hmsb]
    rw [Word.toBitVec64_toNat hU, Word.toNat_def]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, hval2, decide_eq_true_eq]
    rcases hqcase with hq | hq <;> rw [hq]
    · rw [if_neg (by omega)]
      omega
    · rw [if_pos (by omega)]
      omega
  · -- unsigned W: the zero-filled word is the zero extension of the low 32 bits
    rw [← BitVec.toNat_inj, BitVec.toNat_setWidth, BitVec.toNat_setWidth, hCn]
    have hU : Word.isU64 (#v[C[0], C[1], 0, 0] : Word (ZMod p)) := by
      apply Word.isU64_of_cases <;>
        simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, ZMod.val_zero] <;> omega
    rw [Word.toBitVec64_toNat hU, Word.toNat_def, Word.toNat_def]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ZMod.val_zero]
    omega
  · rfl

/-- `bComp`'s u64 bit pattern (via `bComp_eq_cComp`). -/
theorem bComp_toBitVec64 (B : Word (ZMod p)) (f : Vector (ZMod p) 8) (hB : B.isU64) :
    Word.toBitVec64 (bComp B f)
      = if f[4] + f[5] = 1 then (BitVec.setWidth 32 (Word.toBitVec64 B)).signExtend 64
        else if f[6] + f[7] = 1 then BitVec.setWidth 64 (BitVec.setWidth 32 (Word.toBitVec64 B))
        else Word.toBitVec64 B := by
  rw [bComp_eq_cComp]
  exact cComp_toBitVec64 B f hB

end CompValue

section CompU

/-- The computational operand's u64 value, dispatched on the variant class (`cComp`'s bit
pattern, over any u64-sorted operand pack). -/
def compU (x : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  .ite (((flagF 4 : Witgen.FExpr (ZMod p)) + flagF 5) =? (1 : ZMod p))
    (sext32U (low32U x))
    (.ite (((flagF 6 : Witgen.FExpr (ZMod p)) + flagF 7) =? (1 : ZMod p)) (low32U x) x)

/-- Evaluating the operand dispatch is `cComp`'s bit pattern. -/
theorem compU_toNat (env : ProverEnvironment (ZMod p)) (x : Witgen.U64Expr (ZMod p))
    {vC : Word (ZMod p)} (hx : ((x.eval { env := env })).toNat = (Word.toBitVec64 vC).toNat)
    (hUC : vC.isU64) :
    ((compU x).eval { env := env }).toNat
      = (Word.toBitVec64 (cComp vC (hintFlags env.hint))).toNat := by
  rw [cComp_toBitVec64 vC _ hUC]
  have hf4 := flagF_eval env 4 (by omega)
  have hf5 := flagF_eval env 5 (by omega)
  have hf6 := flagF_eval env 6 (by omega)
  have hf7 := flagF_eval env 7 (by omega)
  simp only [compU, circuit_norm, hf4, hf5, hf6, hf7, apply_ite (BitVec.toNat)]
  split_ifs
  · exact sext32U_toNat env _ (low32U_toNat env x hx)
  · rw [low32U_toNat env x hx]
    simp only [BitVec.toNat_setWidth]
    omega
  · exact hx

/-- `bComp`'s bit pattern, same dispatch (`bComp_eq_cComp`). -/
theorem compU_toNat_b (env : ProverEnvironment (ZMod p)) (x : Witgen.U64Expr (ZMod p))
    {vB : Word (ZMod p)} (hx : ((x.eval { env := env })).toNat = (Word.toBitVec64 vB).toNat)
    (hUB : vB.isU64) :
    ((compU x).eval { env := env }).toNat
      = (Word.toBitVec64 (bComp vB (hintFlags env.hint))).toNat := by
  rw [bComp_eq_cComp]
  exact compU_toNat env x hx hUB

end CompU

section CompBits

/-- The computational quotient's bit pattern as IR (`quotCompBits`: the low 32 bits
zero-extended for the unsigned W-variants, `quotBits` otherwise). -/
def quotCompBitsU (b c : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  .ite (((flagF 6 : Witgen.FExpr (ZMod p)) + flagF 7) =? (1 : ZMod p))
    (low32U (quotBitsU b c)) (quotBitsU b c)

/-- The computational remainder's bit pattern as IR (`remCompBits`). -/
def remCompBitsU (b c : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  .ite (((flagF 6 : Witgen.FExpr (ZMod p)) + flagF 7) =? (1 : ZMod p))
    (low32U (remBitsU b c)) (remBitsU b c)

variable (env : ProverEnvironment (ZMod p))

/-- Evaluating the computational-quotient dispatch is `quotCompBits`. -/
theorem quotCompBitsU_toNat (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
    (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
    (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
    (hUB : vB.isU64) (hUC : vC.isU64) :
    ((quotCompBitsU (wordU B) (wordU C)).eval { env := env }).toNat
      = (quotCompBits vB vC (hintFlags env.hint)).toNat := by
  have hq := quotBitsU_toNat env B C vB vC hWB hWC hUB hUC
  have hf6 := flagF_eval env 6 (by omega)
  have hf7 := flagF_eval env 7 (by omega)
  simp only [quotCompBitsU, quotCompBits, circuit_norm, hf6, hf7, apply_ite (BitVec.toNat)]
  split_ifs
  · rw [low32U_toNat env _ hq]
    simp only [BitVec.toNat_setWidth]
    omega
  · exact hq

/-- Evaluating the computational-remainder dispatch is `remCompBits`. -/
theorem remCompBitsU_toNat (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
    (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
    (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
    (hUB : vB.isU64) (hUC : vC.isU64) :
    ((remCompBitsU (wordU B) (wordU C)).eval { env := env }).toNat
      = (remCompBits vB vC (hintFlags env.hint)).toNat := by
  have hr := remBitsU_toNat env B C vB vC hWB hWC hUB hUC
  have hf6 := flagF_eval env 6 (by omega)
  have hf7 := flagF_eval env 7 (by omega)
  simp only [remCompBitsU, remCompBits, circuit_norm, hf6, hf7, apply_ite (BitVec.toNat)]
  split_ifs
  · rw [low32U_toNat env _ hr]
    simp only [BitVec.toNat_setWidth]
    omega
  · exact hr

end CompBits

section CompF

/-- The committed computational-operand word as field cells (`cComp`'s limbs: the raw limbs
below 32 bits, the class-dispatched fill above). -/
def compF (w : Word (Expression (ZMod p))) : Vector (Witgen.FExpr (ZMod p)) 4 :=
  let m := U16MSBOperation.populate_msbF (.expr w[1])
  let fill : Witgen.FExpr (ZMod p) :=
    .ite (((flagF 4 : Witgen.FExpr (ZMod p)) + flagF 5) =? (1 : ZMod p))
      (m * (65535 : ZMod p))
      (.ite (((flagF 6 : Witgen.FExpr (ZMod p)) + flagF 7) =? (1 : ZMod p)) 0 0)
  #v[.expr w[0], .expr w[1],
     .ite (((flagF 4 : Witgen.FExpr (ZMod p)) + flagF 5) =? (1 : ZMod p))
       (m * (65535 : ZMod p))
       (.ite (((flagF 6 : Witgen.FExpr (ZMod p)) + flagF 7) =? (1 : ZMod p)) 0 (.expr w[2])),
     .ite (((flagF 4 : Witgen.FExpr (ZMod p)) + flagF 5) =? (1 : ZMod p))
       (m * (65535 : ZMod p))
       (.ite (((flagF 6 : Witgen.FExpr (ZMod p)) + flagF 7) =? (1 : ZMod p)) 0 (.expr w[3]))]

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating a committed operand limb is the corresponding `cComp` limb. -/
theorem compF_eval (env : ProverEnvironment (ZMod p)) (C : Word (Expression (ZMod p)))
    (vC : Word (ZMod p))
    (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
    (hUC : vC.isU64) (i : ℕ) (hi : i < 4) :
    ((compF C)[i]).eval { env := env } = (cComp vC (hintFlags env.hint))[i] := by
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hUC
  have h0 := hWC 0 (by omega); have h1 := hWC 1 (by omega)
  have h2 := hWC 2 (by omega); have h3 := hWC 3 (by omega)
  have hf4 := flagF_eval env 4 (by omega)
  have hf5 := flagF_eval env 5 (by omega)
  have hf6 := flagF_eval env 6 (by omega)
  have hf7 := flagF_eval env 7 (by omega)
  have hm := U16MSBOperation.populate_msbF_eval { env := env } (.expr C[1])
    (by simp only [circuit_norm, h1]; exact u1)
  simp only [circuit_norm, h1] at hm
  interval_cases i <;>
  · simp only [compF, cComp, circuit_norm, hf4, hf5, hf6, hf7, h0, h1, h2, h3, hm,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
    split_ifs <;>
      simp only [circuit_norm, Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]

omit [Fact (2 ^ 24 < p)] in
/-- `bComp`'s limbs, same dispatch. -/
theorem compF_eval_b (env : ProverEnvironment (ZMod p)) (B : Word (Expression (ZMod p)))
    (vB : Word (ZMod p))
    (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
    (hUB : vB.isU64) (i : ℕ) (hi : i < 4) :
    ((compF B)[i]).eval { env := env } = (bComp vB (hintFlags env.hint))[i] := by
  rw [bComp_eq_cComp]
  exact compF_eval env B vB hWB hUB i hi

end CompF

end SP1Clean.DivRemChip
