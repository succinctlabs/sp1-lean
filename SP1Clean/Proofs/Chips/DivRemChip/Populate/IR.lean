import SP1Clean.Proofs.Chips.DivRemChip.Populate

/-! # `DivRemChip` — the witness-IR calculus (A7a)

The u64-sorted expression calculus the DivRem witness twins are built from: two's-complement
**negation as multiplication** (`-t ≡ t·(2^w − 1) (mod 2^w)` — the IR has no subtraction),
magnitude (`bvAbs`), signed division/remainder in `BitVec.toNat_sdiv/srem`'s exact four-case
shape, and the width-32 embedded family (values `< 2^32` inside the u64 sort, with explicit
`% 2^32` wraps). Each builder carries one `toNat` lemma against its `BitVec` twin. Deliberately
**not** `@[circuit_norm]`. -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

section IRCalculus

/-- Two's-complement negation at width 64 (`-t ≡ t·(2^64 − 1)`; the u64 wrap supplies the mod). -/
def negU (x : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  x * (18446744073709551615 : Witgen.U64Expr (ZMod p))

/-- Two's-complement magnitude at width 64 (`bvAbs`). -/
def absU (x : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  .ite (x <? (9223372036854775808 : ℕ)) x (negU x)

/-- Signed division at width 64, in `BitVec.toNat_sdiv`'s four-case shape. -/
def sdivU (x y : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  .ite (x <? (9223372036854775808 : ℕ))
    (.ite (y <? (9223372036854775808 : ℕ)) (x / y) (negU (x / negU y)))
    (.ite (y <? (9223372036854775808 : ℕ)) (negU (negU x / y)) (negU x / negU y))

/-- Signed remainder at width 64, in `BitVec.toNat_srem`'s four-case shape. -/
def sremU (x y : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  .ite (x <? (9223372036854775808 : ℕ))
    (.ite (y <? (9223372036854775808 : ℕ)) (x % y) (x % negU y))
    (.ite (y <? (9223372036854775808 : ℕ)) (negU (negU x % y)) (negU (negU x % negU y)))

/-- Two's-complement negation at width 32 (values `< 2^32`; explicit wrap). -/
def neg32U (x : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  (x * (4294967295 : Witgen.U64Expr (ZMod p))) % (4294967296 : Witgen.U64Expr (ZMod p))

/-- Signed division at width 32 (embedded; operands `< 2^32`). -/
def sdiv32U (x y : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  .ite (x <? (2147483648 : ℕ))
    (.ite (y <? (2147483648 : ℕ)) (x / y) (neg32U (x / neg32U y)))
    (.ite (y <? (2147483648 : ℕ)) (neg32U (neg32U x / y)) (neg32U x / neg32U y))

/-- Signed remainder at width 32 (embedded). -/
def srem32U (x y : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  .ite (x <? (2147483648 : ℕ))
    (.ite (y <? (2147483648 : ℕ)) (x % y) (x % neg32U y))
    (.ite (y <? (2147483648 : ℕ)) (neg32U (neg32U x % y)) (neg32U (neg32U x % neg32U y)))

/-- The low 32 bits (`setWidth 32`). -/
def low32U (x : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  x % (4294967296 : Witgen.U64Expr (ZMod p))

/-- Sign-extension of an embedded 32-bit value to 64 bits (input `< 2^32`). -/
def sext32U (x : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  .ite (x <? (2147483648 : ℕ)) x (x + (18446744069414584320 : Witgen.U64Expr (ZMod p)))

end IRCalculus

section IRCalculusEval

omit [Fact (2 ^ 24 < p)]

variable (env : ProverEnvironment (ZMod p))

/-- `negU` is `BitVec` negation at width 64. -/
theorem negU_toNat (x : Witgen.U64Expr (ZMod p)) {bx : BitVec 64}
    (hx : ((x.eval { env := env })).toNat = bx.toNat) :
    ((negU x).eval { env := env }).toNat = (-bx).toNat := by
  have hlt := bx.isLt
  simp only [negU, circuit_norm, hx, BitVec.toNat_neg]
  omega

/-- `absU` is `bvAbs` at width 64. -/
theorem absU_toNat (x : Witgen.U64Expr (ZMod p)) {bx : BitVec 64}
    (hx : ((x.eval { env := env })).toNat = bx.toNat) :
    ((absU x).eval { env := env }).toNat = (bvAbs bx).toNat := by
  have hlt := bx.isLt
  have hmsb : bx.msb = decide (2 ^ 63 ≤ bx.toNat) := BitVec.msb_eq_decide bx
  simp only [absU, circuit_norm, hx, bvAbs]
  rcases Nat.lt_or_ge bx.toNat (2 ^ 63) with hcase | hcase
  · rw [if_pos (by omega), if_neg (by rw [hmsb]; simp; omega)]
    exact hx
  · rw [if_neg (by omega), if_pos (by rw [hmsb]; simp; omega)]
    exact negU_toNat env x hx

/-- `sdivU` is `BitVec.sdiv` at width 64 (case-aligned with `BitVec.toNat_sdiv`). -/
theorem sdivU_toNat (x y : Witgen.U64Expr (ZMod p)) {bx bY : BitVec 64}
    (hx : ((x.eval { env := env })).toNat = bx.toNat)
    (hy : ((y.eval { env := env })).toNat = bY.toNat) :
    ((sdivU x y).eval { env := env }).toNat = (bx.sdiv bY).toNat := by
  have hltx := bx.isLt
  have hlty := bY.isLt
  have hmx : bx.msb = decide (2 ^ 63 ≤ bx.toNat) := BitVec.msb_eq_decide bx
  have hmy : bY.msb = decide (2 ^ 63 ≤ bY.toNat) := BitVec.msb_eq_decide bY
  have hnx := negU_toNat env x hx
  have hny := negU_toNat env y hy
  rw [BitVec.toNat_sdiv]
  simp only [sdivU, circuit_norm, hx, hy]
  rcases Nat.lt_or_ge bx.toNat (2 ^ 63) with hcx | hcx <;>
    rcases Nat.lt_or_ge bY.toNat (2 ^ 63) with hcy | hcy
  · rw [show bx.msb = false by rw [hmx]; simp; omega,
      show bY.msb = false by rw [hmy]; simp; omega]
    rw [if_pos (by omega), if_pos (by omega)]
    simp only [circuit_norm, hx, hy, BitVec.udiv_eq, BitVec.toNat_udiv]
  · rw [show bx.msb = false by rw [hmx]; simp; omega,
      show bY.msb = true by rw [hmy]; simp; omega]
    rw [if_pos (by omega), if_neg (by omega)]
    refine negU_toNat env _ ?_
    simp only [circuit_norm, hx, hny, BitVec.udiv_eq, BitVec.toNat_udiv]
  · rw [show bx.msb = true by rw [hmx]; simp; omega,
      show bY.msb = false by rw [hmy]; simp; omega]
    rw [if_neg (by omega), if_pos (by omega)]
    refine negU_toNat env _ ?_
    simp only [circuit_norm, hnx, hy, BitVec.udiv_eq, BitVec.toNat_udiv]
  · rw [show bx.msb = true by rw [hmx]; simp; omega,
      show bY.msb = true by rw [hmy]; simp; omega]
    rw [if_neg (by omega), if_neg (by omega)]
    simp only [circuit_norm, hnx, hny, BitVec.udiv_eq, BitVec.toNat_udiv]

/-- `sremU` is `BitVec.srem` at width 64 (case-aligned with `BitVec.toNat_srem`). -/
theorem sremU_toNat (x y : Witgen.U64Expr (ZMod p)) {bx bY : BitVec 64}
    (hx : ((x.eval { env := env })).toNat = bx.toNat)
    (hy : ((y.eval { env := env })).toNat = bY.toNat) :
    ((sremU x y).eval { env := env }).toNat = (bx.srem bY).toNat := by
  have hltx := bx.isLt
  have hlty := bY.isLt
  have hmx : bx.msb = decide (2 ^ 63 ≤ bx.toNat) := BitVec.msb_eq_decide bx
  have hmy : bY.msb = decide (2 ^ 63 ≤ bY.toNat) := BitVec.msb_eq_decide bY
  have hnx := negU_toNat env x hx
  have hny := negU_toNat env y hy
  rw [BitVec.toNat_srem]
  simp only [sremU, circuit_norm, hx, hy]
  rcases Nat.lt_or_ge bx.toNat (2 ^ 63) with hcx | hcx <;>
    rcases Nat.lt_or_ge bY.toNat (2 ^ 63) with hcy | hcy
  · rw [show bx.msb = false by rw [hmx]; simp; omega,
      show bY.msb = false by rw [hmy]; simp; omega]
    rw [if_pos (by omega), if_pos (by omega)]
    simp only [circuit_norm, hx, hy]
  · rw [show bx.msb = false by rw [hmx]; simp; omega,
      show bY.msb = true by rw [hmy]; simp; omega]
    rw [if_pos (by omega), if_neg (by omega)]
    simp only [circuit_norm, hx, hny]
  · rw [show bx.msb = true by rw [hmx]; simp; omega,
      show bY.msb = false by rw [hmy]; simp; omega]
    rw [if_neg (by omega), if_pos (by omega)]
    refine negU_toNat env _ ?_
    simp only [circuit_norm, hnx, hy, BitVec.toNat_umod]
  · rw [show bx.msb = true by rw [hmx]; simp; omega,
      show bY.msb = true by rw [hmy]; simp; omega]
    rw [if_neg (by omega), if_neg (by omega)]
    refine negU_toNat env _ ?_
    simp only [circuit_norm, hnx, hny, BitVec.toNat_umod]

/-- `neg32U` is `BitVec` negation at width 32 (embedded values). -/
theorem neg32U_toNat (x : Witgen.U64Expr (ZMod p)) {bx : BitVec 32}
    (hx : ((x.eval { env := env })).toNat = bx.toNat) :
    ((neg32U x).eval { env := env }).toNat = (-bx).toNat := by
  have hlt := bx.isLt
  simp only [neg32U, circuit_norm, hx, BitVec.toNat_neg]
  omega

/-- `sdiv32U` is `BitVec.sdiv` at width 32 (embedded). -/
theorem sdiv32U_toNat (x y : Witgen.U64Expr (ZMod p)) {bx bY : BitVec 32}
    (hx : ((x.eval { env := env })).toNat = bx.toNat)
    (hy : ((y.eval { env := env })).toNat = bY.toNat) :
    ((sdiv32U x y).eval { env := env }).toNat = (bx.sdiv bY).toNat := by
  have hltx := bx.isLt
  have hlty := bY.isLt
  have hmx : bx.msb = decide (2 ^ 31 ≤ bx.toNat) := BitVec.msb_eq_decide bx
  have hmy : bY.msb = decide (2 ^ 31 ≤ bY.toNat) := BitVec.msb_eq_decide bY
  have hnx := neg32U_toNat env x hx
  have hny := neg32U_toNat env y hy
  rw [BitVec.toNat_sdiv]
  simp only [sdiv32U, circuit_norm, hx, hy]
  rcases Nat.lt_or_ge bx.toNat (2 ^ 31) with hcx | hcx <;>
    rcases Nat.lt_or_ge bY.toNat (2 ^ 31) with hcy | hcy
  · rw [show bx.msb = false by rw [hmx]; simp; omega,
      show bY.msb = false by rw [hmy]; simp; omega]
    rw [if_pos (by omega), if_pos (by omega)]
    simp only [circuit_norm, hx, hy, BitVec.udiv_eq, BitVec.toNat_udiv]
  · rw [show bx.msb = false by rw [hmx]; simp; omega,
      show bY.msb = true by rw [hmy]; simp; omega]
    rw [if_pos (by omega), if_neg (by omega)]
    refine neg32U_toNat env _ ?_
    simp only [circuit_norm, hx, hny, BitVec.udiv_eq, BitVec.toNat_udiv]
  · rw [show bx.msb = true by rw [hmx]; simp; omega,
      show bY.msb = false by rw [hmy]; simp; omega]
    rw [if_neg (by omega), if_pos (by omega)]
    refine neg32U_toNat env _ ?_
    simp only [circuit_norm, hnx, hy, BitVec.udiv_eq, BitVec.toNat_udiv]
  · rw [show bx.msb = true by rw [hmx]; simp; omega,
      show bY.msb = true by rw [hmy]; simp; omega]
    rw [if_neg (by omega), if_neg (by omega)]
    simp only [circuit_norm, hnx, hny, BitVec.udiv_eq, BitVec.toNat_udiv]

/-- `srem32U` is `BitVec.srem` at width 32 (embedded). -/
theorem srem32U_toNat (x y : Witgen.U64Expr (ZMod p)) {bx bY : BitVec 32}
    (hx : ((x.eval { env := env })).toNat = bx.toNat)
    (hy : ((y.eval { env := env })).toNat = bY.toNat) :
    ((srem32U x y).eval { env := env }).toNat = (bx.srem bY).toNat := by
  have hltx := bx.isLt
  have hlty := bY.isLt
  have hmx : bx.msb = decide (2 ^ 31 ≤ bx.toNat) := BitVec.msb_eq_decide bx
  have hmy : bY.msb = decide (2 ^ 31 ≤ bY.toNat) := BitVec.msb_eq_decide bY
  have hnx := neg32U_toNat env x hx
  have hny := neg32U_toNat env y hy
  rw [BitVec.toNat_srem]
  simp only [srem32U, circuit_norm, hx, hy]
  rcases Nat.lt_or_ge bx.toNat (2 ^ 31) with hcx | hcx <;>
    rcases Nat.lt_or_ge bY.toNat (2 ^ 31) with hcy | hcy
  · rw [show bx.msb = false by rw [hmx]; simp; omega,
      show bY.msb = false by rw [hmy]; simp; omega]
    rw [if_pos (by omega), if_pos (by omega)]
    simp only [circuit_norm, hx, hy]
  · rw [show bx.msb = false by rw [hmx]; simp; omega,
      show bY.msb = true by rw [hmy]; simp; omega]
    rw [if_pos (by omega), if_neg (by omega)]
    simp only [circuit_norm, hx, hny]
  · rw [show bx.msb = true by rw [hmx]; simp; omega,
      show bY.msb = false by rw [hmy]; simp; omega]
    rw [if_neg (by omega), if_pos (by omega)]
    refine neg32U_toNat env _ ?_
    simp only [circuit_norm, hnx, hy, BitVec.toNat_umod]
  · rw [show bx.msb = true by rw [hmx]; simp; omega,
      show bY.msb = true by rw [hmy]; simp; omega]
    rw [if_neg (by omega), if_neg (by omega)]
    refine neg32U_toNat env _ ?_
    simp only [circuit_norm, hnx, hny, BitVec.toNat_umod]

/-- `low32U` is `setWidth 32` (embedded). -/
theorem low32U_toNat (x : Witgen.U64Expr (ZMod p)) {bx : BitVec 64}
    (hx : ((x.eval { env := env })).toNat = bx.toNat) :
    ((low32U x).eval { env := env }).toNat = (bx.setWidth 32).toNat := by
  simp only [low32U, circuit_norm, hx, BitVec.toNat_setWidth]

/-- `sext32U` is `signExtend 64` of an embedded 32-bit value. -/
theorem sext32U_toNat (x : Witgen.U64Expr (ZMod p)) {bx : BitVec 32}
    (hx : ((x.eval { env := env })).toNat = bx.toNat) :
    ((sext32U x).eval { env := env }).toNat = (bx.signExtend 64).toNat := by
  have hlt := bx.isLt
  have hmx : bx.msb = decide (2 ^ 31 ≤ bx.toNat) := BitVec.msb_eq_decide bx
  rw [BitVec.toNat_signExtend, BitVec.toNat_setWidth]
  simp only [sext32U, circuit_norm, hx]
  rcases Nat.lt_or_ge bx.toNat (2 ^ 31) with hcase | hcase
  · rw [if_pos (by omega), show bx.msb = false by rw [hmx]; simp; omega]
    simp only [if_neg Bool.false_ne_true]
    omega
  · rw [if_neg (by omega), show bx.msb = true by rw [hmx]; simp; omega, if_pos rfl]
    simp only [circuit_norm, hx]

end IRCalculusEval

section WordAndFlags

/-- The u64 pack of a committed word (`Word.toBitVec64`'s value as IR). -/
def wordU (b : Word (Expression (ZMod p))) : Witgen.U64Expr (ZMod p) :=
  Witgen.U64Expr.val (.expr b[0]) + Witgen.U64Expr.val (.expr b[1]) * 65536
    + Witgen.U64Expr.val (.expr b[2]) * 4294967296
    + Witgen.U64Expr.val (.expr b[3]) * 281474976710656

/-- The seven hinted flag leaves (`[div, rem, remu, divw, remw, divuw, remuw]`). -/
def hintF (k : Fin 7) : Witgen.FExpr (ZMod p) := .hintGet "div_rem_flags" 7 0 k

/-- The eight derived variant flags, mirroring `hintFlags`' encoding (`is_divu` is
`1 − Σ(the seven)`; the IR has no subtraction, so the complement is `1 + (−1)·Σ`). -/
def flagF : ℕ → Witgen.FExpr (ZMod p)
  | 0 => hintF 0
  | 1 => .const (1 : ZMod p) + .const (-1 : ZMod p)
      * ((hintF 0 : Witgen.FExpr (ZMod p)) + hintF 1 + hintF 2 + hintF 3 + hintF 4
        + hintF 5 + hintF 6)
  | 2 => hintF 1
  | 3 => hintF 2
  | 4 => hintF 3
  | 5 => hintF 4
  | 6 => hintF 5
  | 7 => hintF 6
  | _ => 0

end WordAndFlags

section WordAndFlagsEval

omit [Fact (2 ^ 24 < p)]

variable (env : ProverEnvironment (ZMod p))

/-- Evaluating a derived flag is the `hintFlags` accessor cell. -/
theorem flagF_eval (k : ℕ) (hk : k < 8) :
    Witgen.FExpr.eval { env := env } (flagF k) = (hintFlags env.hint)[k]'hk := by
  have hdefault : (default : Vector (ZMod p) 7) = #v[0, 0, 0, 0, 0, 0, 0] := rfl
  interval_cases k <;>
    (simp only [flagF, hintF, hintFlags, circuit_norm, ← hdefault, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ]
     try ring)

end WordAndFlagsEval

section WordEvalP

omit [Fact (2 ^ 24 < p)]

variable (env : ProverEnvironment (ZMod p))

/-- Evaluating the word pack is `Word.toBitVec64`'s value (the limb bounds keep every term and
the sum below `2^64`). -/
theorem wordU_toNat (b : Word (Expression (ZMod p))) (vB : Word (ZMod p))
    (hW : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment b[i] = vB[i])
    (hU : vB.isU64) :
    ((wordU b).eval { env := env }).toNat = (Word.toBitVec64 vB).toNat := by
  obtain ⟨u0, u1, u2, u3⟩ := Word.lt_cases_of_isU64 hU
  have h0 := hW 0 (by omega); have h1 := hW 1 (by omega)
  have h2 := hW 2 (by omega); have h3 := hW 3 (by omega)
  rw [Word.toBitVec64_toNat hU, Word.toNat_def]
  simp only [wordU, circuit_norm, h0, h1, h2, h3]
  omega

end WordEvalP

section Dispatch

/-- RISC-V's divide-by-zero quotient (`allOnes 64`). -/
def allOnesU : Witgen.U64Expr (ZMod p) := (18446744073709551615 : Witgen.U64Expr (ZMod p))

/-- The quotient bit pattern as IR (`quotBits`' dispatch verbatim: the W-classes divide the
embedded low 32 bits and sign-extend, divisor-zero gives `allOnes`). -/
def quotBitsU (b c : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  .ite (((flagF 4 : Witgen.FExpr (ZMod p)) + flagF 5) =? (1 : ZMod p))
    (.ite (low32U c =? (0 : ℕ)) allOnesU (sext32U (sdiv32U (low32U b) (low32U c))))
    (.ite (((flagF 6 : Witgen.FExpr (ZMod p)) + flagF 7) =? (1 : ZMod p))
      (.ite (low32U c =? (0 : ℕ)) allOnesU (sext32U (low32U b / low32U c)))
      (.ite (((flagF 0 : Witgen.FExpr (ZMod p)) + flagF 2) =? (1 : ZMod p))
        (.ite (c =? (0 : ℕ)) allOnesU (sdivU b c))
        (.ite (c =? (0 : ℕ)) allOnesU (b / c))))

/-- The remainder bit pattern as IR (`remBits`' dispatch: divisor-zero gives the sign-extended
low-32 dividend on the W-classes, the dividend itself on the 64-bit ones). -/
def remBitsU (b c : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  .ite (((flagF 4 : Witgen.FExpr (ZMod p)) + flagF 5) =? (1 : ZMod p))
    (.ite (low32U c =? (0 : ℕ)) (sext32U (low32U b))
      (sext32U (srem32U (low32U b) (low32U c))))
    (.ite (((flagF 6 : Witgen.FExpr (ZMod p)) + flagF 7) =? (1 : ZMod p))
      (.ite (low32U c =? (0 : ℕ)) (sext32U (low32U b))
        (sext32U (low32U b % low32U c)))
      (.ite (((flagF 0 : Witgen.FExpr (ZMod p)) + flagF 2) =? (1 : ZMod p))
        (.ite (c =? (0 : ℕ)) b (sremU b c))
        (.ite (c =? (0 : ℕ)) b (b % c))))

end Dispatch

section DispatchEval

variable (env : ProverEnvironment (ZMod p))

/-- Evaluating the quotient dispatch is `quotBits` (of the evaluated words and the hint flags). -/
theorem quotBitsU_toNat (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
    (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
    (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
    (hUB : vB.isU64) (hUC : vC.isU64) :
    ((quotBitsU (wordU B) (wordU C)).eval { env := env }).toNat
      = (quotBits vB vC (hintFlags env.hint)).toNat := by
  have hb := wordU_toNat env B vB hWB hUB
  have hc := wordU_toNat env C vC hWC hUC
  have hlo32b := low32U_toNat env (wordU B) hb
  have hlo32c := low32U_toNat env (wordU C) hc
  have hf4 := flagF_eval env 4 (by omega)
  have hf5 := flagF_eval env 5 (by omega)
  have hf6 := flagF_eval env 6 (by omega)
  have hf7 := flagF_eval env 7 (by omega)
  have hf0 := flagF_eval env 0 (by omega)
  have hf2 := flagF_eval env 2 (by omega)
  have hzc32 : (BitVec.setWidth 32 vC.toBitVec64 = 0)
      ↔ ((BitVec.setWidth 32 vC.toBitVec64).toNat = 0) := by
    rw [← BitVec.toNat_inj]
    simp
  have hzc64 : (vC.toBitVec64 = 0) ↔ (vC.toBitVec64.toNat = 0) := by
    rw [← BitVec.toNat_inj]
    simp
  simp only [quotBitsU, quotBits, circuit_norm, hf4, hf5, hf6, hf7, hf0, hf2, hlo32c,
    hc, hzc32, hzc64]
  split_ifs
  · simp only [allOnesU, circuit_norm, BitVec.toNat_allOnes]
  · exact sext32U_toNat env _ (sdiv32U_toNat env _ _ hlo32b hlo32c)
  · simp only [allOnesU, circuit_norm, BitVec.toNat_allOnes]
  · refine sext32U_toNat env _ ?_
    simp only [circuit_norm, hlo32b, hlo32c, BitVec.udiv_eq, BitVec.toNat_udiv]
  · simp only [allOnesU, circuit_norm, BitVec.toNat_allOnes]
  · exact sdivU_toNat env _ _ hb hc
  · simp only [allOnesU, circuit_norm, BitVec.toNat_allOnes]
  · simp only [circuit_norm, hb, hc, BitVec.udiv_eq, BitVec.toNat_udiv]

/-- Evaluating the remainder dispatch is `remBits`. -/
theorem remBitsU_toNat (B C : Word (Expression (ZMod p))) (vB vC : Word (ZMod p))
    (hWB : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment B[i] = vB[i])
    (hWC : ∀ (i : ℕ) (_ : i < 4), Expression.eval env.toEnvironment C[i] = vC[i])
    (hUB : vB.isU64) (hUC : vC.isU64) :
    ((remBitsU (wordU B) (wordU C)).eval { env := env }).toNat
      = (remBits vB vC (hintFlags env.hint)).toNat := by
  have hb := wordU_toNat env B vB hWB hUB
  have hc := wordU_toNat env C vC hWC hUC
  have hlo32b := low32U_toNat env (wordU B) hb
  have hlo32c := low32U_toNat env (wordU C) hc
  have hf4 := flagF_eval env 4 (by omega)
  have hf5 := flagF_eval env 5 (by omega)
  have hf6 := flagF_eval env 6 (by omega)
  have hf7 := flagF_eval env 7 (by omega)
  have hf0 := flagF_eval env 0 (by omega)
  have hf2 := flagF_eval env 2 (by omega)
  have hzc32 : (BitVec.setWidth 32 vC.toBitVec64 = 0)
      ↔ ((BitVec.setWidth 32 vC.toBitVec64).toNat = 0) := by
    rw [← BitVec.toNat_inj]
    simp
  have hzc64 : (vC.toBitVec64 = 0) ↔ (vC.toBitVec64.toNat = 0) := by
    rw [← BitVec.toNat_inj]
    simp
  simp only [remBitsU, remBits, circuit_norm, hf4, hf5, hf6, hf7, hf0, hf2, hlo32c,
    hc, hzc32, hzc64]
  split_ifs
  · exact sext32U_toNat env _ hlo32b
  · exact sext32U_toNat env _ (srem32U_toNat env _ _ hlo32b hlo32c)
  · exact sext32U_toNat env _ hlo32b
  · refine sext32U_toNat env _ ?_
    have e1 : Witgen.U64Expr.eval { env := env } ((low32U (wordU B)).mod (low32U (wordU C)))
        = Witgen.U64Expr.eval { env := env } (low32U (wordU B))
          % Witgen.U64Expr.eval { env := env } (low32U (wordU C)) := rfl
    rw [e1, UInt64.toNat_mod, hlo32b, hlo32c, BitVec.umod_eq, BitVec.toNat_umod]
  · exact hb
  · exact sremU_toNat env _ _ hb hc
  · exact hb
  · rw [UInt64.toNat_mod, hb, hc, BitVec.umod_eq, BitVec.toNat_umod]

end DispatchEval

end SP1Clean.DivRemChip
