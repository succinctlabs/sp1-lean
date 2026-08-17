import SP1Clean.Proofs.Chips.DivRemChip.Populate.IRWord
import SP1Clean.Proofs.Chips.DivRemChip.Populate.Glue

/-! # `DivRemChip` — witness-IR `c_times_quotient` limbs (A7b)

The 128-bit product block as u64-sorted IR. The value layer (`ctqProd`/`ctqLimbNat`) takes the
sign-dispatched 128-bit product of the computational quotient and operand; the u64 sort cannot
hold 128 bits, so the IR computes the low and high 64-bit slices separately:

* the **low** four limbs read the wrapping 64-bit product directly (`ctqProd_setWidth`: the sign
  choice never reaches them);
* the **high** four limbs read `umulhU` — the textbook four-half decomposition of
  `⌊q·c / 2^64⌋` — plus, on the signed classes, the two's-complement correction
  `− msb(q)·c − msb(c)·q (mod 2^64)` spelled with `negU` (the standard `mulh`-from-`umulh`
  identity, proved here as `ctqProd_shift_toNat`).

Everything stays in the u64 sort; only the final `.toField` casts commit the limbs. -/

namespace SP1Clean.DivRemChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

section CtqIR

/-- The high 64 bits of the full 64×64 unsigned product (`⌊x·y / 2^64⌋`), by the textbook
four-half decomposition. Every intermediate stays below `2^64`. -/
def umulhU (x y : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  (x >>> 32) * (y >>> 32)
    + ((x >>> 32) * (y % 4294967296)) >>> 32
    + ((x % 4294967296) * (y >>> 32)) >>> 32
    + (((x % 4294967296) * (y % 4294967296)) >>> 32
        + ((x >>> 32) * (y % 4294967296)) % 4294967296
        + ((x % 4294967296) * (y >>> 32)) % 4294967296) >>> 32

/-- The high 64-bit slice of the sign-dispatched 128-bit product: `umulhU` on the unsigned
classes, minus the two's-complement corrections on the signed ones. -/
def ctqHiU (q c : Witgen.U64Expr (ZMod p)) : Witgen.U64Expr (ZMod p) :=
  .ite (((flagF 0 : Witgen.FExpr (ZMod p)) + flagF 2 + flagF 4 + flagF 5) =? (1 : ZMod p))
    (umulhU q c + negU ((q >>> 63) * c) + negU ((c >>> 63) * q))
    (umulhU q c)

/-- u16 limb `k` of the 128-bit product, u64-sorted: the wrapping low product for `k < 4`, the
`ctqHiU` slice above. -/
def ctqLimbU (q c : Witgen.U64Expr (ZMod p)) (k : ℕ) : Witgen.U64Expr (ZMod p) :=
  if k < 4 then (q * c) >>> (16 * k) % 65536
  else ctqHiU q c >>> (16 * (k - 4)) % 65536

end CtqIR

section CtqNat

/-- Half-width factors keep a product under the u64 wrap. -/
private lemma mul_lt_2p64 {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) : a * b < 2 ^ 64 :=
  calc a * b ≤ (2 ^ 32 - 1) * (2 ^ 32 - 1) := Nat.mul_le_mul (by omega) (by omega)
    _ < 2 ^ 64 := by norm_num

/-- The four-half decomposition computes the high word: for `a b < 2^64`,
`hh + hl' + lh' + mid' = a·b / 2^64` (primed terms are the shifted carries). -/
private lemma umulh_nat (a b : ℕ) (ha : a < 2 ^ 64) (hb : b < 2 ^ 64) :
    a / 2 ^ 32 * (b / 2 ^ 32)
      + a / 2 ^ 32 * (b % 2 ^ 32) / 2 ^ 32
      + a % 2 ^ 32 * (b / 2 ^ 32) / 2 ^ 32
      + (a % 2 ^ 32 * (b % 2 ^ 32) / 2 ^ 32
          + a / 2 ^ 32 * (b % 2 ^ 32) % 2 ^ 32
          + a % 2 ^ 32 * (b / 2 ^ 32) % 2 ^ 32) / 2 ^ 32
      = a * b / 2 ^ 64 := by
  have hsplit : a * b
      = a % 2 ^ 32 * (b % 2 ^ 32)
        + 2 ^ 32 * (a / 2 ^ 32 * (b % 2 ^ 32) + a % 2 ^ 32 * (b / 2 ^ 32))
        + 2 ^ 64 * (a / 2 ^ 32 * (b / 2 ^ 32)) := by
    conv_lhs => rw [← Nat.div_add_mod a (2 ^ 32), ← Nat.div_add_mod b (2 ^ 32)]
    ring
  have hll : a % 2 ^ 32 * (b % 2 ^ 32) < 2 ^ 64 := mul_lt_2p64 (by omega) (by omega)
  have hlh : a / 2 ^ 32 * (b % 2 ^ 32) < 2 ^ 64 := mul_lt_2p64 (by omega) (by omega)
  have hhl : a % 2 ^ 32 * (b / 2 ^ 32) < 2 ^ 64 := mul_lt_2p64 (by omega) (by omega)
  omega

end CtqNat

section CtqEval

variable (env : ProverEnvironment (ZMod p))

omit [Fact (2 ^ 24 < p)] in
/-- Evaluating the four-half decomposition is `⌊x·y / 2^64⌋` of the evaluated operands (no
intermediate wraps: halves are `< 2^32`, so every product and carry sum stays below `2^64`). -/
theorem umulhU_toNat (x y : Witgen.U64Expr (ZMod p)) {xv yv : ℕ}
    (hx : ((x.eval { env := env })).toNat = xv) (hy : ((y.eval { env := env })).toNat = yv) :
    ((umulhU x y).eval { env := env }).toNat = xv * yv / 2 ^ 64 := by
  have hxlt : xv < 2 ^ 64 := hx ▸ (x.eval { env := env }).toNat_lt
  have hylt : yv < 2 ^ 64 := hy ▸ (y.eval { env := env }).toNat_lt
  rw [← umulh_nat xv yv hxlt hylt]
  have hhi_x : xv / 2 ^ 32 < 2 ^ 32 := by omega
  have hhi_y : yv / 2 ^ 32 < 2 ^ 32 := by omega
  have hlo_x : xv % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hlo_y : yv % 2 ^ 32 < 2 ^ 32 := Nat.mod_lt _ (by norm_num)
  have hhh : xv / 2 ^ 32 * (yv / 2 ^ 32) ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hlh : xv / 2 ^ 32 * (yv % 2 ^ 32) ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hhl : xv % 2 ^ 32 * (yv / 2 ^ 32) ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  have hll : xv % 2 ^ 32 * (yv % 2 ^ 32) ≤ 4294967295 * 4294967295 :=
    Nat.mul_le_mul (by omega) (by omega)
  simp only [umulhU, circuit_norm, hx, hy, Nat.shiftRight_eq_div_pow,
    show (4294967296 : ℕ) = 2 ^ 32 from by norm_num]

/-- Evaluating a product limb is `ctqLimbNat` (of the raw operand words): the low four limbs read
the wrapping product (`ctqProd_setWidth`), the high four the `umulhU` slice with the signed
classes' two's-complement corrections — the `mulh`-from-`umulh` identity, discharged here per
sign case. -/
theorem ctqLimbU_toNat (q c : Witgen.U64Expr (ZMod p)) (B C : Word (ZMod p))
    (hq : ((q.eval { env := env })).toNat
      = (Word.toBitVec64 (populateQuotComp B C (hintFlags env.hint))).toNat)
    (hc : ((c.eval { env := env })).toNat
      = (Word.toBitVec64 (cComp C (hintFlags env.hint))).toNat)
    (k : ℕ) (hk : k < 8) :
    ((ctqLimbU q c k).eval { env := env }).toNat
      = ctqLimbNat B C (hintFlags env.hint) k := by
  -- opaque the two operand values (fvars, not `set` lets — the kernel must never unfold
  -- them back into the word terms inside the product congruences)
  obtain ⟨qN, hqN⟩ : ∃ n, (Word.toBitVec64 (populateQuotComp B C (hintFlags env.hint))).toNat = n :=
    ⟨_, rfl⟩
  obtain ⟨cN, hcN⟩ : ∃ n, (Word.toBitVec64 (cComp C (hintFlags env.hint))).toNat = n := ⟨_, rfl⟩
  rw [hqN] at hq
  rw [hcN] at hc
  have hqNlt : qN < 2 ^ 64 := hqN ▸ (Word.toBitVec64 (populateQuotComp B C (hintFlags env.hint))).isLt
  have hcNlt : cN < 2 ^ 64 := hcN ▸ (Word.toBitVec64 (cComp C (hintFlags env.hint))).isLt
  have hP128 : (ctqProd B C (hintFlags env.hint)).toNat < 2 ^ 128 :=
    (ctqProd B C (hintFlags env.hint)).isLt
  -- the low slice: `ctqProd` truncates to the wrapping product in every class
  have hlow : (ctqProd B C (hintFlags env.hint)).toNat % 2 ^ 64 = qN * cN % 2 ^ 64 := by
    have h := congrArg BitVec.toNat (ctqProd_setWidth B C (hintFlags env.hint))
    rw [BitVec.toNat_setWidth, BitVec.toNat_mul, hqN, hcN] at h
    exact h
  -- the high slice: the sign-dispatched `mulh` value
  have hhi : (ctqProd B C (hintFlags env.hint)).toNat / 2 ^ 64
      = if (hintFlags env.hint)[0] + (hintFlags env.hint)[2] + (hintFlags env.hint)[4]
          + (hintFlags env.hint)[5] = 1
        then (qN * cN / 2 ^ 64 + (2 ^ 64 - qN / 2 ^ 63 * cN % 2 ^ 64)
              + (2 ^ 64 - cN / 2 ^ 63 * qN % 2 ^ 64)) % 2 ^ 64
        else qN * cN / 2 ^ 64 := by
    have hmq : (Word.toBitVec64 (populateQuotComp B C (hintFlags env.hint))).msb
        = decide (2 ^ 63 ≤ qN) := hqN ▸ BitVec.msb_eq_decide _
    have hmc : (Word.toBitVec64 (cComp C (hintFlags env.hint))).msb
        = decide (2 ^ 63 ≤ cN) := hcN ▸ BitVec.msb_eq_decide _
    have hprod_le : qN * cN ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    unfold ctqProd
    split
    · -- signed classes: expand the sign extensions and case the two msbs
      show (BitVec.signExtend 128 (Word.toBitVec64 (populateQuotComp B C (hintFlags env.hint)))
            * BitVec.signExtend 128 (Word.toBitVec64 (cComp C (hintFlags env.hint)))).toNat
          / 2 ^ 64
          = (qN * cN / 2 ^ 64 + (2 ^ 64 - qN / 2 ^ 63 * cN % 2 ^ 64)
              + (2 ^ 64 - cN / 2 ^ 63 * qN % 2 ^ 64)) % 2 ^ 64
      rw [BitVec.toNat_mul, BitVec.toNat_signExtend, BitVec.toNat_signExtend,
        BitVec.toNat_setWidth_of_le (by norm_num), BitVec.toNat_setWidth_of_le (by norm_num),
        hmq, hmc]
      rcases Nat.lt_or_ge qN (2 ^ 63) with hq63 | hq63 <;>
        rcases Nat.lt_or_ge cN (2 ^ 63) with hc63 | hc63 <;>
        simp only [decide_eq_true_eq] <;>
        [rw [if_neg (by omega), if_neg (by omega)];
         rw [if_neg (by omega), if_pos (by omega)];
         rw [if_pos (by omega), if_neg (by omega)];
         rw [if_pos (by omega), if_pos (by omega)]] <;>
        simp only [Nat.add_mul, Nat.mul_add] <;>
        [rw [show qN / 2 ^ 63 = 0 from by omega, show cN / 2 ^ 63 = 0 from by omega];
         rw [show qN / 2 ^ 63 = 0 from by omega, show cN / 2 ^ 63 = 1 from by omega];
         rw [show qN / 2 ^ 63 = 1 from by omega, show cN / 2 ^ 63 = 0 from by omega];
         rw [show qN / 2 ^ 63 = 1 from by omega, show cN / 2 ^ 63 = 1 from by omega]] <;>
        simp only [Nat.zero_mul, Nat.one_mul, Nat.mul_zero, hqN, hcN] <;>
        omega
    · show (BitVec.setWidth 128 (Word.toBitVec64 (populateQuotComp B C (hintFlags env.hint)))
            * BitVec.setWidth 128 (Word.toBitVec64 (cComp C (hintFlags env.hint)))).toNat / 2 ^ 64
          = qN * cN / 2 ^ 64
      rw [BitVec.toNat_mul, BitVec.toNat_setWidth_of_le (by norm_num),
        BitVec.toNat_setWidth_of_le (by norm_num), hqN, hcN]
      omega
  rcases Nat.lt_or_ge k 4 with hk4 | hk4
  · -- low limbs: the wrapping 64-bit product
    rw [ctqLimbNat, show ctqLimbU q c k = (q * c) >>> (16 * k) % 65536 from if_pos hk4]
    have hpush : (((q * c) >>> (16 * k) % 65536 : Witgen.U64Expr (ZMod p)).eval
        { env := env }).toNat = qN * cN % 2 ^ 64 / 2 ^ (16 * k) % 65536 := by
      simp only [circuit_norm, hq, hc, Nat.shiftRight_eq_div_pow]
    rw [hpush]
    have : qN * cN % 2 ^ 64 / 2 ^ (16 * k) % 65536
        = (ctqProd B C (hintFlags env.hint)).toNat / 2 ^ (16 * k) % 65536 := by
      interval_cases k <;> omega
    rw [this]
    norm_num
  · -- high limbs: the `ctqHiU` slice
    rw [ctqLimbNat, show ctqLimbU q c k = ctqHiU q c >>> (16 * (k - 4)) % 65536
      from if_neg (by omega)]
    have hf0 := flagF_eval env 0 (by omega)
    have hf2 := flagF_eval env 2 (by omega)
    have hf4 := flagF_eval env 4 (by omega)
    have hf5 := flagF_eval env 5 (by omega)
    have hHiEval : ((ctqHiU q c).eval { env := env }).toNat
        = (ctqProd B C (hintFlags env.hint)).toNat / 2 ^ 64 := by
      rw [hhi]
      have hmq01 : qN / 2 ^ 63 = 0 ∨ qN / 2 ^ 63 = 1 := by omega
      have hmc01 : cN / 2 ^ 63 = 0 ∨ cN / 2 ^ 63 = 1 := by omega
      have hH := umulhU_toNat env q c hq hc
      simp only [ctqHiU, circuit_norm, hf0, hf2, hf4, hf5]
      split_ifs
      · -- signed: the wrapping correction chain
        simp only [negU, circuit_norm, hq, hc, Nat.shiftRight_eq_div_pow, hH]
        have hprod_div : qN * cN / 2 ^ 64 < 2 ^ 64 := by
          have hpl : qN * cN ≤ (2 ^ 64 - 1) * (2 ^ 64 - 1) :=
            Nat.mul_le_mul (by omega) (by omega)
          omega
        rcases hmq01 with hmq | hmq <;> rcases hmc01 with hmc | hmc <;>
          rw [hmq, hmc] <;> omega
      · exact hH
  -- assemble: shift the high value into the limb
    have hpush : ((ctqHiU q c >>> (16 * (k - 4)) % 65536 : Witgen.U64Expr (ZMod p)).eval
        { env := env }).toNat
        = (ctqProd B C (hintFlags env.hint)).toNat / 2 ^ 64 / 2 ^ (16 * (k - 4)) % 65536 := by
      simp only [circuit_norm, hHiEval, Nat.shiftRight_eq_div_pow]
    rw [hpush]
    have : (ctqProd B C (hintFlags env.hint)).toNat / 2 ^ 64 / 2 ^ (16 * (k - 4)) % 65536
        = (ctqProd B C (hintFlags env.hint)).toNat / 2 ^ (16 * k) % 65536 := by
      rw [Nat.div_div_eq_div_mul, ← pow_add, show 64 + 16 * (k - 4) = 16 * k from by omega]
    rw [this]
    norm_num

/-- The committed limb cell: the u64 limb cast to the field sort. -/
def ctqLimbF (q c : Witgen.U64Expr (ZMod p)) (k : ℕ) : Witgen.FExpr (ZMod p) :=
  (ctqLimbU q c k).toField

/-- Evaluating a committed limb cell is the corresponding `populateCtq` cell. -/
theorem ctqLimbF_eval (q c : Witgen.U64Expr (ZMod p)) (B C : Word (ZMod p))
    (hq : ((q.eval { env := env })).toNat
      = (Word.toBitVec64 (populateQuotComp B C (hintFlags env.hint))).toNat)
    (hc : ((c.eval { env := env })).toNat
      = (Word.toBitVec64 (cComp C (hintFlags env.hint))).toNat)
    (k : ℕ) (hk : k < 8) :
    ((ctqLimbF q c k).eval { env := env })
      = (populateCtq B C (hintFlags env.hint))[k] := by
  have h := ctqLimbU_toNat env q c B C hq hc k hk
  simp only [ctqLimbF, circuit_norm, FiniteField.fromNat, h, populateCtq, Vector.getElem_ofFn]

end CtqEval

end SP1Clean.DivRemChip
