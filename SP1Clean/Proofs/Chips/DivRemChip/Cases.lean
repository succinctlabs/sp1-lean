import SP1Clean.FormalModel.Contracts.DivRem
import SP1Clean.Proofs.Chips.DivRemChip.Math

/-! # `DivRemChip` — isolated arithmetic case proofs

This is the lightweight proof layer between SP1's row constraints and the public `DivRemContract`.
It deliberately imports neither the chip circuit nor Clean's circuit elaborator.  A future
constraint proof should extract one of the evidence predicates below from a real row; the theorems
in this file then establish the ISA result without seeing column offsets, subcircuit witnesses, or
interaction requirements.

The split is by four quotient/remainder families, not eight instructions.  Division and remainder
share all arithmetic and differ only in the final `RoutedEvidence` equality selecting one half of the
pair.  Signed exceptional cases are explicit constructors, so divide-by-zero and overflow cannot be
silently hidden in side assumptions.
-/

namespace SP1Clean.DivRemChip.Cases

open SP1Clean.DivRemContract

/-! ## Pure family evidence -/

/-- Euclidean evidence for the 64-bit unsigned family. -/
structure Unsigned64Evidence (rs1 rs2 quotient remainder : BitVec 64) : Prop where
  identity : rs1.toNat = rs2.toNat * quotient.toNat + remainder.toNat
  remainder_lt : rs2.toNat ≠ 0 → remainder.toNat < rs2.toNat
  divisor_zero : rs2.toNat = 0 →
    quotient.toNat = 2 ^ 64 - 1 ∧ remainder.toNat = rs1.toNat

/-- The unsigned Euclidean evidence determines both `DIVU` and `REMU`. -/
theorem Unsigned64Evidence.sound {rs1 rs2 quotient remainder : BitVec 64}
    (h : Unsigned64Evidence rs1 rs2 quotient remainder) :
    PairSpec .unsigned64 rs1 rs2 quotient remainder := by
  simpa [PairSpec, Family.result, RV64.divu, RV64.remu] using
    udiv_umod_bitvec h.identity h.remainder_lt h.divisor_zero

/-- The three semantically distinct branches of signed 64-bit division. -/
inductive Signed64Evidence (rs1 rs2 quotient remainder : BitVec 64) : Prop where
  | normal
      (divisor_ne_zero : rs2 ≠ 0#64)
      (identity : rs1.toInt = rs2.toInt * quotient.toInt + remainder.toInt)
      (remainder_lt : remainder.toInt.natAbs < rs2.toInt.natAbs)
      (remainder_nonneg : 0 ≤ rs1.toInt → 0 ≤ remainder.toInt)
      (remainder_nonpos : rs1.toInt ≤ 0 → remainder.toInt ≤ 0)
  | divisorZero
      (divisor_zero : rs2 = 0#64)
      (quotient_eq : quotient = -1#64)
      (remainder_eq : remainder = rs1)
  | overflow
      (dividend_eq : rs1 = BitVec.intMin 64)
      (divisor_eq : rs2 = -1#64)
      (quotient_eq : quotient = rs1)
      (remainder_eq : remainder = 0#64)

/-- Each explicit signed-64 branch determines both `DIV` and `REM`. -/
theorem Signed64Evidence.sound {rs1 rs2 quotient remainder : BitVec 64}
    (h : Signed64Evidence rs1 rs2 quotient remainder) :
    PairSpec .signed64 rs1 rs2 quotient remainder := by
  cases h with
  | normal hc hid hlt hpos hneg =>
      simpa [PairSpec, Family.result] using div_rem_of_identity hc hid hlt hpos hneg
  | divisorZero hc hq hr =>
      simpa [PairSpec, Family.result] using div_rem_divzero hc hq hr
  | overflow hb hc hq hr =>
      simpa [PairSpec, Family.result] using div_rem_overflow hb hc hq hr

/-- Euclidean evidence for the low-32 unsigned family.  The architectural 64-bit result is the sign
extension of `quotient` or `remainder`, exactly as required by `DIVUW`/`REMUW`. -/
structure Unsigned32Evidence
    (rs1 rs2 : BitVec 64) (quotient remainder : BitVec 32) : Prop where
  identity : (BitVec.extractLsb 31 0 rs1).toNat =
    (BitVec.extractLsb 31 0 rs2).toNat * quotient.toNat + remainder.toNat
  remainder_lt : (BitVec.extractLsb 31 0 rs2).toNat ≠ 0 →
    remainder.toNat < (BitVec.extractLsb 31 0 rs2).toNat
  divisor_zero : (BitVec.extractLsb 31 0 rs2).toNat = 0 →
    quotient.toNat = 2 ^ 32 - 1 ∧
      remainder.toNat = (BitVec.extractLsb 31 0 rs1).toNat

/-- The unsigned low-32 evidence determines both `DIVUW` and `REMUW`. -/
theorem Unsigned32Evidence.sound {rs1 rs2 : BitVec 64} {quotient remainder : BitVec 32}
    (h : Unsigned32Evidence rs1 rs2 quotient remainder) :
    PairSpec .unsigned32 rs1 rs2 (BitVec.signExtend 64 quotient)
      (BitVec.signExtend 64 remainder) := by
  simpa [PairSpec, Family.result] using
    divuw_remuw_of_identity h.identity h.remainder_lt h.divisor_zero

/-- The three semantically distinct branches of signed low-32 division. -/
inductive Signed32Evidence
    (rs1 rs2 : BitVec 64) (quotient remainder : BitVec 32) : Prop where
  | normal
      (divisor_ne_zero : BitVec.extractLsb 31 0 rs2 ≠ 0#32)
      (identity : (BitVec.extractLsb 31 0 rs1).toInt =
        (BitVec.extractLsb 31 0 rs2).toInt * quotient.toInt + remainder.toInt)
      (remainder_lt : remainder.toInt.natAbs <
        (BitVec.extractLsb 31 0 rs2).toInt.natAbs)
      (remainder_nonneg : 0 ≤ (BitVec.extractLsb 31 0 rs1).toInt → 0 ≤ remainder.toInt)
      (remainder_nonpos : (BitVec.extractLsb 31 0 rs1).toInt ≤ 0 → remainder.toInt ≤ 0)
  | divisorZero
      (divisor_zero : BitVec.extractLsb 31 0 rs2 = 0#32)
      (quotient_eq : quotient = -1#32)
      (remainder_eq : remainder = BitVec.extractLsb 31 0 rs1)
  | overflow
      (dividend_eq : BitVec.extractLsb 31 0 rs1 = BitVec.intMin 32)
      (divisor_eq : BitVec.extractLsb 31 0 rs2 = -1#32)
      (quotient_eq : quotient = BitVec.extractLsb 31 0 rs1)
      (remainder_eq : remainder = 0#32)

/-- Each explicit signed low-32 branch determines both `DIVW` and `REMW`. -/
theorem Signed32Evidence.sound {rs1 rs2 : BitVec 64} {quotient remainder : BitVec 32}
    (h : Signed32Evidence rs1 rs2 quotient remainder) :
    PairSpec .signed32 rs1 rs2 (BitVec.signExtend 64 quotient)
      (BitVec.signExtend 64 remainder) := by
  cases h with
  | normal hc hid hlt hpos hneg =>
      simpa [PairSpec, Family.result] using divw_remw_of_identity hc hid hlt hpos hneg
  | divisorZero hc hq hr =>
      simpa [PairSpec, Family.result] using divw_remw_divzero hc hq hr
  | overflow hb hc hq hr =>
      simpa [PairSpec, Family.result] using divw_remw_overflow hb hc hq hr

/-! ## Uniform family and row routing -/

/-- Uniform evidence consumed by the chip integration proof.  Word variants retain their native
32-bit quotient/remainder witnesses and expose only their sign-extended architectural results. -/
def FamilyEvidence (family : Family) (rs1 rs2 quotient remainder : BitVec 64) : Prop :=
  match family with
  | .signed64 => Signed64Evidence rs1 rs2 quotient remainder
  | .unsigned64 => Unsigned64Evidence rs1 rs2 quotient remainder
  | .signed32 => ∃ quotient32 remainder32 : BitVec 32,
      quotient = BitVec.signExtend 64 quotient32 ∧
      remainder = BitVec.signExtend 64 remainder32 ∧
      Signed32Evidence rs1 rs2 quotient32 remainder32
  | .unsigned32 => ∃ quotient32 remainder32 : BitVec 32,
      quotient = BitVec.signExtend 64 quotient32 ∧
      remainder = BitVec.signExtend 64 remainder32 ∧
      Unsigned32Evidence rs1 rs2 quotient32 remainder32

/-- Uniform family evidence establishes the stable semantic pair contract. -/
theorem FamilyEvidence.sound {family : Family} {rs1 rs2 quotient remainder : BitVec 64}
    (h : FamilyEvidence family rs1 rs2 quotient remainder) :
    PairSpec family rs1 rs2 quotient remainder := by
  cases family with
  | signed64 => exact Signed64Evidence.sound h
  | unsigned64 => exact Unsigned64Evidence.sound h
  | signed32 =>
      obtain ⟨quotient32, remainder32, rfl, rfl, hcase⟩ := h
      exact Signed32Evidence.sound hcase
  | unsigned32 =>
      obtain ⟨quotient32, remainder32, rfl, rfl, hcase⟩ := h
      exact Unsigned32Evidence.sound hcase

/-- Arithmetic evidence plus the chip's final output-routing equality for one selected opcode. -/
def RoutedEvidence (case : Case) (rs1 rs2 result : BitVec 64) : Prop :=
  ∃ quotient remainder,
    FamilyEvidence case.family rs1 rs2 quotient remainder ∧
      result = case.output.pick quotient remainder

/-- Routed family evidence establishes the selected opcode's result. -/
theorem RoutedEvidence.sound {case : Case} {rs1 rs2 result : BitVec 64}
    (h : RoutedEvidence case rs1 rs2 result) : result = case.result rs1 rs2 := by
  obtain ⟨quotient, remainder, hfamily, rfl⟩ := h
  simpa [Case.result] using (FamilyEvidence.sound hfamily).pick case.output

/-- Evidence-shaped replacement for a raw per-op circuit proof.  The heavy integration layer only
needs to establish this implication from the selected row's constraints. -/
def EvidenceSpec {p : ℕ} [NeZero p] (case : Case) (isReal : ZMod p)
    (rs1 rs2 result : Word (ZMod p)) (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  isReal = 1 → case.flag cols = 1 →
    RoutedEvidence case (Word.toBitVec64 rs1) (Word.toBitVec64 rs2) (Word.toBitVec64 result)

/-- Isolated evidence closes the public semantic case contract. -/
theorem EvidenceSpec.sound {p : ℕ} [NeZero p] {case : Case} {isReal : ZMod p}
    {rs1 rs2 result : Word (ZMod p)} {cols : DivRemChip.Columns (ZMod p)}
    (h : EvidenceSpec case isReal rs1 rs2 result cols) :
    CaseSpec case isReal rs1 rs2 result cols :=
  fun hreal hflag => (h hreal hflag).sound

/-- Evidence for all cases, in the same uniform shape as `DivRemContract.CasesSpec`. -/
def EvidenceSpecs {p : ℕ} [NeZero p] (isReal : ZMod p)
    (rs1 rs2 result : Word (ZMod p)) (cols : DivRemChip.Columns (ZMod p)) : Prop :=
  ∀ case, EvidenceSpec case isReal rs1 rs2 result cols

/-- Once evidence extraction is complete, all eight public case obligations follow immediately. -/
theorem EvidenceSpecs.sound {p : ℕ} [NeZero p] {isReal : ZMod p}
    {rs1 rs2 result : Word (ZMod p)} {cols : DivRemChip.Columns (ZMod p)}
    (h : EvidenceSpecs isReal rs1 rs2 result cols) :
    CasesSpec isReal rs1 rs2 result cols :=
  fun case => (h case).sound

/-- Evidence-shaped row contract exported to the full circuit proof.  Selection and gate
booleanness are structural facts; arithmetic remains in the uniformly isolated `EvidenceSpecs`. -/
structure RowEvidence {p : ℕ} [NeZero p] (isReal : ZMod p)
    (rs1 rs2 result : Word (ZMod p)) (cols : DivRemChip.Columns (ZMod p)) : Prop where
  isReal_binary : isReal = 0 ∨ isReal = 1
  selection : SelectionSpec isReal cols
  cases : EvidenceSpecs isReal rs1 rs2 result cols

/-- The evidence-shaped row interface refines the stable public row contract. -/
theorem RowEvidence.sound {p : ℕ} [NeZero p] {isReal : ZMod p}
    {rs1 rs2 result : Word (ZMod p)} {cols : DivRemChip.Columns (ZMod p)}
    (h : RowEvidence isReal rs1 rs2 result cols) :
    RowSpec isReal rs1 rs2 result cols :=
  ⟨h.isReal_binary, h.selection, h.cases.sound⟩

end SP1Clean.DivRemChip.Cases
