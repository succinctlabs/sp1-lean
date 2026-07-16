import SP1Clean.Extracted.DivRemChip
import SP1Clean.Math.Word
import RISCV.Instructions

/-! # The semantic contract of SP1's combined divide/remainder chip

This module is deliberately independent of the chip circuit and its proof decomposition.  It is the
stable target for both sides of verification:

* the generated SP1 row selects exactly one of the eight committed cases;
* an isolated arithmetic proof establishes `CaseSpec` for each case; and
* the whole-chip proof shows that its constraints implement `RowSpec`.

Division by zero and signed overflow are not side assumptions.  They are already specified by the
corresponding `RV64` functions and therefore remain visible at this boundary.
-/

namespace SP1Clean.DivRemContract

open Extracted (DivRemCols)

/-- The eight instructions implemented by SP1's single `DivRemChip`. -/
inductive Case where
  | div
  | divu
  | rem
  | remu
  | divw
  | remw
  | divuw
  | remuw
deriving DecidableEq, Repr

/-- The four arithmetic families shared by quotient and remainder instructions.  Keeping this split
explicit lets the expensive circuit proof establish one quotient/remainder pair and then route the
selected half, instead of repeating the same arithmetic in eight opcode proofs. -/
inductive Family where
  | signed64
  | unsigned64
  | signed32
  | unsigned32
deriving DecidableEq, Repr

/-- Which member of a quotient/remainder pair an instruction returns. -/
inductive Output where
  | quotient
  | remainder
deriving DecidableEq, Repr

/-- Arithmetic family implemented by an instruction case. -/
def Case.family : Case → Family
  | .div | .rem => .signed64
  | .divu | .remu => .unsigned64
  | .divw | .remw => .signed32
  | .divuw | .remuw => .unsigned32

/-- Half of the family result returned by an instruction case. -/
def Case.output : Case → Output
  | .div | .divu | .divw | .divuw => .quotient
  | .rem | .remu | .remw | .remuw => .remainder

/-- SP1's internal RISC-V opcode number for a divide/remainder case. -/
def Case.opcode : Case → ℕ
  | .div => 15
  | .divu => 16
  | .rem => 17
  | .remu => 18
  | .divw => 25
  | .remw => 27
  | .divuw => 26
  | .remuw => 28

/-- The committed selector column belonging to a case. -/
def Case.flag {F : Type} (case : Case) (cols : DivRemCols F) : F :=
  match case with
  | .div => cols.is_div
  | .divu => cols.is_divu
  | .rem => cols.is_rem
  | .remu => cols.is_remu
  | .divw => cols.is_divw
  | .remw => cols.is_remw
  | .divuw => cols.is_divuw
  | .remuw => cols.is_remuw

/-- ISA result for one half of an arithmetic family. Arguments are named in architectural order
(`rs1`, then `rs2`); the underlying RV64 helpers take `rs2` first. -/
def Family.result (family : Family) (output : Output) (rs1 rs2 : BitVec 64) : BitVec 64 :=
  match family, output with
  | .signed64, .quotient => RV64.div rs2 rs1
  | .signed64, .remainder => RV64.rem rs2 rs1
  | .unsigned64, .quotient => RV64.divu rs2 rs1
  | .unsigned64, .remainder => RV64.remu rs2 rs1
  | .signed32, .quotient => RV64.divw rs2 rs1
  | .signed32, .remainder => RV64.remw rs2 rs1
  | .unsigned32, .quotient => RV64.divuw rs2 rs1
  | .unsigned32, .remainder => RV64.remuw rs2 rs1

/-- ISA result of a case, factored through its family and selected output. -/
def Case.result (case : Case) (rs1 rs2 : BitVec 64) : BitVec 64 :=
  case.family.result case.output rs1 rs2

/-- Select a member of an already-established quotient/remainder pair. -/
def Output.pick (output : Output) (quotient remainder : BitVec 64) : BitVec 64 :=
  match output with
  | .quotient => quotient
  | .remainder => remainder

/-- Semantic target for an isolated family proof.  This is deliberately below `CaseSpec`: one
family proof establishes both results, while the chip constraints separately route the selected
result to `cols.a`. -/
def PairSpec (family : Family) (rs1 rs2 quotient remainder : BitVec 64) : Prop :=
  quotient = family.result .quotient rs1 rs2 ∧
    remainder = family.result .remainder rs1 rs2

/-- A family proof supplies whichever half an opcode selects. -/
theorem PairSpec.pick {family : Family} {rs1 rs2 quotient remainder : BitVec 64}
    (h : PairSpec family rs1 rs2 quotient remainder) (output : Output) :
    output.pick quotient remainder = family.result output rs1 rs2 := by
  cases output
  · exact h.1
  · exact h.2

/-- The flag-weighted opcode consumed by the R-type reader. -/
def encodedOpcode {p : ℕ} (cols : DivRemCols (ZMod p)) : ZMod p :=
  cols.is_divu * 16 + cols.is_remu * 18 + cols.is_div * 15 + cols.is_rem * 17
    + cols.is_divw * 25 + cols.is_remw * 27 + cols.is_divuw * 26 + cols.is_remuw * 28

/-- `case` is the unique selected instruction in the committed row.  Requiring every other flag to
be zero makes this useful independently of a particular algebraic one-hot encoding. -/
def Selected {p : ℕ} (cols : DivRemCols (ZMod p)) (case : Case) : Prop :=
  case.flag cols = 1 ∧ ∀ other, other ≠ case → other.flag cols = 0

/-- A real row commits to one (and, by `Selected`, only one) divide/remainder case. Padding rows are
not semantically constrained by this interface. -/
def SelectionSpec {p : ℕ} (isReal : ZMod p) (cols : DivRemCols (ZMod p)) : Prop :=
  isReal = 1 → ∃ case, Selected cols case

/-- The isolated semantic obligation for one instruction case. -/
def CaseSpec {p : ℕ} [NeZero p] (case : Case) (isReal : ZMod p)
    (rs1 rs2 result : Word (ZMod p)) (cols : DivRemCols (ZMod p)) : Prop :=
  isReal = 1 → case.flag cols = 1 →
    Word.toBitVec64 result = case.result (Word.toBitVec64 rs1) (Word.toBitVec64 rs2)

/-- All eight isolated case obligations, without choosing how they are proved. -/
def CasesSpec {p : ℕ} [NeZero p] (isReal : ZMod p) (rs1 rs2 result : Word (ZMod p))
    (cols : DivRemCols (ZMod p)) : Prop :=
  ∀ case, CaseSpec case isReal rs1 rs2 result cols

/-- Stable arithmetic/selection contract exported by the chip layer. Reader and bus behavior remain
separate chip-level obligations because they describe row plumbing, not division arithmetic. -/
structure RowSpec {p : ℕ} [NeZero p] (isReal : ZMod p) (rs1 rs2 result : Word (ZMod p))
    (cols : DivRemCols (ZMod p)) : Prop where
  isReal_binary : isReal = 0 ∨ isReal = 1
  selection : SelectionSpec isReal cols
  cases : CasesSpec isReal rs1 rs2 result cols

theorem Selected.unique {p : ℕ} [Fact p.Prime] {cols : DivRemCols (ZMod p)} {x y : Case}
    (hx : Selected cols x) (hy : Selected cols y) : x = y := by
  by_contra hxy
  have hy0 := hx.2 y (Ne.symm hxy)
  exact zero_ne_one (hy0.symm.trans hy.1)

/-- Pointwise normal form of a selected row's flags. -/
theorem Selected.flag_eq {p : ℕ} {cols : DivRemCols (ZMod p)} {case : Case}
    (h : Selected cols case) (other : Case) :
    other.flag cols = if other = case then 1 else 0 := by
  by_cases heq : other = case
  · subst other
    simp [h.1]
  · simp [heq, h.2 other heq]

/-- Selection reduces the flag-weighted reader opcode to the selected case's opcode. -/
theorem Selected.encodedOpcode {p : ℕ} [Fact p.Prime] {cols : DivRemCols (ZMod p)}
    {case : Case} (h : Selected cols case) :
    encodedOpcode cols = (case.opcode : ZMod p) := by
  have hdiv := h.flag_eq .div
  have hdivu := h.flag_eq .divu
  have hrem := h.flag_eq .rem
  have hremu := h.flag_eq .remu
  have hdivw := h.flag_eq .divw
  have hremw := h.flag_eq .remw
  have hdivuw := h.flag_eq .divuw
  have hremuw := h.flag_eq .remuw
  cases case <;>
    simp [Case.flag] at hdiv hdivu hrem hremu hdivw hremw hdivuw hremuw <;>
    simp [DivRemContract.encodedOpcode, Case.opcode, hdiv, hdivu, hrem, hremu, hdivw,
      hremw, hdivuw, hremuw]

/-- The selection contract really determines a unique instruction on every real row. -/
theorem SelectionSpec.existsUnique {p : ℕ} [Fact p.Prime] {isReal : ZMod p}
    {cols : DivRemCols (ZMod p)} (h : SelectionSpec isReal cols) (hr : isReal = 1) :
    ∃! case, Selected cols case := by
  obtain ⟨case, hcase⟩ := h hr
  exact ⟨case, hcase, fun other hother => Selected.unique hother hcase⟩

end SP1Clean.DivRemContract
