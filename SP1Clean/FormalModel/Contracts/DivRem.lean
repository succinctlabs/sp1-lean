import SP1Clean.Extracted.DivRemChip
import SP1Clean.Math.Word
import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Proofs.Operations.IsEqualWordOperation.Formal
import SP1Clean.Proofs.Operations.LtOperationUnsigned.Formal
import SP1Clean.Proofs.Operations.MulOperation.Formal
import SP1Clean.Native.Operations.DivRemOperation.OwnAsserts
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

namespace SP1Clean.DivRemCompare

open SP1Clean.Extracted (DivRemCols)

/-- The semantic evidence certified by the DivRem row's **comparison/sign assertion cluster**
(`Native/Operations/DivRemOperation/Compare.lean`): the conjunction of the fifteen composed
sub-operations' semantic `Spec`s, instantiated at the committed `DivRemCols` fields and gated
exactly as the chip gates them (`is_real_not_word` / the word-variant sum `e2` / `is_real` /
`abs_c_alu_event` / `abs_rem_alu_event` / `remainder_check_multiplicity`).

Each conjunct is the exact hypothesis shape the evidence-extraction layer consumes
(`Proofs/Chips/DivRemChip/Extract.lean`: `overflow_of_iseqword`/`overflow_of_iseqword_word` take
the four `IsEqualWordOperation.Spec`s, the divide-by-zero readout takes the
`IsZeroWordOperation.Spec`, and the `Cases.lean` evidence families take the two `AddOperation`
negation identities, the `LtOperationUnsigned` range fact, and the seven `U16MSBOperation` sign
bits via each op's `result_semantic`), so chip-level assembly is pure plumbing. Per the
semantic-not-structural principle, no constraint equation is restated here — the sub-operations'
own `Spec`s are the semantic currency. -/
def CompareSpec {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] (cols : DivRemCols (ZMod p)) : Prop :=
  let bpv := cols.adapter.op_b_memory.prev_value
  let cpv := cols.adapter.op_c_memory.prev_value
  let irnw := cols.is_real_not_word
  let e2 := cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw
  -- (1-4) signed-overflow detection: `b` vs `i64::MIN`, `c` vs `-1` — full-word @ `irnw`,
  -- low-half @ `e2`.
  IsEqualWordOperation.Spec
    ⟨#v[bpv[0], bpv[1], bpv[2], bpv[3]], #v[0, 0, 0, 32768], cols.is_overflow_b, irnw⟩ ∧
  IsEqualWordOperation.Spec
    ⟨#v[cpv[0], cpv[1], cpv[2], cpv[3]], #v[65535, 65535, 65535, 65535],
     cols.is_overflow_c, irnw⟩ ∧
  IsEqualWordOperation.Spec
    ⟨#v[bpv[0], bpv[1], 0, 0], #v[0, 32768, 0, 0], cols.is_overflow_b, e2⟩ ∧
  IsEqualWordOperation.Spec
    ⟨#v[cpv[0], cpv[1], 0, 0], #v[65535, 65535, 0, 0], cols.is_overflow_c, e2⟩ ∧
  -- (5) divide-by-zero detection on the committed operand `c`.
  IsZeroWordOperation.Spec ⟨cols.c, cols.is_c_0, cols.is_real⟩ ∧
  -- (6-7) the `|c|` and `|remainder|` two's-complement negation identities.
  AddOperation.Spec
    ⟨cols.c, cols.abs_c, ⟨cols.c_neg_operation.value⟩, cols.abs_c_alu_event⟩ ∧
  AddOperation.Spec
    ⟨cols.remainder_comp, cols.abs_remainder, ⟨cols.rem_neg_operation.value⟩,
     cols.abs_rem_alu_event⟩ ∧
  -- (8) the Euclidean remainder range comparison `|remainder| < max(|c|, 1)`.
  LtOperationUnsigned.Spec
    ⟨cols.abs_remainder, cols.max_abs_c_or_1, cols.remainder_lt_operation,
     cols.remainder_check_multiplicity⟩ ∧
  -- (9-15) sign-bit extractions: b/c/remainder high u16 (@ `irnw`), b/c/remainder/quotient
  -- low-half-high u16 (@ `e2`).
  U16MSBOperation.Spec ⟨bpv[3], cols.b_msb, irnw⟩ ∧
  U16MSBOperation.Spec ⟨cpv[3], cols.c_msb, irnw⟩ ∧
  U16MSBOperation.Spec ⟨cols.remainder[3], cols.rem_msb, irnw⟩ ∧
  U16MSBOperation.Spec ⟨bpv[1], cols.b_msb, e2⟩ ∧
  U16MSBOperation.Spec ⟨cpv[1], cols.c_msb, e2⟩ ∧
  U16MSBOperation.Spec ⟨cols.remainder[1], cols.rem_msb, e2⟩ ∧
  U16MSBOperation.Spec ⟨cols.quotient[1], cols.quot_msb, e2⟩

end SP1Clean.DivRemCompare

namespace SP1Clean.DivRemCore

open SP1Clean.Extracted (DivRemCols)

/-- The DivRem row's own assertZero tail, **as evaluated field equations**: every entry of the
`DivRemChip.ownAsserts` chain (the `[E13…E367, adapter.op_a_0]` list, whose carrier-generic body is
here instantiated at `R = ZMod p`) is zero on the committed row.

This is the `DivRemCore` contract's one **deliberately-raw** component: it is exactly the content
the `assertZeros (ownAsserts cols)` block of the gadget's `main` contributes to `h_holds` (each
constraint expression evaluates to `0`), transported to the evaluated row by
`DivRemCore.ownAsserts_map_eval` (`Proofs/Operations/DivRemOperation/Core.lean`). Per the
semantic-not-structural principle the 121 equations are *not* restated semantically here — their
semantic form IS the chip-level evidence layer (`Proofs/Chips/DivRemChip/{Soundness,Cases}.lean`),
which extracts each needed equation by list membership. The selection facts a consumer most often
needs (`is_real`/flag binariness, the one-hot sum, `SelectionSpec`) are already derived out of this
bundle into `CoreSpec`'s explicit conjuncts. -/
def OwnAssertsHold {p : ℕ} (cols : DivRemCols (ZMod p)) : Prop :=
  ∀ x ∈ DivRemChip.ownAsserts cols, x = 0

/-- The semantic evidence certified by the DivRem row's **product/own-assert/byte-range assertion
cluster** (`Native/Operations/DivRemOperation/Core.lean`), `DivRemCompare.CompareSpec`'s structural
twin:

* the two composed `MulOperation` semantic `Spec`s at the committed instantiations — `lower`
  (`is_mul = is_real`) and `upper` (`is_real_not_word` gate, `is_mulh = is_div + is_rem`,
  `is_mulhu = is_divu + is_remu`) — exactly the `Assumptions → Spec` currency
  `Proofs/Chips/DivRemChip/Extract.lean`'s `mul_lo_spec`/`mul_hi_spec_*` consume;
* the product-glue limb links in the form `rwlo_product`/`rwhi_product_{unsigned,signed}` expect:
  `c_times_quotient[i] = product[2i] + product[2i+1]·256` against `lower`'s bytes 0–7
  unconditionally, and against `upper`'s bytes 8–15 under the 64-bit gate
  `g64 = is_div + is_divu + is_rem + is_remu`;
* the raw `OwnAssertsHold` bundle (see its docstring);
* the derived selection facts: `is_real`/`is_real_not_word`/all eight variant flags binary, the
  ungated one-hot sum `E367`, and `DivRemContract.SelectionSpec` (a real row selects a case);
* mirroring `MulOperation.Spec`'s convention of carrying its own byte pulls' facts (its `RawSpec`
  ranges), the cluster's 34 u16 `Range` pulls as gated `.val < 2^16` facts — the 8 carry-chain
  composites (`E123…E151`) and the `abs_c`/`abs_remainder`/`quotient`/`remainder`/
  `c_times_quotient` limbs on `is_real`, plus the two word-variant checks on
  `remainder[1]`/`quotient[1]` on `e2`. -/
def CoreSpec {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)] (cols : DivRemCols (ZMod p)) : Prop :=
  let g64 := cols.is_div + cols.is_divu + cols.is_rem + cols.is_remu
  let e2 := cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw
  let rn := cols.rem_neg * 65535
  let lo := cols.c_times_quotient_lower
  let up := cols.c_times_quotient_upper
  -- (1-2) the two `c_times_quotient` product structs' semantic contracts.
  MulOperation.Spec
    ⟨cols.quotient_comp, cols.c, lo, cols.is_real, cols.is_real, 0, 0, 0, 0⟩ ∧
  MulOperation.Spec
    ⟨cols.quotient_comp, cols.c, up, cols.is_real_not_word, 0,
     cols.is_div + cols.is_rem, cols.is_divu + cols.is_remu, 0, 0⟩ ∧
  -- (3) the low product glue: `c_times_quotient[0..3]` are `lower`'s bytes 0..7, unconditionally.
  (cols.c_times_quotient[0] = lo.product[0] + lo.product[1] * 256) ∧
  (cols.c_times_quotient[1] = lo.product[2] + lo.product[3] * 256) ∧
  (cols.c_times_quotient[2] = lo.product[4] + lo.product[5] * 256) ∧
  (cols.c_times_quotient[3] = lo.product[6] + lo.product[7] * 256) ∧
  -- (4) the high product glue: on the 64-bit variants, `c_times_quotient[4..7]` are `upper`'s
  -- bytes 8..15.
  (g64 = 1 →
    cols.c_times_quotient[4] = up.product[8] + up.product[9] * 256 ∧
    cols.c_times_quotient[5] = up.product[10] + up.product[11] * 256 ∧
    cols.c_times_quotient[6] = up.product[12] + up.product[13] * 256 ∧
    cols.c_times_quotient[7] = up.product[14] + up.product[15] * 256) ∧
  -- (5) the raw own-assert bundle (`E13…E367`, `op_a_0`).
  OwnAssertsHold cols ∧
  -- (6) derived selection facts: gate/flag binariness (`E355`/`E343`/`E325…E339`), the ungated
  -- one-hot sum (`E367`), and the committed-case selection on real rows.
  (cols.is_real = 0 ∨ cols.is_real = 1) ∧
  (cols.is_real_not_word = 0 ∨ cols.is_real_not_word = 1) ∧
  (cols.is_div = 0 ∨ cols.is_div = 1) ∧ (cols.is_divu = 0 ∨ cols.is_divu = 1) ∧
  (cols.is_rem = 0 ∨ cols.is_rem = 1) ∧ (cols.is_remu = 0 ∨ cols.is_remu = 1) ∧
  (cols.is_divw = 0 ∨ cols.is_divw = 1) ∧ (cols.is_remw = 0 ∨ cols.is_remw = 1) ∧
  (cols.is_divuw = 0 ∨ cols.is_divuw = 1) ∧ (cols.is_remuw = 0 ∨ cols.is_remuw = 1) ∧
  (cols.is_divu + cols.is_remu + cols.is_div + cols.is_rem
    + cols.is_divw + cols.is_remw + cols.is_divuw + cols.is_remuw = 1) ∧
  DivRemContract.SelectionSpec cols.is_real cols ∧
  -- (7) the 32 `is_real`-gated u16 byte-range facts: the carry-chain composites `E123…E151`, then
  -- the `abs_c`/`abs_remainder`/`quotient`/`remainder`/`c_times_quotient` limbs.
  (cols.is_real = 1 →
    (cols.c_times_quotient[0] + cols.remainder_comp[0]
      - cols.carry[0] * 65536).val < 2 ^ 16 ∧
    (cols.c_times_quotient[1] + cols.remainder_comp[1]
      - cols.carry[1] * 65536 + cols.carry[0]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[2] + cols.remainder_comp[2]
      - cols.carry[2] * 65536 + cols.carry[1]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[3] + cols.remainder_comp[3]
      - cols.carry[3] * 65536 + cols.carry[2]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[4] + rn - cols.carry[4] * 65536 + cols.carry[3]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[5] + rn - cols.carry[5] * 65536 + cols.carry[4]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[6] + rn - cols.carry[6] * 65536 + cols.carry[5]).val < 2 ^ 16 ∧
    (cols.c_times_quotient[7] + rn - cols.carry[7] * 65536 + cols.carry[6]).val < 2 ^ 16 ∧
    (∀ i (_ : i < 4), cols.abs_c[i].val < 2 ^ 16) ∧
    (∀ i (_ : i < 4), cols.abs_remainder[i].val < 2 ^ 16) ∧
    (∀ i (_ : i < 4), cols.quotient[i].val < 2 ^ 16) ∧
    (∀ i (_ : i < 4), cols.remainder[i].val < 2 ^ 16) ∧
    (∀ i (_ : i < 8), cols.c_times_quotient[i].val < 2 ^ 16)) ∧
  -- (8) the two `e2`-gated word-variant range checks (live even on padding word rows).
  (e2 = 1 → cols.remainder[1].val < 2 ^ 16 ∧ cols.quotient[1].val < 2 ^ 16)

end SP1Clean.DivRemCore
