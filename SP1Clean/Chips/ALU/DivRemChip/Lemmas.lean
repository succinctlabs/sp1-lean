import SP1Clean.Chips.ALU.DivRemChip.Cols
import SP1Clean.Reader.RTypeReader
import SP1Chips.DivRem.DivRemChip

/-! # `DivRemChip` cols-level lemmas (soundness sketch)

The lemmas below name the AddChip-style midpoints between the SP1 row's
`.allHold` constraint layer and the cols-level `FormalSpec`. The
**forward** (soundness) direction is achievable by mirroring the SP1-side
`DivRem.spec.{div,divu,…}` proofs; the **backward** (completeness)
direction is blocked (see barrier 1). This file sketches the forward
shape and isolates the concrete "underlying" lemmas it still needs.

## Two barriers (why this isn't a finished AddChip clone)

1. **No chip-level `iff_sp1_full` for DivRem.** The backward direction
   (`FormalSpec → allHold`) would reconstruct the 246-column witness
   layout from the 8 semantic `RV64.{div,…}` equations alone — impossible
   without a chip-level biconditional. `MulOperation` ships only `of_sp1`
   (forward); `LtOperationUnsigned` lacks `iff_sp1_full`. Completeness is
   therefore out of scope (CLEAN_FUTURE.md "scope-fence").

2. **`main`'s sub-circuit graph omits the ~150 inline wiring gates.** The
   core `_root_.DivRem.div_rem` arithmetic lemma consumes ~150 inline
   `assertZero` equations (`eq_lb0`, `eq_qbc0`, `of_eq_q0`, `cn_ac0`, …)
   in addition to the sub-operation semantics. `Circuit.lean`'s `main`
   composes the 17 sub-operation sub-circuits + 5 binary gates but does
   *not* emit those inline gates, so the chip's elaborated `h_holds`
   can't reach `div_rem`. Closing chip-level `soundness` (as opposed to
   the SP1-row `allHold_iff_structural` forward direction below) requires
   mirroring those gates into `main` (~200 LoC).

## What the SP1-side proof tells us (shape of `spec.div`)

`DivRem.spec.div Main cstrs h_is_real h_is_div` (SP1Chips/DivRem/DivRem.lean:561)
proves `Word.toBitVec64 a = (execute_DIV_REM_pure b c .DRS).1` by:
1. `(allHold_constraints_iff Main).mp cstrs` → destructure into the 17
   sub-operation sub-constraint `.allHold`s + ~150 inline gate equations.
2. Lift each sub-operation to its semantic form via the operation `spec`
   lemmas: `MulOperation.spec.mul`, `MulOperation.spec.mulh.gen`,
   `IsEqualWordOperation.spec.gen` (×4), `IsZeroWordOperation.spec`,
   `U16MSBOperation.spec.gen` (×7), `AddOperation.spec.gen` (×2),
   `LtOperationUnsigned.spec.nat.gen`.
3. Feed all of that to the core `DivRem.div_rem` lemma → BitVec equation.

The Clean chip's `h_holds` already provides step 2's *output* (the
sub-operation Clean `Spec`s are the semantic form). So the forward
`allHold_iff_structural` below just needs steps 1 + 3 + the
`execute_DIV_REM_pure ↔ RV64.{div,…}` bridges sketched next. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.DivRem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## Underlying dependency: `execute_DIV_REM_pure ↔ RV64.{div,…}` bridges

The SP1 `spec.{div,…}` lemmas produce the result in `execute_DIV_REM_pure`
form; `FormalSpec` (Spec.lean:613) states it in `RV64.{div,…}` form. RISCV's
`SailPureToInstructions` provides `rtype_{add,sub,…}_eq` but stops short of
the DIV/REM family, so these 8 bridges are new "underlying" lemmas.

Arg order: `spec.div` calls `execute_DIV_REM_pure op_b op_c`; `FormalSpec`
states `RV64.div op_c op_b`. With `RV64.div rs2 rs1 = rs1.sdiv rs2`, the
two coincide. Each is a pure BitVec↔Int division identity.

**All 8 are now proven** (no sorries). Proof techniques:
- **Unsigned (`divu`/`remu`)**: `(b.udiv c).toNat = b.toNat / c.toNat` holds
  definitionally; close via `toNat` + `Nat.mod_eq_of_lt`.
- **Signed (`div`/`rem`)**: route through `toInt` using core
  `BitVec.toInt_sdiv` (`(a.sdiv b).toInt = (a.toInt.tdiv b.toInt).bmod (2^w)`)
  and `BitVec.toInt_srem`; the INT_MIN/−1 overflow special-case `bmod`s to
  the same value (`decide`).
- **Unsigned word (`divuw`/`remuw`)**: width-32 `toNat` round-trip wrapped
  in `signExtend` congruence — no `bmod` needed.
- **Signed word (`divw`/`remw`)**: `toInt` route + `BitVec.toInt_signExtend_of_le`;
  `remw` closes via a `tmod`-magnitude bound, `divw` needs the cross-width
  `bmod` identity (`Int.bmod_eq_of_le`) with the strict `tdiv < 2^31` bound
  established by ruling out the overflow boundary via `Int.natAbs_tdiv`. -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma execute_div_fst_eq_rv64_div (b c : BitVec 64) :
    (execute_DIV_REM_pure b c .DRS).1 = RV64.div c b := by
  simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int, RV64.div]
  by_cases hc : c = 0#64
  · subst hc
    apply BitVec.eq_of_toInt_eq
    simp
  · have hci : ¬ (c.toInt = 0) := fun h => hc (BitVec.eq_of_toInt_eq (by rw [h]; rfl))
    rw [if_neg hc, if_neg hci]
    apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_sdiv, BitVec.toInt_ofInt]
    split
    · rename_i hov
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hov
      obtain ⟨hb, hc'⟩ := hov
      rw [hb, hc']
      decide
    · rfl

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma execute_rem_snd_eq_rv64_rem (b c : BitVec 64) :
    (execute_DIV_REM_pure b c .DRS).2 = RV64.rem c b := by
  simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int, RV64.rem]
  rw [← BitVec.toInt_srem]
  exact BitVec.ofInt_toInt

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma execute_divu_fst_eq_rv64_divu (b c : BitVec 64) :
    (execute_DIV_REM_pure b c .DRU).1 = RV64.divu c b := by
  unfold execute_DIV_REM_pure execute_DIV_REM_pure_int RV64.divu
  by_cases hc : c = 0#64
  · subst hc; simp
  · have hc' : c.toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
    have hcz : (↑c.toNat : ℤ) ≠ 0 := by exact_mod_cast hc'
    simp only [hc, if_false, hcz]
    change BitVec.ofNat 64 ((↑b.toNat : ℤ).tdiv ↑c.toNat).toNat = b.udiv c
    rw [show (↑b.toNat : ℤ).tdiv ↑c.toNat = ↑(b.toNat / c.toNat) from rfl, Int.toNat_natCast]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    change b.toNat / c.toNat % 2 ^ 64 = b.toNat / c.toNat
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) b.isLt)

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma execute_remu_snd_eq_rv64_remu (b c : BitVec 64) :
    (execute_DIV_REM_pure b c .DRU).2 = RV64.remu c b := by
  unfold execute_DIV_REM_pure execute_DIV_REM_pure_int RV64.remu
  change BitVec.ofNat 64 ((↑b.toNat : ℤ).tmod ↑c.toNat).toNat = b.umod c
  rw [show (↑b.toNat : ℤ).tmod ↑c.toNat = ↑(b.toNat % c.toNat) from rfl, Int.toNat_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  change b.toNat % c.toNat % 2 ^ 64 = b.toNat % c.toNat
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) b.isLt)

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- The signed 32-bit `tdiv` result stays in `[-2^31, 2^31)` away from the
`INT_MIN / −1` overflow case. This is the boundary fact behind `divw`'s
cross-width `bmod` identity (`(tdiv).bmod 2^64 = (tdiv).bmod 2^32` only holds
because the result fits in signed 32 bits — at the overflow boundary `2^31`
the two `bmod`s would disagree). The strict upper bound is recovered by ruling
out `tdiv = 2^31`, which forces `a.natAbs = 2^31 ∧ b.natAbs = 1` (via
`Int.natAbs_tdiv`), i.e. exactly the excluded overflow. -/
private lemma tdiv_int32_range {a b : ℤ} (ha : -2 ^ 31 ≤ a) (ha' : a < 2 ^ 31)
    (hbne : b ≠ 0) (hnov : ¬(a = -2 ^ 31 ∧ b = -1)) :
    -2 ^ 31 ≤ a.tdiv b ∧ a.tdiv b < 2 ^ 31 := by
  have hle := Int.natAbs_tdiv_le_natAbs a b
  have hane : a.natAbs ≤ 2 ^ 31 := by omega
  refine ⟨by omega, ?_⟩
  by_contra hge
  rw [not_lt] at hge
  have htd : a.tdiv b = 2 ^ 31 := by omega
  have hna := Int.natAbs_tdiv a b
  rw [htd] at hna
  have hna' : (2 : ℕ) ^ 31 = a.natAbs / b.natAbs := by simpa using hna
  have hcne : b.natAbs ≠ 0 := by omega
  have hmul : 2 ^ 31 * b.natAbs ≤ a.natAbs := by
    conv_lhs => rw [hna']
    exact Nat.div_mul_le_self _ _
  have hbna1 : b.natAbs = 1 := by omega
  have hana : a.natAbs = 2 ^ 31 := by rw [hbna1, Nat.div_one] at hna'; omega
  have hav : a = -2 ^ 31 := by omega
  have hbv : b = -1 := by
    rcases (show b = 1 ∨ b = -1 by omega) with h1 | h1
    · exfalso; rw [h1, Int.tdiv_one] at htd; omega
    · exact h1
  exact hnov ⟨hav, hbv⟩

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma execute_divw_fst_eq_rv64_divw (b c : BitVec 64) :
    (execute_DIV_REM_pure b c .DRWS).1 = RV64.divw c b := by
  simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int, RV64.divw]
  set b32 := BitVec.extractLsb 31 0 b
  set c32 := BitVec.extractLsb 31 0 c
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by norm_num : (32 : ℕ) ≤ 64), BitVec.toInt_ofInt]
  by_cases hc : c32 = 0#32
  · rw [hc]; simp
  · have hci : ¬ (c32.toInt = 0) := fun h => hc (BitVec.eq_of_toInt_eq (by rw [h]; rfl))
    rw [if_neg hc, if_neg hci, BitVec.toInt_sdiv]
    have hb := @BitVec.toInt_lt 32 b32
    have hb' := BitVec.le_toInt b32
    split
    · rename_i hov
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hov
      obtain ⟨hbv, hcv⟩ := hov
      rw [hbv, hcv]; decide
    · rename_i hnov
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hnov
      have hrange := tdiv_int32_range hb' hb hci hnov
      rw [Int.bmod_eq_of_le (by omega) (by omega), Int.bmod_eq_of_le (by omega) (by omega)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma execute_remw_snd_eq_rv64_remw (b c : BitVec 64) :
    (execute_DIV_REM_pure b c .DRWS).2 = RV64.remw c b := by
  simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int, RV64.remw]
  set b32 := BitVec.extractLsb 31 0 b
  set c32 := BitVec.extractLsb 31 0 c
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by norm_num : (32 : ℕ) ≤ 64),
      BitVec.toInt_srem, BitVec.toInt_ofInt]
  have hbound : (b32.toInt.tmod c32.toInt).natAbs ≤ b32.toInt.natAbs := by
    rw [Int.natAbs_tmod]; exact Nat.mod_le _ _
  have hb := @BitVec.toInt_lt 32 b32
  have hb' := BitVec.le_toInt b32
  apply Int.bmod_eq_of_le <;> omega

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma execute_divuw_fst_eq_rv64_divuw (b c : BitVec 64) :
    (execute_DIV_REM_pure b c .DRWU).1 = RV64.divuw c b := by
  simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int, RV64.divuw]
  congr 1
  set b32 := BitVec.extractLsb 31 0 b with hb32
  set c32 := BitVec.extractLsb 31 0 c with hc32
  by_cases hc : c32 = 0#32
  · rw [hc]; simp
  · have hc' : c32.toNat ≠ 0 := fun h => hc (BitVec.eq_of_toNat_eq (by simpa using h))
    have hcz : (↑c32.toNat : ℤ) ≠ 0 := by exact_mod_cast hc'
    rw [if_neg hc, if_neg hcz]
    change BitVec.ofNat 32 ((↑b32.toNat : ℤ).tdiv ↑c32.toNat).toNat = b32.udiv c32
    rw [show (↑b32.toNat : ℤ).tdiv ↑c32.toNat = ↑(b32.toNat / c32.toNat) from rfl,
        Int.toNat_natCast]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat]
    change b32.toNat / c32.toNat % 2 ^ 32 = b32.toNat / c32.toNat
    exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) b32.isLt)

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma execute_remuw_snd_eq_rv64_remuw (b c : BitVec 64) :
    (execute_DIV_REM_pure b c .DRWU).2 = RV64.remuw c b := by
  simp only [execute_DIV_REM_pure, execute_DIV_REM_pure_int, RV64.remuw]
  congr 1
  set b32 := BitVec.extractLsb 31 0 b with hb32
  set c32 := BitVec.extractLsb 31 0 c with hc32
  change BitVec.ofNat 32 ((↑b32.toNat : ℤ).tmod ↑c32.toNat).toNat = b32.umod c32
  rw [show (↑b32.toNat : ℤ).tmod ↑c32.toNat = ↑(b32.toNat % c32.toNat) from rfl,
      Int.toNat_natCast]
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_ofNat]
  change b32.toNat % c32.toNat % 2 ^ 32 = b32.toNat % c32.toNat
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.mod_le _ _) b32.isLt)

/-! ## STUB. AddChip-style cols → Main → cols round-trip.

Blocked on `toMain : DivRemCols (ZMod p) → Vector (ZMod p) 246` not
existing yet (AddCols ships one at `Structs.lean:76`; DivRem's mirror is
~250 LoC of mechanical projection). -/
omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
lemma fromMain_toMain (_cols : DivRemCols (ZMod p))
    (_h_trusted : True) : True := by trivial

/-- Bridge SP1 row `.allHold` (under `is_real = 1`) to the structural
`FormalSpec`. **Forward direction is the achievable soundness path**;
backward is blocked (barrier 1). Body `sorry`'d, but the forward shape is:

```
rintro cstrs
have h_is_real : _root_.DivRem.is_real Main := by simpa using _h_is_real
-- Pull operand U64 bounds + op_a_0 + reader sub-specs out of the row.
obtain ⟨_, _, _, _, h_isU64_b, h_isU64_c, _, _⟩ :=
  _root_.DivRem.correct_prologue_facts Main cstrs h_is_real
-- The 4 *structural* FormalSpec conjuncts come from the migrated
-- `allHold_constraints_iff` RHS + the reader `Spec_iff_sp1` bridges
-- (same as AddChip uses for its CPUState/RTypeReader conjuncts):
--   • CPUState.Gated.Assertion.Spec   ← CPUState sub-`.allHold`  via Spec_iff_sp1
--   • RTypeReader.Gated.Assertion.Spec ← RTypeReader sub-`.allHold` via Spec_iff_sp1
--   • is_real ∈ {0,1}                 ← Or.inr h_is_real
--   • op_a_0 = 0                       ← inline gate Main[13] = 0
refine ⟨?cpu, ?rtr, Or.inr h_is_real, ?op_a_0, fun _ => ⟨?isU64, ?div, ?divu,
        ?rem, ?remu, ?divw, ?remw, ?divuw, ?remuw⟩⟩
-- Each variant conjunct delegates to the SP1-side `spec.<v>` lemma, then
-- rewrites `execute_DIV_REM_pure … ↔ RV64.<v> …` with the bridge above:
case div =>
  intro h_is_div
  have h_bv := _root_.DivRem.spec.div Main cstrs h_is_real (by simpa using h_is_div)
  rw [execute_div_fst_eq_rv64_div] at h_bv
  exact h_bv          -- modulo `fromMain`/Word projection defeq
-- … divu/rem/remu/divw/remw/divuw/remuw identically, each pairing
--   `_root_.DivRem.spec.<v>` with `execute_<v>_…_eq_rv64_<v>`.
-- The `?isU64` arm comes from `Word.isU64_of_cases` inside the relevant
-- `spec.<v>` (the chip writes back a verified-U64 result on real rows).
```

Remaining real work: (a) the 8 bridge lemmas above; (b) lining up the
`fromMain Main` field projections with `spec.<v>`'s raw `Main[k]` indices
(mechanical, `rfl`-after-`fromMain` like AddChip's `sp1_*_cols_fromMain`);
(c) the two reader `Spec_iff_sp1` rewrites for the structural conjuncts. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 246) (_h_is_real : Main[244] = 1) :
    (_root_.DivRem.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  sorry

/-- **STUB**. AddChip's soundness midpoint: assemble `FormalSpec` from the
chip's 17 sub-circuit Clean `Spec`s + 5 scalar gates. For DivRem this is
blocked by barrier 2 — the sub-circuit `Spec`s alone don't determine the 8
`RV64.{div,…}` equations without the ~150 inline wiring gates that `main`
omits. The achievable route is via the SP1 row instead
(`allHold_iff_structural` forward), once chip `main` emits those gates. -/
lemma formalSpec_of_subcircuit_specs
    (cols : DivRemCols (ZMod p))
    (_h_is_real : cols.is_real = 1) :
    Assertion.FormalSpec cols := by
  sorry

/-- **STUB**. AddChip's completeness midpoint: peel `FormalSpec` into the
17 sub-circuit `Spec`s. Structurally unprovable for DivRem without
`MulOperation.iff_sp1_full` (barrier 1) — `FormalSpec` carries only the 8
semantic equations, not the carry/MulOp/AddOp witness columns. -/
lemma subcircuit_specs_of_formalSpec
    (_cols : DivRemCols (ZMod p))
    (_h_is_real : (_cols).is_real = 1)
    (_h_spec : Assertion.FormalSpec _cols) :
    True := by trivial

end SP1Clean.DivRem
