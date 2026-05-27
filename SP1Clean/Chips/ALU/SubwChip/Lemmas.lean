import SP1Clean.Chips.ALU.SubwChip.Cols
import SP1Operations.Operation.SubwOperation.SubwOperation
import SP1Clean.Operations.SubwOperation
import SP1Clean.Reader.RTypeReader
import SP1Chips.Subw.Common
import RISCV.Instructions

/-! # `SubwChip` cols-level lemmas

Two non-trivial lemmas that bridge cols-level data to SP1's flat-row
machinery:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` (cols → Main → cols
  round-trip), conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_real`.
- `allHold_iff_structural` — bridges `(_root_.Subw.constraints Main).allHold`
  under `is_real = 1` to the conjunction of `CPUState.Gated.Spec`,
  `RTypeReader.Gated.Spec`, the trailing `Main[13] = 0` op_a_0 gate, and
  the semantic-only (`HWord.isU32 ∧ BV32 eq ∧ msb_eq`) triple from
  `SubwOperation.iff_sp1_full`'s RHS. The byte-borrow + sign-extension
  decomposition that SP1's `SubwOperation` threads internally is *not*
  exposed; it's reconstructed on demand via
  `SubwOperation.iff_sp1_full`. Used downstream by `SailBridge.lean`.

Mirrors `SP1Clean/SubChip/Lemmas.lean` post-migration, diverging only in
the semantic-clause shape (BV32 + msb_eq vs Sub's BV64 + isU64) to match
the W-form storage and avoid a costly BV64↔BV32+msb inversion. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Subw

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols round-trip),
conditional on `cols.adapter_cols.is_trusted = cols.is_real`. -/
lemma fromMain_toMain (cols : SubwCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, subw_value, subw_msb, is_real, adapter_cols⟩
  have : adapter_cols.is_trusted = is_real := by simpa using h_trusted
  simp [this, SubwCols.ext_iff, CPUState.ext_iff,
    RTypeReader.ext_iff, MemoryAccessInSharedCols.ext_iff,
    UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_⟩, ?_⟩
  all_goals simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Subw.constraints Main` is exactly the conjunction of
`CPUState.Gated.Assertion.Spec`, `RTypeReader.Gated.Assertion.Spec`,
`Main[13] = 0` (the chip-level `op_a_0` zero gate), and the
semantic-only triple `(HWord.isU32 ⟨#v[Main[28], Main[29]]⟩ ∧ BV32 eq ∧
msb_eq)` from `SubwOperation.iff_sp1_full`'s RHS, under
`is_real = Main[31] = 1`. The byte-borrow + sign-extension
decomposition that SP1's `SubwOperation` threads internally is *not*
exposed in the RHS — it's reconstructed via `SubwOperation.iff_sp1_full`
which needs the `Word.isU64` bounds of op_b / op_c (available from
`RTypeReader.Gated.Spec`'s `RegisterAccess.Spec` sub-conjuncts). Used
inside the Sail clause's external bridge
(`SailBridge.sail_correct_of_formalSpec`) to construct an `allHold`
from the structural pieces of `FormalSpec`. -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 32) (h_is_real : Main[31] = 1) :
    (_root_.Subw.constraints Main).allHold ↔
      (SP1Clean.CPUState.Gated.Assertion.Spec
          ⟨{ clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
             pc := #v[Main[3], Main[4], Main[5]] },
           #v[Main[3] + 4, Main[4], Main[5]], 8, Main[31]⟩ ∧
       SP1Clean.RTypeReader.Gated.Assertion.Spec
          ⟨Main[0], Main[2] + Main[1] * 65536, 20,
           #v[Main[3], Main[4], Main[5]],
           #v[Main[28], Main[29], Main[30] * 65535, Main[30] * 65535],
           { op_a := Main[6],
             op_a_memory :=
               { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                 access_timestamp :=
                   { prev_low := Main[11], diff_low_limb := Main[12] } },
             op_a_0 := Main[13], op_b := Main[14],
             op_b_memory :=
               { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                 access_timestamp :=
                   { prev_low := Main[19], diff_low_limb := Main[20] } },
             op_c := Main[21],
             op_c_memory :=
               { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
                 access_timestamp :=
                   { prev_low := Main[26], diff_low_limb := Main[27] } } },
           Main[31], Main[31]⟩ ∧
       Main[13] = 0 ∧
       HWord.isU32 (p := p) #v[Main[28], Main[29]] ∧
       HWord.toBitVec32 (p := p) #v[Main[28], Main[29]] =
         execute_RTYPEW_pure_32_w
           #v[Main[15], Main[16], Main[17], Main[18]]
           #v[Main[22], Main[23], Main[24], Main[25]] .SUBW ∧
       Main[30] =
         if (HWord.toBitVec32 (p := p) #v[Main[28], Main[29]]).msb
         then 1 else 0) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [_root_.Subw.allHold_constraints_iff Main, h_is_real,
      SP1Clean.CPUState.Gated.Assertion.Spec_iff_sp1,
      SP1Clean.RTypeReader.Gated.Assertion.Spec_iff_sp1]
  refine ⟨?_, ?_⟩
  · -- Forward: allHold → structural conjuncts + (isU32 ∧ BV32 eq ∧ msb_eq).
    rintro ⟨h_subwop, h_cpu, h_rtr, _, h_op_a_0⟩
    have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h_isU64_b : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] :=
      (h_rtr.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have h_isU64_c : Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] :=
      (h_rtr.2.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have ⟨h_isU32_v, h_bv32, h_msb_eq⟩ :=
      (SubwOperation.iff_sp1_full h_isU64_b h_isU64_c).mp h_subwop
    exact ⟨h_cpu, h_rtr, h_op_a_0, h_isU32_v, h_bv32, h_msb_eq⟩
  · -- Backward: structural conjuncts + (isU32 ∧ BV32 eq ∧ msb_eq) → allHold.
    rintro ⟨h_cpu, h_rtr, h_op_a_0, h_isU32_v, h_bv32, h_msb_eq⟩
    have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h_isU64_b : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] :=
      (h_rtr.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have h_isU64_c : Word.isU64 #v[Main[22], Main[23], Main[24], Main[25]] :=
      (h_rtr.2.2.2.2.1.resolve_left h_one_ne_zero).2.2
    have h_subwop :=
      (SubwOperation.iff_sp1_full
          (cols := { value := #v[Main[28], Main[29]],
                     msb := { msb := Main[30] } })
          h_isU64_b h_isU64_c).mpr
        ⟨h_isU32_v, h_bv32, h_msb_eq⟩
    refine ⟨h_subwop, h_cpu, h_rtr, ?_, h_op_a_0⟩
    ring

/-- Bridge the `SubwOperation.spec` 32-bit BitVec equation +
sign-extension MSB to the 64-bit `RV64.subw` semantic. Given the
natural-form `SubwOp.Spec` plus operand `Word.isU64` bounds, the
sign-extended Word `#v[value[0], value[1], msb*65535, msb*65535]`
equals `RV64.subw c.toBitVec64 b.toBitVec64`. Used by
`Assertion.soundness` to discharge the BitVec conjunct of
`FormalSpec`. -/
lemma rv64_subw_eq_of_subwop_spec
    (b c : Word (ZMod p)) (value : HWord (ZMod p)) (msb : ZMod p)
    (h_isU64_b : b.isU64) (h_isU64_c : c.isU64)
    (h_subwop : SP1Clean.SubwOp.Spec b c
      ({ value := value, msb := { msb := msb } } : SubwOperation (ZMod p))) :
    Word.toBitVec64 #v[value[0], value[1], msb * 65535, msb * 65535] =
      RV64.subw c.toBitVec64 b.toBitVec64 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Bridge the natural-form Spec to `SubwOperation.constraints.allHold`,
  -- then apply `SubwOperation.spec` for the 32-bit equation + msb fact.
  have h_allHold : (SubwOperation.constraints b c
        { value := value, msb := { msb := msb } } 1).allHold :=
    (SP1Clean.SubwOp.iff_sp1 _ _ _).mpr h_subwop
  obtain ⟨h_isU32_v, h_subw_bv, h_msb_eq⟩ :=
    SubwOperation.spec h_isU64_b h_isU64_c h_allHold
  -- Unfold `RV64.subw` and bridge `BitVec.extractLsb' 0 32 ·.toBitVec64`
  -- to `·.low.toBitVec32` via `Word.setWidth_eq_low` (which uses
  -- `BitVec.setWidth`; the two are defeq for narrowing).
  simp only [RV64.subw]
  have h_b_low :
      BitVec.extractLsb' 0 32 b.toBitVec64 = b.low.toBitVec32 := by
    rw [show BitVec.extractLsb' 0 32 b.toBitVec64 =
          BitVec.setWidth 32 b.toBitVec64 from rfl]
    exact Word.setWidth_eq_low h_isU64_b
  have h_c_low :
      BitVec.extractLsb' 0 32 c.toBitVec64 = c.low.toBitVec32 := by
    rw [show BitVec.extractLsb' 0 32 c.toBitVec64 =
          BitVec.setWidth 32 c.toBitVec64 from rfl]
    exact Word.setWidth_eq_low h_isU64_c
  rw [h_b_low, h_c_low]
  -- Substitute the SubwOperation.spec equation:
  --   value.toBitVec32 = b.low.toBitVec32 - c.low.toBitVec32
  -- but the unfolded `RV64.subw` form uses `BitVec.sub` instead of `HSub.hSub`;
  -- bridge both directions.
  rw [show b.low.toBitVec32.sub c.low.toBitVec32 = HWord.toBitVec32 value by
    rw [h_subw_bv]; rfl]
  -- Apply `sign_extend_32_to_64_msb`: signExtend 64 value.toBitVec32 equals
  -- the Word with high limbs `if msb then 65535 else 0`. Combined with
  -- `msb = if … then 1 else 0`, the high limbs match `msb * 65535`.
  -- Reduce the `{ value, msb }` projections in `h_msb_eq` first.
  simp only at h_msb_eq h_isU32_v
  rw [HWord.sign_extend_32_to_64_msb h_isU32_v]
  -- Discharge `msb * 65535 = if … then 65535 else 0` via `h_msb_eq`.
  rw [h_msb_eq]
  by_cases h : (HWord.toBitVec32 value).msb = true
  · simp [h]
  · simp [h]

/-! ## Chip-level FormalSpec ↔ sub-circuit Specs

The two lemmas below name the *stable midpoint* of `SubwChip`'s
`soundness` / `completeness` proofs: after `circuit_proof_start`
unfolds the Clean elaboration plumbing and the proof destructures
`h_input` / `h_assumptions` / `h_holds` (or `h_spec`), the proof state
contains exactly four named hypotheses — one per `main` sub-circuit
emission (`SubwOp.assertion`, `CPUState.Gated.assertion`,
`RTypeReader.Gated.assertion`, `op_a_0 === 0`). Surfacing that midpoint
as top-level named theorems decouples the sub-circuit composition graph
from `circuit_proof_start`'s opaque output, and lets `Circuit.lean`'s
proofs collapse to "destructure → invoke the named lemma".

Mirrors `SP1Clean/Chips/ALU/SubChip/Lemmas.lean`, with two
SubwChip-specific differences: `SubwOp.Assertion.Assumptions = True`
(so the sub-circuit witness is taken in `Spec` form directly, not the
`Assumptions → Spec` function form Add/Sub use), and the chip
`FormalSpec` has an extra `(is_real = 1 → BV32 triple)` conjunct
matching `SubwOperation.iff_sp1_full`'s RHS plus a trailing
`(is_real = 1 → RV64.subw eq)` clause derived inline via
`rv64_subw_eq_of_subwop_spec`. -/

/-- **Forward** (soundness midpoint): assemble the chip-level
`FormalSpec` from the per-sub-circuit Specs. The `SubwOp` hypothesis is
taken in its borrow-form `Assertion.Spec` directly (since
`SubwOp.Assertion.Assumptions = True`, no `Assumptions → Spec` function
form is needed). The semantic BV32 triple and `RV64.subw` clauses are
constructed internally using `is_real = 1` plus the `Word.isU64
op_b/op_c` bounds pulled from `h_rtr` via
`RTypeReader.Gated.Assertion.isU64_operands_of_spec`. -/
lemma formalSpec_of_subcircuit_specs
    (cols : SubwCols (ZMod p))
    (h_is_real : cols.is_real = 1)
    (h_subwop : SP1Clean.SubwOp.Assertion.Spec
        ⟨cols.adapter.op_b_memory.prev_value,
         cols.adapter.op_c_memory.prev_value,
         cols.subw_value, cols.subw_msb⟩)
    (h_cpu : SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state,
         #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
         8, cols.is_real⟩)
    (h_rtr : SP1Clean.RTypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536, 20,
         cols.state.pc,
         #v[cols.subw_value[0], cols.subw_value[1],
            cols.subw_msb * 65535, cols.subw_msb * 65535],
         cols.adapter, cols.is_real, cols.adapter_cols.is_trusted⟩)
    (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    FormalSpec cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_isU64_b, h_isU64_c⟩ :=
    SP1Clean.RTypeReader.Gated.Assertion.isU64_operands_of_spec h_is_real h_rtr
  have h_subwop_nat :=
    (SP1Clean.SubwOp.Assertion_Spec_iff_Spec _ _ _ _).mp h_subwop
  refine ⟨h_cpu, h_rtr, h_op_a_0, ?_, ?_⟩
  · intro _h_is_real_eq
    have h_subwop_allHold := (SP1Clean.SubwOp.iff_sp1 _ _ _).mpr h_subwop_nat
    exact (SubwOperation.iff_sp1_full h_isU64_b h_isU64_c).mp h_subwop_allHold
  · intro _h_is_real_eq
    exact rv64_subw_eq_of_subwop_spec _ _ _ _ h_isU64_b h_isU64_c h_subwop_nat

/-- **Backward** (completeness midpoint): peel the chip-level
`FormalSpec` apart into per-sub-circuit `Spec`s. The `SubwOp` conjunct
is returned in its borrow-form `Assertion.Spec`, reconstructed from the
BV32 triple stored in `FormalSpec`'s `is_real = 1 → ...` conjunct via
`iff_sp1_full.mpr` and the round-trip `iff_sp1.mp ∘ Assertion_Spec_iff_Spec.mpr`. -/
lemma subcircuit_specs_of_formalSpec
    (cols : SubwCols (ZMod p))
    (h_is_real : cols.is_real = 1)
    (h_spec : FormalSpec cols) :
    SP1Clean.SubwOp.Assertion.Spec
        ⟨cols.adapter.op_b_memory.prev_value,
         cols.adapter.op_c_memory.prev_value,
         cols.subw_value, cols.subw_msb⟩ ∧
    SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state,
         #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
         8, cols.is_real⟩ ∧
    SP1Clean.RTypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536, 20,
         cols.state.pc,
         #v[cols.subw_value[0], cols.subw_value[1],
            cols.subw_msb * 65535, cols.subw_msb * 65535],
         cols.adapter, cols.is_real, cols.adapter_cols.is_trusted⟩ ∧
    cols.adapter.op_a_0 = 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_cpu, h_rtr, h_op_a_0, h_sem, _h_rv64⟩ := h_spec
  obtain ⟨h_isU64_b, h_isU64_c⟩ :=
    SP1Clean.RTypeReader.Gated.Assertion.isU64_operands_of_spec h_is_real h_rtr
  have ⟨h_isU32, h_bv32, h_msb_eq⟩ := h_sem h_is_real
  have h_subwop_allHold :=
    (SubwOperation.iff_sp1_full
        (cols := { value := cols.subw_value,
                   msb := { msb := cols.subw_msb } })
        h_isU64_b h_isU64_c).mpr
      ⟨h_isU32, h_bv32, h_msb_eq⟩
  have h_subwop_nat := (SP1Clean.SubwOp.iff_sp1 _ _ _).mp h_subwop_allHold
  have h_subwop :=
    (SP1Clean.SubwOp.Assertion_Spec_iff_Spec _ _ _ _).mpr h_subwop_nat
  exact ⟨h_subwop, h_cpu, h_rtr, h_op_a_0⟩

end SP1Clean.Subw
