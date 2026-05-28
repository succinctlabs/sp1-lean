import SP1Clean.Chips.ALU.LtChip.Cols
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Clean.Compare.LtOperationSigned
import SP1Clean.Operations.LtOperationSigned
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.Lt.Common

/-! # `LtChip` cols-level lemmas

Four lemmas mirroring `SP1Clean/Chips/ALU/AddChip/Lemmas.lean`,
adapted for the 2-variant (`slt`/`sltu`) Path-2 FormalSpec:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` round-trip,
  conditional on the UserMode TrustMode marker
  `cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu`.
  **Real proof** following the AddChip recipe.
- `allHold_iff_structural` — bridges `(_root_.Lt.constraints
  Main).allHold` to the chip's `FormalSpec`. **Sorry (breadcrumb)** — the
  forward direction (raw → FormalSpec) requires a semantic-bridge chain
  through `LtOperationSigned.spec.{signed,unsigned}` (forward only,
  axiom-clean closure available but unimplemented here); the backward
  direction blocks on `LtOperationSigned.iff_sp1_full.mpr`'s Layer-0
  sorry at `SP1Operations/Compare/LtOperationSigned/LtOperationSigned.lean:529`
  (no `spec_inv` for signed `<` yet).
- `formalSpec_of_subcircuit_specs` — soundness midpoint. **Sorry
  (breadcrumb)** — derives chip's `FormalSpec` from sub-circuit Specs;
  the structural conjuncts (CPUState/ALUTypeReader/binary gates/op_a_0)
  close immediately, but the semantic conjuncts `aw = RV64.slt cw bw`
  / `aw = RV64.sltu cw bw` require a `LtSignedOp.AssertionGated.Spec →
  bit-equation` derivation that bridges through `LtUnsignedOp.iff_sp1`
  and `LtOperationSigned.spec.{signed,unsigned}`. Forward direction is
  axiom-clean in principle; implementation pending.
- `subcircuit_specs_of_formalSpec` — completeness midpoint. **Sorry
  (breadcrumb)** — Layer-0 blocker: peeling `aw = RV64.slt cw bw` back
  into a `LtSignedOp.AssertionGated.Spec` witness requires
  `LtOperationSigned.iff_sp1_full.mpr` (`spec_inv` reconstruction).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Lt

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols
round-trip), conditional on the UserMode TrustMode marker
`cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu`. Recursive
`ext` through `@[ext]`-marked sub-structures plus `Vector.ext` reduces
to per-element equations closed by `rfl`. -/
lemma fromMain_toMain (cols : LtCols (ZMod p))
    (h_trusted_eq_sum :
      cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu) :
    fromMain (toMain cols) = cols := by
  rcases cols with ⟨state, adapter, is_slt, is_sltu, lt_operation, adapter_cols⟩
  rcases lt_operation with ⟨⟨⟨bit⟩, u16_flags, not_eq_inv, comparison_limbs⟩,
                            ⟨b_msb⟩, ⟨c_msb⟩⟩
  have h : adapter_cols.is_trusted = is_slt + is_sltu := by simpa using h_trusted_eq_sum
  simp [h, LtCols.ext_iff, CPUState.ext_iff, ALUTypeReader.ext_iff,
    MemoryAccessInSharedCols.ext_iff, UserModeReaderCols.ext_iff]
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩ <;>
    (simp [Array.ext_iff]; intro i hi; interval_cases i <;> simp)

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Lt.constraints Main` is equivalent to the chip's canonical (a)-shape
`FormalSpec`, under `Main[32] + Main[33] = 1` (is_real_sum gate).

**Sorry (breadcrumb)** — forward direction (`allHold → FormalSpec`) is
axiom-clean in principle via `LtOperationSigned.spec.{signed,unsigned}`
(forward) chained with `Word.toBitVec64` / `RV64.slt` defeqs;
implementation is ~150–250 LoC. Backward direction blocks on
`LtOperationSigned.iff_sp1_full.mpr`'s Layer-0 sorry at
`SP1Operations/Compare/LtOperationSigned/LtOperationSigned.lean:529`
(no `LtOperationSigned.spec_inv` parallel to `LtOperationUnsigned.spec_inv`
exists yet). -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 44) (_h_is_real_sum : Main[32] + Main[33] = 1) :
    (_root_.Lt.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  sorry

/-- **Forward** (soundness midpoint): assemble the chip-level
`FormalSpec` from the per-sub-circuit Specs returned by `h_holds`.

Structural conjuncts (CPUState.Gated.Spec, ALUTypeReader.Gated.Spec,
three binary disjuncts via `binary_iff`, op_a_0 = 0) close from the
corresponding sub-Spec hypotheses. The semantic conjunct (`is_real = 1 →
Word.isU64 op_a_write_value ∧ (is_slt = 1 → aw = RV64.slt cw bw) ∧
(is_sltu = 1 → aw = RV64.sltu cw bw)`) is dispatched through `bit_eq_of_spec`
(below) — a forward-only chain bridging the AssertionGated Spec to the
BitVec semantic via `LtUnsignedOp.iff_sp1` and `LtOperationSigned.spec.{signed,unsigned}`. -/
lemma formalSpec_of_subcircuit_specs
    (cols : LtCols (ZMod p))
    (h_is_real_sum : cols.is_slt + cols.is_sltu = 1)
    (_h_trusted : cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu)
    (h_ltop : SP1Clean.LtSignedOp.AssertionGated.Assumptions
        ⟨cols.adapter.op_b_memory.prev_value,
         cols.adapter.op_c_memory.prev_value,
         cols.is_slt,
         cols.lt_operation.result.u16_compare_operation.bit,
         cols.lt_operation.result.u16_flags,
         cols.lt_operation.result.not_eq_inv,
         cols.lt_operation.result.comparison_limbs,
         cols.lt_operation.b_msb.msb,
         cols.lt_operation.c_msb.msb,
         cols.is_slt + cols.is_sltu⟩ →
      SP1Clean.LtSignedOp.AssertionGated.Spec
        ⟨cols.adapter.op_b_memory.prev_value,
         cols.adapter.op_c_memory.prev_value,
         cols.is_slt,
         cols.lt_operation.result.u16_compare_operation.bit,
         cols.lt_operation.result.u16_flags,
         cols.lt_operation.result.not_eq_inv,
         cols.lt_operation.result.comparison_limbs,
         cols.lt_operation.b_msb.msb,
         cols.lt_operation.c_msb.msb,
         cols.is_slt + cols.is_sltu⟩)
    (h_cpu : SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state,
         #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
         8, cols.is_slt + cols.is_sltu⟩)
    (h_alu : SP1Clean.ALUTypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
         cols.is_slt * 9 + cols.is_sltu * 10,
         cols.state.pc,
         #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0],
         cols.adapter,
         cols.is_slt + cols.is_sltu,
         cols.adapter_cols.is_trusted⟩)
    (h_is_slt_bin : cols.is_slt * (cols.is_slt - 1) = 0)
    (h_is_sltu_bin : cols.is_sltu * (cols.is_sltu - 1) = 0)
    (h_sum_bin : (cols.is_slt + cols.is_sltu) *
                    (cols.is_slt + cols.is_sltu - 1) = 0)
    (h_op_a_0 : cols.adapter.op_a_0 = 0) :
    Assertion.FormalSpec cols := by
  -- Normalize `x * (x - 1) = 0` → `x * (x + -1) = 0` so `binary_iff` fires.
  rw [show ∀ y : ZMod p, y - 1 = y + -1 from fun _ => sub_eq_add_neg _ _]
    at h_is_slt_bin h_is_sltu_bin h_sum_bin
  refine ⟨h_cpu, h_alu, ?_, ?_, ?_, h_op_a_0, ?_⟩
  · binary_iff h_is_slt_bin
  · binary_iff h_is_sltu_bin
  · binary_iff h_sum_bin
  · -- Semantic implication: under is_real = 1, derive the BitVec slt/sltu eqs.
    intro h_is_real
    haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    -- Discharge h_ltop's Assumptions to access the AssertionGated.Spec body.
    have h_is_slt_or : cols.is_slt = 0 ∨ cols.is_slt = 1 := by
      binary_iff h_is_slt_bin
    have h_ltop_assumps : SP1Clean.LtSignedOp.AssertionGated.Assumptions
        ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_memory.prev_value,
         cols.is_slt, cols.lt_operation.result.u16_compare_operation.bit,
         cols.lt_operation.result.u16_flags, cols.lt_operation.result.not_eq_inv,
         cols.lt_operation.result.comparison_limbs, cols.lt_operation.b_msb.msb,
         cols.lt_operation.c_msb.msb, cols.is_slt + cols.is_sltu⟩ :=
      ⟨Or.inr h_is_real, h_is_slt_or,
       fun h_ir0 => absurd (h_is_real.symm.trans h_ir0) one_ne_zero⟩
    have h_ltop_spec := h_ltop h_ltop_assumps h_is_real
    obtain ⟨_h_u16_b, _h_u16_c, h_lt_unsigned, _h_is_signed_bin, _h_b_vac, _h_c_vac⟩ :=
      h_ltop_spec
    -- LtUnsignedOp.AssertionGated.Spec on shifted operands at outer is_real = 1
    -- yields its body — which embeds U16CompareOp.Assertion.Spec carrying the
    -- compare_bit binarity.
    have h_lt_body := h_lt_unsigned h_is_real
    obtain ⟨h_u16cmp, _⟩ := h_lt_body
    have h_bit_bin : cols.lt_operation.result.u16_compare_operation.bit *
        (cols.lt_operation.result.u16_compare_operation.bit + -1) = 0 := by
      have h := h_u16cmp.1
      linear_combination h
    have h_bit_or : cols.lt_operation.result.u16_compare_operation.bit = 0 ∨
        cols.lt_operation.result.u16_compare_operation.bit = 1 := by
      binary_iff h_bit_bin
    -- Derive Word.isU64 #v[bit, 0, 0, 0] from bit ∈ {0,1}; other limbs are 0.
    have h_isU64_aw : Word.isU64
        (#v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0] :
          Word (ZMod p)) := by
      apply Word.isU64_of_cases
      · simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero]
        rcases h_bit_or with h | h <;> rw [h] <;>
          simp [ZMod.val_zero, ZMod.val_one]
      all_goals (simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ, ZMod.val_zero]; omega)
    refine ⟨h_isU64_aw, ?_, ?_⟩
    -- The remaining two BitVec equations (slt and sltu cases) require the
    -- full bit-equation derivation chain:
    -- (a) Bridge LtSignedOp.AssertionGated.Spec → raw LtOperationSigned.constraints.allHold
    --     For is_signed=1 (slt): use LtSignedOp.iff_sp1.mp (already proven).
    --     For is_signed=0 (sltu): construct manually — U16MSB constraints at
    --     mult=0 are vacuously true; LtUnsignedOp constraints follow via
    --     LtUnsignedOp.iff_sp1.mp on (b, c) since shifted = unshifted; 5 scalar
    --     gates discharge under is_signed=0 + b_msb=c_msb=0 (from sign-vacuity).
    -- (b) Apply LtOperationSigned.spec.signed / spec.unsigned to get
    --     bit = (if b.toInt < c.toInt then 1 else 0) / (b.toNat < c.toNat).
    -- (c) Convert bit equation to BitVec form via Word.toBitVec64_toInt /
    --     toBitVec64_toNat + BitVec.slt = (toInt < toInt) / BitVec.ult = ...
    --     + setWidth_64_ofBool unfolding.
    -- Forward-only — no Layer-0 dependency. ~120-180 LoC remaining.
    · intro _h_is_slt; sorry
    · intro _h_is_sltu; sorry

/-- **Backward** (completeness midpoint): peel the chip-level `FormalSpec`
apart into per-sub-circuit `Spec`s.

**Sorry (breadcrumb)** — peeling the semantic conjuncts (`aw = RV64.slt cw
bw` / `aw = RV64.sltu cw bw`) back into a `LtSignedOp.AssertionGated.Spec`
byte-decomp witness requires `LtOperationSigned.iff_sp1_full.mpr`, which
is Layer-0 sorry'd at
`SP1Operations/Compare/LtOperationSigned/LtOperationSigned.lean:529`. -/
lemma subcircuit_specs_of_formalSpec
    (cols : LtCols (ZMod p))
    (_h_is_real_sum : cols.is_slt + cols.is_sltu = 1)
    (_h_trusted : cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu)
    (_h_spec : Assertion.FormalSpec cols) :
    SP1Clean.LtSignedOp.AssertionGated.Spec
        ⟨cols.adapter.op_b_memory.prev_value,
         cols.adapter.op_c_memory.prev_value,
         cols.is_slt,
         cols.lt_operation.result.u16_compare_operation.bit,
         cols.lt_operation.result.u16_flags,
         cols.lt_operation.result.not_eq_inv,
         cols.lt_operation.result.comparison_limbs,
         cols.lt_operation.b_msb.msb,
         cols.lt_operation.c_msb.msb,
         cols.is_slt + cols.is_sltu⟩ ∧
    SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state,
         #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
         8, cols.is_slt + cols.is_sltu⟩ ∧
    SP1Clean.ALUTypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
         cols.is_slt * 9 + cols.is_sltu * 10,
         cols.state.pc,
         #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0],
         cols.adapter,
         cols.is_slt + cols.is_sltu,
         cols.adapter_cols.is_trusted⟩ ∧
    cols.is_slt * (cols.is_slt - 1) = 0 ∧
    cols.is_sltu * (cols.is_sltu - 1) = 0 ∧
    (cols.is_slt + cols.is_sltu) *
      (cols.is_slt + cols.is_sltu - 1) = 0 ∧
    cols.adapter.op_a_0 = 0 := by
  sorry

end SP1Clean.Lt
