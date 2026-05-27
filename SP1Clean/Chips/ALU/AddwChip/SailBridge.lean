import SP1Clean.Chips.ALU.AddwChip.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridge for `AddwChip`

AddwChip bundles two RV64IM variants — ADDW (R-type) and ADDIW (I-type) —
behind the shared `imm_c` flag at `cols.adapter.imm_c`. This file provides
two on-demand Sail-equivalence bridges, one per variant. Both consume the
chip-level `FormalSpec` (defined in `Cols.lean`) and produce the monadic
Sail equivalence to `_root_.Addw.spec_addw` / `_root_.Addiw.spec_addiw`.

Both bridges compose:
- `fromMain_toMain` (round-trip on the cols struct under the UserMode
  TrustMode marker, supplied by the chip's `Assumptions`),
- `allHold_iff_structural` (reconstruct `(Addw.constraints (toMain cols)).allHold`
  from the structural conjuncts of `FormalSpec`),
- `_root_.Addw.correct_addw` or `_root_.Addiw.correct_addw` (the
  Main-level Sail-equivalence proof). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addw

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Common bridge: reconstruct `(_root_.Addw.constraints (toMain cols)).allHold`
from the chip-level `FormalSpec` and the UserMode TrustMode marker. -/
private theorem allHold_of_formalSpec
    (cols : AddwCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted = cols.is_real)
    (h_is_real : cols.is_real = 1) :
    (_root_.Addw.constraints (toMain cols)).allHold := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_cpu, h_alu, h_op_a_0, _h_addwop_gated, h_sem⟩ := h_spec
  have h_round_trip := fromMain_toMain cols h_assumptions
  have h_isreal' : (toMain cols)[35] = 1 := h_is_real
  -- Re-state each cols-level Spec hypothesis through `fromMain (toMain cols)`
  -- (which equals `cols` by h_round_trip).
  have h_cpu' : SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨(fromMain (toMain cols)).state,
         #v[(fromMain (toMain cols)).state.pc[0] + 4,
            (fromMain (toMain cols)).state.pc[1],
            (fromMain (toMain cols)).state.pc[2]],
         8, (fromMain (toMain cols)).is_real⟩ := by
    rw [h_round_trip]; exact h_cpu
  have h_alu' : SP1Clean.ALUTypeReader.Gated.Assertion.Spec
        ⟨(fromMain (toMain cols)).state.clk_high,
         (fromMain (toMain cols)).state.clk_0_16 +
            (fromMain (toMain cols)).state.clk_16_24 * 65536, 19,
         (fromMain (toMain cols)).state.pc,
         #v[(fromMain (toMain cols)).addw_value[0],
            (fromMain (toMain cols)).addw_value[1],
            (fromMain (toMain cols)).addw_msb * 65535,
            (fromMain (toMain cols)).addw_msb * 65535],
         (fromMain (toMain cols)).adapter,
         (fromMain (toMain cols)).is_real,
         (fromMain (toMain cols)).adapter_cols.is_trusted⟩ := by
    rw [h_round_trip]; exact h_alu
  -- Apply h_sem under `is_real = 1` to recover the (isU64, BV64) pair.
  have h_pair := h_sem h_is_real
  obtain ⟨h_isU64_v, h_bv64⟩ := h_pair
  have h_isU64_v' : Word.isU64
      (#v[(toMain cols)[32], (toMain cols)[33],
          (toMain cols)[34] * 65535, (toMain cols)[34] * 65535]
        : Word (ZMod p)) := h_isU64_v
  have h_bv64' :
      Word.toBitVec64 (#v[(toMain cols)[32], (toMain cols)[33],
                           (toMain cols)[34] * 65535, (toMain cols)[34] * 65535]
        : Word (ZMod p)) =
      RV64.addw (Word.toBitVec64 (#v[(toMain cols)[25], (toMain cols)[26],
                                      (toMain cols)[27], (toMain cols)[28]]
                  : Word (ZMod p)))
                (Word.toBitVec64 (#v[(toMain cols)[15], (toMain cols)[16],
                                      (toMain cols)[17], (toMain cols)[18]]
                  : Word (ZMod p))) := h_bv64
  rw [allHold_iff_structural (toMain cols) h_isreal']
  exact ⟨h_cpu', h_alu', h_op_a_0, h_isU64_v', h_bv64'⟩

/-- Cols-level Sail bridge for ADDW (R-type, `imm_c = 0`). -/
theorem sail_correct_addw_of_formalSpec
    (cols : AddwCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted = cols.is_real)
    (h_is_real : cols.is_real = 1)
    (h_is_addw : cols.adapter.imm_c = 0)
    (s : SailState)
    (h_init : addwInitialState_cols cols s) :
    (sp1_addw_cols cols).run s =
      (_root_.Addw.spec_addw (.Regidx (sp1_op_c_cols cols))
                             (.Regidx (sp1_op_b_cols cols))
                             (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_round_trip := fromMain_toMain cols h_assumptions
  have h_state := h_init (toMain cols) h_round_trip
  have h_allHold := allHold_of_formalSpec cols h_spec h_assumptions h_is_real
  have h_isreal' : (toMain cols)[35] = 1 := h_is_real
  have h_is_addw' : (toMain cols)[31] = 0 := h_is_addw
  -- Apply Main-level `Addw.correct_addw`; the result reads `sp1_X (toMain cols)`,
  -- which is definitionally `sp1_X_cols cols` for each helper.
  exact (_root_.Addw.correct_addw (toMain cols) s h_allHold h_isreal' h_is_addw'
      h_state).symm

/-- Cols-level Sail bridge for ADDIW (I-type, `imm_c = 1`). -/
theorem sail_correct_addiw_of_formalSpec
    (cols : AddwCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : cols.adapter_cols.is_trusted = cols.is_real)
    (h_is_real : cols.is_real = 1)
    (h_is_addiw : cols.adapter.imm_c = 1)
    (s : SailState)
    (h_init : addwInitialState_cols cols s) :
    (sp1_addw_cols cols).run s =
      (_root_.Addiw.spec_addiw (sp1_op_c_imm_cols cols)
                               (.Regidx (sp1_op_b_cols cols))
                               (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_round_trip := fromMain_toMain cols h_assumptions
  have h_state := h_init (toMain cols) h_round_trip
  have h_allHold := allHold_of_formalSpec cols h_spec h_assumptions h_is_real
  have h_isreal' : (toMain cols)[35] = 1 := h_is_real
  have h_is_addiw' : (toMain cols)[31] = 1 := h_is_addiw
  exact (_root_.Addiw.correct_addw (toMain cols) s h_allHold h_isreal' h_is_addiw'
      h_state).symm

end SP1Clean.Addw
