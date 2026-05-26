import SP1Clean.SubwChip.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridge for `SubwChip`

Unlike AddwChip (which bundles ADDW + ADDIW), SubwChip is single-variant
(no SUBIW in RV64I), so this file exports a single bridge theorem
mirroring `SP1Clean/SubChip/SailBridge.lean`'s pattern.

`sail_correct_of_formalSpec` composes:
- `fromMain_toMain` (round-trip on the cols struct, conditional on the
  UserMode TrustMode marker from `Assumptions`),
- `allHold_iff_structural` (reconstruct `(Subw.constraints (toMain cols)).allHold`
  from the structural conjuncts of `FormalSpec`),
- `_root_.Subw.correct_subw` (the Main-level Sail-equivalence proof in
  `SP1Chips/Subw/SubwChip.lean`). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Subw

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem sail_correct_of_formalSpec
    (cols : SubwCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (s : SailState)
    (h_init : subwInitialState_cols cols s) :
    (sp1_subw_cols cols).run s =
      (_root_.Subw.spec_subw (.Regidx (sp1_op_c_cols cols))
                             (.Regidx (sp1_op_b_cols cols))
                             (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_cpu, h_rtr, h_op_a_0, h_sem⟩ := h_spec
  obtain ⟨h_trusted, h_is_real⟩ := h_assumptions
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_isreal' : (toMain cols)[31] = 1 := h_is_real
  -- Re-state each cols-level Spec hypothesis through `fromMain (toMain cols)`
  -- (which equals `cols` by h_round_trip); the `(fromMain (toMain cols)).Y`
  -- projections unfold to the matching `(toMain cols)[k]` / `#v[…]` forms
  -- by `@[reducible]` on `fromMain`/`toMain`, lining up with the goal
  -- `allHold_iff_structural` produces.
  have h_cpu' : SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨(fromMain (toMain cols)).state,
         #v[(fromMain (toMain cols)).state.pc[0] + 4,
            (fromMain (toMain cols)).state.pc[1],
            (fromMain (toMain cols)).state.pc[2]],
         8, (fromMain (toMain cols)).is_real⟩ := by
    rw [h_round_trip]; exact h_cpu
  have h_rtr' : SP1Clean.RTypeReader.Gated.Assertion.Spec
        ⟨(fromMain (toMain cols)).state.clk_high,
         (fromMain (toMain cols)).state.clk_0_16 +
            (fromMain (toMain cols)).state.clk_16_24 * 65536, 20,
         (fromMain (toMain cols)).state.pc,
         #v[(fromMain (toMain cols)).subw_value[0],
            (fromMain (toMain cols)).subw_value[1],
            (fromMain (toMain cols)).subw_msb * 65535,
            (fromMain (toMain cols)).subw_msb * 65535],
         (fromMain (toMain cols)).adapter,
         (fromMain (toMain cols)).is_real,
         (fromMain (toMain cols)).adapter_cols.is_trusted⟩ := by
    rw [h_round_trip]; exact h_rtr
  have h_sem' :
      HWord.isU32 (fromMain (toMain cols)).subw_value ∧
      HWord.toBitVec32 (fromMain (toMain cols)).subw_value =
        execute_RTYPEW_pure_32_w
          (fromMain (toMain cols)).adapter.op_b_memory.prev_value
          (fromMain (toMain cols)).adapter.op_c_memory.prev_value .SUBW ∧
      (fromMain (toMain cols)).subw_msb =
        if (HWord.toBitVec32 (fromMain (toMain cols)).subw_value).msb
        then 1 else 0 := by
    rw [h_round_trip]; exact h_sem h_is_real
  have h_allHold : (_root_.Subw.constraints (toMain cols)).allHold := by
    rw [allHold_iff_structural (toMain cols) h_isreal']
    exact ⟨h_cpu', h_rtr', h_op_a_0, h_sem'.1, h_sem'.2.1, h_sem'.2.2⟩
  -- Apply Main-level `Subw.correct_subw`; the result reads `sp1_X (toMain cols)`,
  -- which is definitionally `sp1_X_cols cols` for each helper.
  exact (_root_.Subw.correct_subw (toMain cols) s h_allHold h_isreal' h_state).symm

end SP1Clean.Subw
