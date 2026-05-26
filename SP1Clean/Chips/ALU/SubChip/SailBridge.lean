import SP1Clean.Chips.ALU.SubChip.Circuit
import SP1Chips.Soundness
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # External Sail-equivalence bridge for `SubChip`

The chip's `Assertion.FormalSpec` (`Circuit.lean`) carries only a pure
BitVec `RV64.sub` fact for the ALU semantic; the monadic Sail equivalence
to `_root_.Sub.spec_sub` is *not* in `FormalSpec`. This file provides the
on-demand bridge that downstream trace-Sail proofs invoke to recover the
Sail-monadic form.

`sail_correct_of_formalSpec` composes:
- `fromMain_toMain` (round-trip on the cols struct, conditional on the
  UserMode TrustMode marker from `Assumptions`),
- `allHold_iff_structural` (reconstruct `(Sub.constraints (toMain cols)).allHold`
  from the structural conjuncts of `FormalSpec`),
- `_root_.Sub.correct_sub` (the Main-level Sail-equivalence proof in
  `SP1Chips/Sub/SubChip.lean`).

Mirrors `SP1Clean/AddChip/SailBridge.lean` 1-for-1 with `Add` → `Sub`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Sub

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem sail_correct_of_formalSpec
    (cols : SubCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_real : cols.is_real = 1)
    (s : SailState)
    (h_init : subInitialState_cols cols s) :
    (sp1_sub_cols cols).run s =
      (_root_.Sub.spec_sub (.Regidx (sp1_op_c_cols cols))
                           (.Regidx (sp1_op_b_cols cols))
                           (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_cpu, h_rtr, h_op_a_0, h_sem⟩ := h_spec
  obtain ⟨h_trusted, _⟩ := h_assumptions
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_isreal' : (toMain cols)[32] = 1 := h_is_real
  -- Reconstruct SP1's `allHold` on `toMain cols` from the structural conjuncts
  -- of the Gated FormalSpec. Each `h_X` cols-level Spec gets re-stated
  -- through `fromMain (toMain cols)` (≡ cols by h_round_trip); the
  -- `(fromMain (toMain cols)).Y` projections then unfold to the matching
  -- `(toMain cols)[k]` / `#v[…]` forms by `@[reducible]` on `fromMain`/`toMain`,
  -- lining up with the goal `allHold_iff_structural` produces.
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
            (fromMain (toMain cols)).state.clk_16_24 * 65536, 2,
         (fromMain (toMain cols)).state.pc,
         (fromMain (toMain cols)).op_a_write_value,
         (fromMain (toMain cols)).adapter,
         (fromMain (toMain cols)).is_real,
         (fromMain (toMain cols)).adapter_cols.is_trusted⟩ := by
    rw [h_round_trip]; exact h_rtr
  have h_sem' :
      Word.isU64 (fromMain (toMain cols)).op_a_write_value ∧
      Word.toBitVec64 (fromMain (toMain cols)).op_a_write_value =
        RV64.sub
          (Word.toBitVec64
            (fromMain (toMain cols)).adapter.op_c_memory.prev_value)
          (Word.toBitVec64
            (fromMain (toMain cols)).adapter.op_b_memory.prev_value) := by
    rw [h_round_trip]; exact h_sem h_is_real
  have h_allHold : (_root_.Sub.constraints (toMain cols)).allHold := by
    rw [allHold_iff_structural (toMain cols) h_isreal']
    exact ⟨h_cpu', h_rtr', h_op_a_0, h_sem'.1, h_sem'.2⟩
  -- Apply Main-level `Sub.correct_sub`; the result reads `sp1_X (toMain cols)`,
  -- which is definitionally `sp1_X_cols cols` for each helper.
  exact (_root_.Sub.correct_sub (toMain cols) s h_allHold h_isreal' h_state).symm

end SP1Clean.Sub
