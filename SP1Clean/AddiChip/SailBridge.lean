import SP1Clean.AddiChip.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridge for `AddiChip`

The chip's `Assertion.FormalSpec` (`Circuit.lean`) carries only a pure
BitVec `RV64.add` fact for the ALU semantic; the monadic Sail equivalence
to `_root_.Addi.spec_addi` is *not* in `FormalSpec`. This file provides the
on-demand bridge that downstream trace-Sail proofs invoke to recover the
Sail-monadic form.

`sail_correct_of_formalSpec` composes:
- `fromMain_toMain` (round-trip on the cols struct, conditional on the
  UserMode TrustMode marker from `Assumptions`),
- `allHold_iff_structural` (reconstruct `(Addi.constraints (toMain cols)).allHold`
  from the structural conjuncts of `FormalSpec`),
- `_root_.Addi.correct_addi` (the Main-level Sail-equivalence proof in
  `SP1Chips/Addi/AddiChip.lean`). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addi

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem sail_correct_of_formalSpec
    (cols : AddiCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_real : cols.is_real = 1)
    (s : SailState)
    (h_init : addiInitialState_cols cols s) :
    (sp1_addi_cols cols).run s =
      (_root_.Addi.spec_addi (sp1_op_c_cols cols)
                             (.Regidx (sp1_op_b_cols cols))
                             (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_addop, h_cpu, h_itr, h_op_a_0, _h_rv64add⟩ := h_spec
  -- Round-trip: `fromMain (toMain cols) = cols`, using the UserMode
  -- TrustMode marker from `Assumptions`.
  have h_round_trip := fromMain_toMain cols h_assumptions
  have h_state := h_init (toMain cols) h_round_trip
  -- `(toMain cols)[29] = cols.is_real = 1` reduces by `@[reducible]` toMain.
  have h_isreal' : (toMain cols)[29] = 1 := h_is_real
  -- Reconstruct SP1's `allHold` on `toMain cols` from the new Gated
  -- FormalSpec conjuncts via `fromMain (toMain cols)` ≡ `cols`.
  have h_addop' : SP1Clean.AddOp.RawSpec
        (fromMain (toMain cols)).adapter.op_b_memory.prev_value
        (fromMain (toMain cols)).adapter.op_c_imm
        (fromMain (toMain cols)).op_a_write_value := by
    rw [h_round_trip]; exact h_addop
  have h_cpu' : SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨(fromMain (toMain cols)).state,
         #v[(fromMain (toMain cols)).state.pc[0] + 4,
            (fromMain (toMain cols)).state.pc[1],
            (fromMain (toMain cols)).state.pc[2]],
         8, (fromMain (toMain cols)).is_real⟩ := by
    rw [h_round_trip]; exact h_cpu
  have h_itr' : SP1Clean.ITypeReader.Gated.Assertion.Spec
        ⟨(fromMain (toMain cols)).state.clk_high,
         (fromMain (toMain cols)).state.clk_0_16 +
            (fromMain (toMain cols)).state.clk_16_24 * 65536, 1,
         (fromMain (toMain cols)).state.pc,
         (fromMain (toMain cols)).op_a_write_value,
         (fromMain (toMain cols)).adapter,
         (fromMain (toMain cols)).is_real,
         (fromMain (toMain cols)).adapter_cols.is_trusted⟩ := by
    rw [h_round_trip]; exact h_itr
  have h_allHold : (_root_.Addi.constraints (toMain cols)).allHold := by
    rw [allHold_iff_structural (toMain cols) h_isreal']
    exact ⟨h_addop', h_cpu', h_itr', h_op_a_0⟩
  -- Apply Main-level `Addi.correct_addi`; the result reads `sp1_X (toMain cols)`,
  -- which is definitionally `sp1_X_cols cols` for each helper.
  exact (_root_.Addi.correct_addi (toMain cols) s h_allHold h_isreal' h_state).symm

end SP1Clean.Addi
