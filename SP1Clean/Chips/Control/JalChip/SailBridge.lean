import SP1Clean.Chips.Control.JalChip.Circuit
import SP1Chips.Soundness

/-! # External Sail-equivalence bridge for `JalChip`

The chip's `Assertion.FormalSpec` (`Chips/Spec.lean`) carries only structural
sub-circuit Specs (CPUState.Gated, AddOp × 2, JTypeReader.Gated, alignment
lookup) — the per-row Sail-monadic equivalence to `_root_.Jal.spec_jal` is
*not* in `FormalSpec`. This file provides the on-demand bridge that
downstream trace-Sail proofs invoke to recover the Sail-monadic form.

`sail_correct_of_formalSpec` composes:
- `fromMain_toMain` (round-trip on the cols struct, conditional on the
  UserMode TrustMode marker from `Assumptions`),
- `allHold_iff_structural` (reconstruct `(Jal.constraints (toMain cols)).allHold`
  from the structural conjuncts of `FormalSpec`),
- `_root_.Jal.SP1JAL_correct` (the Main-level Sail-equivalence proof in
  `SP1Chips/Jal/JalChip.lean`),
- A `BitVec.ofNat 5 = ·#'h` bridge for the cols-level `sp1_op_a_cols`,
  whose Main-level counterpart `Jal.sp1_op_a Main cstrs h_is_real` carries
  the dependent `< 32` register-index bound. Both forms coincide as
  `BitVec 5` values under `Main[6].val < 32`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Jal

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

open LeanRV64D.Functions BitVec Sail

theorem sail_correct_of_formalSpec
    (cols : JalCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (s : SailState)
    (h_init : jalInitialState_cols cols s)
    (hs : SailState.isInitialized s) :
    (sp1_jal_cols cols).run s =
      (_root_.Jal.spec_jal (sp1_op_b_cols cols)
        (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_trusted, h_is_real, _h_isU64_pc, _h_isU64_opb⟩ := h_assumptions
  -- Round-trip: `fromMain (toMain cols) = cols`, using the UserMode
  -- TrustMode marker from `Assumptions`.
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_isreal' : (toMain cols)[30] = 1 := h_is_real
  -- Lift each structural FormalSpec conjunct from cols to `fromMain (toMain cols)`
  -- so the `@[reducible] toMain`/`fromMain` projections unfold to the literal
  -- `(toMain cols)[k]` / `#v[…]` form expected by `allHold_iff_structural`'s RHS.
  obtain ⟨h_cpu, h_addop_jump, h_addop_ret, h_jtr, h_next_pc_3, h_op_a_w_3,
          h_or_gate, h_align⟩ := h_spec
  -- Each sub-Spec rewritten through h_round_trip ≡ cols.
  have h_cpu' : SP1Clean.CPUState.Gated.Assertion.Spec
      ⟨(fromMain (toMain cols)).state,
       #v[(fromMain (toMain cols)).next_pc[0], (fromMain (toMain cols)).next_pc[1],
          (fromMain (toMain cols)).next_pc[2]],
       8, (fromMain (toMain cols)).is_real⟩ := by
    rw [h_round_trip]; exact h_cpu
  have h_addop_jump' : SP1Clean.AddOp.Assertion.Spec
      ⟨(fromMain (toMain cols)).state.pc.push 0,
       (fromMain (toMain cols)).adapter.op_b_imm,
       (fromMain (toMain cols)).next_pc,
       (fromMain (toMain cols)).is_real⟩ := by
    rw [h_round_trip]; exact h_addop_jump
  have h_addop_ret' : SP1Clean.AddOp.Assertion.Spec
      ⟨(fromMain (toMain cols)).state.pc.push 0,
       #v[(4 : ZMod p), 0, 0, 0],
       (fromMain (toMain cols)).op_a_write_value,
       (fromMain (toMain cols)).is_real - (fromMain (toMain cols)).adapter.op_a_0⟩ := by
    rw [h_round_trip]; exact h_addop_ret
  have h_jtr' : SP1Clean.JTypeReader.Gated.Assertion.Spec
      ⟨(fromMain (toMain cols)).state.clk_high,
       (fromMain (toMain cols)).state.clk_0_16 +
         (fromMain (toMain cols)).state.clk_16_24 * 65536, 46,
       (fromMain (toMain cols)).state.pc,
       (fromMain (toMain cols)).op_a_write_value,
       (fromMain (toMain cols)).adapter,
       (fromMain (toMain cols)).is_real,
       (fromMain (toMain cols)).adapter_cols.is_trusted⟩ := by
    rw [h_round_trip]; exact h_jtr
  -- Reshape Gated.Spec to the `1, 1` pinning form expected by allHold_iff_structural.
  have h_jtr_pinned : SP1Clean.JTypeReader.Gated.Assertion.Spec
      ⟨(fromMain (toMain cols)).state.clk_high,
       (fromMain (toMain cols)).state.clk_0_16 +
         (fromMain (toMain cols)).state.clk_16_24 * 65536, 46,
       (fromMain (toMain cols)).state.pc,
       (fromMain (toMain cols)).op_a_write_value,
       (fromMain (toMain cols)).adapter,
       1, 1⟩ := by
    have h1 : (fromMain (toMain cols)).is_real = 1 := by rw [h_round_trip]; exact h_is_real
    have h2 : (fromMain (toMain cols)).adapter_cols.is_trusted = 1 := by
      rw [h_round_trip]; rw [h_trusted]; exact h_is_real
    have := h_jtr'
    rw [h1, h2] at this
    exact this
  have h_next_pc_3' : (fromMain (toMain cols)).next_pc[3] = 0 := by
    rw [h_round_trip]; exact h_next_pc_3
  have h_op_a_w_3' : (fromMain (toMain cols)).op_a_write_value[3] = 0 := by
    rw [h_round_trip]; exact h_op_a_w_3
  have h_or_gate' :
      (fromMain (toMain cols)).is_real = 1 ∨
      (fromMain (toMain cols)).adapter.op_a_0 = 0 := by
    rw [h_round_trip]; exact h_or_gate
  have h_align' :
      (fromMain (toMain cols)).is_real = 1 →
        ((fromMain (toMain cols)).next_pc[0] * (4 : ZMod p)⁻¹).val < 16384 := by
    rw [h_round_trip]; exact h_align
  -- Assemble allHold via allHold_iff_structural. The RHS's literal Vector
  -- forms `#v[Main[k], …]` line up with `(fromMain (toMain cols)).X[i]` via
  -- @[reducible] fromMain.
  have h_allHold : (_root_.Jal.constraints (toMain cols)).allHold := by
    rw [allHold_iff_structural (toMain cols) h_isreal']
    exact ⟨h_cpu', h_addop_jump', h_addop_ret', h_jtr_pinned,
           h_next_pc_3', h_op_a_w_3', h_or_gate', h_align'⟩
  -- Apply Main-level `Jal.SP1JAL_correct` and bridge sp1_op_a's dependent form
  -- to the cols-level `BitVec.ofNat 5 …` form.
  have h_eq := (_root_.Jal.SP1JAL_correct (toMain cols) s h_allHold h_isreal'
    h_state hs).symm
  have h_op_a_lt32 : (toMain cols)[6].val < 32 :=
    _root_.Jal.op_a_lt32_of_constraints h_allHold h_isreal'
  have h_op_a_bridge :
      sp1_op_a_cols cols = _root_.Jal.sp1_op_a (toMain cols) h_allHold h_isreal' := by
    change BitVec.ofNat 5 cols.adapter.op_a.val
         = (toMain cols)[6].val#'h_op_a_lt32
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ofNat, BitVec.toNat_ofNatLT]
    change cols.adapter.op_a.val % 2 ^ 5 = (toMain cols)[6].val
    rw [Nat.mod_eq_of_lt (show cols.adapter.op_a.val < 2 ^ 5 from h_op_a_lt32)]
    rfl
  have h_jal_bridge :
      (sp1_jal_cols cols).run s = (_root_.Jal.sp1_jal (toMain cols)).run s := rfl
  rw [h_op_a_bridge, h_jal_bridge]
  change (_root_.Jal.sp1_jal (toMain cols)).run s
       = (_root_.Jal.spec_jal (_root_.Jal.sp1_op_b (toMain cols))
          (.Regidx (_root_.Jal.sp1_op_a (toMain cols) h_allHold h_isreal'))).run s
  exact h_eq

end SP1Clean.Jal
