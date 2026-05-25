import SP1Clean.AddChip.Circuit
import SP1Chips.Soundness
import RISCV.SailToRV64
import RISCV.SailPureToInstructions

/-! # External Sail-equivalence bridge for `AddChip`

The chip's `Assertion.FormalSpec` (`Circuit.lean`) carries only a pure
BitVec `RV64.add` fact for the ALU semantic; the monadic Sail equivalence
to `_root_.Add.spec_add` is *not* in `FormalSpec`. This file provides the
on-demand bridge that downstream trace-Sail proofs invoke to recover the
Sail-monadic form.

`sail_correct_of_formalSpec` composes:
- `fromMain_toMain` (round-trip on the cols struct, conditional on the
  UserMode TrustMode marker from `Assumptions`),
- `allHold_iff_structural` (reconstruct `(Add.constraints (toMain cols)).allHold`
  from the structural conjuncts of `FormalSpec`),
- `_root_.Add.correct_add` (the Main-level Sail-equivalence proof in
  `SP1Chips/Add/AddChip.lean`).

A future iteration may swap the `Add.correct_add` invocation for the
direct `RISCV.SailToRV64.rtype_add_eq` +
`RISCV.SailPureToInstructions.rtype_add_eq` bridge from the
`succinctlabs/riscv-lean` fork — the BitVec equation in `FormalSpec`
makes that lift trivial once those bridge lemmas are wired through
Sail's `skeleton_binary` unfolding. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Add

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem sail_correct_of_formalSpec
    (cols : AddCols (ZMod p))
    (h_spec : Assertion.FormalSpec cols)
    (h_assumptions : Assertion.Assumptions cols)
    (h_is_real : cols.is_real = 1)
    (s : SailState)
    (h_init : addInitialState_cols cols s) :
    (sp1_add_cols cols).run s =
      (_root_.Add.spec_add (.Regidx (sp1_op_c_cols cols))
                           (.Regidx (sp1_op_b_cols cols))
                           (.Regidx (sp1_op_a_cols cols))).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_addop, h_cpu, h_rtr, h_isreal, h_op_a_0, _h_rv64add⟩ := h_spec
  -- Round-trip: `fromMain (toMain cols) = cols`, using the UserMode
  -- TrustMode marker from `Assumptions`.
  have h_round_trip := fromMain_toMain cols h_assumptions
  have h_state := h_init (toMain cols) h_round_trip
  -- `(toMain cols)[32] = cols.is_real = 1` reduces by `@[reducible]` toMain.
  have h_isreal' : (toMain cols)[32] = 1 := h_is_real
  -- Reconstruct SP1's `allHold` on `toMain cols` from the structural conjuncts.
  -- Trick: re-state each cols-level Spec hypothesis through `fromMain (toMain cols)`
  -- (which equals `cols` by h_round_trip). The `(fromMain (toMain cols)).X`
  -- projections then unfold to the matching `(toMain cols)[k]` / `#v[…]` forms
  -- by `@[reducible]` on `fromMain` and `toMain`, lining up with the goal that
  -- `allHold_iff_structural` produces.
  have h_addop' : SP1Clean.AddOp.Spec
        (fromMain (toMain cols)).adapter.op_b_memory.prev_value
        (fromMain (toMain cols)).adapter.op_c_memory.prev_value
        (fromMain (toMain cols)).op_a_write_value := by
    rw [h_round_trip]; exact h_addop
  have h_rtr' : SP1Clean.RTypeReader.rtypeReaderSpec
        ((fromMain (toMain cols)).state.clk_0_16 +
            (fromMain (toMain cols)).state.clk_16_24 * 65536) 0
        (fromMain (toMain cols)).state.pc
        (fromMain (toMain cols)).op_a_write_value
        (fromMain (toMain cols)).adapter := by
    rw [h_round_trip]; exact h_rtr
  have h_allHold : (_root_.Add.constraints (toMain cols)).allHold := by
    rw [allHold_iff_structural (toMain cols) h_isreal']
    refine ⟨h_addop', h_cpu, h_rtr', ?_, h_op_a_0⟩
    change cols.is_real * (cols.is_real - 1) = 0
    linear_combination h_isreal
  -- Apply Main-level `Add.correct_add`; the result reads `sp1_X (toMain cols)`,
  -- which is definitionally `sp1_X_cols cols` for each helper.
  exact (_root_.Add.correct_add (toMain cols) s h_allHold h_isreal' h_state).symm

end SP1Clean.Add
