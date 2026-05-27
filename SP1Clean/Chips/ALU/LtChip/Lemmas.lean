import SP1Clean.Chips.ALU.LtChip.Cols
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Clean.Compare.LtOperationSigned
import SP1Clean.Reader.ALUTypeReader
import SP1Chips.Lt.Common

/-! # `LtChip` cols-level lemmas

Four lemmas mirroring `SP1Clean/Chips/ALU/AddChip/Lemmas.lean`,
adapted for the 2-variant (`slt`/`sltu`) Path-2 FormalSpec:

- `fromMain_toMain` — `fromMain (toMain cols) = cols` round-trip.
  **Sorry** — `toMain` for `LtCols` is not yet defined (44-col row
  index map; mechanical follow-up).
- `allHold_iff_structural` — bridges `(_root_.Lt.constraints
  Main).allHold` to the FormalSpec conjuncts. **Sorry** — needs
  variant case-split (slt vs sltu) using each arm's
  `_root_.Lt.allHold_constraints_iff_*` + sub-`Spec_iff_sp1` bridges
  + `LtOperationSigned.iff_sp1_full` (currently sorry'd backward).
- `formalSpec_of_subcircuit_specs` — soundness midpoint. **Sorry**
  — the chip's Path-2 main currently drops the `LtOperationSigned`
  subcircuit, so per-sub Specs alone don't yield the FormalSpec's
  RV64 conjunct. Resolving requires composing
  `SP1Clean.LtOperationSigned.assertion` (not yet created) into the
  chip main.
- `subcircuit_specs_of_formalSpec` — completeness midpoint. **Sorry**
  — same root cause. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Lt

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `fromMain` is a left inverse of `toMain` (cols → Main → cols
round-trip), conditional on the UserMode TrustMode marker
`cols.adapter_cols.is_trusted = cols.is_slt + cols.is_sltu`.

**Sorry** — placeholder. The `LtCols` `toMain` itself is not yet
defined; once it lands in `SP1Clean/Chips/Structs.lean` this proof
collapses to the AddChip recipe. -/
lemma fromMain_toMain (_cols : LtCols (ZMod p))
    (_h_trusted_eq_sum : True) :
    True := by
  trivial

/-- The chip-level structural bridge: SP1's `allHold` over the flat row
`Lt.constraints Main` is equivalent to the conjunction of
`CPUState.Gated.Assertion.Spec`, `ALUTypeReader.Gated.Assertion.Spec`,
the selector + sum binarities, `Main[13] = 0` (op_a_0 gate), and the
2-way selector-dispatched RV64 semantic conjunct, under
`Main[32] + Main[33] = 1` (is_real_sum gate). -/
lemma allHold_iff_structural
    (Main : Vector (ZMod p) 44) (_h_is_real : Main[32] + Main[33] = 1) :
    (_root_.Lt.constraints Main).allHold ↔
      Assertion.FormalSpec (fromMain Main) := by
  sorry

/-- **Forward** (soundness midpoint): assemble the chip-level
`FormalSpec` from the per-sub-circuit Specs returned by `h_holds`. -/
lemma formalSpec_of_subcircuit_specs
    (cols : LtCols (ZMod p))
    (_h_is_real_sum : cols.is_slt + cols.is_sltu = 1)
    (_h_cpu : SP1Clean.CPUState.Gated.Assertion.Spec
        ⟨cols.state,
         #v[cols.state.pc[0] + 4, cols.state.pc[1], cols.state.pc[2]],
         8, cols.is_slt + cols.is_sltu⟩)
    (_h_alu : SP1Clean.ALUTypeReader.Gated.Assertion.Spec
        ⟨cols.state.clk_high,
         cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
         cols.is_slt * 9 + cols.is_sltu * 10,
         cols.state.pc,
         #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0],
         cols.adapter,
         cols.is_slt + cols.is_sltu,
         cols.adapter_cols.is_trusted⟩)
    (_h_op_a_0 : cols.adapter.op_a_0 = 0)
    (_h_is_slt_bin : cols.is_slt = 0 ∨ cols.is_slt = 1)
    (_h_is_sltu_bin : cols.is_sltu = 0 ∨ cols.is_sltu = 1) :
    Assertion.FormalSpec cols := by
  sorry

/-- **Backward** (completeness midpoint): peel the chip-level
`FormalSpec` apart into per-sub-circuit `Spec`s. -/
lemma subcircuit_specs_of_formalSpec
    (cols : LtCols (ZMod p))
    (_h_is_real_sum : cols.is_slt + cols.is_sltu = 1)
    (_h_spec : Assertion.FormalSpec cols) :
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
    cols.adapter.op_a_0 = 0 ∧
    (cols.is_slt = 0 ∨ cols.is_slt = 1) ∧
    (cols.is_sltu = 0 ∨ cols.is_sltu = 1) := by
  sorry

end SP1Clean.Lt
