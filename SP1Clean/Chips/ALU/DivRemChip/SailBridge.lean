import SP1Clean.Chips.ALU.DivRemChip.Circuit
import SP1Chips.DivRem.DivRemChip

/-! # Sail-equivalence bridge for `DivRemChip` (8 variants)

8 Sail-equivalence theorems — one per variant
(`div`/`divu`/`rem`/`remu`/`divw`/`remw`/`divuw`/`remuw`) — each a thin
re-export of the corresponding variant `_root_.<Variant>.correct_*` from
`SP1Chips/DivRem/DivRemChip.lean`. Each takes the SP1 row `Main`, the
chip's `.allHold`, the variant flag (`is_<v>`), and the initial-state
witness; produces the Sail-monadic equivalence
`(spec_<v> ...).run s = (sp1_op Main).run s`.

## Why these are Main-form (not cols/FormalSpec-form)

The canonical AddChip pattern wraps Sail equivalence behind a cols-level
`FormalSpec` (via `sail_correct_of_formalSpec`). That works for AddChip
because `AddOperation.iff_sp1_full` is bidirectional — `FormalSpec` can
be reverted to `(constraints Main).allHold` to invoke the SP1-level
`correct_add`. DivRem has no chip-level `iff_sp1_full` (only forward
variant lemmas), and `MulOperation` ships only `of_sp1` (forward); a
genuine `FormalSpec → allHold` reconstruction is unprovable without
`MulOperation.iff_sp1_full` (per CLEAN_FUTURE.md Phase B6).

Until that lands upstream, this bridge stays at the `.allHold` boundary
— callers carry `(_root_.DivRem.constraints Main).allHold` directly,
which trace-soundness machinery already produces. -/

set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

namespace SP1Clean.DivRem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]

/-- `div` (RV64M 64-bit signed division): re-export of
`_root_.DivRem.Poly.correct_div`. -/
theorem sail_correct_div_of_allHold
    (Main : Vector (ZMod p) 246) (s : SailState)
    (cstrs : (_root_.DivRem.constraints Main).allHold)
    (h_is_real : _root_.DivRem.is_real Main)
    (h_is_div : _root_.DivRem.is_div Main)
    (state_cstrs : (_root_.DivRem.constraints Main).initialState s) :
    let op_c := _root_.DivRem.sp1_op_c Main
    let op_b := _root_.DivRem.sp1_op_b Main
    let op_a := _root_.DivRem.sp1_op_a Main
    (_root_.Div.spec_div (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.DivRem.Poly.sp1_op Main).run s :=
  _root_.DivRem.Poly.correct_div Main s cstrs h_is_real h_is_div state_cstrs

/-- `divu` (RV64M 64-bit unsigned division). -/
theorem sail_correct_divu_of_allHold
    (Main : Vector (ZMod p) 246) (s : SailState)
    (cstrs : (_root_.DivRem.constraints Main).allHold)
    (h_is_real : _root_.DivRem.is_real Main)
    (h_is_divu : _root_.DivRem.is_divu Main)
    (state_cstrs : (_root_.DivRem.constraints Main).initialState s) :
    let op_c := _root_.DivRem.sp1_op_c Main
    let op_b := _root_.DivRem.sp1_op_b Main
    let op_a := _root_.DivRem.sp1_op_a Main
    (_root_.Divu.spec_divu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.DivRem.Poly.sp1_op Main).run s :=
  _root_.DivRem.Poly.correct_divu Main s cstrs h_is_real h_is_divu state_cstrs

/-- `rem` (RV64M 64-bit signed remainder). -/
theorem sail_correct_rem_of_allHold
    (Main : Vector (ZMod p) 246) (s : SailState)
    (cstrs : (_root_.DivRem.constraints Main).allHold)
    (h_is_real : _root_.DivRem.is_real Main)
    (h_is_rem : _root_.DivRem.is_rem Main)
    (state_cstrs : (_root_.DivRem.constraints Main).initialState s) :
    let op_c := _root_.DivRem.sp1_op_c Main
    let op_b := _root_.DivRem.sp1_op_b Main
    let op_a := _root_.DivRem.sp1_op_a Main
    (_root_.Rem.spec_rem (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.DivRem.Poly.sp1_op Main).run s :=
  _root_.DivRem.Poly.correct_rem Main s cstrs h_is_real h_is_rem state_cstrs

/-- `remu` (RV64M 64-bit unsigned remainder). -/
theorem sail_correct_remu_of_allHold
    (Main : Vector (ZMod p) 246) (s : SailState)
    (cstrs : (_root_.DivRem.constraints Main).allHold)
    (h_is_real : _root_.DivRem.is_real Main)
    (h_is_remu : _root_.DivRem.is_remu Main)
    (state_cstrs : (_root_.DivRem.constraints Main).initialState s) :
    let op_c := _root_.DivRem.sp1_op_c Main
    let op_b := _root_.DivRem.sp1_op_b Main
    let op_a := _root_.DivRem.sp1_op_a Main
    (_root_.Remu.spec_remu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.DivRem.Poly.sp1_op Main).run s :=
  _root_.DivRem.Poly.correct_remu Main s cstrs h_is_real h_is_remu state_cstrs

/-- `divw` (RV64M 32-bit signed division, sign-extended to 64 bits). -/
theorem sail_correct_divw_of_allHold
    (Main : Vector (ZMod p) 246) (s : SailState)
    (cstrs : (_root_.DivRem.constraints Main).allHold)
    (h_is_real : _root_.DivRem.is_real Main)
    (h_is_divw : _root_.DivRem.is_divw Main)
    (state_cstrs : (_root_.DivRem.constraints Main).initialState s) :
    let op_c := _root_.DivRem.sp1_op_c Main
    let op_b := _root_.DivRem.sp1_op_b Main
    let op_a := _root_.DivRem.sp1_op_a Main
    (_root_.Divw.spec_divw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.DivRem.Poly.sp1_op Main).run s :=
  _root_.DivRem.Poly.correct_divw Main s cstrs h_is_real h_is_divw state_cstrs

/-- `remw` (RV64M 32-bit signed remainder, sign-extended). -/
theorem sail_correct_remw_of_allHold
    (Main : Vector (ZMod p) 246) (s : SailState)
    (cstrs : (_root_.DivRem.constraints Main).allHold)
    (h_is_real : _root_.DivRem.is_real Main)
    (h_is_remw : _root_.DivRem.is_remw Main)
    (state_cstrs : (_root_.DivRem.constraints Main).initialState s) :
    let op_c := _root_.DivRem.sp1_op_c Main
    let op_b := _root_.DivRem.sp1_op_b Main
    let op_a := _root_.DivRem.sp1_op_a Main
    (_root_.Remw.spec_remw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.DivRem.Poly.sp1_op Main).run s :=
  _root_.DivRem.Poly.correct_remw Main s cstrs h_is_real h_is_remw state_cstrs

/-- `divuw` (RV64M 32-bit unsigned division, zero-extended). -/
theorem sail_correct_divuw_of_allHold
    (Main : Vector (ZMod p) 246) (s : SailState)
    (cstrs : (_root_.DivRem.constraints Main).allHold)
    (h_is_real : _root_.DivRem.is_real Main)
    (h_is_divuw : _root_.DivRem.is_divuw Main)
    (state_cstrs : (_root_.DivRem.constraints Main).initialState s) :
    let op_c := _root_.DivRem.sp1_op_c Main
    let op_b := _root_.DivRem.sp1_op_b Main
    let op_a := _root_.DivRem.sp1_op_a Main
    (_root_.Divuw.spec_divuw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.DivRem.Poly.sp1_op Main).run s :=
  _root_.DivRem.Poly.correct_divuw Main s cstrs h_is_real h_is_divuw state_cstrs

/-- `remuw` (RV64M 32-bit unsigned remainder). -/
theorem sail_correct_remuw_of_allHold
    (Main : Vector (ZMod p) 246) (s : SailState)
    (cstrs : (_root_.DivRem.constraints Main).allHold)
    (h_is_real : _root_.DivRem.is_real Main)
    (h_is_remuw : _root_.DivRem.is_remuw Main)
    (state_cstrs : (_root_.DivRem.constraints Main).initialState s) :
    let op_c := _root_.DivRem.sp1_op_c Main
    let op_b := _root_.DivRem.sp1_op_b Main
    let op_a := _root_.DivRem.sp1_op_a Main
    (_root_.Remuw.spec_remuw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.DivRem.Poly.sp1_op Main).run s :=
  _root_.DivRem.Poly.correct_remuw Main s cstrs h_is_real h_is_remuw state_cstrs

end SP1Clean.DivRem
