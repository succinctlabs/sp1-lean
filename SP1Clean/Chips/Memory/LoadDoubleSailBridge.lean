import SP1Clean.Chips.Memory.LoadDoubleSailCols

/-! # External Sail-equivalence bridge for `LoadDoubleChip`

Pilot for the per-chip Sail bridge pattern, mirroring
`SP1Clean/Chips/ALU/AddChip/SailBridge.lean`. The chip's
`AssertionGated.FormalSpec` (`SP1Clean/Chips/Spec.lean`) carries the
structural sub-circuit Specs plus a semantic `Word.isU64 load_prev_value`
clause (conditional on `is_real = 1`); the monadic Sail equivalence to
`_root_.Load.LoadDouble.spec_ld` is *not* in `FormalSpec`. This file
provides the on-demand bridge `sail_correct_of_allHold`.

## Design note

Unlike `AddChip/SailBridge.lean` which derives `allHold` from `FormalSpec`
via `allHold_iff_structural`, the LoadDouble bridge takes `allHold` directly
as a precondition. This sidesteps a non-trivial structural bridge (the
chip's FormalSpec uses `Assertion.Spec` forms while `_root_.Load.LoadDouble.correct_ld`
needs the SP1-native `constraints.allHold`; the existing `iff_sp1_of_is_ld`
proves `constraints.allHold ↔ SpecForIff_of_is_ld` but `SpecForIff_of_is_ld`
uses *legacy* `cpuStateSpec`/`itypeReaderSpec` forms that don't directly
match the `Assertion.Spec` forms in `FormalSpec`).

Trace-level callers compute `(toMain cols)` and discharge `allHold` via
`iff_sp1_of_is_ld` (which they already have for the chip's iff bridge).
The chip's `AssertionGated.FormalSpec` + `Assumptions` (carrying
`LoadMemoryAccessGated.Contract`) remain the canonical Clean-DSL surface;
this file is the on-ramp to the Sail-equivalence theorem.

A future refactor (Phase 4 alongside Byte/Half/Word) can replace the
direct `allHold` precondition with a full `FormalSpec`-driven derivation
once the per-sub-circuit `Assertion.Spec ↔ legacy Spec` bridges are
extracted as reusable lemmas. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions Sail SailState

namespace SP1Clean.LoadDouble

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The cols-level Sail equivalence: given the chip's `Assumptions`,
the round-trip TrustMode assumption, `is_real = 1`, the SP1-native
`allHold` (discharged via `iff_sp1_of_is_ld`), the cols-level
`initialState`, and the standard Sail preconditions, the chip's
`sp1_ld_cols` matches the Sail `spec_ld`. -/
theorem sail_correct_of_allHold
    (cols : LoadDoubleCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real)
    (h_is_real : cols.is_real = 1)
    (h_cstrs : (_root_.Load.LoadDouble.constraints (toMain cols)).allHold)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_init : loadDoubleInitialState_cols cols s)
    (h_fits_in_mem :
      let reg_val :=
        (Word.toBitVec64 cols.adapter.op_b_memory.prev_value).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c_cols cols)).toNat
      reg_val + offset + 8 < 2 ^ 64)
    (h_is_aligned :
      is_aligned_vaddr (virtaddr.Virtaddr
        (Word.toBitVec64 cols.adapter.op_b_memory.prev_value +
          BitVec.signExtend 64 (sp1_imm_c_cols cols))) 8 = true) :
    (_root_.Load.LoadDouble.spec_ld
        (sp1_imm_c_cols cols)
        (.Regidx (sp1_op_b_cols cols))
        (.Regidx (sp1_op_a_cols cols))).run s =
      (sp1_ld_cols cols).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Round-trip: `fromMain (toMain cols) = cols`.
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  -- `(toMain cols)[38] = cols.is_real = 1` reduces by `@[reducible]` toMain.
  have h_is_ld : (toMain cols)[38] = 1 := h_is_real
  -- Reduce the Main-level preconditions of `correct_ld`:
  -- The `(toMain cols)[15..18]` indexing reduces to `cols.adapter.op_b_memory.prev_value`
  -- limbs by `@[reducible]` `toMain`; similarly `(toMain cols)[21]` reduces to
  -- `cols.adapter.op_c_imm[0]`. Wrap in the helper-form expected by `correct_ld`.
  have h_fits_main :
      let reg_val :=
        (Word.toBitVec64 #v[(toMain cols)[15], (toMain cols)[16],
                            (toMain cols)[17], (toMain cols)[18]]).toNat
      let offset := (BitVec.signExtend 64
        (_root_.Load.LoadDouble.sp1_imm_c (toMain cols))).toNat
      reg_val + offset + 8 < 2 ^ 64 := by
    simpa using h_fits_in_mem
  have h_align_main : is_aligned_vaddr (virtaddr.Virtaddr
        (Word.toBitVec64 #v[(toMain cols)[15], (toMain cols)[16],
                            (toMain cols)[17], (toMain cols)[18]] +
          BitVec.signExtend 64
            (BitVec.ofNat 12 ((toMain cols)[21].val)))) 8 = true := by
    simpa [sp1_imm_c_cols] using h_is_aligned
  -- Apply Main-level `Load.LoadDouble.correct_ld`.
  have h_main := _root_.Load.LoadDouble.correct_ld (toMain cols) s hs hs_config
    h_cstrs h_state h_is_ld h_fits_main h_align_main
  -- h_main has form `(spec_ld (sp1_imm_c (toMain cols)) (.Regidx (sp1_ob_b _))
  --   (.Regidx (sp1_op_a _))).run s = (sp1_ld (toMain cols)).run s`. Bridge to
  -- cols form via the round-trip simp lemmas.
  simp only at h_main
  -- Pre-rewrite both sides into cols form before .symm to match the goal.
  rw [show _root_.Load.LoadDouble.sp1_ld (toMain cols) = sp1_ld_cols cols from by
    rw [← sp1_ld_cols_fromMain, h_round_trip],
   show _root_.Load.LoadDouble.sp1_imm_c (toMain cols) = sp1_imm_c_cols cols from by
    rw [← sp1_imm_c_cols_fromMain, h_round_trip],
   show _root_.Load.LoadDouble.sp1_ob_b (toMain cols) = sp1_op_b_cols cols from by
    rw [← sp1_op_b_cols_fromMain, h_round_trip],
   show _root_.Load.LoadDouble.sp1_op_a (toMain cols) = sp1_op_a_cols cols from by
    rw [← sp1_op_a_cols_fromMain, h_round_trip]] at h_main
  exact h_main

end SP1Clean.LoadDouble
