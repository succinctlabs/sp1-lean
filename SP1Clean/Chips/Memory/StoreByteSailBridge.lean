import SP1Clean.Chips.Memory.StoreByteChip

/-! # External Sail-equivalence bridge for `StoreByteChip`

Mirrors `StoreDoubleSailBridge.lean` for the byte (width 1) variant.
Takes `(StoreByte.constraints (toMain cols)).allHold` directly. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions Sail SailState

namespace SP1Clean.StoreByte

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem sail_correct_of_allHold
    (cols : StoreByteCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_real)
    (h_is_real : cols.is_real = 1)
    (h_cstrs : (_root_.Store.StoreByte.constraints (toMain cols)).allHold)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_init : storeByteInitialState_cols cols s)
    (h_fits_in_mem :
      let reg_val :=
        (Word.toBitVec64 cols.adapter.op_b_memory.prev_value).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c_cols cols)).toNat
      reg_val + offset + 1 < 2 ^ 64) :
    (_root_.Store.StoreByte.spec_sb
        (sp1_imm_c_cols cols)
        (.Regidx (sp1_op_a_cols cols))
        (.Regidx (sp1_op_b_cols cols))).run s =
      (sp1_sb_cols cols).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_is_real_main : (toMain cols)[49] = 1 := h_is_real
  have h_fits_main :
      let reg_val :=
        (Word.toBitVec64 #v[(toMain cols)[15], (toMain cols)[16],
                            (toMain cols)[17], (toMain cols)[18]]).toNat
      let offset := (BitVec.signExtend 64
        (_root_.Store.StoreByte.sp1_imm_c (toMain cols))).toNat
      reg_val + offset + 1 < 2 ^ 64 := by
    simpa using h_fits_in_mem
  have h_main := _root_.Store.StoreByte.correct (toMain cols) s hs hs_config
    h_cstrs h_state h_is_real_main h_fits_main
  simp only at h_main
  rw [show _root_.Store.StoreByte.sp1_sb (toMain cols) = sp1_sb_cols cols from by
    rw [← sp1_sb_cols_fromMain, h_round_trip],
   show _root_.Store.StoreByte.sp1_imm_c (toMain cols) = sp1_imm_c_cols cols from by
    rw [← sp1_imm_c_cols_fromMain, h_round_trip],
   show _root_.Store.StoreByte.sp1_op_a (toMain cols) = sp1_op_a_cols cols from by
    rw [← sp1_op_a_cols_fromMain, h_round_trip],
   show _root_.Store.StoreByte.sp1_ob_b (toMain cols) = sp1_op_b_cols cols from by
    rw [← sp1_op_b_cols_fromMain, h_round_trip]] at h_main
  exact h_main

end SP1Clean.StoreByte
