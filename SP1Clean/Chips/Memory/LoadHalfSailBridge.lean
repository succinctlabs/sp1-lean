import SP1Clean.Chips.Memory.LoadHalfChip

/-! # External Sail-equivalence bridges for `LoadHalfChip` (LH + LHU). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions Sail SailState

namespace SP1Clean.LoadHalf

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- SailBridge for the signed Load Half (LH) variant. -/
theorem sail_correct_of_allHold_lh
    (cols : LoadHalfCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_lh + cols.is_lhu)
    (h_is_lh : cols.is_lh = 1)
    (h_cstrs : (_root_.Load.LoadHalf.constraints (toMain cols)).allHold)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_init : loadHalfInitialState_cols cols s)
    (h_fits_in_mem :
      let reg_val :=
        (Word.toBitVec64 cols.adapter.op_b_memory.prev_value).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c_cols cols)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned :
      is_aligned_vaddr (virtaddr.Virtaddr
        (Word.toBitVec64 cols.adapter.op_b_memory.prev_value +
          BitVec.signExtend 64
            (BitVec.ofNat 12 cols.adapter.op_c_imm[0].val))) 2 = true) :
    (_root_.Load.LoadHalf.spec_lh
        (sp1_imm_c_cols cols)
        (.Regidx (sp1_op_b_cols cols))
        (.Regidx (sp1_op_a_cols cols))).run s =
      (sp1_load_half_cols cols).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_is_lh_main : (toMain cols)[42] = 1 := h_is_lh
  have h_fits_main :
      let reg_val :=
        (Word.toBitVec64 #v[(toMain cols)[15], (toMain cols)[16],
                            (toMain cols)[17], (toMain cols)[18]]).toNat
      let offset := (BitVec.signExtend 64
        (_root_.Load.LoadHalf.sp1_imm_c (toMain cols))).toNat
      reg_val + offset + 2 < 2 ^ 64 := by
    simpa using h_fits_in_mem
  have h_align_main : is_aligned_vaddr (virtaddr.Virtaddr
        (Word.toBitVec64 #v[(toMain cols)[15], (toMain cols)[16],
                            (toMain cols)[17], (toMain cols)[18]] +
          BitVec.signExtend 64
            (BitVec.ofNat 12 ((toMain cols)[21].val)))) 2 = true := by
    simpa [sp1_imm_c_cols] using h_is_aligned
  have h_main := _root_.Load.LoadHalf.correct_lh (toMain cols) s hs hs_config
    h_cstrs h_state h_is_lh_main h_fits_main h_align_main
  simp only at h_main
  rw [show _root_.Load.LoadHalf.sp1_load_half (toMain cols) = sp1_load_half_cols cols from by
    rw [← sp1_load_half_cols_fromMain, h_round_trip],
   show _root_.Load.LoadHalf.sp1_imm_c (toMain cols) = sp1_imm_c_cols cols from by
    rw [← sp1_imm_c_cols_fromMain, h_round_trip],
   show _root_.Load.LoadHalf.sp1_ob_b (toMain cols) = sp1_op_b_cols cols from by
    rw [← sp1_op_b_cols_fromMain, h_round_trip],
   show _root_.Load.LoadHalf.sp1_op_a (toMain cols) = sp1_op_a_cols cols from by
    rw [← sp1_op_a_cols_fromMain, h_round_trip]] at h_main
  exact h_main

/-- SailBridge for the unsigned Load Half (LHU) variant. -/
theorem sail_correct_of_allHold_lhu
    (cols : LoadHalfCols (ZMod p))
    (h_trusted : cols.adapter_cols.is_trusted = cols.is_lh + cols.is_lhu)
    (h_is_lhu : cols.is_lhu = 1)
    (h_cstrs : (_root_.Load.LoadHalf.constraints (toMain cols)).allHold)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_init : loadHalfInitialState_cols cols s)
    (h_fits_in_mem :
      let reg_val :=
        (Word.toBitVec64 cols.adapter.op_b_memory.prev_value).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c_cols cols)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned :
      is_aligned_vaddr (virtaddr.Virtaddr
        (Word.toBitVec64 cols.adapter.op_b_memory.prev_value +
          BitVec.signExtend 64
            (BitVec.ofNat 12 cols.adapter.op_c_imm[0].val))) 2 = true) :
    (_root_.Load.LoadHalf.spec_lhu
        (sp1_imm_c_cols cols)
        (.Regidx (sp1_op_b_cols cols))
        (.Regidx (sp1_op_a_cols cols))).run s =
      (sp1_load_half_cols cols).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_round_trip := fromMain_toMain cols h_trusted
  have h_state := h_init (toMain cols) h_round_trip
  have h_is_lhu_main : (toMain cols)[43] = 1 := h_is_lhu
  have h_fits_main :
      let reg_val :=
        (Word.toBitVec64 #v[(toMain cols)[15], (toMain cols)[16],
                            (toMain cols)[17], (toMain cols)[18]]).toNat
      let offset := (BitVec.signExtend 64
        (_root_.Load.LoadHalf.sp1_imm_c (toMain cols))).toNat
      reg_val + offset + 2 < 2 ^ 64 := by
    simpa using h_fits_in_mem
  have h_align_main : is_aligned_vaddr (virtaddr.Virtaddr
        (Word.toBitVec64 #v[(toMain cols)[15], (toMain cols)[16],
                            (toMain cols)[17], (toMain cols)[18]] +
          BitVec.signExtend 64
            (BitVec.ofNat 12 ((toMain cols)[21].val)))) 2 = true := by
    simpa [sp1_imm_c_cols] using h_is_aligned
  have h_main := _root_.Load.LoadHalf.correct_lhu (toMain cols) s hs hs_config
    h_cstrs h_state h_is_lhu_main h_fits_main h_align_main
  simp only at h_main
  rw [show _root_.Load.LoadHalf.sp1_load_half (toMain cols) = sp1_load_half_cols cols from by
    rw [← sp1_load_half_cols_fromMain, h_round_trip],
   show _root_.Load.LoadHalf.sp1_imm_c (toMain cols) = sp1_imm_c_cols cols from by
    rw [← sp1_imm_c_cols_fromMain, h_round_trip],
   show _root_.Load.LoadHalf.sp1_ob_b (toMain cols) = sp1_op_b_cols cols from by
    rw [← sp1_op_b_cols_fromMain, h_round_trip],
   show _root_.Load.LoadHalf.sp1_op_a (toMain cols) = sp1_op_a_cols cols from by
    rw [← sp1_op_a_cols_fromMain, h_round_trip]] at h_main
  exact h_main

end SP1Clean.LoadHalf
