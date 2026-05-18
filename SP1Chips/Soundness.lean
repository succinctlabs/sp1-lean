import SP1Chips.AddChip
import SP1Chips.AddiChip
import SP1Chips.AddwChip
import SP1Chips.BitwiseChip
import SP1Chips.BranchChip
import SP1Chips.DivRemChip
import SP1Chips.JalChip
import SP1Chips.JalrChip
import SP1Chips.LoadByteChip
import SP1Chips.LoadDoubleChip
import SP1Chips.LoadHalfChip
import SP1Chips.LoadWordChip
import SP1Chips.LoadX0Chip
import SP1Chips.LtChip
import SP1Chips.MulChip
import SP1Chips.ShiftLeftChip
import SP1Chips.ShiftRightChip
import SP1Chips.StoreByteChip
import SP1Chips.StoreDoubleChip
import SP1Chips.StoreHalfChip
import SP1Chips.StoreWordChip
import SP1Chips.SubChip
import SP1Chips.SubwChip
import SP1Chips.UTypeChip

/-!
# High-level chip soundness aggregator

One `soundness_<chip>` theorem per instruction chip, combining all per-opcode
`correct_*_poly` theorems into a single statement. The chip's unified SP1
implementation appears once on the left-hand side; the right-hand side is an
`if … then spec_<op1> else if … then spec_<op2> else …` cascade dispatching on
the chip's opcode-selector columns.

When no selector is active, the equation degenerates to `sp1_<chip> = sp1_<chip>`
— so the cascade carries the soundness claim only for opcodes the chip actually
handles. Each proof is a one-line delegation to the per-opcode `correct_<op>_poly`.

The file exists to give readers a single per-chip statement to read, rather than
having to stitch together five-to-eight opcode-specific theorems per chip.
-/

open LeanRV64D.Functions BitVec Sail

-- The if-then-else dispatch in multi-opcode soundness theorems uses propositional
-- selectors (`is_<op>_poly Main`) which reduce to ZMod equalities. We pull in
-- classical decidability for these statements rather than threading explicit
-- `Decidable` instances through every chip.
set_option linter.style.openClassical false
open Classical

section
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

/-! ## Single-opcode chips (trivial aliases) -/

theorem soundness_add (Main : Vector (ZMod p) 33) (s : SailState)
    (cstrs : (Add.constraints Main).allHold_poly)
    (h_is_real : Main[32] = 1)
    (state_cstrs : (Add.constraints Main).initialState_poly s) :
    (Add.sp1_add Main).run s =
      (Add.spec_add (.Regidx (Add.sp1_op_c Main)) (.Regidx (Add.sp1_op_b Main))
        (.Regidx (Add.sp1_op_a Main))).run s :=
  (Add.correct_add Main s cstrs h_is_real state_cstrs).symm

theorem soundness_addi (Main : Vector (ZMod p) 30) (s : SailState)
    (cstrs : (Addi.constraints Main).allHold_poly)
    (h_is_real : Main[29] = 1)
    (state_cstrs : (Addi.constraints Main).initialState_poly s) :
    (Addi.sp1_addi Main).run s =
      (Addi.spec_addi (Addi.sp1_op_c Main) (.Regidx (Addi.sp1_op_b Main))
        (.Regidx (Addi.sp1_op_a Main))).run s :=
  (Addi.correct_addi Main s cstrs h_is_real state_cstrs).symm

theorem soundness_sub (Main : Vector (ZMod p) 33) (s : SailState)
    (cstrs : (Sub.constraints Main).allHold_poly)
    (h_is_real : Main[32] = 1)
    (state_cstrs : (Sub.constraints Main).initialState_poly s) :
    (Sub.sp1_sub Main).run s =
      (Sub.spec_sub (.Regidx (Sub.sp1_op_c Main)) (.Regidx (Sub.sp1_op_b Main))
        (.Regidx (Sub.sp1_op_a Main))).run s :=
  (Sub.correct_sub Main s cstrs h_is_real state_cstrs).symm

theorem soundness_subw (Main : Vector (ZMod p) 32) (s : SailState)
    (cstrs : (Subw.constraints Main).allHold_poly)
    (h_is_real : Main[31] = 1)
    (state_cstrs : (Subw.constraints Main).initialState_poly s) :
    (Subw.sp1_subw Main).run s =
      (Subw.spec_subw (.Regidx (Subw.sp1_op_c Main)) (.Regidx (Subw.sp1_op_b Main))
        (.Regidx (Subw.sp1_op_a Main))).run s :=
  (Subw.correct_subw Main s cstrs h_is_real state_cstrs).symm

theorem soundness_jal (Main : Vector (ZMod p) 31) (s : SailState)
    (cstrs : (Jal.constraints Main).allHold_poly)
    (h_is_real : Main[30] = 1)
    (state_cstrs : (Jal.constraints Main).initialState_poly s)
    (hs : SailState.isInitialized s) :
    (Jal.sp1_jal Main).run s =
      (Jal.spec_jal (Jal.sp1_op_b Main)
        (.Regidx (Jal.sp1_op_a Main cstrs h_is_real))).run s :=
  (Jal.SP1JAL_correct (Main := Main) (s := s) cstrs h_is_real state_cstrs hs).symm

end

/-! ## AddwChip — two opcodes (addw / addiw), each with its own `sp1_*` def.
We expose them as two single-opcode aliases. -/

section
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

theorem soundness_addw (Main : Vector (ZMod p) 36) (s : SailState)
    (cstrs : (Addw.constraints Main).allHold_poly)
    (h_is_real : Main[35] = 1) (h_is_addw : Main[31] = 0)
    (state_cstrs : (Addw.constraints Main).initialState_poly s) :
    (Addw.sp1_addw Main).run s =
      (Addw.spec_addw (.Regidx (Addw.sp1_op_c Main)) (.Regidx (Addw.sp1_op_b Main))
        (.Regidx (Addw.sp1_op_a Main))).run s :=
  (Addw.correct_addw Main s cstrs h_is_real h_is_addw state_cstrs).symm

theorem soundness_addiw (Main : Vector (ZMod p) 36) (s : SailState)
    (cstrs : (Addw.constraints Main).allHold_poly)
    (h_is_real : Main[35] = 1) (h_is_addiw : Main[31] = 1)
    (state_cstrs : (Addw.constraints Main).initialState_poly s) :
    (Addiw.sp1_addiw Main).run s =
      (Addiw.spec_addiw (Addiw.sp1_op_c Main)
        (.Regidx (Addiw.sp1_op_b Main))
        (.Regidx (Addiw.sp1_op_a Main))).run s :=
  (Addiw.correct_addw Main s cstrs h_is_real h_is_addiw state_cstrs).symm

end

/-! ## Memory chips with extra hypotheses (alignment, fits-in-memory). -/

section
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

theorem soundness_jalr (Main : Vector (ZMod p) 35) (s : SailState)
    (cstrs : (Jalr.constraints Main).allHold_poly)
    (h_is_real : Main[25] = 1)
    (hs : SailState.isInitialized s)
    (state_cstrs : (Jalr.constraints Main).initialState_poly s)
    (hv : SailState.isValidMemConfig s hs) :
    (Jalr.sp1_jalr Main).run s =
      (Jalr.spec_jalr (Jalr.sp1_op_c Main) (.Regidx (Jalr.sp1_op_b Main))
        (.Regidx (Jalr.sp1_op_a Main))).run s :=
  (Jalr.JALR_correct (Main := Main) (s := s) cstrs h_is_real hs state_cstrs hv).symm

theorem soundness_load_double (Main : Vector (ZMod p) 39) (s : SailState)
    (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadDouble.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadDouble.constraints Main).initialState_poly s)
    (h_is_ld : Main[38] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadDouble.sp1_imm_c Main)).toNat
      reg_val + offset + 8 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 8 = true) :
    (Load.LoadDouble.sp1_ld Main).run s =
      (Load.LoadDouble.spec_ld (Load.LoadDouble.sp1_imm_c Main)
        (.Regidx (Load.LoadDouble.sp1_ob_b Main))
        (.Regidx (Load.LoadDouble.sp1_op_a Main))).run s :=
  (Load.LoadDouble.correct_ld Main s hs hs_config h_cstrs state_cstrs h_is_ld
    h_fits_in_mem h_is_aligned).symm

end

/-! ## Multi-opcode chips with uniform hypotheses — dispatched soundness. -/

section
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

/-- UType chip: dispatches between LUI (Main[29] = 0) and AUIPC (Main[29] = 1)
under a unified `h_is_real : Main[30] = 1`. -/
theorem soundness_utype (Main : Vector (ZMod p) 31) (s : SailState)
    (cstrs : (UType.constraints Main).allHold_poly)
    (h_is_real : Main[30] = 1)
    (state_cstrs : (UType.constraints Main).initialState_poly s) :
    (UType.sp1_utype Main).run s =
      (if Main[29] = 1 then
        (UType.spec_auipc (UType.sp1_op_b Main)
          (.Regidx (UType.sp1_op_a Main))).run s
      else if Main[29] = 0 then
        (UType.spec_lui (UType.sp1_op_b Main)
          (.Regidx (UType.sp1_op_a Main))).run s
      else (UType.sp1_utype Main).run s) := by
  split_ifs with h_auipc h_lui
  · exact (UType.correct_auipc Main s cstrs h_is_real h_auipc state_cstrs).symm
  · exact (UType.correct_lui Main s cstrs h_is_real h_lui state_cstrs).symm
  · rfl

/-- ShiftLeft chip: dispatches between sll / slli / sllw / slliw via the
selector pair (Main[62] register-form, Main[63] word-form) × (Main[31] immediate flag). -/
theorem soundness_shift_left (Main : Vector (ZMod p) 65) (s : SailState)
    (cstrs : (ShiftLeft.constraints Main).allHold_poly)
    (state_cstrs : (ShiftLeft.constraints Main).initialState_poly s) :
    (ShiftLeft.sp1_shift_left Main).run s =
      (if ShiftLeft.is_sll_poly Main then
        (Sll.Poly.spec_sll (.Regidx (ShiftLeft.sp1_op_c_poly Main))
          (.Regidx (ShiftLeft.sp1_op_b_poly Main))
          (.Regidx (ShiftLeft.sp1_op_a_poly Main))).run s
      else if ShiftLeft.is_slli_poly Main then
        (Slli.Poly.spec_slli (ShiftLeft.sp1_op_c_imm_poly Main)
          (.Regidx (ShiftLeft.sp1_op_b_poly Main))
          (.Regidx (ShiftLeft.sp1_op_a_poly Main))).run s
      else if ShiftLeft.is_sllw_poly Main then
        (Sllw.Poly.spec_sllw (.Regidx (ShiftLeft.sp1_op_c_poly Main))
          (.Regidx (ShiftLeft.sp1_op_b_poly Main))
          (.Regidx (ShiftLeft.sp1_op_a_poly Main))).run s
      else if ShiftLeft.is_slliw_poly Main then
        (Slliw.Poly.spec_slliw (ShiftLeft.sp1_op_c_imm_w_poly Main)
          (.Regidx (ShiftLeft.sp1_op_b_poly Main))
          (.Regidx (ShiftLeft.sp1_op_a_poly Main))).run s
      else (ShiftLeft.sp1_shift_left Main).run s) := by
  split_ifs with h1 h2 h3 h4
  · exact (Sll.Poly.correct_sll Main s cstrs h1 state_cstrs).symm
  · exact (Slli.Poly.correct_slli Main s cstrs h2 state_cstrs).symm
  · exact (Sllw.Poly.correct_sllw Main s cstrs h3 state_cstrs).symm
  · exact (Slliw.Poly.correct_slliw Main s cstrs h4 state_cstrs).symm
  · rfl

/-- ShiftRight chip: dispatches between srl / srli / sra / srai / srlw / srliw /
sraw / sraiw via the (Main[64..67] selector, Main[31] immediate flag) combinations. -/
theorem soundness_shift_right (Main : Vector (ZMod p) 69) (s : SailState)
    (cstrs : (ShiftRight.constraints Main).allHold_poly)
    (state_cstrs : (ShiftRight.constraints Main).initialState_poly s) :
    (ShiftRight.sp1_shift_right Main).run s =
      (if ShiftRight.is_srl_poly Main then
        (Srl.Poly.spec_srl (.Regidx (ShiftRight.sp1_op_c_poly Main))
          (.Regidx (ShiftRight.sp1_op_b_poly Main))
          (.Regidx (ShiftRight.sp1_op_a_poly Main))).run s
      else if ShiftRight.is_srli_poly Main then
        (Srli.Poly.spec_srli (ShiftRight.sp1_op_c_imm_poly Main)
          (.Regidx (ShiftRight.sp1_op_b_poly Main))
          (.Regidx (ShiftRight.sp1_op_a_poly Main))).run s
      else if ShiftRight.is_sra_poly Main then
        (Sra.Poly.spec_sra (.Regidx (ShiftRight.sp1_op_c_poly Main))
          (.Regidx (ShiftRight.sp1_op_b_poly Main))
          (.Regidx (ShiftRight.sp1_op_a_poly Main))).run s
      else if ShiftRight.is_srai_poly Main then
        (Srai.Poly.spec_srai (ShiftRight.sp1_op_c_imm_poly Main)
          (.Regidx (ShiftRight.sp1_op_b_poly Main))
          (.Regidx (ShiftRight.sp1_op_a_poly Main))).run s
      else if ShiftRight.is_srlw_poly Main then
        (Srlw.Poly.spec_srlw (.Regidx (ShiftRight.sp1_op_c_poly Main))
          (.Regidx (ShiftRight.sp1_op_b_poly Main))
          (.Regidx (ShiftRight.sp1_op_a_poly Main))).run s
      else if ShiftRight.is_srliw_poly Main then
        (Srliw.Poly.spec_srliw (ShiftRight.sp1_op_c_imm_w_poly Main)
          (.Regidx (ShiftRight.sp1_op_b_poly Main))
          (.Regidx (ShiftRight.sp1_op_a_poly Main))).run s
      else if ShiftRight.is_sraw_poly Main then
        (Sraw.Poly.spec_sraw (.Regidx (ShiftRight.sp1_op_c_poly Main))
          (.Regidx (ShiftRight.sp1_op_b_poly Main))
          (.Regidx (ShiftRight.sp1_op_a_poly Main))).run s
      else if ShiftRight.is_sraiw_poly Main then
        (Sraiw.Poly.spec_sraiw (ShiftRight.sp1_op_c_imm_w_poly Main)
          (.Regidx (ShiftRight.sp1_op_b_poly Main))
          (.Regidx (ShiftRight.sp1_op_a_poly Main))).run s
      else (ShiftRight.sp1_shift_right Main).run s) := by
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact (Srl.Poly.correct_srl Main s cstrs h1 state_cstrs).symm
  · exact (Srli.Poly.correct_srli Main s cstrs h2 state_cstrs).symm
  · exact (Sra.Poly.correct_sra Main s cstrs h3 state_cstrs).symm
  · exact (Srai.Poly.correct_srai Main s cstrs h4 state_cstrs).symm
  · exact (Srlw.Poly.correct_srlw Main s cstrs h5 state_cstrs).symm
  · exact (Srliw.Poly.correct_srliw Main s cstrs h6 state_cstrs).symm
  · exact (Sraw.Poly.correct_sraw Main s cstrs h7 state_cstrs).symm
  · exact (Sraiw.Poly.correct_sraiw Main s cstrs h8 state_cstrs).symm
  · rfl

/-- Bitwise chip: dispatches between xor / or / and (Main[31] = 0) and their
immediate-form siblings (Main[31] = 1) via the Main[48..50] selector. -/
theorem soundness_bitwise (Main : Vector (ZMod p) 51) (s : SailState)
    (cstrs : (Bitwise.constraints Main).allHold_poly)
    (state_cstrs : (Bitwise.constraints Main).initialState_poly s) :
    (Bitwise.sp1_bitwise Main).run s =
      (if Bitwise.is_xor_poly Main then
        (Xor.spec_xor (.Regidx (Xor.sp1_op_c Main)) (.Regidx (Xor.sp1_op_b Main))
          (.Regidx (Xor.sp1_op_a Main))).run s
      else if Bitwise.is_or_poly Main then
        (Or.spec_or (.Regidx (Or.sp1_op_c Main)) (.Regidx (Or.sp1_op_b Main))
          (.Regidx (Or.sp1_op_a Main))).run s
      else if Bitwise.is_and_poly Main then
        (And.spec_and (.Regidx (And.sp1_op_c Main)) (.Regidx (And.sp1_op_b Main))
          (.Regidx (And.sp1_op_a Main))).run s
      else if Bitwise.is_xori_poly Main then
        (Xori.spec_xori (Xori.sp1_op_c Main) (.Regidx (Xori.sp1_op_b Main))
          (.Regidx (Xori.sp1_op_a Main))).run s
      else if Bitwise.is_ori_poly Main then
        (Ori.spec_ori (Ori.sp1_op_c Main) (.Regidx (Ori.sp1_op_b Main))
          (.Regidx (Ori.sp1_op_a Main))).run s
      else if Bitwise.is_andi_poly Main then
        (Andi.spec_andi (Andi.sp1_op_c Main) (.Regidx (Andi.sp1_op_b Main))
          (.Regidx (Andi.sp1_op_a Main))).run s
      else (Bitwise.sp1_bitwise Main).run s) := by
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact (Xor.correct_xor Main s cstrs h1 state_cstrs).symm
  · exact (Or.correct_or Main s cstrs h2 state_cstrs).symm
  · exact (And.correct_and Main s cstrs h3 state_cstrs).symm
  · exact (Xori.correct_xori Main s cstrs h4 state_cstrs).symm
  · exact (Ori.correct_ori Main s cstrs h5 state_cstrs).symm
  · exact (Andi.correct_andi Main s cstrs h6 state_cstrs).symm
  · rfl

/-- Lt chip: dispatches between slt / sltu (Main[31] = 0) and slti / sltiu
(Main[31] = 1) via the Main[32]/Main[33] selectors. -/
theorem soundness_lt (Main : Vector (ZMod p) 44) (s : SailState)
    (cstrs : (Lt.constraints Main).allHold_poly)
    (state_cstrs : (Lt.constraints Main).initialState_poly s) :
    (Lt.sp1_lt Main).run s =
      (if Lt.is_slt_poly Main then
        (Slt.spec_slt (.Regidx (Slt.sp1_op_c Main)) (.Regidx (Slt.sp1_op_b Main))
          (.Regidx (Slt.sp1_op_a Main))).run s
      else if Lt.is_sltu_poly Main then
        (Sltu.spec_sltu (.Regidx (Sltu.sp1_op_c Main)) (.Regidx (Sltu.sp1_op_b Main))
          (.Regidx (Sltu.sp1_op_a Main))).run s
      else if Lt.is_slti_poly Main then
        (Slti.spec_slti (Slti.sp1_op_c Main) (.Regidx (Slti.sp1_op_b Main))
          (.Regidx (Slti.sp1_op_a Main))).run s
      else if Lt.is_sltiu_poly Main then
        (Sltiu.spec_sltiu (Sltiu.sp1_op_c Main) (.Regidx (Sltiu.sp1_op_b Main))
          (.Regidx (Sltiu.sp1_op_a Main))).run s
      else (Lt.sp1_lt Main).run s) := by
  split_ifs with h1 h2 h3 h4
  · exact (Slt.correct_slt Main s cstrs h1 state_cstrs).symm
  · exact (Sltu.correct_sltu Main s cstrs h2 state_cstrs).symm
  · exact (Slti.correct_slti Main s cstrs h3 state_cstrs).symm
  · exact (Sltiu.correct_sltiu Main s cstrs h4 state_cstrs).symm
  · rfl

end

section
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]

/-- Mul chip: dispatches between mul / mulh / mulhu / mulhsu / mulw via the
Main[77..81] selector (all with Main[30] = 0). Requires `Fact (2 ^ 24 < p)`. -/
theorem soundness_mul (Main : Vector (ZMod p) 82) (s : SailState)
    (cstrs : (Mul.constraints Main).allHold_poly)
    (state_cstrs : (Mul.constraints Main).initialState_poly s) :
    (Mul.sp1_mul_chip Main).run s =
      (if Mul.is_mul_poly Main then
        (Mul.Poly.spec_mul (.Regidx (Mul.sp1_op_c_poly Main))
          (.Regidx (Mul.sp1_op_b_poly Main))
          (.Regidx (Mul.sp1_op_a_poly Main))).run s
      else if Mul.is_mulh_poly Main then
        (Mulh.Poly.spec_mulh (.Regidx (Mul.sp1_op_c_poly Main))
          (.Regidx (Mul.sp1_op_b_poly Main))
          (.Regidx (Mul.sp1_op_a_poly Main))).run s
      else if Mul.is_mulhu_poly Main then
        (Mulhu.Poly.spec_mulhu (.Regidx (Mul.sp1_op_c_poly Main))
          (.Regidx (Mul.sp1_op_b_poly Main))
          (.Regidx (Mul.sp1_op_a_poly Main))).run s
      else if Mul.is_mulhsu_poly Main then
        (Mulhsu.Poly.spec_mulhsu (.Regidx (Mul.sp1_op_c_poly Main))
          (.Regidx (Mul.sp1_op_b_poly Main))
          (.Regidx (Mul.sp1_op_a_poly Main))).run s
      else if Mul.is_mulw_poly Main then
        (Mulw.Poly.spec_mulw (.Regidx (Mul.sp1_op_c_poly Main))
          (.Regidx (Mul.sp1_op_b_poly Main))
          (.Regidx (Mul.sp1_op_a_poly Main))).run s
      else (Mul.sp1_mul_chip Main).run s) := by
  split_ifs with h1 h2 h3 h4 h5
  · exact (Mul.Poly.correct_mul Main s cstrs h1 state_cstrs).symm
  · exact (Mulh.Poly.correct_mulh Main s cstrs h2 state_cstrs).symm
  · exact (Mulhu.Poly.correct_mulhu Main s cstrs h3 state_cstrs).symm
  · exact (Mulhsu.Poly.correct_mulhsu Main s cstrs h4 state_cstrs).symm
  · exact (Mulw.Poly.correct_mulw Main s cstrs h5 state_cstrs).symm
  · rfl

/-- DivRem chip: dispatches between all 8 variants via the Main[201..208] selectors.
Requires `Fact (2 ^ 24 < p)` (same as the per-opcode correct theorems). -/
theorem soundness_divrem (Main : Vector (ZMod p) 246) (s : SailState)
    (cstrs : (DivRem.constraints Main).allHold_poly)
    (h_is_real : DivRem.is_real_poly Main)
    (state_cstrs : (DivRem.constraints Main).initialState_poly s) :
    (DivRem.Poly.sp1_op Main).run s =
      (if DivRem.is_div_poly Main then
        (Div.spec_div (.Regidx (DivRem.sp1_op_c_poly Main))
          (.Regidx (DivRem.sp1_op_b_poly Main))
          (.Regidx (DivRem.sp1_op_a_poly Main))).run s
      else if DivRem.is_divu_poly Main then
        (Divu.spec_divu (.Regidx (DivRem.sp1_op_c_poly Main))
          (.Regidx (DivRem.sp1_op_b_poly Main))
          (.Regidx (DivRem.sp1_op_a_poly Main))).run s
      else if DivRem.is_rem_poly Main then
        (Rem.spec_rem (.Regidx (DivRem.sp1_op_c_poly Main))
          (.Regidx (DivRem.sp1_op_b_poly Main))
          (.Regidx (DivRem.sp1_op_a_poly Main))).run s
      else if DivRem.is_remu_poly Main then
        (Remu.spec_remu (.Regidx (DivRem.sp1_op_c_poly Main))
          (.Regidx (DivRem.sp1_op_b_poly Main))
          (.Regidx (DivRem.sp1_op_a_poly Main))).run s
      else if DivRem.is_divw_poly Main then
        (Divw.spec_divw (.Regidx (DivRem.sp1_op_c_poly Main))
          (.Regidx (DivRem.sp1_op_b_poly Main))
          (.Regidx (DivRem.sp1_op_a_poly Main))).run s
      else if DivRem.is_remw_poly Main then
        (Remw.spec_remw (.Regidx (DivRem.sp1_op_c_poly Main))
          (.Regidx (DivRem.sp1_op_b_poly Main))
          (.Regidx (DivRem.sp1_op_a_poly Main))).run s
      else if DivRem.is_divuw_poly Main then
        (Divuw.spec_divuw (.Regidx (DivRem.sp1_op_c_poly Main))
          (.Regidx (DivRem.sp1_op_b_poly Main))
          (.Regidx (DivRem.sp1_op_a_poly Main))).run s
      else if DivRem.is_remuw_poly Main then
        (Remuw.spec_remuw (.Regidx (DivRem.sp1_op_c_poly Main))
          (.Regidx (DivRem.sp1_op_b_poly Main))
          (.Regidx (DivRem.sp1_op_a_poly Main))).run s
      else (DivRem.Poly.sp1_op Main).run s) := by
  split_ifs with h1 h2 h3 h4 h5 h6 h7 h8
  · exact (DivRem.Poly.correct_div Main s cstrs h_is_real h1 state_cstrs).symm
  · exact (DivRem.Poly.correct_divu Main s cstrs h_is_real h2 state_cstrs).symm
  · exact (DivRem.Poly.correct_rem Main s cstrs h_is_real h3 state_cstrs).symm
  · exact (DivRem.Poly.correct_remu Main s cstrs h_is_real h4 state_cstrs).symm
  · exact (DivRem.Poly.correct_divw Main s cstrs h_is_real h5 state_cstrs).symm
  · exact (DivRem.Poly.correct_remw Main s cstrs h_is_real h6 state_cstrs).symm
  · exact (DivRem.Poly.correct_divuw Main s cstrs h_is_real h7 state_cstrs).symm
  · exact (DivRem.Poly.correct_remuw Main s cstrs h_is_real h8 state_cstrs).symm
  · rfl

end

section
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

/-- Branch chip: dispatches between beq / bne / blt / bge / bltu / bgeu via the
Main[28..33] selectors. Requires `hs : s.isInitialized` (Sail-side memory model). -/
theorem soundness_branch (Main : Vector (ZMod p) 45) (s : SailState)
    (hs : s.isInitialized)
    (cstrs : (Branch.constraints Main).allHold_poly)
    (state_cstrs : (Branch.constraints Main).initialState_poly s) :
    (Branch.sp1_branch Main).run s =
      (if Branch.is_beq_poly Main then
        (Branch.BEQ.spec_beq (Branch.sp1_imm Main)
          (.Regidx (Branch.sp1_op_b Main)) (.Regidx (Branch.sp1_op_a Main))).run s
      else if Branch.is_bne_poly Main then
        (Branch.BNE.spec_bne (Branch.sp1_imm Main)
          (.Regidx (Branch.sp1_op_b Main)) (.Regidx (Branch.sp1_op_a Main))).run s
      else if Branch.is_blt_poly Main then
        (Branch.BLT.spec_blt (Branch.sp1_imm Main)
          (.Regidx (Branch.sp1_op_b Main)) (.Regidx (Branch.sp1_op_a Main))).run s
      else if Branch.is_bge_poly Main then
        (Branch.BGE.spec_bge (Branch.sp1_imm Main)
          (.Regidx (Branch.sp1_op_b Main)) (.Regidx (Branch.sp1_op_a Main))).run s
      else if Branch.is_bltu_poly Main then
        (Branch.BLTU.spec_bltu (Branch.sp1_imm Main)
          (.Regidx (Branch.sp1_op_b Main)) (.Regidx (Branch.sp1_op_a Main))).run s
      else if Branch.is_bgeu_poly Main then
        (Branch.BGEU.spec_bgeu (Branch.sp1_imm Main)
          (.Regidx (Branch.sp1_op_b Main)) (.Regidx (Branch.sp1_op_a Main))).run s
      else (Branch.sp1_branch Main).run s) := by
  split_ifs with h1 h2 h3 h4 h5 h6
  · exact (Branch.BEQ.correct_beq Main s hs h1 cstrs state_cstrs).symm
  · exact (Branch.BNE.correct_bne Main s hs h2 cstrs state_cstrs).symm
  · exact (Branch.BLT.correct_blt Main s hs h3 cstrs state_cstrs).symm
  · exact (Branch.BGE.correct_bge Main s hs h4 cstrs state_cstrs).symm
  · exact (Branch.BLTU.correct_bltu Main s hs h5 cstrs state_cstrs).symm
  · exact (Branch.BGEU.correct_bgeu Main s hs h6 cstrs state_cstrs).symm
  · rfl

end

/-! ## Memory chips with per-opcode `h_fits_in_mem` / `h_is_aligned` hypotheses.

These chips share a unified `sp1_<chip>` already, but each opcode in a chip can
have its own memory-shape side conditions (byte vs half vs word vs double width).
We expose each opcode as a separate alias rather than fold them into a single
dispatch — the per-opcode side conditions don't cleanly factor through a single
hypothesis. -/

section
variable {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

/-- LoadByte chip, signed (lb): 1-byte memory read. -/
theorem soundness_load_byte_lb (Main : Vector (ZMod p) 47) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadByte.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadByte.constraints Main).initialState_poly s)
    (h_is_lb : Main[45] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadByte.sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64) :
    (Load.LoadByte.sp1_load_byte Main).run s =
      (Load.LoadByte.spec_lb (Load.LoadByte.sp1_imm_c Main)
        (.Regidx (Load.LoadByte.sp1_ob_b Main))
        (.Regidx (Load.LoadByte.sp1_op_a Main))).run s :=
  (Load.LoadByte.correct_lb Main s hs hs_config h_cstrs state_cstrs h_is_lb
    h_fits_in_mem).symm

/-- LoadByte chip, unsigned (lbu). -/
theorem soundness_load_byte_lbu (Main : Vector (ZMod p) 47) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadByte.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadByte.constraints Main).initialState_poly s)
    (h_is_lbu : Main[46] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadByte.sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64) :
    (Load.LoadByte.sp1_load_byte Main).run s =
      (Load.LoadByte.spec_lbu (Load.LoadByte.sp1_imm_c Main)
        (.Regidx (Load.LoadByte.sp1_ob_b Main))
        (.Regidx (Load.LoadByte.sp1_op_a Main))).run s :=
  (Load.LoadByte.correct_lbu Main s hs hs_config h_cstrs state_cstrs h_is_lbu
    h_fits_in_mem).symm

/-- LoadHalf chip, signed (lh): 2-byte memory read, 2-byte aligned. -/
theorem soundness_load_half_lh (Main : Vector (ZMod p) 44) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadHalf.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadHalf.constraints Main).initialState_poly s)
    (h_is_lh : Main[42] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadHalf.sp1_imm_c Main)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 2 = true) :
    (Load.LoadHalf.sp1_load_half Main).run s =
      (Load.LoadHalf.spec_lh (Load.LoadHalf.sp1_imm_c Main)
        (.Regidx (Load.LoadHalf.sp1_ob_b Main))
        (.Regidx (Load.LoadHalf.sp1_op_a Main))).run s :=
  (Load.LoadHalf.correct_lh Main s hs hs_config h_cstrs state_cstrs h_is_lh
    h_fits_in_mem h_is_aligned).symm

/-- LoadHalf chip, unsigned (lhu). -/
theorem soundness_load_half_lhu (Main : Vector (ZMod p) 44) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadHalf.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadHalf.constraints Main).initialState_poly s)
    (h_is_lhu : Main[43] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadHalf.sp1_imm_c Main)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 2 = true) :
    (Load.LoadHalf.sp1_load_half Main).run s =
      (Load.LoadHalf.spec_lhu (Load.LoadHalf.sp1_imm_c Main)
        (.Regidx (Load.LoadHalf.sp1_ob_b Main))
        (.Regidx (Load.LoadHalf.sp1_op_a Main))).run s :=
  (Load.LoadHalf.correct_lhu Main s hs hs_config h_cstrs state_cstrs h_is_lhu
    h_fits_in_mem h_is_aligned).symm

/-- LoadWord chip, signed (lw): 4-byte memory read, 4-byte aligned. -/
theorem soundness_load_word_lw (Main : Vector (ZMod p) 44) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadWord.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadWord.constraints Main).initialState_poly s)
    (h_is_lw : Main[42] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadWord.sp1_imm_c Main)).toNat
      reg_val + offset + 4 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 4 = true) :
    (Load.LoadWord.sp1_load_word Main).run s =
      (Load.LoadWord.spec_lw (Load.LoadWord.sp1_imm_c Main)
        (.Regidx (Load.LoadWord.sp1_ob_b Main))
        (.Regidx (Load.LoadWord.sp1_op_a Main))).run s :=
  (Load.LoadWord.correct_lw Main s hs hs_config h_cstrs state_cstrs h_is_lw
    h_fits_in_mem h_is_aligned).symm

/-- LoadWord chip, unsigned (lwu). -/
theorem soundness_load_word_lwu (Main : Vector (ZMod p) 44) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadWord.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadWord.constraints Main).initialState_poly s)
    (h_is_lwu : Main[43] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadWord.sp1_imm_c Main)).toNat
      reg_val + offset + 4 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 4 = true) :
    (Load.LoadWord.sp1_load_word Main).run s =
      (Load.LoadWord.spec_lwu (Load.LoadWord.sp1_imm_c Main)
        (.Regidx (Load.LoadWord.sp1_ob_b Main))
        (.Regidx (Load.LoadWord.sp1_op_a Main))).run s :=
  (Load.LoadWord.correct_lwu Main s hs hs_config h_cstrs state_cstrs h_is_lwu
    h_fits_in_mem h_is_aligned).symm

/-- StoreByte chip (sb): 1-byte memory write. No alignment hypothesis (byte writes
are trivially aligned). -/
theorem soundness_store_byte (Main : Vector (ZMod p) 50) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Store.StoreByte.constraints Main).allHold_poly)
    (state_cstrs : (Store.StoreByte.constraints Main).initialState_poly s)
    (h_is_real : Main[49] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Store.StoreByte.sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64) :
    (Store.StoreByte.sp1_sb Main).run s =
      (Store.StoreByte.spec_sb (Store.StoreByte.sp1_imm_c Main)
        (.Regidx (Store.StoreByte.sp1_op_a Main))
        (.Regidx (Store.StoreByte.sp1_ob_b Main))).run s :=
  (Store.StoreByte.correct Main s hs hs_config h_cstrs state_cstrs h_is_real
    h_fits_in_mem).symm

/-- StoreHalf chip (sh): 2-byte memory write, 2-byte aligned. -/
theorem soundness_store_half (Main : Vector (ZMod p) 45) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Store.StoreHalf.constraints Main).allHold_poly)
    (state_cstrs : (Store.StoreHalf.constraints Main).initialState_poly s)
    (h_is_real : Main[44] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Store.StoreHalf.sp1_imm_c Main)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (Store.StoreHalf.sp1_imm_c Main))) 2 = true) :
    (Store.StoreHalf.sp1_sb Main).run s =
      (Store.StoreHalf.spec_sb (Store.StoreHalf.sp1_imm_c Main)
        (.Regidx (Store.StoreHalf.sp1_op_a Main))
        (.Regidx (Store.StoreHalf.sp1_ob_b Main))).run s :=
  (Store.StoreHalf.correct Main s hs hs_config h_cstrs state_cstrs h_is_real
    h_fits_in_mem h_is_aligned).symm

/-- StoreWord chip (sw): 4-byte memory write, 4-byte aligned. -/
theorem soundness_store_word (Main : Vector (ZMod p) 44) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Store.StoreWord.constraints Main).allHold_poly)
    (state_cstrs : (Store.StoreWord.constraints Main).initialState_poly s)
    (h_is_real : Main[43] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Store.StoreWord.sp1_imm_c Main)).toNat
      reg_val + offset + 4 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 (Word.toNat_poly #v[Main[21], Main[22], Main[23], Main[24]])))) 4
      = true) :
    (Store.StoreWord.sp1_sb Main).run s =
      (Store.StoreWord.spec_sb (Store.StoreWord.sp1_imm_c Main)
        (.Regidx (Store.StoreWord.sp1_op_a Main))
        (.Regidx (Store.StoreWord.sp1_ob_b Main))).run s :=
  (Store.StoreWord.correct Main s hs hs_config h_cstrs state_cstrs h_is_real
    h_fits_in_mem h_is_aligned).symm

/-- StoreDouble chip (sd): 8-byte memory write, 8-byte aligned. -/
theorem soundness_store_double (Main : Vector (ZMod p) 39) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Store.StoreDouble.constraints Main).allHold_poly)
    (state_cstrs : (Store.StoreDouble.constraints Main).initialState_poly s)
    (h_is_real : Main[38] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Store.StoreDouble.sp1_imm_c Main)).toNat
      reg_val + offset + 8 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (Store.StoreDouble.sp1_imm_c Main))) 8 = true) :
    (Store.StoreDouble.sp1_sb Main).run s =
      (Store.StoreDouble.spec_sb (Store.StoreDouble.sp1_imm_c Main)
        (.Regidx (Store.StoreDouble.sp1_op_a Main))
        (.Regidx (Store.StoreDouble.sp1_ob_b Main))).run s :=
  (Store.StoreDouble.correct Main s hs hs_config h_cstrs state_cstrs h_is_real
    h_fits_in_mem h_is_aligned).symm

/-! ### LoadX0 chip — seven opcodes (lb/lbu/lh/lhu/lw/lwu/ld). Each has its own
width and alignment requirement. -/

private abbrev LX0_imm (Main : Vector (ZMod p) 48) : BitVec 64 :=
  BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val)
private abbrev LX0_reg (Main : Vector (ZMod p) 48) : BitVec 64 :=
  Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]

theorem soundness_load_x0_lb (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_lb : Main[41] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 1 = true) :
    (Load.LoadX0.sp1_loadX0 Main).run s =
      (Load.LoadX0.spec_loadX0_lb (Load.LoadX0.sp1_imm_c Main)
        (.Regidx (Load.LoadX0.sp1_ob_b Main))
        (.Regidx (Load.LoadX0.sp1_op_a Main))).run s :=
  (Load.LoadX0.correct_loadX0_lb Main s hs hs_config h_cstrs state_cstrs
    h_is_loadX0_lb h_fits_in_mem h_is_aligned).symm

theorem soundness_load_x0_lbu (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_lbu : Main[42] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 1 = true) :
    (Load.LoadX0.sp1_loadX0 Main).run s =
      (Load.LoadX0.spec_loadX0_lbu (Load.LoadX0.sp1_imm_c Main)
        (.Regidx (Load.LoadX0.sp1_ob_b Main))
        (.Regidx (Load.LoadX0.sp1_op_a Main))).run s :=
  (Load.LoadX0.correct_loadX0_lbu Main s hs hs_config h_cstrs state_cstrs
    h_is_loadX0_lbu h_fits_in_mem h_is_aligned).symm

theorem soundness_load_x0_lh (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_lh : Main[43] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 2 = true) :
    (Load.LoadX0.sp1_loadX0 Main).run s =
      (Load.LoadX0.spec_loadX0_lh (Load.LoadX0.sp1_imm_c Main)
        (.Regidx (Load.LoadX0.sp1_ob_b Main))
        (.Regidx (Load.LoadX0.sp1_op_a Main))).run s :=
  (Load.LoadX0.correct_loadX0_lh Main s hs hs_config h_cstrs state_cstrs
    h_is_loadX0_lh h_fits_in_mem h_is_aligned).symm

theorem soundness_load_x0_lhu (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_lhu : Main[44] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 2 = true) :
    (Load.LoadX0.sp1_loadX0 Main).run s =
      (Load.LoadX0.spec_loadX0_lhu (Load.LoadX0.sp1_imm_c Main)
        (.Regidx (Load.LoadX0.sp1_ob_b Main))
        (.Regidx (Load.LoadX0.sp1_op_a Main))).run s :=
  (Load.LoadX0.correct_loadX0_lhu Main s hs hs_config h_cstrs state_cstrs
    h_is_loadX0_lhu h_fits_in_mem h_is_aligned).symm

theorem soundness_load_x0_lw (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_lw : Main[45] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 4 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 4 = true) :
    (Load.LoadX0.sp1_loadX0 Main).run s =
      (Load.LoadX0.spec_loadX0_lw (Load.LoadX0.sp1_imm_c Main)
        (.Regidx (Load.LoadX0.sp1_ob_b Main))
        (.Regidx (Load.LoadX0.sp1_op_a Main))).run s :=
  (Load.LoadX0.correct_loadX0_lw Main s hs hs_config h_cstrs state_cstrs
    h_is_loadX0_lw h_fits_in_mem h_is_aligned).symm

theorem soundness_load_x0_lwu (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_lwu : Main[46] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 4 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 4 = true) :
    (Load.LoadX0.sp1_loadX0 Main).run s =
      (Load.LoadX0.spec_loadX0_lwu (Load.LoadX0.sp1_imm_c Main)
        (.Regidx (Load.LoadX0.sp1_ob_b Main))
        (.Regidx (Load.LoadX0.sp1_op_a Main))).run s :=
  (Load.LoadX0.correct_loadX0_lwu Main s hs hs_config h_cstrs state_cstrs
    h_is_loadX0_lwu h_fits_in_mem h_is_aligned).symm

theorem soundness_load_x0_ld (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s) (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (Load.LoadX0.constraints Main).allHold_poly)
    (state_cstrs : (Load.LoadX0.constraints Main).initialState_poly s)
    (h_is_loadX0_ld : Main[47] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 8 < 2 ^ 64)
    (h_is_aligned : is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 8 = true) :
    (Load.LoadX0.sp1_loadX0 Main).run s =
      (Load.LoadX0.spec_loadX0_ld (Load.LoadX0.sp1_imm_c Main)
        (.Regidx (Load.LoadX0.sp1_ob_b Main))
        (.Regidx (Load.LoadX0.sp1_op_a Main))).run s :=
  (Load.LoadX0.correct_loadX0_ld Main s hs hs_config h_cstrs state_cstrs
    h_is_loadX0_ld h_fits_in_mem h_is_aligned).symm

end
