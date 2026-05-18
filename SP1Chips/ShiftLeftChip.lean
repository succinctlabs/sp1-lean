import SP1Foundations
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.ShiftLeft.Sll
import SP1Chips.ShiftLeft.Sllw

open LeanRV64D.Functions
open BitVec

namespace ShiftLeft

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 65)

-- Unified SP1 implementation for the ShiftLeft chip. The four variants (sll, slli,
-- sllw, slliw) all write the same Main columns to the destination register; the
-- chip's constraints determine which Sail spec those columns implement.
def sp1_shift_left : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]])

end ShiftLeft

namespace Sll.Poly

open ShiftLeft

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 65)
  (s : SailState)

noncomputable def spec_sll (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SLL
  pure ()

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: chip cstrs flatten + ALU iff_poly + state simp + spec.*_poly application chains; mirrors MulChip pattern.
theorem correct_sll
    (cstrs : (constraints Main).allHold_poly)
    (h_is_sll : is_sll_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_sll (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_shift_left Main).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_sll, eq_imm⟩ := h_is_sll
  have h_real := is_real_eq_one_of_sll Main cstrs eq_sll
  -- Get bounds.
  have ⟨h6_lt, h14_lt, h_imm0_op_c_lt, h_pc_lt, is_U64_b, is_U64_c, _h_imm1, _h_a0_zeros⟩ :=
    bounds_poly Main cstrs h_real
  have h21_lt : Main[21].val < 32 := h_imm0_op_c_lt eq_imm
  -- Process state_cstrs.
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
    h6_lt, h14_lt, h21_lt, h_real, eq_imm] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  -- Monadic chain.
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_sll, sp1_shift_left, execute, execute_RTYPE']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  have spec_eq := spec.sll_poly Main ⟨eq_sll, eq_imm⟩ cstrs
  have hp : 2 ^ 17 < p := Fact.out
  by_cases h_is_op_a_0 : Main[6] = 0
  · -- a = 0 case: a's are all 0, so shift_result = 0; both spec/sp1 just bump PC.
    simp_all
    have h_shift_zero : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] <<<
        ((Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], Main[28]]).toNat % 64) : BitVec 64) = 0#64 := by
      rw [← spec_eq]
      simp [Word.toBitVec64_poly, Word.toNat_poly_def, ZMod.val_zero]
    rw [if_pos h_shift_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
  · simp_all
    have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    rw [exec_RTYPE_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp_all [bitVecToRegidxVal]

end Sll.Poly

namespace Slli.Poly

open ShiftLeft

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 65)
  (s : SailState)

noncomputable def spec_slli (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIOP shamt rs1 rd sop.SLLI
  pure ()

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: chip cstrs flatten + ALU iff_poly + state simp + spec.*_poly application chains; mirrors MulChip pattern.
theorem correct_slli
    (cstrs : (constraints Main).allHold_poly)
    (h_is_slli : is_slli_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_imm_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_slli op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_shift_left Main).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_sll, eq_imm⟩ := h_is_slli
  have h_real := is_real_eq_one_of_sll Main cstrs eq_sll
  have ⟨h6_lt, h14_lt, _h_imm0_op_c_lt, h_pc_lt, is_U64_b, is_U64_c, h_imm1, _h_a0_zeros⟩ :=
    bounds_poly Main cstrs h_real
  obtain ⟨e_25, h_26, h_27, h_28, h_25_lt_64_via_sll, _h_25_lt_32_via_sllw⟩ := h_imm1 eq_imm
  have h_25_lt_64 : Main[25].val < 64 := h_25_lt_64_via_sll eq_sll
  have h_21_lt_64 : Main[21].val < 64 := by rw [e_25]; exact h_25_lt_64
  -- Process state_cstrs.
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
    h6_lt, h14_lt, h_real, eq_imm] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b⟩ := state_cstrs
  have spec_eq := spec.slli_poly Main ⟨eq_sll, eq_imm⟩ cstrs
  have hp : 2 ^ 17 < p := Fact.out
  -- Monadic chain.
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_slli, sp1_shift_left, execute, execute_SHIFTIOP']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_imm_poly, read_op_b]
  -- Bridge: shamt vector matches #v[Main[25..28]] (used in both branches).
  have h_shamt_eq : (#v[((BitVec.ofNat 6 Main[21].val).toNat : ZMod p), 0, 0, 0] : Word (ZMod p))
                  = #v[Main[25], Main[26], Main[27], Main[28]] := by
    have h_21_toNat : (BitVec.ofNat 6 Main[21].val).toNat = Main[21].val := by
      simp; omega
    rw [h_21_toNat, ZMod.natCast_zmod_val]
    rw [e_25, h_26, h_27, h_28]
  -- Bridge SHIFTIOP_pure to RTYPE_pure_w_poly (before by_cases; preserves Fact instance).
  rw [exec_SHIFTIOP_pure_bv_to_w_poly _ _ _ is_U64_b]
  simp only [execute_SHIFTIOP_pure_w_poly]
  rw [h_shamt_eq]
  rw [show rop_of_sop sop.SLLI = rop.SLL from rfl]
  by_cases h_is_op_a_0 : Main[6] = 0
  · -- a = 0 case: a's are all 0, so shift_result = 0; both spec/sp1 just bump PC.
    simp_all
    have h_shift_zero : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] <<<
        ((Word.toBitVec64_poly #v[Main[25], (0 : ZMod p), 0, 0]).toNat % 64) : BitVec 64) = 0#64 := by
      rw [← spec_eq]
      simp [Word.toBitVec64_poly, Word.toNat_poly_def, ZMod.val_zero]
    rw [if_pos h_shift_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
  · simp_all
    have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp_all [bitVecToRegidxVal]

end Slli.Poly

namespace Sllw.Poly

open ShiftLeft

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 65)
  (s : SailState)

noncomputable def spec_sllw (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SLLW
  pure ()

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: chip cstrs flatten + ALU iff_poly + state simp + spec.*_poly application chains; mirrors MulChip pattern.
theorem correct_sllw
    (cstrs : (constraints Main).allHold_poly)
    (h_is_sllw : is_sllw_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_sllw (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_shift_left Main).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_sllw, eq_imm⟩ := h_is_sllw
  have h_real := is_real_eq_one_of_sllw Main cstrs eq_sllw
  have ⟨h6_lt, h14_lt, h_imm0_op_c_lt, h_pc_lt, is_U64_b, is_U64_c, _h_imm1, _h_a0_zeros⟩ :=
    bounds_poly Main cstrs h_real
  have h21_lt : Main[21].val < 32 := h_imm0_op_c_lt eq_imm
  -- Process state_cstrs.
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
    h6_lt, h14_lt, h21_lt, h_real, eq_imm] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  -- Monadic chain.
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_sllw, sp1_shift_left, execute, execute_RTYPEW']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  have spec_eq := spec.sllw_poly Main ⟨eq_sllw, eq_imm⟩ cstrs
  have hp : 2 ^ 17 < p := Fact.out
  -- Convert the BitVec-level execute_RTYPEW_pure in the goal to the polymorphic
  -- Word form, so it matches spec_eq's RHS.
  rw [exec_RTYPEW_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · -- a = 0 case: a's are all 0, so shift_result = 0; both spec/sp1 just bump PC.
    simp_all
    have h_shift_zero : BitVec.signExtend 64
        ((Word.low_poly (#v[Main[15], Main[16], Main[17], Main[18]] : Word (ZMod p))).toBitVec32_poly <<<
          (((Word.low_poly (#v[Main[25], Main[26], Main[27], Main[28]] : Word (ZMod p))).toBitVec32_poly).toNat % 32)) = 0#64 := by
      rw [← spec_eq]
      simp [Word.toBitVec64_poly, Word.toNat_poly_def, ZMod.val_zero]
    rw [if_pos h_shift_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
  · simp_all
    have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp_all [bitVecToRegidxVal]

end Sllw.Poly

namespace Slliw.Poly

open ShiftLeft

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 65)
  (s : SailState)

noncomputable def spec_slliw (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIWOP shamt rs1 rd sopw.SLLIW
  pure ()

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: chip cstrs flatten + ALU iff_poly + state simp + spec.*_poly application chains; mirrors MulChip pattern.
theorem correct_slliw
    (cstrs : (constraints Main).allHold_poly)
    (h_is_slliw : is_slliw_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_imm_w_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_slliw op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_shift_left Main).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_slliw, eq_imm⟩ := h_is_slliw
  have h_real := is_real_eq_one_of_sllw Main cstrs eq_slliw
  have ⟨h6_lt, h14_lt, _h_imm0_op_c_lt, h_pc_lt, is_U64_b, is_U64_c, h_imm1, _h_a0_zeros⟩ :=
    bounds_poly Main cstrs h_real
  obtain ⟨e_25, h_26, h_27, h_28, _h_25_lt_64_via_sll, h_25_lt_32_via_sllw⟩ := h_imm1 eq_imm
  have h_25_lt_32 : Main[25].val < 32 := h_25_lt_32_via_sllw eq_slliw
  have h_21_lt_32 : Main[21].val < 32 := by rw [e_25]; exact h_25_lt_32
  -- Process state_cstrs.
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
    h6_lt, h14_lt, h_real, eq_imm] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b⟩ := state_cstrs
  have spec_eq := spec.slliw_poly Main ⟨eq_slliw, eq_imm⟩ cstrs
  have hp : 2 ^ 17 < p := Fact.out
  -- Monadic chain.
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_slliw, sp1_shift_left, execute, execute_SHIFTIWOP']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_imm_w_poly, read_op_b]
  -- Bridge: shamt vector matches #v[Main[25..28]] (5-bit shamt for sllw).
  have h_shamt_eq : (#v[((BitVec.ofNat 5 Main[21].val).toNat : ZMod p), 0, 0, 0] : Word (ZMod p))
                  = #v[Main[25], Main[26], Main[27], Main[28]] := by
    have h_21_toNat : (BitVec.ofNat 5 Main[21].val).toNat = Main[21].val := by
      simp; omega
    rw [h_21_toNat, ZMod.natCast_zmod_val]
    rw [e_25, h_26, h_27, h_28]
  -- Bridge SHIFTIWOP_pure to RTYPEW_pure_w_poly.
  rw [exec_SHIFTIWOP_pure_bv_to_w_poly _ _ _ is_U64_b]
  simp only [execute_SHIFTIWOP_pure_w_poly]
  rw [h_shamt_eq]
  rw [show ropw_of_sopw sopw.SLLIW = ropw.SLLW from rfl]
  by_cases h_is_op_a_0 : Main[6] = 0
  · -- a = 0 case.
    simp_all
    have h_shift_zero : BitVec.signExtend 64
        ((Word.low_poly (#v[Main[15], Main[16], Main[17], Main[18]] : Word (ZMod p))).toBitVec32_poly <<<
          (((Word.low_poly (#v[Main[25], (0 : ZMod p), 0, 0] : Word (ZMod p))).toBitVec32_poly).toNat % 32)) = 0#64 := by
      rw [← spec_eq]
      simp [Word.toBitVec64_poly, Word.toNat_poly_def, ZMod.val_zero]
    rw [if_pos h_shift_zero]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
  · simp_all
    have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp_all [bitVecToRegidxVal]

end Slliw.Poly
