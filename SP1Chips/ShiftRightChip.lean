import SP1Foundations
import SP1Operations.Operation.U16MSBOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.ALUTypeReader
import SP1Chips.ShiftRight.Srl
import SP1Chips.ShiftRight.Srlw
import SP1Chips.ShiftRight.Sra
import SP1Chips.ShiftRight.Sraw

open LeanRV64D.Functions
open BitVec

namespace Srl.Poly

open ShiftRight

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 69)
  (s : SailState)

noncomputable def spec_srl_poly (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SRL
  pure ()

def sp1_srl_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]])

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: chip cstrs flatten + ALU iff_poly + state simp + spec.*_poly application.
theorem correct_srl_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_srl : is_srl_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_srl_poly (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_srl_poly Main).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_srl, eq_imm⟩ := h_is_srl
  have h_real := is_real_eq_one_of_srl Main cstrs eq_srl
  have ⟨h6_lt, h14_lt, h_imm0_op_c_lt, h_pc_lt, is_U64_b, is_U64_c, _h_imm1, _h_a0_zeros⟩ :=
    bounds_poly Main cstrs h_real
  have h21_lt : Main[21].val < 32 := h_imm0_op_c_lt eq_imm
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
    h6_lt, h14_lt, h21_lt, h_real, eq_imm] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_srl_poly, sp1_srl_poly, execute, execute_RTYPE']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  have spec_eq := spec.srl_poly Main ⟨eq_srl, eq_imm⟩ cstrs
  have hp : 2 ^ 17 < p := Fact.out
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
    have h_shift_zero : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] >>>
        ((Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], Main[28]]).toNat % 64) :
        BitVec 64) = 0#64 := by
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

end Srl.Poly

namespace Srli.Poly

open ShiftRight

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 69)
  (s : SailState)

noncomputable def spec_srli_poly (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIOP shamt rs1 rd sop.SRLI
  pure ()

def sp1_srli_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]])

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: chip cstrs flatten + ALU iff_poly + state simp + spec.*_poly application.
theorem correct_srli_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_srli : is_srli_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_imm_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_srli_poly op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_srli_poly Main).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_srl, eq_imm⟩ := h_is_srli
  have h_real := is_real_eq_one_of_srl Main cstrs eq_srl
  have ⟨h6_lt, h14_lt, _h_imm0_op_c_lt, h_pc_lt, is_U64_b, is_U64_c, h_imm1, _h_a0_zeros⟩ :=
    bounds_poly Main cstrs h_real
  obtain ⟨e_25, h_26, h_27, h_28, h_25_lt_64_via_sr, _h_25_lt_32_via_sw⟩ := h_imm1 eq_imm
  have h_25_lt_64 : Main[25].val < 64 := h_25_lt_64_via_sr (Or.inl eq_srl)
  have h_21_lt_64 : Main[21].val < 64 := by rw [e_25]; exact h_25_lt_64
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
    h6_lt, h14_lt, h_real, eq_imm] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b⟩ := state_cstrs
  have spec_eq := spec.srli_poly Main ⟨eq_srl, eq_imm⟩ cstrs
  have hp : 2 ^ 17 < p := Fact.out
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_srli_poly, sp1_srli_poly, execute, execute_SHIFTIOP']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_imm_poly, read_op_b]
  have h_shamt_eq : (#v[((BitVec.ofNat 6 Main[21].val).toNat : ZMod p), 0, 0, 0] : Word (ZMod p))
                  = #v[Main[25], Main[26], Main[27], Main[28]] := by
    have h_21_toNat : (BitVec.ofNat 6 Main[21].val).toNat = Main[21].val := by
      simp; omega
    rw [h_21_toNat, ZMod.natCast_zmod_val]
    rw [e_25, h_26, h_27, h_28]
  rw [exec_SHIFTIOP_pure_bv_to_w_poly _ _ _ is_U64_b]
  simp only [execute_SHIFTIOP_pure_w_poly]
  rw [h_shamt_eq]
  rw [show rop_of_sop sop.SRLI = rop.SRL from rfl]
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
    have h_shift_zero : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]] >>>
        ((Word.toBitVec64_poly (#v[Main[25], 0, 0, 0] : Word (ZMod p))).toNat % 64) :
        BitVec 64) = 0#64 := by
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

end Srli.Poly

namespace Sra.Poly

open ShiftRight

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 69)
  (s : SailState)

noncomputable def spec_sra_poly (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPE rs2 rs1 rd rop.SRA
  pure ()

def sp1_sra_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]])

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: chip cstrs flatten + ALU iff_poly + state simp + spec.*_poly application.
theorem correct_sra_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_sra : is_sra_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_sra_poly (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sra_poly Main).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_sra, eq_imm⟩ := h_is_sra
  have h_real := is_real_eq_one_of_sra Main cstrs eq_sra
  have ⟨h6_lt, h14_lt, h_imm0_op_c_lt, h_pc_lt, is_U64_b, is_U64_c, _h_imm1, _h_a0_zeros⟩ :=
    bounds_poly Main cstrs h_real
  have h21_lt : Main[21].val < 32 := h_imm0_op_c_lt eq_imm
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
    h6_lt, h14_lt, h21_lt, h_real, eq_imm] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_sra_poly, sp1_sra_poly, execute, execute_RTYPE']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  have spec_eq := spec.sra_poly Main ⟨eq_sra, eq_imm⟩ cstrs
  have hp : 2 ^ 17 < p := Fact.out
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
    have h_shift_zero : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).sshiftRight
        ((Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], Main[28]]).toNat % 64) = 0#64 := by
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

end Sra.Poly

namespace Srai.Poly

open ShiftRight

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 69)
  (s : SailState)

noncomputable def spec_srai_poly (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIOP shamt rs1 rd sop.SRAI
  pure ()

def sp1_srai_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]])

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: chip cstrs flatten + ALU iff_poly + state simp + spec.*_poly application.
theorem correct_srai_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_srai : is_srai_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_imm_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_srai_poly op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_srai_poly Main).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_sra, eq_imm⟩ := h_is_srai
  have h_real := is_real_eq_one_of_sra Main cstrs eq_sra
  have ⟨h6_lt, h14_lt, _h_imm0_op_c_lt, h_pc_lt, is_U64_b, is_U64_c, h_imm1, _h_a0_zeros⟩ :=
    bounds_poly Main cstrs h_real
  obtain ⟨e_25, h_26, h_27, h_28, h_25_lt_64_via_sr, _h_25_lt_32_via_sw⟩ := h_imm1 eq_imm
  have h_25_lt_64 : Main[25].val < 64 := h_25_lt_64_via_sr (Or.inr eq_sra)
  have h_21_lt_64 : Main[21].val < 64 := by rw [e_25]; exact h_25_lt_64
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
    h6_lt, h14_lt, h_real, eq_imm] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b⟩ := state_cstrs
  have spec_eq := spec.srai_poly Main ⟨eq_sra, eq_imm⟩ cstrs
  have hp : 2 ^ 17 < p := Fact.out
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_srai_poly, sp1_srai_poly, execute, execute_SHIFTIOP']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_imm_poly, read_op_b]
  have h_shamt_eq : (#v[((BitVec.ofNat 6 Main[21].val).toNat : ZMod p), 0, 0, 0] : Word (ZMod p))
                  = #v[Main[25], Main[26], Main[27], Main[28]] := by
    have h_21_toNat : (BitVec.ofNat 6 Main[21].val).toNat = Main[21].val := by
      simp; omega
    rw [h_21_toNat, ZMod.natCast_zmod_val]
    rw [e_25, h_26, h_27, h_28]
  rw [exec_SHIFTIOP_pure_bv_to_w_poly _ _ _ is_U64_b]
  simp only [execute_SHIFTIOP_pure_w_poly]
  rw [h_shamt_eq]
  rw [show rop_of_sop sop.SRAI = rop.SRA from rfl]
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
    have h_shift_zero : (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).sshiftRight
        ((Word.toBitVec64_poly (#v[Main[25], 0, 0, 0] : Word (ZMod p))).toNat % 64) = 0#64 := by
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

end Srai.Poly

namespace Srlw.Poly

open ShiftRight

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 69)
  (s : SailState)

noncomputable def spec_srlw_poly (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SRLW
  pure ()

def sp1_srlw_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]])

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: chip cstrs flatten + ALU iff_poly + state simp + spec.*_poly application chains; mirrors MulChip pattern.
theorem correct_srlw_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_srlw : is_srlw_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_srlw_poly (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_srlw_poly Main).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_srlw, eq_imm⟩ := h_is_srlw
  have h_real := is_real_eq_one_of_srlw Main cstrs eq_srlw
  have ⟨h6_lt, h14_lt, h_imm0_op_c_lt, h_pc_lt, is_U64_b, is_U64_c, _h_imm1, _h_a0_zeros⟩ :=
    bounds_poly Main cstrs h_real
  have h21_lt : Main[21].val < 32 := h_imm0_op_c_lt eq_imm
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
    h6_lt, h14_lt, h21_lt, h_real, eq_imm] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_srlw_poly, sp1_srlw_poly, execute, execute_RTYPEW']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  have spec_eq := spec.srlw_poly Main ⟨eq_srlw, eq_imm⟩ cstrs
  have hp : 2 ^ 17 < p := Fact.out
  rw [exec_RTYPEW_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
    have h_shift_zero : BitVec.signExtend 64
        ((Word.low_poly (#v[Main[15], Main[16], Main[17], Main[18]] : Word (ZMod p))).toBitVec32_poly >>>
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

end Srlw.Poly

namespace Srliw.Poly

open ShiftRight

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 69)
  (s : SailState)

noncomputable def spec_srliw_poly (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIWOP shamt rs1 rd sopw.SRLIW
  pure ()

def sp1_srliw_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]])

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: chip cstrs flatten + ALU iff_poly + state simp + spec.*_poly application chains; mirrors MulChip pattern.
theorem correct_srliw_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_srliw : is_srliw_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_imm_w_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_srliw_poly op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_srliw_poly Main).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_srlw, eq_imm⟩ := h_is_srliw
  have h_real := is_real_eq_one_of_srlw Main cstrs eq_srlw
  have ⟨h6_lt, h14_lt, _h_imm0_op_c_lt, h_pc_lt, is_U64_b, is_U64_c, h_imm1, _h_a0_zeros⟩ :=
    bounds_poly Main cstrs h_real
  obtain ⟨e_25, h_26, h_27, h_28, _h_25_lt_64_via_sr, h_25_lt_32_via_sw⟩ := h_imm1 eq_imm
  have h_25_lt_32 : Main[25].val < 32 := h_25_lt_32_via_sw (Or.inl eq_srlw)
  have h_21_lt_32 : Main[21].val < 32 := by rw [e_25]; exact h_25_lt_32
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
    h6_lt, h14_lt, h_real, eq_imm] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b⟩ := state_cstrs
  have spec_eq := spec.srliw_poly Main ⟨eq_srlw, eq_imm⟩ cstrs
  have hp : 2 ^ 17 < p := Fact.out
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_srliw_poly, sp1_srliw_poly, execute, execute_SHIFTIWOP']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_imm_w_poly, read_op_b]
  have h_shamt_eq : (#v[((BitVec.ofNat 5 Main[21].val).toNat : ZMod p), 0, 0, 0] : Word (ZMod p))
                  = #v[Main[25], Main[26], Main[27], Main[28]] := by
    have h_21_toNat : (BitVec.ofNat 5 Main[21].val).toNat = Main[21].val := by
      simp; omega
    rw [h_21_toNat, ZMod.natCast_zmod_val]
    rw [e_25, h_26, h_27, h_28]
  rw [exec_SHIFTIWOP_pure_bv_to_w_poly _ _ _ is_U64_b]
  simp only [execute_SHIFTIWOP_pure_w_poly]
  rw [h_shamt_eq]
  rw [show ropw_of_sopw sopw.SRLIW = ropw.SRLW from rfl]
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
    have h_shift_zero : BitVec.signExtend 64
        ((Word.low_poly (#v[Main[15], Main[16], Main[17], Main[18]] : Word (ZMod p))).toBitVec32_poly >>>
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

end Srliw.Poly

namespace Sraw.Poly

open ShiftRight

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 69)
  (s : SailState)

noncomputable def spec_sraw_poly (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_RTYPEW rs2 rs1 rd ropw.SRAW
  pure ()

def sp1_sraw_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]])

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: chip cstrs flatten + ALU iff_poly + state simp + spec.*_poly application chains; mirrors MulChip pattern.
theorem correct_sraw_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_sraw : is_sraw_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_sraw_poly (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sraw_poly Main).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_sraw, eq_imm⟩ := h_is_sraw
  have h_real := is_real_eq_one_of_sraw Main cstrs eq_sraw
  have ⟨h6_lt, h14_lt, h_imm0_op_c_lt, h_pc_lt, is_U64_b, is_U64_c, _h_imm1, _h_a0_zeros⟩ :=
    bounds_poly Main cstrs h_real
  have h21_lt : Main[21].val < 32 := h_imm0_op_c_lt eq_imm
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
    h6_lt, h14_lt, h21_lt, h_real, eq_imm] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_sraw_poly, sp1_sraw_poly, execute, execute_RTYPEW']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  have spec_eq := spec.sraw_poly Main ⟨eq_sraw, eq_imm⟩ cstrs
  have hp : 2 ^ 17 < p := Fact.out
  rw [exec_RTYPEW_pure_bv_to_w_poly _ _ _ is_U64_b is_U64_c]
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
    have h_shift_zero : BitVec.signExtend 64
        ((Word.low_poly (#v[Main[15], Main[16], Main[17], Main[18]] : Word (ZMod p))).toBitVec32_poly.sshiftRight
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

end Sraw.Poly

namespace Sraiw.Poly

open ShiftRight

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]
  (Main : Vector (ZMod p) 69)
  (s : SailState)

noncomputable def spec_sraiw_poly (shamt : BitVec 6) (rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_SHIFTIWOP shamt rs1 rd sopw.SRAIW
  pure ()

def sp1_sraiw_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[32], Main[33], Main[34], Main[35]])

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: chip cstrs flatten + ALU iff_poly + state simp + spec.*_poly application chains; mirrors MulChip pattern.
theorem correct_sraiw_poly
    (cstrs : (constraints Main).allHold_poly)
    (h_is_sraiw : is_sraiw_poly Main)
    (state_cstrs : (constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_imm_w_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_sraiw_poly op_c (.Regidx op_b) (.Regidx op_a)).run s = (sp1_sraiw_poly Main).run s := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨eq_sraw, eq_imm⟩ := h_is_sraiw
  have h_real := is_real_eq_one_of_sraw Main cstrs eq_sraw
  have ⟨h6_lt, h14_lt, _h_imm0_op_c_lt, h_pc_lt, is_U64_b, is_U64_c, h_imm1, _h_a0_zeros⟩ :=
    bounds_poly Main cstrs h_real
  obtain ⟨e_25, h_26, h_27, h_28, _h_25_lt_64_via_sr, h_25_lt_32_via_sw⟩ := h_imm1 eq_imm
  have h_25_lt_32 : Main[25].val < 32 := h_25_lt_32_via_sw (Or.inr eq_sraw)
  have h_21_lt_32 : Main[21].val < 32 := by rw [e_25]; exact h_25_lt_32
  simp [SP1ConstraintList.initialState_poly, constraints, SP1Constraint.toStateProp_poly,
    List.Forall, U16MSBOperation.constraints, CPUState.constraints, ALUTypeReader.constraints,
    h6_lt, h14_lt, h_real, eq_imm] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b⟩ := state_cstrs
  have spec_eq := spec.sraiw_poly Main ⟨eq_sraw, eq_imm⟩ cstrs
  have hp : 2 ^ 17 < p := Fact.out
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_sraiw_poly, sp1_sraiw_poly, execute, execute_SHIFTIWOP']
  rw [Sail.run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_imm_w_poly, read_op_b]
  have h_shamt_eq : (#v[((BitVec.ofNat 5 Main[21].val).toNat : ZMod p), 0, 0, 0] : Word (ZMod p))
                  = #v[Main[25], Main[26], Main[27], Main[28]] := by
    have h_21_toNat : (BitVec.ofNat 5 Main[21].val).toNat = Main[21].val := by
      simp; omega
    rw [h_21_toNat, ZMod.natCast_zmod_val]
    rw [e_25, h_26, h_27, h_28]
  rw [exec_SHIFTIWOP_pure_bv_to_w_poly _ _ _ is_U64_b]
  simp only [execute_SHIFTIWOP_pure_w_poly]
  rw [h_shamt_eq]
  rw [show ropw_of_sopw sopw.SRAIW = ropw.SRAW from rfl]
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
    have h_shift_zero : BitVec.signExtend 64
        ((Word.low_poly (#v[Main[15], Main[16], Main[17], Main[18]] : Word (ZMod p))).toBitVec32_poly.sshiftRight
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

end Sraiw.Poly
