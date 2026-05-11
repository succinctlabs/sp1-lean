import SP1Operations.Operation.MulOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Chips.Mul.Constraints

open LeanRV64D.Functions
open BitVec

namespace Mul.Poly

open Mul

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
  (Main : Vector (ZMod p) 82)
  (s : SailState)

noncomputable def spec_mul_poly (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd { result_part := .Low, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned }
  pure ()

def sp1_mul_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[28], Main[29], Main[30], Main[31]])

open Sail

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: the chip cstrs flatten + reader iff_poly + state simp + spec.mul_poly application
-- chains push past the default 200K budget; AddChip uses the 1.6M default but Mul has 5× the
-- variant flags + 16-byte product to thread through.
theorem correct_mul_poly
    (cstrs : (Mul.constraints Main).allHold_poly)
    (h_is_mul : Mul.is_mul_poly Main)
    (state_cstrs : (Mul.constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_mul_poly (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_mul_poly Main).run s := by
  obtain ⟨h_77, h_M30⟩ := h_is_mul
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have ⟨h_78, h_79, h_80, h_81⟩ := (Mul.single_op_poly Main cstrs).1 h_77
  have h_is_real_eq_one := Mul.is_real_eq_one_of_mul Main cstrs h_77
  have ⟨is_U64_b, is_U64_c⟩ := Mul.ops_U64_b_c_poly Main cstrs h_is_real_eq_one
  have h11_val : (11 : ZMod p).val = 11 :=
    ZMod.val_natCast_of_lt (by omega : (11 : ℕ) < p)
  -- Flatten chip cstrs.
  simp only [SP1ConstraintList.allHold_poly, Mul.constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨mul_op_cstrs, cpu_cstrs⟩, reader_cstrs⟩, _, _, _, _, _, _, _⟩ := cstrs
  -- Reader bounds via iff_is_real_poly + opcode reduction.
  rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real_eq_one] at cpu_cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real_eq_one] at reader_cstrs
  simp [h_77, h_78, h_79, h_80, h_81, Opcode.ofNat, Nat.ble, h11_val] at reader_cstrs
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b', is_U64_c'⟩⟩, _⟩⟩ := reader_cstrs
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h_op_a_lt
    rwa [h32] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1
    rwa [h32] at this
  have h21 : Main[21].val < 32 := by
    have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2
    rwa [h32] at this
  -- state_cstrs handling
  simp [SP1ConstraintList.initialState_poly, Mul.constraints, SP1Constraint.toStateProp_poly,
    List.Forall, MulOperation.constraints, U16toU8OperationSafe.constraints,
    U16MSBOperation.constraints, CPUState.constraints, RTypeReader.constraints,
    h6, h14, h21, h_77, h_78, h_79, h_80, h_81, h_M30, h_is_real_eq_one] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  -- Apply MulOperation.spec.mul_poly (requires is_real = 1)
  rw [h_is_real_eq_one] at mul_op_cstrs
  have ⟨is_U64_aw, aw_eq⟩ :=
    MulOperation.spec.mul_poly is_U64_b is_U64_c mul_op_cstrs h_77
  -- Monadic manipulation
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_mul_poly, sp1_mul_poly, execute, execute_MUL']
  rw [run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  -- Reduce `mop_of_mul_op {result := Low, signed_rs1 := Unsigned, signed_rs2 := Unsigned}` → `mop.MUL`
  rw [show mop_of_mul_op { result_part := .Low, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned }
      = mop.MUL from rfl]
  rw [← aw_eq]
  -- Preserve Fact instances across simp_all (which would collapse them to Fact True).
  have h17 : 2 ^ 17 < p := Fact.out
  -- Bridge: Main[3].val < 65536 from the trusted_instr's PC-bound conjunct.
  have h_pc3 : Main[3].val < 65536 := by
    have h3 : Main[3] < (65536 : ZMod p) := by
      simp_all  -- pulls h_pc_bound from `left✝³` in hypotheses
    have : Main[3].val < (65536 : ZMod p).val := h3
    rwa [val_65536_zmod_p] at this
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

end Mul.Poly

namespace Mulh.Poly

open Mul

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
  (Main : Vector (ZMod p) 82)
  (s : SailState)

noncomputable def spec_mulh_poly (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed }
  pure ()

def sp1_mulh_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[28], Main[29], Main[30], Main[31]])

open Sail

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: see correct_mul_poly comment.
theorem correct_mulh_poly
    (cstrs : (Mul.constraints Main).allHold_poly)
    (h_is_mulh : Mul.is_mulh_poly Main)
    (state_cstrs : (Mul.constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_mulh_poly (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_mulh_poly Main).run s := by
  obtain ⟨h_78, h_M30⟩ := h_is_mulh
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have ⟨h_77, h_79, h_80, h_81⟩ := (Mul.single_op_poly Main cstrs).2.1 h_78
  have h_is_real_eq_one := Mul.is_real_eq_one_of_mulh Main cstrs h_78
  have ⟨is_U64_b, is_U64_c⟩ := Mul.ops_U64_b_c_poly Main cstrs h_is_real_eq_one
  have h12_val : (12 : ZMod p).val = 12 :=
    ZMod.val_natCast_of_lt (by omega : (12 : ℕ) < p)
  simp only [SP1ConstraintList.allHold_poly, Mul.constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨mul_op_cstrs, cpu_cstrs⟩, reader_cstrs⟩, _, _, _, _, _, _, _⟩ := cstrs
  rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real_eq_one] at cpu_cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real_eq_one] at reader_cstrs
  simp [h_77, h_78, h_79, h_80, h_81, Opcode.ofNat, Nat.ble, h12_val] at reader_cstrs
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b', is_U64_c'⟩⟩, _⟩⟩ := reader_cstrs
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h_op_a_lt
    rwa [h32] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1
    rwa [h32] at this
  have h21 : Main[21].val < 32 := by
    have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2
    rwa [h32] at this
  simp [SP1ConstraintList.initialState_poly, Mul.constraints, SP1Constraint.toStateProp_poly,
    List.Forall, MulOperation.constraints, U16toU8OperationSafe.constraints,
    U16MSBOperation.constraints, CPUState.constraints, RTypeReader.constraints,
    h6, h14, h21, h_77, h_78, h_79, h_80, h_81, h_M30, h_is_real_eq_one] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  rw [h_is_real_eq_one] at mul_op_cstrs
  have ⟨is_U64_aw, aw_eq⟩ :=
    MulOperation.spec.mulh_poly is_U64_b is_U64_c mul_op_cstrs h_78
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_mulh_poly, sp1_mulh_poly, execute, execute_MUL']
  rw [run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  rw [show mop_of_mul_op { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Signed }
      = mop.MULH from rfl]
  rw [← aw_eq]
  have h17 : 2 ^ 17 < p := Fact.out
  have h_pc3 : Main[3].val < 65536 := by
    have h3 : Main[3] < (65536 : ZMod p) := by simp_all
    have : Main[3].val < (65536 : ZMod p).val := h3
    rwa [val_65536_zmod_p] at this
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

end Mulh.Poly

namespace Mulhu.Poly

open Mul

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
  (Main : Vector (ZMod p) 82)
  (s : SailState)

noncomputable def spec_mulhu_poly (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned }
  pure ()

def sp1_mulhu_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[28], Main[29], Main[30], Main[31]])

open Sail

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: see correct_mul_poly comment.
theorem correct_mulhu_poly
    (cstrs : (Mul.constraints Main).allHold_poly)
    (h_is_mulhu : Mul.is_mulhu_poly Main)
    (state_cstrs : (Mul.constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_mulhu_poly (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_mulhu_poly Main).run s := by
  obtain ⟨h_79, h_M30⟩ := h_is_mulhu
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have ⟨h_77, h_78, h_80, h_81⟩ := (Mul.single_op_poly Main cstrs).2.2.1 h_79
  have h_is_real_eq_one := Mul.is_real_eq_one_of_mulhu Main cstrs h_79
  have ⟨is_U64_b, is_U64_c⟩ := Mul.ops_U64_b_c_poly Main cstrs h_is_real_eq_one
  have h13_val : (13 : ZMod p).val = 13 :=
    ZMod.val_natCast_of_lt (by omega : (13 : ℕ) < p)
  simp only [SP1ConstraintList.allHold_poly, Mul.constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨mul_op_cstrs, cpu_cstrs⟩, reader_cstrs⟩, _, _, _, _, _, _, _⟩ := cstrs
  rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real_eq_one] at cpu_cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real_eq_one] at reader_cstrs
  simp [h_77, h_78, h_79, h_80, h_81, Opcode.ofNat, Nat.ble, h13_val] at reader_cstrs
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b', is_U64_c'⟩⟩, _⟩⟩ := reader_cstrs
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h_op_a_lt
    rwa [h32] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1
    rwa [h32] at this
  have h21 : Main[21].val < 32 := by
    have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2
    rwa [h32] at this
  simp [SP1ConstraintList.initialState_poly, Mul.constraints, SP1Constraint.toStateProp_poly,
    List.Forall, MulOperation.constraints, U16toU8OperationSafe.constraints,
    U16MSBOperation.constraints, CPUState.constraints, RTypeReader.constraints,
    h6, h14, h21, h_77, h_78, h_79, h_80, h_81, h_M30, h_is_real_eq_one] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  rw [h_is_real_eq_one] at mul_op_cstrs
  have ⟨is_U64_aw, aw_eq⟩ :=
    MulOperation.spec.mulhu_poly is_U64_b is_U64_c mul_op_cstrs h_79
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_mulhu_poly, sp1_mulhu_poly, execute, execute_MUL']
  rw [run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  rw [show mop_of_mul_op { result_part := .High, signed_rs1 := .Unsigned, signed_rs2 := .Unsigned }
      = mop.MULHU from rfl]
  rw [← aw_eq]
  have h17 : 2 ^ 17 < p := Fact.out
  have h_pc3 : Main[3].val < 65536 := by
    have h3 : Main[3] < (65536 : ZMod p) := by simp_all
    have : Main[3].val < (65536 : ZMod p).val := h3
    rwa [val_65536_zmod_p] at this
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

end Mulhu.Poly

namespace Mulhsu.Poly

open Mul

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
  (Main : Vector (ZMod p) 82)
  (s : SailState)

noncomputable def spec_mulhsu_poly (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MUL rs2 rs1 rd { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned }
  pure ()

def sp1_mulhsu_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[28], Main[29], Main[30], Main[31]])

open Sail

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: see correct_mul_poly comment.
theorem correct_mulhsu_poly
    (cstrs : (Mul.constraints Main).allHold_poly)
    (h_is_mulhsu : Mul.is_mulhsu_poly Main)
    (state_cstrs : (Mul.constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_mulhsu_poly (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_mulhsu_poly Main).run s := by
  obtain ⟨h_80, h_M30⟩ := h_is_mulhsu
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have ⟨h_77, h_78, h_79, h_81⟩ := (Mul.single_op_poly Main cstrs).2.2.2.1 h_80
  have h_is_real_eq_one := Mul.is_real_eq_one_of_mulhsu Main cstrs h_80
  have ⟨is_U64_b, is_U64_c⟩ := Mul.ops_U64_b_c_poly Main cstrs h_is_real_eq_one
  have h14_val : (14 : ZMod p).val = 14 :=
    ZMod.val_natCast_of_lt (by omega : (14 : ℕ) < p)
  simp only [SP1ConstraintList.allHold_poly, Mul.constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨mul_op_cstrs, cpu_cstrs⟩, reader_cstrs⟩, _, _, _, _, _, _, _⟩ := cstrs
  rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real_eq_one] at cpu_cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real_eq_one] at reader_cstrs
  simp [h_77, h_78, h_79, h_80, h_81, Opcode.ofNat, Nat.ble, h14_val] at reader_cstrs
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b', is_U64_c'⟩⟩, _⟩⟩ := reader_cstrs
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h_op_a_lt
    rwa [h32] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1
    rwa [h32] at this
  have h21 : Main[21].val < 32 := by
    have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2
    rwa [h32] at this
  simp [SP1ConstraintList.initialState_poly, Mul.constraints, SP1Constraint.toStateProp_poly,
    List.Forall, MulOperation.constraints, U16toU8OperationSafe.constraints,
    U16MSBOperation.constraints, CPUState.constraints, RTypeReader.constraints,
    h6, h14, h21, h_77, h_78, h_79, h_80, h_81, h_M30, h_is_real_eq_one] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  rw [h_is_real_eq_one] at mul_op_cstrs
  have ⟨is_U64_aw, aw_eq⟩ :=
    MulOperation.spec.mulhsu_poly is_U64_b is_U64_c mul_op_cstrs h_80
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_mulhsu_poly, sp1_mulhsu_poly, execute, execute_MUL']
  rw [run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  rw [show mop_of_mul_op { result_part := .High, signed_rs1 := .Signed, signed_rs2 := .Unsigned }
      = mop.MULHSU from rfl]
  rw [← aw_eq]
  have h17 : 2 ^ 17 < p := Fact.out
  have h_pc3 : Main[3].val < 65536 := by
    have h3 : Main[3] < (65536 : ZMod p) := by simp_all
    have : Main[3].val < (65536 : ZMod p).val := h3
    rwa [val_65536_zmod_p] at this
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

end Mulhsu.Poly

namespace Mulw.Poly

open Mul

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] [Fact (2 ^ 24 < p)]
  (Main : Vector (ZMod p) 82)
  (s : SailState)

noncomputable def spec_mulw_poly (rs2 rs1 rd : regidx) : SailM Unit := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  _ ← execute_MULW rs2 rs1 rd
  pure ()

def sp1_mulw_poly : SailM Unit := do
  let op_a := sp1_op_a_poly Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  Sail.write_reg op_a (Word.toBitVec64_poly #v[Main[28], Main[29], Main[30], Main[31]])

open Sail

set_option maxHeartbeats 8000000 in
-- 8M heartbeats: see correct_mul_poly comment.
theorem correct_mulw_poly
    (cstrs : (Mul.constraints Main).allHold_poly)
    (h_is_mulw : Mul.is_mulw_poly Main)
    (state_cstrs : (Mul.constraints Main).initialState_poly s) :
    let op_c := sp1_op_c_poly Main
    let op_b := sp1_op_b_poly Main
    let op_a := sp1_op_a_poly Main
    (spec_mulw_poly (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s = (sp1_mulw_poly Main).run s := by
  obtain ⟨h_81, h_M30⟩ := h_is_mulw
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp_lt : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have ⟨h_77, h_78, h_79, h_80⟩ := (Mul.single_op_poly Main cstrs).2.2.2.2 h_81
  have h_is_real_eq_one := Mul.is_real_eq_one_of_mulw Main cstrs h_81
  have ⟨is_U64_b, is_U64_c⟩ := Mul.ops_U64_b_c_poly Main cstrs h_is_real_eq_one
  have h24_val : (24 : ZMod p).val = 24 :=
    ZMod.val_natCast_of_lt (by omega : (24 : ℕ) < p)
  simp only [SP1ConstraintList.allHold_poly, Mul.constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp_poly_assertZero, sub_eq_zero, mul_eq_zero] at cstrs
  obtain ⟨⟨⟨mul_op_cstrs, cpu_cstrs⟩, reader_cstrs⟩, _, _, _, _, _, _, _⟩ := cstrs
  rw [CPUState.allHold_constraints_iff_is_real_poly h_is_real_eq_one] at cpu_cstrs
  rw [RTypeReader.allHold_constraints_iff_is_real_poly h_is_real_eq_one] at reader_cstrs
  simp [h_77, h_78, h_79, h_80, h_81, Opcode.ofNat, Nat.ble, h24_val] at reader_cstrs
  obtain ⟨trusted_instr_prop, h_op_a_lt, _, _, _, _, _,
          ⟨⟨_, _, ⟨_, is_U64_b', is_U64_c'⟩⟩, _⟩⟩ := reader_cstrs
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h6 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h_op_a_lt
    rwa [h32] at this
  have h14 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := trusted_instr_prop.1
    rwa [h32] at this
  have h21 : Main[21].val < 32 := by
    have : Main[21].val < (32 : ZMod p).val := trusted_instr_prop.2
    rwa [h32] at this
  simp [SP1ConstraintList.initialState_poly, Mul.constraints, SP1Constraint.toStateProp_poly,
    List.Forall, MulOperation.constraints, U16toU8OperationSafe.constraints,
    U16MSBOperation.constraints, CPUState.constraints, RTypeReader.constraints,
    h6, h14, h21, h_77, h_78, h_79, h_80, h_81, h_M30, h_is_real_eq_one] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_op_c⟩ := state_cstrs
  rw [h_is_real_eq_one] at mul_op_cstrs
  have ⟨is_U64_aw, aw_eq⟩ :=
    MulOperation.spec.mulw_poly is_U64_b is_U64_c mul_op_cstrs h_81
  simp only [BitVec.ofNatLT_eq_ofNat] at *
  simp [spec_mulw_poly, sp1_mulw_poly, execute, execute_MULW']
  rw [run_readReg, read_pc]
  simp [sp1_op_a_poly, sp1_op_b_poly, sp1_op_c_poly, read_op_b, read_op_c]
  rw [← aw_eq]
  have h17 : 2 ^ 17 < p := Fact.out
  have h_pc3 : Main[3].val < 65536 := by
    have h3 : Main[3] < (65536 : ZMod p) := by simp_all
    have : Main[3].val < (65536 : ZMod p).val := h3
    rwa [val_65536_zmod_p] at this
  by_cases h_is_op_a_0 : Main[6] = 0
  · simp_all
  · have h6_val : Main[6].val ≠ 0 := by
      intro h; apply h_is_op_a_0; exact (ZMod.val_eq_zero _).mp h
    have h_bv_neq : BitVec.ofNat 5 Main[6].val ≠ 0#5 := by
      intro heq; rw [← BitVec.toNat_inj] at heq; simp at heq; omega
    rw [if_neg h_bv_neq, if_neg h_bv_neq]
    rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
        Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
        show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    simp [bitVecToRegidxVal]

end Mulw.Poly
