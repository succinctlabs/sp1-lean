import SP1Foundations
import SP1Chips.Store.StoreByte.Constraints
import SP1Operations.Operation.AddrAddOperation
import SP1Operations.Reader.ITypeReaderImmutable

open LeanRV64D.Functions Sail SailState

namespace Store

namespace StoreByte

variable
  {p : ℕ} [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)]

noncomputable def spec_sb (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_STORE imm rs1 rs2 (width := 1)

def sp1_op_a (Main : Vector (ZMod p) 50) : BitVec 5 :=
  BitVec.ofNat 5 Main[6].val

def sp1_ob_b (Main : Vector (ZMod p) 50) : BitVec 5 :=
  BitVec.ofNat 5 Main[14].val

def sp1_imm_c (Main : Vector (ZMod p) 50) : BitVec 12 :=
  BitVec.ofNat 12 (Word.toNat_poly #v[Main[21], Main[22], Main[23], Main[24]])

def sp1_sb (Main : Vector (ZMod p) 50) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64_poly #v[Main[3] + 4, Main[4], Main[5], 0])
  let addr : BitVec 64 := Word.toBitVec64_poly #v[Main[25], Main[26], Main[27], 0]
  Sail.ConcurrencyInterfaceV1.write_ram 64 1 0#64 addr
    (Word.toBitVec64_poly #v[Main[7], Main[8], Main[9], Main[10]])
  return RETIRE_SUCCESS

set_option maxHeartbeats 1600000 in
-- StoreDouble pattern + single-byte data shape (uses run_vmem_write_of_width_1').
set_option debug.skipKernelTC true in
theorem correct (Main : Vector (ZMod p) 50)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (StoreByte.constraints Main).allHold_poly)
    (state_cstrs : (StoreByte.constraints Main).initialState_poly s)
    (h_is_real : Main[49] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    (h_below_clint :
      let reg_val := Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]]
      let offset := BitVec.signExtend 64 (sp1_imm_c Main)
      BitVec.toNat (reg_val + offset) + 1 ≤ 33554432) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_sb imm_c (.Regidx op_a) (.Regidx op_b)).run s = (sp1_sb Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_mprv_disabled, h_cur_privilege⟩ := hs_config
  rw [StoreByte.constraints] at h_cstrs
  simp [SP1ConstraintList.allHold_poly] at h_cstrs
  simp [AddressOperation.constraints, sub_eq_zero, SP1Constraint.toProp_poly,
    h_is_real] at h_cstrs
  obtain ⟨h_add_addr, _h_a, _h_b, _h_c, h40, _h_d, _h_cpu, h_reader, _h_cstrs_rest⟩ := h_cstrs
  have hp_lt : 131072 < p := by
    have := Fact.out (p := 2 ^ 17 < p)
    have h17 : (2 : ℕ) ^ 17 = 131072 := by decide
    omega
  have h32 : (32 : ZMod p).val = 32 := val_32_zmod_p
  have h65 : (65536 : ZMod p).val = 65536 := val_65536_zmod_p
  have h36_lt : (36 : ℕ) < p := by omega
  have h36_val : (36 : ZMod p).val = 36 := ZMod.val_natCast_of_lt h36_lt
  simp [ITypeReaderImmutable.constraints,
      SP1Constraint.toProp_poly, Opcode.ofNat, Nat.ble, h36_val] at h_reader
  have h_imm_c : Word.toBitVec64_poly #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
    clear *- h_reader; simp_all only
  have h6_lt_zmod : Main[6] < (32 : ZMod p) := by clear *- h_reader; simp_all only
  have h14_lt_zmod : Main[14] < (32 : ZMod p) := by clear *- h_reader; simp_all only
  have h6_32 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_lt_zmod; rwa [h32] at this
  have h14_32 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_lt_zmod; rwa [h32] at this
  simp [SP1ConstraintList.initialState_poly, StoreByte.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp_poly,
    AddrAddOperation.constraints,
    CPUState.constraints, ITypeReaderImmutable.constraints,
    Opcode.ofNat, Nat.ble, h_is_real, h6_32, h14_32, h36_val] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, _h_imm_state⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h15u64 : Word.isU64_poly #v[Main[15], Main[16], Main[17], Main[18]] := by
    clear *- h_reader; simp_all only
  have h21_lt_zmod : Main[21] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h22_lt_zmod : Main[22] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h23_lt_zmod : Main[23] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h24_lt_zmod : Main[24] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h21u64 : Word.isU64_poly #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases_poly <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · have : Main[21].val < (65536 : ZMod p).val := h21_lt_zmod; rwa [h65] at this
    · have : Main[22].val < (65536 : ZMod p).val := h22_lt_zmod; rwa [h65] at this
    · have : Main[23].val < (65536 : ZMod p).val := h23_lt_zmod; rwa [h65] at this
    · have : Main[24].val < (65536 : ZMod p).val := h24_lt_zmod; rwa [h65] at this
  have haddr_add := AddrAddOperation.spec_of_constraints_poly _ _ h15u64 h21u64 _ h_add_addr
  simp [spec_sb]
  simp [run_readReg_of_isInitialized s _ hs]
  simp [h_read_pc]
  simp [execute_STORE]
  simp only [BitVec.ofNatLT_eq_ofNat] at h6_op_a h14_op_a
  simp [op_a, sp1_op_a, h6_op_a]
  simp [op_b, sp1_ob_b, h14_op_a]
  simp [AddrAddOperation.spec_poly] at haddr_add
  simp [sp1_sb, haddr_add.2]
  rw [run_vmem_write_of_width_1' (BitVec.ofNat 5 Main[14].val)
    (Word.toBitVec64_poly #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 imm_c)
    (BitVec.ofNat 8 Main[7].val)]
  · simp [sp1_sb, h_imm_c, imm_c, Sail.ConcurrencyInterfaceV1.write_ram, PreSail.write_ram,
      PreSail.writeBytes, PreSail.writeByte]
    constructor
    · have h_pc3 : Main[3].val < 65536 := by
        have h3 : Main[3] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
        have : Main[3].val < (65536 : ZMod p).val := h3
        rwa [h65] at this
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          Word.toBitVec64_poly_lowLimb_add_nat _ _ _ _ 4 (by omega),
          show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    · apply congr_arg₂ s.mem.insert
      · simp [Word.toBitVec64_poly, Word.toNat_poly_def, sp1_imm_c]
        congr 4
        simp [BitVec.toNat_eq]
        omega
      · simp [BitVec.toNat_eq]
  · simp [SailState.isInitialized, hs]
  · simpa using h14_op_a
  · simp [is_aligned_vaddr]
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  · simp
    simpa [Std.ExtDHashMap.get_insert]
  · simpa [imm_c, sp1_imm_c] using h_below_clint

end StoreByte

end Store
