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
  BitVec.ofNat 12 (Word.toNat #v[Main[21], Main[22], Main[23], Main[24]])

def sp1_sb (Main : Vector (ZMod p) 50) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  let addr : BitVec 64 := Word.toBitVec64 #v[Main[25], Main[26], Main[27], 0]
  Sail.ConcurrencyInterfaceV1.write_ram 64 1 0#64 addr
    (Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]])
  return RETIRE_SUCCESS

-- StoreDouble pattern + single-byte data shape (uses run_vmem_write_of_width_1').
-- The bullet-1 monadic-write equation is discharged by `store_byte_post_vmem_eq`
-- (bare-`BitVec` recipe-2 lift, `docs/PROOF_PATTERNS.md` §3) so this proof no longer
-- requires `set_option debug.skipKernelTC true` or the previous maxHeartbeats bump.
theorem correct (Main : Vector (ZMod p) 50)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (StoreByte.constraints Main).allHold)
    (state_cstrs : (StoreByte.constraints Main).initialState s)
    (h_is_real : Main[49] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_sb imm_c (.Regidx op_a) (.Regidx op_b)).run s = (sp1_sb Main).run s := by
  extract_lets op_a op_b imm_c
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨_, _, _, _, _⟩ := hs_config
  rw [StoreByte.constraints] at h_cstrs
  simp [SP1ConstraintList.allHold] at h_cstrs
  simp [AddressOperation.constraints, sub_eq_zero, SP1Constraint.toProp,
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
      SP1Constraint.toProp, Opcode.ofNat, Nat.ble, h36_val] at h_reader
  have h_imm_c : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21].val) := by
    clear *- h_reader; simp_all only
  have h6_lt_zmod : Main[6] < (32 : ZMod p) := by clear *- h_reader; simp_all only
  have h14_lt_zmod : Main[14] < (32 : ZMod p) := by clear *- h_reader; simp_all only
  have h6_32 : Main[6].val < 32 := by
    have : Main[6].val < (32 : ZMod p).val := h6_lt_zmod; rwa [h32] at this
  have h14_32 : Main[14].val < 32 := by
    have : Main[14].val < (32 : ZMod p).val := h14_lt_zmod; rwa [h32] at this
  simp [SP1ConstraintList.initialState, StoreByte.constraints,
    AddressOperation.constraints, SP1Constraint.toStateProp,
    AddrAddOperation.constraints,
    CPUState.constraints, ITypeReaderImmutable.constraints,
    Opcode.ofNat, Nat.ble, h_is_real, h6_32, h14_32, h36_val] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, _h_imm_state⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc
  have h15u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by
    clear *- h_reader; simp_all only
  have h21_lt_zmod : Main[21] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h22_lt_zmod : Main[22] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h23_lt_zmod : Main[23] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h24_lt_zmod : Main[24] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
  have h21u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    apply Word.isU64_of_cases <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]
    · have : Main[21].val < (65536 : ZMod p).val := h21_lt_zmod; rwa [h65] at this
    · have : Main[22].val < (65536 : ZMod p).val := h22_lt_zmod; rwa [h65] at this
    · have : Main[23].val < (65536 : ZMod p).val := h23_lt_zmod; rwa [h65] at this
    · have : Main[24].val < (65536 : ZMod p).val := h24_lt_zmod; rwa [h65] at this
  have haddr_add := AddrAddOperation.spec_of_constraints _ _ h15u64 h21u64 _ h_add_addr
  -- Derive `h_in_range` from the chip's address-bounds constraints.
  obtain ⟨h25_lt, h26_lt, h27_lt, _⟩ := Word.lt_cases_of_isU64 haddr_add.1
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at h25_lt h26_lt h27_lt
  obtain ⟨h_addr_lo, h_addr_hi⟩ :=
    AddressOperation.addr_limbs_bounds Main[25] Main[26] Main[27] Main[28]
      h25_lt h26_lt h27_lt h40
  -- (b + c).toNat agrees with the limb sum via haddr_add.2 + toBitVec64_toNat
  have h_addr_eq :
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
        Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
        Main[25].val + Main[26].val * 2 ^ 16 + Main[27].val * 2 ^ 32 := by
    rw [← haddr_add.2, Word.toBitVec64_toNat haddr_add.1,
      Word.toNat_def]
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ZMod.val_zero]
    omega
  have h_offset_eq :
      Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
        BitVec.signExtend 64 (sp1_imm_c Main) := by
    rw [h_imm_c, sp1_imm_c]
    congr 1
    apply BitVec.eq_of_toNat_eq
    simp only [Word.toNat_def, Vector.getElem_mk, List.getElem_toArray,
      List.getElem_cons_zero, List.getElem_cons_succ, BitVec.toNat_ofNat]
    omega
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt
          (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
            BitVec.signExtend 64 (sp1_imm_c Main)) 0))
        (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true := by
    rw [← h_offset_eq]
    exact range_subset_sp1_pma _ 1 (by omega)
      (by rw [h_addr_eq]; exact h_addr_lo)
      (by rw [h_addr_eq]; omega)
  simp [spec_sb]
  simp [run_readReg_of_isInitialized s _ hs]
  simp [h_read_pc]
  simp [execute_STORE]
  simp only [BitVec.ofNatLT_eq_ofNat] at h6_op_a h14_op_a
  simp [op_a, sp1_op_a, h6_op_a]
  simp [op_b, sp1_ob_b, h14_op_a]
  simp [AddrAddOperation.spec] at haddr_add
  simp [sp1_sb, haddr_add.2]
  rw [run_vmem_write_of_width_1' (BitVec.ofNat 5 Main[14].val)
    (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 imm_c)
    (BitVec.ofNat 8 Main[7].val)]
  · have h_pc3 : Main[3].val < 65536 := by
      have h3 : Main[3] < (65536 : ZMod p) := by clear *- h_reader; simp_all only
      have : Main[3].val < (65536 : ZMod p).val := h3
      rwa [h65] at this
    have h_pc_lift : Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0]
        = Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4#64 := by
      rw [show (4#64 : BitVec 64) = BitVec.ofNat 64 4 from rfl,
          Word.toBitVec64_lowLimb_add_nat _ _ _ _ 4 (by omega),
          show ((4 : ℕ) : ZMod p) = 4 from by push_cast; rfl]
    rw [h_pc_lift, show Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]
                      = BitVec.signExtend 64 imm_c from h_offset_eq]
    exact store_byte_post_vmem_eq s
      (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4#64)
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] +
        BitVec.signExtend 64 imm_c)
      (BitVec.ofNat 8 Main[7].val)
  · simp [SailState.isInitialized, hs]
  · simpa using h14_op_a
  · exact (is_aligned_vaddr_iff_mod _ 1).mpr (Nat.mod_one _)
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  · simp
    simpa [Std.ExtDHashMap.get_insert]
  · simpa [imm_c, sp1_imm_c] using h_in_range

end StoreByte

end Store
