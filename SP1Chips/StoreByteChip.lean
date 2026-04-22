import SP1Foundations
import SP1Chips.Store.StoreByte.Constraints
import SP1Operations.Operation.AddrAddOperation

open LeanRV64D.Functions Sail SailState

namespace Store

namespace StoreByte

noncomputable def spec_sb (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_STORE imm rs1 rs2 (width := 1)

def sp1_op_a (Main : Vector (Fin KB) 52) : BitVec 5 :=
  BitVec.ofNat 5 Main[6]

def sp1_ob_b (Main : Vector (Fin KB) 52) : BitVec 5 :=
  BitVec.ofNat 5 Main[14]

def sp1_imm_c (Main : Vector (Fin KB) 52) : BitVec 12 :=
  BitVec.ofNat 12 (Word.toNat #v[Main[21], Main[22], Main[23], Main[24]])

def sp1_sb (Main : Vector (Fin KB) 52) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3] + 4, Main[4], Main[5], 0])
  let addr : BitVec 64 := Word.toBitVec64 #v[Main[26], Main[27], Main[28], 0]
  Sail.ConcurrencyInterfaceV1.write_ram 64 1 0#64 addr
    (Word.toBitVec64 #v[Main[7], Main[8], Main[9], Main[10]])
  return RETIRE_SUCCESS

theorem correct (Main : Vector (Fin KB) 52)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (StoreByte.constraints Main).allHold)
    (state_cstrs : (StoreByte.constraints Main).initialState s)
    (h_is_real : Main[50] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2^64)
    (h_below_clint :
      let reg_val := Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]
      let offset := BitVec.signExtend 64 (sp1_imm_c Main)
      BitVec.toNat (reg_val + offset) + 1 ≤ 33554432) :
    let op_a := sp1_op_a Main
    let op_b := sp1_ob_b Main
    let imm_c := sp1_imm_c Main
    (spec_sb imm_c (.Regidx op_a) (.Regidx op_b)).run s = (sp1_sb Main).run s := by
  extract_lets op_a op_b imm_c

  -- Extract the facts about the config registers in the state
  obtain ⟨h_mprv_disabled, h_cur_privilege⟩ := hs_config

  -- Extract the main constraints from the chip
  rw [StoreByte.constraints] at h_cstrs
  simp [SP1ConstraintList.allHold] at h_cstrs
  simp [AddressOperation.constraints, sub_eq_zero, h_is_real] at h_cstrs
  obtain ⟨h_add_addr, h49, h38, h39, h40, h49, h_cpu, h_reader, h_cstrs⟩ := h_cstrs

  -- Extract constraints about the reader
  simp [ITypeReaderImmutable.constraints,
      SP1Constraint.toProp, Opcode.ofNat, Nat.ble] at h_reader
  have h25 : Main[25] = 1 := by have := h_reader.2.2.1.resolve_right (by decide); omega
  simp [h25] at *
  have h_imm_c : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
      BitVec.signExtend 64 (BitVec.ofNat 12 Main[21]) := by clear *- h_reader; simp_all only
  have h6_32 : Main[6] < 32 := by clear *- h_reader; simp_all only
  have h14_32 : Main[14] < 32 := by clear *- h_reader; simp_all only
  have h2728 : ¬ (Main[27] = 0 ∧ Main[28] = 0) := by clear *- h40; aesop

  -- Extract constraints about the state of operations
  simp [StoreByte.constraints, AddressOperation.constraints,
    SP1Constraint.toStateProp, AddrAddOperation.constraints,
    CPUState.constraints, ITypeReaderImmutable.constraints,
    Opcode.ofNat, Nat.ble, h_is_real, h6_32, h14_32, h2728] at state_cstrs
  obtain ⟨h_read_pc, h6_op_a, h14_op_a, h_imm_state⟩ := state_cstrs
  rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_read_pc

  have h15u64 : Word.isU64 #v[Main[15], Main[16], Main[17], Main[18]] := by
    clear *- h_reader; simp_all only
  have h21u64 : Word.isU64 #v[Main[21], Main[22], Main[23], Main[24]] := by
    clear *- h_reader; apply Word.isU64_of_cases <;> (simp; omega)

  -- Extract constraints about the addr add
  have haddr_add := AddrAddOperation.spec_of_constraints _ _ h15u64 h21u64 _ h_add_addr

  -- Simplify the monadic computation
  simp [spec_sb]
  simp [run_readReg_of_isInitialized s _ hs]
  simp [h_read_pc]
  simp [execute_STORE]
  simp only [BitVec.ofNatLT_eq_ofNat] at h6_op_a h14_op_a
  simp [op_a, sp1_op_a, h6_op_a]
  simp [op_b, sp1_ob_b, h14_op_a]
  simp [AddrAddOperation.spec] at haddr_add
  simp [sp1_sb, haddr_add.2]

  -- Apply the main helper lemma
  rw [run_vmem_write_of_width_1' (BitVec.ofNat 5 Main[14])
    (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]])
    (BitVec.signExtend 64 imm_c)
    (BitVec.ofNat 8 ↑Main[7])]

  -- Arithmetic Caclulations
  · simp [sp1_sb, h_imm_c, imm_c, Sail.ConcurrencyInterfaceV1.write_ram, PreSail.write_ram,
      PreSail.writeBytes, PreSail.writeByte]
    constructor
    · simp [Word.toBitVec64, Word.toNat, Fin.val_add]
      refine congr_arg (BitVec.ofNat 64) ?_
      simp [BitVec.toNat_ofNat]
      omega
    · apply congr_arg₂ s.mem.insert
      · simp [Word.toBitVec64, Word.toNat_def, sp1_imm_c]
        congr 4
        simp [BitVec.toNat_eq]
        omega
      · simp [BitVec.toNat_eq]

  -- Other hypothesis for the lemma
  · simp [SailState.isInitialized, hs]
  · simpa using h14_op_a
  · simp [is_aligned_vaddr]
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  · simp
    simpa [Std.ExtDHashMap.get_insert]
  · simpa [imm_c, sp1_imm_c] using h_below_clint

end StoreByte

end Store
