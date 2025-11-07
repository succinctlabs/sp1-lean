import SP1Foundations
import SP1Chips.Load.LoadDouble.Constraints

open LeanRV64D.Functions Sail SailState

namespace Load

namespace LoadDouble

noncomputable def spec_ld (imm : BitVec 12) (rs1 rs2 : regidx) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm rs1 rs2 (is_unsigned := true) (width := 8)

def sp1_op_a (Main : Vector (Fin KB) 41) : BitVec 5 := BitVec.ofNat 5 Main[6]
def sp1_ob_b (Main : Vector (Fin KB) 41) : BitVec 5 := BitVec.ofNat 5 Main[14]
def sp1_imm_c (Main : Vector (Fin KB) 41) : BitVec 12 := BitVec.ofNat 12 Main[21]

def sp1_ld (Main : Vector (Fin KB) 41) : SailM ExecutionResult := do
  let op_a := sp1_op_a Main
  Sail.writeReg Register.nextPC (Word.toBitVec64 #v[Main[3], Main[4], Main[5], 0] + 4)
  Sail.write_reg op_a (Word.toBitVec64 #v[Main[30], Main[31], Main[32], Main[33]])
  return RETIRE_SUCCESS

set_option maxHeartbeats 2000000 in
theorem correct_lb (Main : Vector (Fin KB) 41)
    (s : SailState) (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (constraints Main).allHold)
    (state_cstrs : (constraints Main).initialState s)
    (h_is_real : Main[39] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat
      reg_val + offset + 8 < 2^64) :
    let op_a := .Regidx (sp1_op_a Main)
    let op_b := .Regidx (sp1_ob_b Main)
    let imm_c := sp1_imm_c Main
    (spec_ld imm_c op_b op_a).run s = (sp1_ld Main).run s := by
  extract_lets op_a op_b imm_c

  obtain ⟨h_mprv_disabled, h_cur_privilege, h_clint_base, h_clint_size,
    h_plat_ram_base, h_plat_rom_base⟩ := hs_config

  rw [LoadDouble.allHold_constraints_iff Main h_is_real] at h_cstrs

  obtain ⟨haddr, h29, h26, hcpu, hreader, h36, h34, h, h37, h38, h30, h13⟩ := h_cstrs

  simp [ITypeReader.constraints, sub_eq_zero] at hreader
  have h25 : Main[25] = 1 := by clear *- hreader; simp_all only
  simp [h25, SP1Constraint.toProp, Opcode.ofNat, Nat.ble, Nat.beq] at hreader

  have h6 : Main[6] < 32 := by simp_all only
  have h14 : Main[14] < 32 := by simp_all only

  have hsign : Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]] =
    BitVec.signExtend 64 (BitVec.ofNat 12 Main[21]) := by simp_all only

  simp [constraints, AddressOperation.constraints, SP1Constraint.toStateProp,
    AddrAddOperation.constraints, CPUState.constraints, ITypeReader.constraints,
    h_is_real, h6, h14, BitVec.ofNatLT_eq_ofNat] at state_cstrs
  obtain ⟨read_pc, read_op_a, read_op_b, read_mem⟩ := state_cstrs

  have h26 : ¬ (Main[26] < 32) := by sorry
  simp [h26] at read_mem

  simp [CPUState.constraints, SP1Constraint.toProp] at hcpu
  clear hcpu

  have haddr_add : (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat +
      (Word.toBitVec64 #v[Main[21], Main[22], Main[23], Main[24]]).toNat =
      (Word.toNat #v[Main[26], Main[27], Main[28], 0]) := by sorry

  simp [sp1_ld, spec_ld,
    op_a, op_b, imm_c, sp1_op_a, sp1_ob_b, sp1_imm_c,
    run_readReg_of_isInitialized s _ hs,
    execute_LOAD,
    ]

  rw [Std.ExtDHashMap.get?_eq_some_get (hs Register.PC), Option.some_inj] at read_pc
  rw [read_pc, ← hsign]

  clear read_pc hsign

  rw [run_vmem_read_of_width_8' (BitVec.ofNat 5 Main[14])
        (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]) _
        (BitVec.ofNat 8 Main[30]) (BitVec.ofNat 8 (Main[30] >>> 8))
        (BitVec.ofNat 8 Main[31]) (BitVec.ofNat 8 (Main[31] >>> 8))
        (BitVec.ofNat 8 Main[32]) (BitVec.ofNat 8 (Main[32] >>> 8))
        (BitVec.ofNat 8 Main[33]) (BitVec.ofNat 8 (Main[33] >>> 8))]
  · by_cases h6 : BitVec.ofNat 5 Main[6] = 0#5

    · simp [h6]

      sorry
    · simp [h6]

      sorry
  · aesop
  · simpa
  ·
    sorry
  · constructor <;> simpa [Std.ExtDHashMap.get_insert]
  · simp
    simpa [Std.ExtDHashMap.get_insert]
  · clear *- read_mem haddr_add
    simp [haddr_add]
    aesop

  stop
  ·
    sorry
