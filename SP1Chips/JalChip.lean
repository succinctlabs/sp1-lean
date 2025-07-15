import SP1Operations

namespace JalChip

def constraints (Main : Vector (Fin BB) 31) : SP1ConstraintList :=
  let E0 : Fin BB := Main[30] - 1
  let E1 : Fin BB := Main[30] * E0
  let CS0 : SP1ConstraintList := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[Main[14], Main[15], Main[16], Main[17]] { value := #v[Main[22], Main[23], Main[24], Main[25]] } Main[30]
  let E2 : Fin BB := Main[1] * 65536
  let E3 : Fin BB := Main[2] + E2
  let E4 : Fin BB := Main[30] - 1
  let E5 : Fin BB := Main[30] * E4
  let E6 : Fin BB := E3 + 8
  let E7 : Fin BB := Main[2] - 1
  let E8 : Fin BB := E7 * 1761607681
  let E9 : Fin BB := Main[30] - Main[13]
  let CS1 : SP1ConstraintList := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0] { value := #v[Main[26], Main[27], Main[28], Main[29]] } E9
  let E10 : Fin BB := Main[13] * Main[26]
  let E11 : Fin BB := Main[13] * Main[27]
  let E12 : Fin BB := Main[13] * Main[28]
  let E13 : Fin BB := Main[1] * 65536
  let E14 : Fin BB := Main[2] + E13
  let E15 : Fin BB := Main[30] - 1
  let E16 : Fin BB := Main[30] * E15
  let E17 : Fin BB := Main[26] - 0
  let E18 : Fin BB := Main[13] * E17
  let E19 : Fin BB := Main[27] - 0
  let E20 : Fin BB := Main[13] * E19
  let E21 : Fin BB := Main[28] - 0
  let E22 : Fin BB := Main[13] * E21
  let E23 : Fin BB := Main[29] - 0
  let E24 : Fin BB := Main[13] * E23
  let E25 : Fin BB := E14 + 3
  let E26 : Fin BB := Main[30] - 1
  let E27 : Fin BB := Main[30] * E26
  let E28 : Fin BB := E25 - Main[11]
  let E29 : Fin BB := E28 - 1
  let E30 : Fin BB := E29 - Main[12]
  let E31 : Fin BB := E30 * 2013235201
  [
    (.assertZero E1),
    (.assertZero Main[25]),
    (.assertZero E5),
    (.receive (.state Main[0] E3 Main[3] Main[4] Main[5]) Main[30]),
    (.send (.state Main[0] E6 Main[22] Main[23] Main[24]) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 7) E8 13 0) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[1] 0) Main[30]),
    (.assertZero Main[29]),
    (.assertZero E10),
    (.assertZero E11),
    (.assertZero E12),
    (.assertZero E16),
    (.assertZero E18),
    (.assertZero E20),
    (.assertZero E22),
    (.assertZero E24),
    (.assertZero E27),
    (.send (.byte (ByteOpcode.ofNat 7) Main[12] 16 0) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E31 0) Main[30]),
    (.send (.memory Main[0] Main[11] Main[6] 0 0 Main[7] Main[8] Main[9] Main[10]) Main[30]),
    (.receive (.memory Main[0] E25 Main[6] 0 0 Main[26] Main[27] Main[28] Main[29]) Main[30]),
  ] ++ CS0 ++ CS1

open LeanRV64IM.Functions

lemma eq_zero_of_constraints (Main : Vector (Fin BB) 31)
    (h_cstrs : (constraints Main).allHold) : Main[25] = 0 := by
  simp [constraints] at h_cstrs
  aesop

lemma link_eq_of_constraints (Main : Vector (Fin BB) 31)
    (h_cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) :
    BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48) =
      BitVec.ofNat 64 (Main[3] + Main[4] * 2^16 + Main[5] * 2^32) + 4 := by
  simp [constraints] at h_cstrs
  have : (AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0]
      { value := #v[Main[26], Main[27], Main[28], Main[29]] } (Main[30] - Main[13])).allHold := by
    sorry

  sorry

lemma add_imm_eq_of_constarints (Main : Vector (Fin BB) 31)
    (h_cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) :
    BitVec.ofNat 64 (Main[22] + Main[23] * 65536 + Main[24] * 4294967296) =
        BitVec.ofNat 64 (Main[3] + Main[4] * 65536 + ↑Main[5] * 4294967296) +
          BitVec.ofNat 64 (Main[14] + Main[15] * 65536 + Main[16] * 4294967296 + Main[17] * 281474976710656) := by
  simp [constraints] at h_cstrs
  have : (AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[Main[14], Main[15], Main[16], Main[17]]
      { value := #v[Main[22], Main[23], Main[24], Main[25]] } Main[30]).allHold := by
    sorry
  sorry

lemma ofInt_ofNat_of_constraints (Main : Vector (Fin BB) 31)
    (h_cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) :
    let imm_nat : ℕ := Main[14] + Main[15] * 65536 + Main[16] * 4294967296 + Main[17] * 281474976710656
    BitVec.ofInt 64 (BitVec.ofNat 21 (imm_nat)).toInt = (BitVec.ofNat 64 (imm_nat)) := by
  sorry

def specJal (imm : BitVec 21) (rd : regidx) : SailM Unit := do
  set_next_pc (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
  let _ ← execute_JAL imm rd

def sp1Jal (Main : Vector (Fin BB) 31) : SailM Unit := do
  let rd := regidx.Regidx Main[6].val
  let init_pc := BitVec.ofNat 64 (Main[3] + Main[4] * 2^16 + Main[5] * 2^32)
  let imm := BitVec.ofNat 64 (Main[14] + Main[15] * 2^16 + Main[16] * 2^32 + Main[17] * 2^48)
  let new_pc := BitVec.ofNat 64 (Main[22] + Main[23] * 2^16 + Main[24] * 2^32 + Main[25] * 2^48)
  let link := BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48)
  wX_bits rd link
  set_next_pc new_pc

theorem SP1JAL_correct (Main : Vector (Fin BB) 31)
    (h_cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) -- Is a real column
    -- dt: this is a hack until `Sail.BitVec.access` plays nicely
    (h_access : ∀ virtaddr, Sail.BitVec.access (bits_of_virtaddr virtaddr) 1 = 0#1)
    (h_ext_zca : currentlyEnabled extension.Ext_Zca = return false)
    -- dt: this is sort of cheating, could actually write this in the spec instead.
    (h_pc : Sail.readReg Register.PC =
      return BitVec.ofNat 64 (Main[3] + Main[4] * 2^16 + Main[5] * 2^32)) :
    let imm := BitVec.ofNat 64 (Main[14] + Main[15] * 2^16 + Main[16] * 2^32 + Main[17] * 2^48)
    sp1Jal Main = specJal imm (regidx.Regidx Main[6].val) := by

  let init_pc := BitVec.ofNat 64 (Main[3] + Main[4] * 2^16 + Main[5] * 2^32)
  let imm := BitVec.ofNat 64 (Main[14] + Main[15] * 2^16 + Main[16] * 2^32 + Main[17] * 2^48)
  let new_pc := BitVec.ofNat 64 (Main[22] + Main[23] * 2^16 + Main[24] * 2^32 + Main[25] * 2^48)
  let link := BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48)

  unfold sp1Jal specJal

  simp [map_eq_bind_pure_comp, execute_JAL, h_is_real]

  have h25 : Main[25] = 0 := by
    refine eq_zero_of_constraints Main h_cstrs

  have h_link : BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48) =
      BitVec.ofNat 64 (Main[3] + Main[4] * 2^16 + Main[5] * 2^32) + 4 := by
    refine link_eq_of_constraints Main h_cstrs h_is_real

  have h_imm :
      BitVec.ofNat 64 (Main[22] + Main[23] * 65536 + Main[24] * 4294967296) =
        BitVec.ofNat 64 (Main[3] + Main[4] * 65536 + ↑Main[5] * 4294967296) +
          BitVec.ofNat 64 (Main[14] + Main[15] * 65536 + Main[16] * 4294967296 + Main[17] * 281474976710656) := by
    refine add_imm_eq_of_constarints Main h_cstrs h_is_real

  have h_of_int : let imm_nat : ℕ := Main[14] + Main[15] * 65536 + Main[16] * 4294967296 + Main[17] * 281474976710656
      BitVec.ofInt 64 (BitVec.ofNat 21 (imm_nat)).toInt = (BitVec.ofNat 64 (imm_nat)) :=
    ofInt_ofNat_of_constraints Main h_cstrs h_is_real

  erw [h_link]
  simp_rw [h_access]

  simp [h25, h_ext_zca, h_link, h_pc,
    LeanRV64IM.Functions.not, get_next_pc, bit_to_bool, bool_bit_backwards,
    bits_of_virtaddr, ext_control_check_pc, set_next_pc,
    sign_extend, Sail.BitVec.signExtend, BitVec.signExtend]

  refine bind_congr fun () => congr_arg set_next_pc ?_

  rw [h_of_int, h_imm]

end JalChip
