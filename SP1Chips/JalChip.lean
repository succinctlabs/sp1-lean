import SP1Operations.Operation.AddOperation

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
  let E9 : Fin BB := Main[30] - 1
  let E10 : Fin BB := E9 * Main[13]
  let E11 : Fin BB := Main[30] - Main[13]
  let CS1 : SP1ConstraintList := AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0] { value := #v[Main[26], Main[27], Main[28], Main[29]] } E11
  let E12 : Fin BB := Main[13] * Main[26]
  let E13 : Fin BB := Main[13] * Main[27]
  let E14 : Fin BB := Main[13] * Main[28]
  let E15 : Fin BB := Main[1] * 65536
  let E16 : Fin BB := Main[2] + E15
  let E17 : Fin BB := Main[30] - 1
  let E18 : Fin BB := Main[30] * E17
  let E19 : Fin BB := Main[26] - 0
  let E20 : Fin BB := Main[13] * E19
  let E21 : Fin BB := Main[27] - 0
  let E22 : Fin BB := Main[13] * E21
  let E23 : Fin BB := Main[28] - 0
  let E24 : Fin BB := Main[13] * E23
  let E25 : Fin BB := Main[29] - 0
  let E26 : Fin BB := Main[13] * E25
  let E27 : Fin BB := E16 + 3
  let E28 : Fin BB := Main[30] - 1
  let E29 : Fin BB := Main[30] * E28
  let E30 : Fin BB := E27 - Main[11]
  let E31 : Fin BB := E30 - 1
  let E32 : Fin BB := E31 - Main[12]
  let E33 : Fin BB := E32 * 2013235201
  [
    (.assertZero E1),
    (.assertZero Main[25]),
    (.assertZero E5),
    (.receive (.state Main[0] E3 Main[3] Main[4] Main[5]) Main[30]),
    (.send (.state Main[0] E6 Main[22] Main[23] Main[24]) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 6) E8 13 0) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 Main[1] 0) Main[30]),
    (.assertZero E10),
    (.assertZero Main[29]),
    (.assertZero E12),
    (.assertZero E13),
    (.assertZero E14),
    (.assertZero E18),
    (.send (.program Main[3] Main[4] Main[5] (Opcode.ofNat 33) Main[6] Main[14] Main[15] Main[16] Main[17] Main[18] Main[19] Main[20] Main[21] Main[13] 1 1 111 0 0) Main[30]),
    (.assertZero E20),
    (.assertZero E22),
    (.assertZero E24),
    (.assertZero E26),
    (.assertZero E29),
    (.send (.byte (ByteOpcode.ofNat 6) Main[12] 16 0) Main[30]),
    (.send (.byte (ByteOpcode.ofNat 3) 0 E33 0) Main[30]),
    (.send (.memory Main[0] Main[11] Main[6] 0 0 Main[7] Main[8] Main[9] Main[10]) Main[30]),
    (.receive (.memory Main[0] E27 Main[6] 0 0 Main[26] Main[27] Main[28] Main[29]) Main[30]),
  ] ++ CS0 ++ CS1

open LeanRV64IM.Functions

lemma eq_zero_of_constraints (Main : Vector (Fin BB) 31)
    (h_cstrs : (constraints Main).allHold) : Main[25] = 0 := by
  simp [constraints] at h_cstrs
  aesop

lemma isU64_of_constraints (Main : Vector (Fin BB) 31)
    (h_cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) :
    Word.isU64 #v[Main[3], Main[4], Main[5], 0] := by
  simp [constraints, h_is_real, SP1Constraint.toProp] at h_cstrs
  refine Word.isU64_of_cases ?_ ?_ ?_ ?_ ?_
  · aesop
  · aesop
  · aesop
  · aesop

lemma isU64_of_constraints' (Main : Vector (Fin BB) 31)
    (h_cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) :
    Word.isU64 #v[Main[14], Main[15], Main[16], Main[17]] := by
  simp [constraints, h_is_real, SP1Constraint.toProp] at h_cstrs
  refine Word.isU64_of_cases ?_ ?_ ?_ ?_ ?_
  · aesop
  · aesop
  · aesop
  · aesop

lemma program_constraints_allHold (Main : Vector (Fin BB) 31)
    (h_cstrs : (constraints Main).allHold) :
    SP1Constraint.toProp (.send (.program Main[3] Main[4] Main[5] (Opcode.ofNat 33)
      Main[6] Main[14] Main[15] Main[16] Main[17] Main[18] Main[19]
      Main[20] Main[21] Main[13] 1 1 111 0 0) Main[30]) := by
  simp [constraints] at h_cstrs
  aesop

lemma link_eq_of_constraints (Main : Vector (Fin BB) 31)
    (h_cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) (h_op_a : Main[13] = 0) :
    BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48) =
      BitVec.ofNat 64 (Main[3] + Main[4] * 2^16 + Main[5] * 2^32) + 4 := by
  have h345 := isU64_of_constraints Main h_cstrs h_is_real
  simp [constraints] at h_cstrs
  have : (AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[4, 0, 0, 0]
      { value := #v[Main[26], Main[27], Main[28], Main[29]] } (Main[30] - Main[13])).allHold := by
    aesop
  have := AddOperation.correct _ _ _ _ ?_ this h345 ?_
  simp [Word.toBitVec64] at this
  have := this.2
  refine this.trans ?_
  simp [Word.toNat]
  · simp [h_op_a, h_is_real]
  · apply Word.isU64_of_cases <;> simp

lemma add_imm_eq_of_constarints (Main : Vector (Fin BB) 31)
    (h_cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) :
    BitVec.ofNat 64 (Main[22] + Main[23] * 65536 + Main[24] * 4294967296) =
        BitVec.ofNat 64 (Main[3] + Main[4] * 65536 + ↑Main[5] * 4294967296) +
          BitVec.ofNat 64 (Main[14] + Main[15] * 65536 + Main[16] * 4294967296 + Main[17] * 281474976710656) := by
  have h345 := isU64_of_constraints Main h_cstrs h_is_real
  have h1415 := isU64_of_constraints' Main h_cstrs h_is_real
  simp [constraints] at h_cstrs
  have : (AddOperation.constraints #v[Main[3], Main[4], Main[5], 0] #v[Main[14], Main[15], Main[16], Main[17]]
      { value := #v[Main[22], Main[23], Main[24], Main[25]] } Main[30]).allHold := by
    aesop
  have := AddOperation.correct _ _ _ _ h_is_real this h345 h1415
  simp [Word.toBitVec64] at this
  have := this.2
  have h25 : Main[25] = 0 := h_cstrs.2.1
  simp [Word.toNat, h25] at this
  exact this

/-- dt: should extract this out and clean up more -/
lemma ofInt_ofNat_of_constraints (Main : Vector (Fin BB) 31)
    (h_cstrs : (constraints Main).allHold)
    (h_is_real : Main[30] = 1) :
    let imm_nat : ℕ := Main[14] + Main[15] * 65536 + Main[16] * 4294967296 + Main[17] * 281474976710656
    BitVec.ofInt 64 (BitVec.ofNat 21 (imm_nat)).toInt = (BitVec.ofNat 64 (imm_nat)) := by
  have := program_constraints_allHold Main h_cstrs
  simp [SP1Constraint.toProp, h_is_real, Opcode.ofNat, Nat.ble] at this

--------------------------

def specJal (imm : BitVec 21) (rd : regidx) : SailM Unit := do
  set_next_pc (Sail.BitVec.addInt (← Sail.readReg Register.PC) 4)
  let _ ← execute_JAL imm rd

def sp1Jal (Main : Vector (Fin BB) 31) : SailM Unit := do
  let rd := regidx.Regidx Main[6].val
  let new_pc := BitVec.ofNat 64 (Main[22] + Main[23] * 2^16 + Main[24] * 2^32 + Main[25] * 2^48)
  let link := BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48)
  wX_bits rd link
  set_next_pc new_pc

lemma execute_JAL_eq_of (imm : BitVec 21) (rd : regidx)
    (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (pc : RegisterType Register.PC) (h : (pc + sign_extend imm) % 4 = 0)
    (hs : s.regs.get? Register.PC = pc) :
    (execute_JAL imm rd).run s = (do
      let target ← pure ((← Sail.readReg Register.PC) + (sign_extend (m := 64) imm))
      wX_bits rd (← (get_next_pc ()))
      (set_next_pc target)
      (pure RETIRE_SUCCESS)).run s := by
  rw [execute_JAL]
  simp [ext_control_check_pc, bit_to_bool]
  simp [Sail.BitVec.access, bits_of_virtaddr]
  simp [bool_bit_backwards, BitVec.ofBool]
  sorry
  -- rw [readReg_bind_bind_duplicate]
  -- have := run_readReg_bind_of_forall
  --   (reg := Register.PC)
  --   (f := fun v => (v + sign_extend imm)[1])
  --   (y := false)
  --   (mx := fun b : Bool => do
  --     let v' ← Sail.readReg Register.PC
  --     let x ←
  --       (match bif b then 1#1 else 0#1 with
  --         | 1#1 => pure true
  --         | 0#1 => pure false
  --         | x => do
  --           Sail.assert false "Pattern match failure at unknown location"
  --           throw Sail.Error.Exit)
  --     let __do_lift ← currentlyEnabled extension.Ext_Zca
  --     bif x && LeanRV64IM.Functions.not __do_lift then
  --         pure
  --           (ExecutionResult.Memory_Exception
  --             (virtaddr.Virtaddr (v' + sign_extend imm), ExceptionType.E_Fetch_Addr_Align ()))
  --       else do
  --         let __do_lift ← get_next_pc ()
  --         wX_bits rd __do_lift
  --         (fun a ↦ RETIRE_SUCCESS) <$> set_next_pc (v' + sign_extend imm))
  -- erw [this]
  -- · simp
  --   simp [currentlyEnabled]
  --   refine congr_arg (EStateM.run · s) ?_
  --   refine bind_congr fun v => ?_
  --   exact readReg_bind_const Register.misa (do
  --     let __do_lift ← get_next_pc ()
  --     wX_bits rd __do_lift
  --     (fun a ↦ RETIRE_SUCCESS) <$> set_next_pc (v + sign_extend imm))
  -- · intro v
  --   simp [hs]
  --   rintro rfl
  --   have := BitVec.mul4_means_0_1_are_0 h
  --   exact this.2

lemma specJal_eq_of_mod (imm : BitVec 21) (rd : regidx)
    (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
    (pc : RegisterType Register.PC)
    (h : (pc + sign_extend imm) % 4 = 0)
    (hs : s.regs.get? Register.PC = pc) :

    (specJal imm rd).run s = (do
      set_next_pc (Sail.BitVec.addInt pc 4)
      let target ← pure (pc + (sign_extend (m := 64) imm))
      wX_bits rd (← (get_next_pc ()))
      (set_next_pc target)).run s := by
  rw [specJal]
  simp [EStateM.run_bind]
  stop
  have : Sail.readReg Register.PC s = EStateM.Result.ok pc s := sorry
  simp [this]
  cases set_next_pc (Sail.BitVec.addInt pc 4) s
  ·
    simp
    simp [EStateM.Result.map]
    rw [execute_JAL_eq_of imm rd _ pc h]

    · simp [EStateM.run_bind]

      sorry
    ·
      sorry
  simp

-- set_option debug.skipKernelTC true in
-- set_option maxHeartbeats 300000 in
-- theorem SP1JAL_correct (Main : Vector (Fin BB) 31)
--     (h_cstrs : (constraints Main).allHold)
--     (h_is_real : Main[30] = 1) -- Is a real column
--     (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
--     -- dt: get this from constraints
--     (h_pc : s.regs.get? Register.PC =
--       some (BitVec.ofNat 64 (Main[3] + Main[4] * 2^16 + Main[5] * 2^32)))
--     (h_misa : s.regs.get? Register.misa = some 2)
--     :
--     let imm := BitVec.ofNat 64 (Main[14] + Main[15] * 2^16 + Main[16] * 2^32 + Main[17] * 2^48)
--     (sp1Jal Main).run s = (specJal imm (regidx.Regidx Main[6].val)).run s := by

--   let init_pc := BitVec.ofNat 64 (Main[3] + Main[4] * 2^16 + Main[5] * 2^32)
--   let imm := BitVec.ofNat 64 (Main[14] + Main[15] * 2^16 + Main[16] * 2^32 + Main[17] * 2^48)
--   let new_pc := BitVec.ofNat 64 (Main[22] + Main[23] * 2^16 + Main[24] * 2^32 + Main[25] * 2^48)
--   let link := BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48)

--   unfold sp1Jal


--   -- refine _root_.trans ?_ (specJal_eq_of_mod _ _ _ init_pc (by
--   --   simp

--   --   sorry
--   -- ) (h_pc)).symm
--   -- refine congr_arg (fun mx => EStateM.run mx s) ?_
--   unfold specJal
--   unfold execute_JAL

--   simp only [BB_eq, BitVec.natCast_eq_ofNat, Nat.reducePow, Nat.reduceLeDiff,
--     BitVec.setWidth_ofNat_of_le, pure_bind]

--   rw [run_readReg_bind, h_pc]
--   simp
--   stop
--   rw [run_readReg_bind]
--   simp

--   rw [Std.ExtDHashMap.get?_insert]
--   simp [h_pc]

--   simp [ext_control_check_pc]

--   simp [bit_to_bool, bool_bit_backwards, Sail.BitVec.access, bits_of_virtaddr]

--   have : (BitVec.ofNat 64 (↑Main[3] + ↑Main[4] * 65536 + ↑Main[5] * 4294967296) +
--             sign_extend (BitVec.ofNat 21 (↑Main[14] + ↑Main[15] * 65536 + ↑Main[16] * 4294967296 + ↑Main[17] * 281474976710656)))[1] = false := sorry

--   simp [this, currentlyEnabled]
--   rw [run_readReg_bind]
--   simp

--   -- have := ext_control_check_pc
--   --         (BitVec.ofNat 64 (↑Main[3] + ↑Main[4] * 65536 + ↑Main[5] * 4294967296) +
--   --           sign_extend
--   --             (BitVec.ofNat 21
--   --               (↑Main[14] + ↑Main[15] * 65536 + ↑Main[16] * 4294967296 + ↑Main[17] * 281474976710656)))

--   simp [Std.ExtDHashMap.get?_insert, h_misa]
--   simp [get_next_pc]
--   rw [run_readReg_bind]

--   simp [LeanRV64IM.Functions.not, hartSupports]

--   simp [← SailState.wX_bits_is_regidx_write,
--     SailState.regidx_write]

--   by_cases h6 : Main[6] = 0
--   · simp [h6]

--     sorry

--   have h6' : BitVec.ofNat 5 Main[6] = 0#5 := sorry
--   simp [h6', EStateM.run_bind]



--   have h25 : Main[25] = 0 := by
--     refine eq_zero_of_constraints Main h_cstrs

--   have h_imm :
--       BitVec.ofNat 64 (Main[22] + Main[23] * 65536 + Main[24] * 4294967296) =
--         BitVec.ofNat 64 (Main[3] + Main[4] * 65536 + ↑Main[5] * 4294967296) +
--           BitVec.ofNat 64 (Main[14] + Main[15] * 65536 + Main[16] * 4294967296 + Main[17] * 281474976710656) := by
--     refine add_imm_eq_of_constarints Main h_cstrs h_is_real

--   have h_of_int : let imm_nat : ℕ := Main[14] + Main[15] * 65536 + Main[16] * 4294967296 + Main[17] * 281474976710656
--       BitVec.ofInt 64 (BitVec.ofNat 21 (imm_nat)).toInt = (BitVec.ofNat 64 (imm_nat)) :=
--     ofInt_ofNat_of_constraints Main h_cstrs h_is_real

--   simp [h25]

--   have op_a_is_bool : Main[13] = 0 ∨ Main[13] = 1 := by
--     simp [constraints, h_is_real, SP1Constraint.toProp, Opcode.ofNat, Nat.ble] at h_cstrs
--     aesop

--   cases Or.symm op_a_is_bool with
--   | inl op_a_is_one =>
--       simp [constraints, op_a_is_one, h_is_real] at h_cstrs
--       have h26 : Main[26] = 0 := by aesop
--       have h27 : Main[27] = 0 := by aesop
--       have h28 : Main[28] = 0 := by aesop
--       have h29 : Main[29] = 0 := by aesop
--       have h6 : Main[6] = 0 := by
--         simp [SP1Constraint.toProp] at h_cstrs
--         simp_all only [BB_eq, Fin.isValue, Nat.reducePow]
--       simp_all
--       -- simp [h25, h26, h27, h28, h29, h6]
--       -- rw [h_imm]
--       -- simp only [set_next_pc, BB_eq, h_pc, Nat.reducePow, get_next_pc, sign_extend,
--       --   Sail.BitVec.signExtend, BitVec.signExtend, pure_bind, writeReg_readReg_bind,
--       --   writeReg_wX_bits_writeReg]
--       -- rw [h_of_int]
--       -- congr 3

--       -- sorry
--       -- unfold wX_bits
--       -- simp only [wX, BitVec.toNat_ofNat, Nat.reducePow, Nat.zero_mod, bne_self_eq_false, cond_false,
--       --   bind_pure_comp, map_pure, pure_bind, BB_eq]
--       -- rfl
--   | inr op_a_is_zero =>

--     have h_link : BitVec.ofNat 64 (Main[26] + Main[27] * 2^16 + Main[28] * 2^32 +  Main[29] * 2^48) =
--         BitVec.ofNat 64 (Main[3] + Main[4] * 2^16 + Main[5] * 2^32) + 4 := by
--       refine link_eq_of_constraints Main h_cstrs h_is_real op_a_is_zero

--     -- erw [h_link]
--     simp only [BB_eq, Nat.reducePow, BitVec.ofNat_eq_ofNat, set_next_pc, h25, Fin.isValue,
--       Fin.coe_ofNat_eq_mod, Nat.zero_mod, zero_mul, add_zero, h_pc, get_next_pc, sign_extend,
--       Sail.BitVec.signExtend, BitVec.signExtend, pure_bind, writeReg_readReg_bind,
--       writeReg_wX_bits_writeReg]
--     congr 1

--     simp [h_imm, h_of_int]


-- #print axioms SP1JAL_correct

end JalChip
