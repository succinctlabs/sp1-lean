import SP1Operations

open BitVec

namespace AddChip

section constraints

def constraints (Main : Vector (Fin BB) 33) : SP1ConstraintList :=
  let E0 : Fin BB := Main[32] - 1
  let E1 : Fin BB := Main[32] * E0
  let CS0 : SP1ConstraintList := AddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[22], Main[23], Main[24], Main[25]] { value := #v[Main[28], Main[29], Main[30], Main[31]] } Main[32]
  let E2 : Fin BB := Main[3] + 4
  let CS1 : SP1ConstraintList := CPUState.constraints { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] } #v[E2, Main[4], Main[5]] 8 Main[32]
  let E3 : Fin BB := Main[1] * 65536
  let E4 : Fin BB := Main[2] + E3
  let CS2 : SP1ConstraintList := RTypeReader.constraints Main[0] E4 #v[Main[3], Main[4], Main[5]] 0 #v[Main[28], Main[29], Main[30], Main[31]] { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13], op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } }, op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } } } Main[32]
  [
    (.assertZero E1),
  ] ++ CS0 ++ CS1 ++ CS2

lemma allHold_constraints_iff (Main : Vector (Fin BB) 33) :
    (constraints Main).allHold ↔
      (Main[32] = 0 ∨ Main[32] = 1) ∧
      (AddOperation.constraints #v[Main[15], Main[16], Main[17], Main[18]] #v[Main[22], Main[23], Main[24], Main[25]]
        { value := #v[Main[28], Main[29], Main[30], Main[31]] } Main[32]).allHold ∧
      (CPUState.constraints
        { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := #v[Main[3], Main[4], Main[5]] }
          #v[Main[3] + 4, Main[4], Main[5]] 8 Main[32]).allHold ∧
      (RTypeReader.constraints Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] 0 #v[Main[28], Main[29], Main[30], Main[31]]
        { op_a := Main[6], op_a_memory := { prev_value := #v[Main[7], Main[8], Main[9], Main[10]], access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } }, op_a_0 := Main[13],
          op_b := Main[14], op_b_memory := { prev_value := #v[Main[15], Main[16], Main[17], Main[18]], access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
          op_c := Main[21], op_c_memory := { prev_value := #v[Main[22], Main[23], Main[24], Main[25]], access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } } } Main[32]).allHold := by
  simp [constraints, sub_eq_zero]

lemma bound_of_constraints (Main : Vector (Fin BB) 33)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[32] = 1) :
    Main[28].val + Main[29] * 2^16 + Main[30] * 2^32 + Main[31] * 2^48 < 2^64 := by
  rw [allHold_constraints_iff] at cstrs
  let ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
  simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat,
    Nat.ble, Nat.beq, ByteOpcode.constrain] at add_cstrs
  have h1 : Main[28].val < 65536 := by tauto
  have h1 : Main[29].val < 65536 := by tauto
  have h1 : Main[30].val < 65536 := by tauto
  have h1 : Main[31].val < 65536 := by tauto
  omega

end constraints

/--
This is just the `ADD` branch of `execute_RTYPE` in LeanRV32D, except that all
monadic acionts are happening in our `StateM` instead of `SailM`.

We should be able to either:
- Modify the Sail compiler so that `SailM` is more workable
- OR prove the equivalence between our `StateM` and `SailM`.
-/
def specAdd (rs2 rs1 rd : regidx) : StateM SP1State Unit := do
  incrementPC -- this is from run_hart_active
  update_reg rd ((← get).2 rs1 + (← get).2 rs2)

-- TODO(gzgz): this should be auto-generate-able from our constraints.
def sp1Add (Main : Vector (Fin BB) 33) : StateM SP1State Unit := do
  setPC (Main[3].val + 4) -- dt: This should actually be coming from `CPUState.constraints` send
  let op_a := regidx.Regidx Main[4].val
  let v := Main[28].val + Main[29] * 2^16 + Main[30] * 2^32 + Main[31] * 2^48
  update_reg op_a (BitVec.ofNat 64 v)

/-- If the constraints all hold, the column is real, and `op_b` and `op_c` are loaded
into the proper registers, then the add chip conforms to the spec. -/
theorem SP1AddChip_Correct (Main : Vector (Fin BB) 33)
    (h_cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_is_real : Main[32] = 1)
    (pc : BitVec 64) (hpc : pc = Main[3].val)
    (reg_state : regidx → BitVec 64)
    (hmem₁ : reg_state (regidx.Regidx Main[10].val) = .ofNat 64 (Main[15].val + Main[16] * 2^16 + Main[17] * 2^32 + Main[18] * 2^48))
    (hmem₂ : reg_state (regidx.Regidx Main[15].val) = .ofNat 64 (Main[22].val + Main[23] * 2^16 + Main[24] * 2^32 + Main[25] * 2^48)) :
    (sp1Add Main).run (pc, reg_state) = (specAdd (.Regidx Main[15].val) (.Regidx Main[10].val) (.Regidx Main[4].val)).run (pc, reg_state) := by
  unfold sp1Add specAdd
  rw [BitVec.natCast_eq_ofNat] at hmem₁ hmem₂
  have hb3 : Main[28].val + Main[29] * 2^16 + Main[30] * 2^32 + Main[31] * 2^48 < 2^64 :=
    bound_of_constraints Main h_cstrs h_is_real

  -- Extract out the individual constraints from each part
  rw [allHold_constraints_iff, h_is_real] at h_cstrs
  obtain ⟨orig_cstrs, add_cstrs, cpu_strs, adapter_cstrs⟩ := h_cstrs

  -- The `RTypeReader` gives bounds on the size of previous memory values
  let op_b_memory_bound : Main[15].val < 2^16 ∧ Main[16] < 2^16 ∧ Main[17] < 2^16 ∧ Main[18] < 2^16 :=
    sorry --RTypeReader.val_op_b_memory_lt_of_constraints adapter_cstrs
  let op_c_memory_bound : Main[22].val < 2^16 ∧ Main[23] < 2^16 ∧ Main[24] < 2^16 ∧ Main[25] < 2^16 :=
    sorry --RTypeReader.val_op_c_memory_lt_of_constraints adapter_cstrs

  simp only [BB, BitVec.natCast_eq_ofNat, StateT.run_modify, StateT.run_bind,
    StateT.run_get, bind_pure_comp, map_pure, Prod.map_apply, id_eq, hpc]

  refine congr_arg (fun out => pure (_, (_, out))) (funext fun reg => ?_)
  by_cases hreg : (regidx.Regidx (BitVec.ofNat 5 ↑Main[4])) = reg
  · rw [hreg, Function.update_self, Function.update_self, hmem₁, hmem₂]
    refine AddOperation.correct
      #v[Main[15], Main[16], Main[17], Main[18]]
      #v[Main[22], Main[23], Main[24], Main[25]]
      { value := #v[Main[28], Main[29], Main[30], Main[31]] }
      1 rfl add_cstrs ?_ ?_
    · refine Word.isU64_of_cases _ ?_ ?_ ?_ ?_ <;> tauto
    · refine Word.isU64_of_cases _ ?_ ?_ ?_ ?_ <;> tauto

  · rw [Function.update_of_ne (Ne.symm hreg), Function.update_of_ne (Ne.symm hreg)]

-- -- #print axioms SP1AddChip_Correct
