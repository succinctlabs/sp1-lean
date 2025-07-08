import SP1Operations

open BitVec

namespace AddChip

section constraints

def constraints (Main : Vector (Fin BB) 23) : SP1ConstraintList :=
  let E0 : Fin BB := Main[22] - 1
  let E1 : Fin BB := Main[22] * E0
  let CS0 : List SP1Constraint := AddOperation.constraints #v[Main[11], Main[12]] #v[Main[16], Main[17]] { value := #v[Main[20], Main[21]] } Main[22]
  let E2 : Fin BB := Main[3] + 4
  let CS1 : List SP1Constraint := CPUState.constraints { clk_0_16 := Main[2], clk_16_24 := Main[1], clk_high := Main[0], pc := Main[3] } E2 8 Main[22]
  let E3 : Fin BB := Main[1] * 65536
  let E4 : Fin BB := Main[2] + E3
  let CS2 : List SP1Constraint := RTypeReader.constraints Main[0] E4 Main[3] 0 #v[Main[20], Main[21]] { op_a := Main[4], op_a_0 := Main[9], op_a_memory := { access_timestamp := { diff_low_limb := Main[8], prev_low := Main[7] }, prev_value := #v[Main[5], Main[6]] }, op_b := Main[10], op_b_memory := { access_timestamp := { diff_low_limb := Main[14], prev_low := Main[13] }, prev_value := #v[Main[11], Main[12]] }, op_c := Main[15], op_c_memory := { access_timestamp := { diff_low_limb := Main[19], prev_low := Main[18] }, prev_value := #v[Main[16], Main[17]] } } Main[22]
  [
    .assertZero E1
  ] ++ CS0 ++ CS1 ++ CS2

lemma allHold_constraints_iff (Main : Vector (Fin BB) 23) :
    (constraints Main).allHold ↔
      (Main[22] = 0 ∨ Main[22] - 1 = 0) ∧
      (AddOperation.constraints
        #v[Main[11], Main[12]] #v[Main[16], Main[17]]
        { value := #v[Main[20], Main[21]] }
        Main[22]).allHold ∧
      (CPUState.constraints
        { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2], pc := Main[3] }
        (Main[3] + 4) 8 Main[22]).allHold ∧
      (RTypeReader.constraints
        Main[0] (Main[2] + Main[1] * 65536) Main[3] 0 #v[Main[20], Main[21]]
        { op_a := Main[4],
          op_a_memory :=
            { prev_value := #v[Main[5], Main[6]],
              access_timestamp := { prev_low := Main[7], diff_low_limb := Main[8] } },
          op_a_0 := Main[9], op_b := Main[10],
          op_b_memory :=
            { prev_value := #v[Main[11], Main[12]],
              access_timestamp := { prev_low := Main[13], diff_low_limb := Main[14] } },
          op_c := Main[15],
          op_c_memory :=
            { prev_value := #v[Main[16], Main[17]],
              access_timestamp := { prev_low := Main[18], diff_low_limb := Main[19] } } }
        Main[22]).allHold := by
  simp [constraints]

lemma bound_of_constraints (Main : Vector (Fin BB) 23)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[22] = 1) : Main[20].val + Main[21].val * 65536 < 2^32 := by
  rw [allHold_constraints_iff] at cstrs
  let ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
  simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat,
    Nat.ble, Nat.beq, ByteOpcode.constrain] at add_cstrs
  have h_low  : Main[20].val < 65536 := add_cstrs.right.right.left
  have h_high : Main[21].val < 65536 := add_cstrs.right.right.right
  omega

def state_constraints
  (Main : Vector (Fin BB) 23)
  (state : SP1State)
  (cstrs : (constraints Main).initialState state)
  (h_is_real : Main[22] = 1)
  : state.regs (regidx.Regidx Main[10].val) = .ofNat 32 (Main[11] + Main[12] * 65536)
    ∧ state.regs (regidx.Regidx Main[15].val) = .ofNat 32 (Main[16] + Main[17] * 65536)
    ∧ state.pc = Main[3].val :=
  by
    simp [constraints, List.Forall, AddOperation.constraints, RTypeReader.constraints, CPUState.constraints, SP1Constraint.toStateProp, h_is_real] at cstrs
    tauto

end constraints

/--
This is just the `ADD` branch of `execute_RTYPE` in LeanRV32D, except that all
monadic acionts are happening in our `StateM` instead of `SailM`.

We should be able to either:
- Modify the Sail compiler so that `SailM` uses functions instead of
  `Std.ExtDHashMaps` underneath.
- OR prove the equivalence between our `StateM` and `SailM`.
-/
def specAdd (rs2 rs1 rd : regidx) : StateM SP1State Unit := do
  incrementPC -- this is from run_hart_active
  update_reg rd ((← get).regs rs1 + (← get).regs rs2)

-- TODO(gzgz): this should be auto-generate-able from our constraints.
def sp1Add (Main : Vector (Fin BB) 23) : StateM SP1State Unit := do
  setPC (Main[3].val + 4) -- dt: This should actually be coming from `CPUState.constraints` send
  let op_a := regidx.Regidx Main[4].val
  update_reg op_a (BitVec.ofNat 32 (↑Main[20] + ↑Main[21] * 65536))

/-- If the constraints all hold, the column is real, and `op_b` and `op_c` are loaded
into the proper registers, then the add chip conforms to the spec. -/
theorem SP1AddChip_Correct (Main : Vector (Fin BB) 23)
    (h_cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_is_real : Main[22] = 1)
    (pc : BitVec 32)
    (reg_state : regidx → BitVec 32)
    (h_state_cstrs : SP1ConstraintList.initialState (constraints Main) { pc := pc, regs := reg_state })
    /- (hmem₁ : reg_state (regidx.Regidx Main[10].val) = .ofNat 32 (Main[11] + Main[12] * 65536)) -/
    /- (hmem₂ : reg_state (regidx.Regidx Main[15].val) = .ofNat 32 (Main[16] + Main[17] * 65536)) -/
    : (sp1Add Main).run { pc := pc, regs := reg_state } = (specAdd (.Regidx Main[15].val) (.Regidx Main[10].val) (.Regidx Main[4].val)).run { pc := pc, regs := reg_state } := by
  unfold sp1Add specAdd
  obtain ⟨hmem₁, ⟨hmem₂, hpc⟩⟩ := state_constraints Main { pc := pc, regs := reg_state } h_state_cstrs h_is_real
  rw [BitVec.natCast_eq_ofNat] at hmem₁ hmem₂
  simp at hmem₁ hmem₂ hpc
  have hb3 : Main[20].val + Main[21].val * 65536 < 2 ^ 32 :=
    bound_of_constraints Main h_cstrs h_is_real

  -- Extract out the individual constraints from each part
  rw [allHold_constraints_iff, h_is_real] at h_cstrs
  obtain ⟨orig_cstrs, add_cstrs, cpu_strs, adapter_cstrs⟩ := h_cstrs

  -- The `RTypeReader` gives bounds on the size of previous memory values
  let op_b_memory_bound : Main[11].1 < 65536 ∧ Main[12].1 < 65536 :=
    RTypeReader.val_op_b_memory_lt_of_constraints adapter_cstrs
  let op_c_memory_bound : Main[16].1 < 65536 ∧ Main[17].1 < 65536 :=
    RTypeReader.val_op_c_memory_lt_of_constraints adapter_cstrs
  have hb1 : Main[11].val + Main[12].val * 65536 < 2 ^ 32 := by omega
  have hb2 : Main[16].val + Main[17].val * 65536 < 2 ^ 32 := by omega

  have h_add_op : (Main[20] + Main[21] * 65536 : ℕ)#'hb3 =
      (Main[11] + Main[12] * 65536 : ℕ)#'hb1 + (Main[16] + Main[17] * 65536)#'hb2 := by
    simpa using AddOperation.correct''
      #v[⟨Main[11], op_b_memory_bound.1⟩, ⟨Main[12], op_b_memory_bound.2⟩]
      #v[⟨Main[16], op_c_memory_bound.1⟩, ⟨Main[17], op_c_memory_bound.2⟩]
      { value := #v[Main[20], Main[21]] }
      ⟨Main[22], by aesop⟩
      (by simp_all)
      (by simp [h_is_real])
      hb3

  simp only [BB, BitVec.natCast_eq_ofNat, StateT.run_modify, StateT.run_bind,
    StateT.run_get, bind_pure_comp, map_pure, id_eq]
  simp only [hpc]
  -- Goal is now about equality of pure values
  refine congr_arg (fun st => pure ((), st)) ?_
  -- Now we need to prove the SP1State structures are equal
  simp only [SP1State.mk.injEq]
  constructor
  · -- pc fields are equal
    simp [BitVec.ofNat]
  · -- regs fields are equal
    funext reg
    by_cases hreg : (regidx.Regidx (BitVec.ofNat 5 ↑Main[4])) = reg
    · -- Case: we're looking at the register being updated
      rw [← hreg, Function.update_self, Function.update_self]
      -- Now prove the values being stored are equal
      rw [hmem₁, hmem₂]
      rw [← BitVec.ofNatLT_eq_ofNat hb3, ← BitVec.ofNatLT_eq_ofNat hb1,
          ← BitVec.ofNatLT_eq_ofNat hb2, h_add_op]
    · -- Case: we're looking at a different register
      rw [Function.update_of_ne (Ne.symm hreg), Function.update_of_ne (Ne.symm hreg)]

-- #print axioms SP1AddChip_Correct
