import SP1Operations.AddOperation
import SP1Operations.RTypeReader
import SP1Operations.CPUState
import LeanRV32D.RiscvInstsEnd

open LeanRV32D.Functions Sail

namespace AddChip

section constraints

def constraints (Main : Vector BabyBear 23) : SP1ConstraintList :=
  let E0 : BabyBear := Main[22] - 1
  let E1 : BabyBear := Main[22] * E0
  let CS0 : List SP1Constraint := AddOperation.constraints #v[Main[11], Main[12]] #v[Main[16], Main[17]] { value := #v[Main[20], Main[21]] } Main[22]
  let E2 : BabyBear := Main[3] + 4
  let CS1 : List SP1Constraint := CPUState.constraints { clk_0_16 := Main[2], clk_16_24 := Main[1], clk_high := Main[0], pc := Main[3] } E2 8 Main[22]
  let E3 : BabyBear := Main[1] * 65536
  let E4 : BabyBear := Main[2] + E3
  let CS2 : List SP1Constraint := RTypeReader.constraints Main[0] E4 Main[3] 0 #v[Main[20], Main[21]] { op_a := Main[4], op_a_0 := Main[9], op_a_memory := { access_timestamp := { diff_low_limb := Main[8], prev_low := Main[7] }, prev_value := #v[Main[5], Main[6]] }, op_b := Main[10], op_b_memory := { access_timestamp := { diff_low_limb := Main[14], prev_low := Main[13] }, prev_value := #v[Main[11], Main[12]] }, op_c := Main[15], op_c_memory := { access_timestamp := { diff_low_limb := Main[19], prev_low := Main[18] }, prev_value := #v[Main[16], Main[17]] } } Main[22]
  [
    .assertZero E1
  ] ++ CS0 ++ CS1 ++ CS2

lemma bound_of_constraints (Main : Vector BabyBear 23)
    (cstrs : (constraints Main).allHold)
    (h_is_real : Main[22] = 1) : Main[20].val + Main[21].val * 65536 < 2^32 := by
  simp [constraints] at cstrs
  let ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := cstrs
  simp [AddOperation.constraints, SP1Constraint.toProp, h_is_real, ByteOpcode.ofNat, Nat.ble, Nat.beq, ByteOpcode.constrain] at add_cstrs
  have h_low  : Main[20].val < 65536 := add_cstrs.right.right.left
  have h_high : Main[21].val < 65536 := add_cstrs.right.right.right
  linarith

lemma toSailM_constraints
    (Main : Vector BabyBear 23) :
    (constraints Main).toSailM = (do
    let _ ← wX_bits (regidx.Regidx (BitVec.ofNat 5 ↑Main[4]))
      (BitVec.ofNat 32 (↑Main[20] + ↑Main[21] * 65536))
    let _ ← wX_bits (regidx.Regidx (BitVec.ofNat 5 ↑Main[10]))
      (BitVec.ofNat 32 (↑Main[11] + ↑Main[12] * 65536))
    let _ ← wX_bits (regidx.Regidx (BitVec.ofNat 5 ↑Main[15]))
      (BitVec.ofNat 32 (↑Main[16] + ↑Main[17] * 65536))) := by
  simp [constraints, SP1ConstraintList.toSailM,
    AddOperation.constraints, CPUState.constraints, RTypeReader.constraints]

end constraints

def specAdd (Main : Vector BabyBear 23) : SailM Unit := do
  let op_a := regidx.Regidx Main[4].val
  let op_b := regidx.Regidx Main[10].val
  let op_c := regidx.Regidx Main[15].val
  let _ ← execute_RTYPE op_b op_c op_a rop.ADD

/-- dt: unclear why this now gives a deep recursion error.
The proof seems to work fine and all simps are bounded -/
theorem SP1Add_Correct (Main : Vector BabyBear 23)
    (h_cstrs : SP1ConstraintList.allHold (constraints Main))
    (h_is_real : Main[22] = 1)
    (mstate : PreSail.SequentialState RegisterType trivialChoiceSource)
    (hmem₁ : mstate.mem[Main[10]]? = some ↑(Main[11].val + Main[12].val * 65536))
    (hmem₂ : mstate.mem[Main[15]]? = some ↑(Main[16].val + Main[17].val * 65536))
    (hreg₁ : Main[4].val % 32 ≠ Main[10] ∧ Main[10].val < 32)
    (hreg₂ : Main[4].val % 32 ≠ Main[15] ∧ Main[15].val < 32) :
    let sp1Add : SailM Unit := (constraints Main).toSailM
    sp1Add.run mstate = (specAdd Main).run mstate := by
  rw [toSailM_constraints]

  let spare_cstrs := h_cstrs
  -- Extract the various constraints from the assumption
  simp only [SP1ConstraintList.allHold, constraints, BabyBearPrime, Fin.isValue, List.cons_append,
    List.nil_append, List.append_assoc, List.forall_cons, SP1Constraint.toProp_assertZero,
    mul_eq_zero, List.forall_append] at h_cstrs
  obtain ⟨orig_cstrs, ⟨add_cstrs, ⟨cpu_strs, adapter_cstrs⟩⟩⟩ := h_cstrs
  rw [h_is_real] at adapter_cstrs add_cstrs

  -- The `RTypeReader` gives bounds on the size of previous memory values
  let op_b_memory_bound : Main[11] < 65536 ∧ Main[12] < 65536 :=
    RTypeReader.op_b_memory_lt_of_constraints adapter_cstrs
  let op_c_memory_bound : Main[16] < 65536 ∧ Main[17] < 65536 :=
    RTypeReader.op_c_memory_lt_of_constraints adapter_cstrs

  -- Bounded representations of the input limbs
  let M11_U16 : U16 := ⟨Main[11], op_b_memory_bound.1⟩
  let M12_U16 : U16 := ⟨Main[12], op_b_memory_bound.2⟩
  let M16_U16 : U16 := ⟨Main[16], op_c_memory_bound.1⟩
  let M17_U16 : U16 := ⟨Main[17], op_c_memory_bound.2⟩
  let M22_U1  : U1  := ⟨Main[22], by aesop⟩
  have hb1 : Main[11].val + Main[12].val * 65536 < 2 ^ 32 := by
    have := M11_U16.in_range; have := M12_U16.in_range; linarith
  have hb2 : Main[16].val + Main[17].val * 65536 < 2 ^ 32 := by
    have := M16_U16.in_range; have := M17_U16.in_range; linarith
  have hb3 : Main[20].val + Main[21].val * 65536 < 2 ^ 32 := by
    apply bound_of_constraints Main spare_cstrs h_is_real

  have hk1 : (Main[11] + Main[12] * 65536).val = Main[11].val + Main[12].val * 65536 := sorry
  have hk2 : (Main[16] + Main[17] * 65536).val = Main[16].val + Main[17].val * 65536 := sorry

  simp only [BabyBearPrime, bind_pure_comp, id_map']
  unfold specAdd

  simp only [execute_RTYPE, Nat.reducePow, Nat.reduceMul, BabyBearPrime, BitVec.natCast_eq_ofNat,
    bind_pure_comp, bind_assoc, bind_map_left, map_bind, Functor.map_map, id_map']
  have :=
      AddOperation.correct'
        #v[⟨Main[11], op_b_memory_bound.1⟩, ⟨Main[12], op_b_memory_bound.2⟩]
        #v[⟨Main[16], op_c_memory_bound.1⟩, ⟨Main[17], op_c_memory_bound.2⟩]
        { value := #v[Main[20], Main[21]] }
        M22_U1
        (by
          simp_all only [BabyBearPrime, Fin.getElem?_fin, Fin.isValue, BitVec.natCast_eq_ofNat,
            one_ne_zero, sub_self, or_true, Nat.reducePow, SP1ConstraintList.allHold, WORD_SIZE,
            Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
            M11_U16, M12_U16, M16_U16, M17_U16, M22_U1])
        (by
          simp_all only [BabyBearPrime, Fin.getElem?_fin, Fin.isValue, BitVec.natCast_eq_ofNat,
            one_ne_zero, sub_self, or_true, Nat.reducePow, M12_U16, M17_U16, M16_U16, M22_U1,
            M11_U16]
          rfl)
        hb3
  simp only [BabyBearPrime, WORD_SIZE, Vector.getElem_mk, List.getElem_toArray,
    List.getElem_cons_zero, List.getElem_cons_succ, BIT_WIDTH, Word.toBV32_U16,
    Fin.coe_ofNat_eq_mod, Nat.reduceMod, M12_U16, M17_U16, M11_U16, M22_U1, M16_U16] at this

  rw [← BitVec.ofNatLT_eq_ofNat hb1,
    ← BitVec.ofNatLT_eq_ofNat hb2,
    ← BitVec.ofNatLT_eq_ofNat hb3,
    this]

  simp only [rX_bits, wX_bits]

  have hid₁ : (BitVec.ofNat 5 ↑Main[15]).toNat = Main[15].val := by
    simp only [BabyBearPrime, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_succ_eq_iff_lt,
      Nat.succ_eq_add_one, Nat.reduceAdd, hreg₂.2, M22_U1]
  have hid₂ : (BitVec.ofNat 5 ↑Main[10]).toNat = Main[10].val := by
    simp only [BabyBearPrime, BitVec.toNat_ofNat, Nat.reducePow, Nat.mod_succ_eq_iff_lt,
      Nat.succ_eq_add_one, Nat.reduceAdd, hreg₁.2, M22_U1]
  rw [hid₁, hid₂,
    run_rX_bind_of_get_mem_eq _ _ _ _ hmem₂,
    run_rX_bind_of_get_mem_eq _ _ _ _ hmem₁]

  rw [wX_comm_of_ne', run_wX_bind_of_get_mem_eq, wX_comm_of_ne,
    run_wX_bind_of_get_mem_eq, add_comm]
  · refine congr_arg (EStateM.run · mstate) (congr_arg _ ?_)

    rw [← BitVec.toNat_inj, BitVec.ofNatLT_eq_ofNat hb1, BitVec.ofNatLT_eq_ofNat hb2]
  · exact hmem₂
  · simp only [BitVec.toNat_ofNat, Nat.reducePow, BabyBearPrime, ne_eq, regno.Regno.injEq, hreg₂,
      not_false_eq_true, M22_U1]
  · exact hmem₁
  · simp only [BitVec.toNat_ofNat, Nat.reducePow, BabyBearPrime, ne_eq, regno.Regno.injEq, hreg₁,
      not_false_eq_true, M22_U1]

end AddChip
