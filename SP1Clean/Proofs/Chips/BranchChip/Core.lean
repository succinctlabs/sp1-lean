import SP1Clean.Proofs.Chips.BranchChip.Contracts
import SP1Clean.Proofs.Chips.BranchChip.Populate
import SP1Clean.Proofs.CircuitProofStart
import SP1Clean.Native.Operations.AddOperation.RawSpec

/-! # Exact Branch circuit proof

Soundness and honest-witness completeness for the native Branch circuit whose local columns,
constraints, and interactions match pinned SP1 v6.4.0.
-/

namespace SP1Clean.BranchChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

theorem soundness :
    GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start_early_struct
  simp only [branchDecision, circuit_norm, h_input] at h_holds ⊢
  let input_is_real := input_isBeq + input_isBne + input_isBlt + input_isBge + input_isBltu + input_isBgeu
  obtain ⟨h_imm, h_rs1U, h_rs2U, h_pcU⟩ := h_assumptions
  obtain ⟨h_lt, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
    h_sumbin, h_isbr_bin, h_isbr,
    h_taken0, h_taken1, h_taken2, h_taken3,
    h_fall0, h_fall1, h_fall2, h_fall3,
    h_cpustate, h_itype, h_byte1, h_byte2, h_byte3⟩ := h_holds
  obtain ⟨⟨_h_ckh, _h_ck1, _h_ck0, hpc⟩, ⟨_h_a,
    ⟨h_amem_pv, _, _⟩, _h_a0, _h_b,
    ⟨h_bmem_pv, _, _⟩, hcimm⟩, _, _, _, _, _, _⟩ := h_input
  have h_realsum : input_is_real =
      input_isBeq + input_isBne + input_isBlt + input_isBge + input_isBltu + input_isBgeu := rfl
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := by
    exact SP1Clean.bool_of_mul_pred h_sumbin
  have hbeq := SP1Clean.bool_of_mul_pred h_beq
  have hbne := SP1Clean.bool_of_mul_pred h_bne
  have hblt := SP1Clean.bool_of_mul_pred h_blt
  have hbge := SP1Clean.bool_of_mul_pred h_bge
  have hbltu := SP1Clean.bool_of_mul_pred h_bltu
  have hbgeu := SP1Clean.bool_of_mul_pred h_bgeu
  have hisbr := SP1Clean.bool_of_mul_pred h_isbr_bin
  have h_clk :=
    Readers.ClkDiscipline.of_cpuState_spec (h_cpustate h_bin)
  let rs1 : Word (ZMod p) :=
    #v[Expression.eval env input_var_adapter_op_a_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[3]]
  let rs2 : Word (ZMod p) :=
    #v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]]
  let pc : Word (ZMod p) :=
    #v[Expression.eval env input_var_state_pc[0],
      Expression.eval env input_var_state_pc[1],
      Expression.eval env input_var_state_pc[2], 0]
  let imm : Word (ZMod p) :=
    #v[Expression.eval env input_var_adapter_op_c_imm[0],
      Expression.eval env input_var_adapter_op_c_imm[1],
      Expression.eval env input_var_adapter_op_c_imm[2],
      Expression.eval env input_var_adapter_op_c_imm[3]]
  let next : Word (ZMod p) :=
    #v[env.get (i₀ + 11), env.get (i₀ + 12), env.get (i₀ + 13), 0]
  have hrs1eq : rs1 =
      #v[input_adapter_op_a_memory_prev_value[0],
        input_adapter_op_a_memory_prev_value[1],
        input_adapter_op_a_memory_prev_value[2],
        input_adapter_op_a_memory_prev_value[3]] := by
    dsimp only [rs1]
    rw [← h_amem_pv]
    simp only [Vector.getElem_map]
  have hrs2eq : rs2 =
      #v[input_adapter_op_b_memory_prev_value[0],
        input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2],
        input_adapter_op_b_memory_prev_value[3]] := by
    dsimp only [rs2]
    rw [← h_bmem_pv]
    simp only [Vector.getElem_map]
  have hpceq : pc =
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
    dsimp only [pc]
    rw [← hpc]
    simp only [Vector.getElem_map]
  have himmeq : imm = input_adapter_op_c_imm := by
    dsimp only [imm]
    rw [← hcimm]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    interval_cases i <;> rfl
  have hrs1U : Word.isU64 rs1 := hrs1eq ▸ h_rs1U
  have hrs2U : Word.isU64 rs2 := hrs2eq ▸ h_rs2U
  have hpcU : Word.isU64 pc := hpceq ▸ h_pcU
  have himmU : Word.isU64 imm := himmeq ▸ h_imm
  have h4U :
      Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_four
  have h_sig_bin :=
    (signed_selector_valid hbeq hbne hblt hbge hbltu hbgeu h_bin).1
  have nextInteract (hr1 : input_is_real = 1) :
      AddOperation.InteractSpec next := by
    have h0 := h_byte1 (congrArg Neg.neg hr1)
    have h1 := h_byte2 (congrArg Neg.neg hr1)
    have h2 := h_byte3 (congrArg Neg.neg hr1)
    simp only [byteChannel] at h0 h1 h2
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := Nat.cast_ofNat
    have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
    rw [← c14] at h0
    rw [← c16] at h1 h2
    have r0 := (byteRowSpec_range _ SP1Clean.BranchChip.h14p).mp h0
    have r1 := (byteRowSpec_range _ SP1Clean.sixteen_lt).mp h1
    have r2 := (byteRowSpec_range _ SP1Clean.sixteen_lt).mp h2
    simp only [AddOperation.InteractSpec, next, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ZMod.val_zero]
    exact ⟨val_lt_65536_of_mul_inv_four_lt r0, r1, r2, by omega⟩
  have takenSemantics (hr1 : input_is_real = 1)
      (hbr1 : env.get (i₀ + 10) = 1) :
      Word.toBitVec64 next =
        Word.toBitVec64 pc + Word.toBitVec64 imm := by
    rw [hbr1, one_mul] at h_taken0 h_taken1 h_taken2 h_taken3
    have hAssert : AddOperation.AssertSpec pc imm next := by
      simp only [AddOperation.AssertSpec, pc, imm, next,
        Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ]
      exact
        ⟨SP1Clean.bool_of_mul_pred h_taken0,
          SP1Clean.bool_of_mul_pred h_taken1,
          SP1Clean.bool_of_mul_pred h_taken2,
          (by
            simpa only [zero_add, sub_zero] using
              (SP1Clean.bool_of_mul_pred h_taken3))⟩
    exact
      (AddOperation.addSemantics_of_carries hpcU himmU hAssert
        (nextInteract hr1)).2
  have fallSemantics (hr1 : input_is_real = 1)
      (hbr0 : env.get (i₀ + 10) = 0) :
      Word.toBitVec64 next =
        Word.toBitVec64 pc +
          Word.toBitVec64 (#v[(4 : ZMod p), 0, 0, 0] :
            Word (ZMod p)) := by
    have hgate :
        input_isBeq + input_isBne + input_isBlt +
            input_isBge + input_isBltu +
              input_isBgeu - env.get (i₀ + 10) = 1 := by
      rw [← h_realsum, hr1, hbr0]
      simp
    rw [hgate, one_mul] at h_fall0 h_fall1 h_fall2 h_fall3
    have hAssert :
        AddOperation.AssertSpec pc
          (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) next := by
      simp only [AddOperation.AssertSpec, pc, next,
        Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero, List.getElem_cons_succ,
        add_zero, zero_add, sub_zero]
      exact
        ⟨SP1Clean.bool_of_mul_pred h_fall0,
          SP1Clean.bool_of_mul_pred h_fall1,
          SP1Clean.bool_of_mul_pred h_fall2,
          SP1Clean.bool_of_mul_pred h_fall3⟩
    exact
      (AddOperation.addSemantics_of_carries hpcU h4U hAssert
        (nextInteract hr1)).2
  refine
    ⟨⟨?_, h_bin,
      ⟨hbeq, hbne, hblt, hbge, hbltu, hbgeu, hisbr⟩,
      ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact h_itype ⟨h_bin, h_bin, h_clk⟩
  · intro real
    apply SP1Clean.BranchChip.flagsOneHot_of_sum_one
      hbeq hbne hblt hbge hbltu hbgeu
    exact h_realsum.symm.trans real
  · intro hr1 hbr1
    have hsem := takenSemantics hr1 hbr1
    rw [hpceq, himmeq] at hsem
    simpa only [next, pc, imm, SP1Clean.BranchChip.nextPcWord,
      SP1Clean.BranchChip.pcWord, Vector.getElem_map,
      Vector.getElem_mapRange, circuit_norm] using hsem
  · intro hr1 hbr0
    have hsem := fallSemantics hr1 hbr0
    rw [hpceq] at hsem
    simpa only [next, pc, SP1Clean.BranchChip.nextPcWord,
      SP1Clean.BranchChip.pcWord, Vector.getElem_map,
      Vector.getElem_mapRange, circuit_norm] using hsem
  · intro hr1
    change input_is_real = 1 at hr1
    have h_lt_spec := LtOperationSigned.result_semantic
      (h_lt ⟨hrs1U, hrs2U, h_bin, h_sig_bin⟩) hr1
    obtain ⟨h_bit, h_eqf⟩ := h_lt_spec
    simp only [circuit_norm] at h_bit h_eqf
    dsimp only [rs1, rs2] at hrs1eq hrs2eq
    rw [hrs1eq, hrs2eq] at h_bit h_eqf
    have hone :
        input_isBeq + input_isBne + input_isBlt +
            input_isBge + input_isBltu +
              input_isBgeu = 1 := by
      rw [← h_realsum]
      exact hr1
    rw [hone, one_mul] at h_isbr
    simp only [SP1Clean.BranchChip.rs1Word,
      SP1Clean.BranchChip.rs2Word]
    exact SP1Clean.BranchChip.branch_conditions_of_decision_eq
      h_rs1U h_rs2U hbeq hbne hblt hbge hbltu hbgeu hisbr hone
      h_bit h_eqf
      (by
        simp only [SP1Clean.BranchChip.branchDecision]
        linear_combination h_isbr)
  · intro hr1
    change input_is_real = 1 at hr1
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := Nat.cast_ofNat
    have hguar := h_byte1 (congrArg Neg.neg hr1)
    simp only [byteChannel] at hguar
    rw [← c14] at hguar
    have halign := val_mod_four_of_mul_inv_four_lt
      ((byteRowSpec_range _ SP1Clean.BranchChip.h14p).mp hguar)
    simpa only [Vector.getElem_map, Vector.getElem_mapRange,
      circuit_norm] using halign
  · refine ⟨⟨h_bin, h_bin, h_clk⟩, ?_, ?_, ?_⟩ <;>
      intro h1 h0 <;>
        exact off_gate_vacuous h_bin h1 h0

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions
      (fun _ _ _ => True) := by
  circuit_proof_start_core
  obtain ⟨h_imm, h_rs1U, h_rs2U, h_pcU, h_bin, h_cpu, h_it,
    h_bt3, h_ft3, hf, h_ranges⟩ := h_assumptions
  have h_brbin := populateBranching_binary input h_rs1U h_rs2U hf h_bin
  have h_brpad := populateBranching_inactive input hf
  have fb0 := hf 0
  have fb1 := hf 1
  have fb2 := hf 2
  have fb3 := hf 3
  have fb4 := hf 4
  have fb5 := hf 5
  clear hf
  simp +instances only [circuit_norm] at h_input
  provable_struct_simp
  let input_is_real := input_isBeq + input_isBne + input_isBlt + input_isBge + input_isBltu + input_isBgeu
  let input_var_is_real := input_var_isBeq + input_var_isBne + input_var_isBlt + input_var_isBge + input_var_isBltu + input_var_isBgeu
  have hsumreal : input_isBeq + input_isBne + input_isBlt + input_isBge + input_isBltu + input_isBgeu = input_is_real := rfl
  change input_is_real = 0 ∨ input_is_real = 1 at h_bin
  change input_isBeq = 0 ∨ input_isBeq = 1 at fb0
  change input_isBne = 0 ∨ input_isBne = 1 at fb1
  change input_isBlt = 0 ∨ input_isBlt = 1 at fb2
  change input_isBge = 0 ∨ input_isBge = 1 at fb3
  change input_isBltu = 0 ∨ input_isBltu = 1 at fb4
  change input_isBgeu = 0 ∨ input_isBgeu = 1 at fb5
  obtain ⟨he_lt, he_br, he_np, -, _⟩ := h_env
  simp +instances only [branchDecision, circuit_norm, h_input] at he_br he_lt he_np
  have h_real_eval : Expression.eval env.toEnvironment input_var_is_real = input_is_real := by
    simp only [input_var_is_real, circuit_norm, h_input]
    rfl
  simp only [branchTargetWord, fallThroughWord] at h_bt3 h_ft3 h_ranges
  have hpc :
      Vector.map (Expression.eval env.toEnvironment) input_var_state_pc =
        input_state_pc := by
    rw [← CircuitType.eval_var_fields]
    exact h_input.1.2.2.2
  have ep : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_state_pc[i] =
        input_state_pc[i] := by
    intro i hi
    rw [← hpc]
    simp only [Vector.getElem_map]
  have ep0 := ep 0 (by omega)
  have ep1 := ep 1 (by omega)
  have ep2 := ep 2 (by omega)
  have ha1eq :
      (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
          Expression.eval env.toEnvironment input_var_state_pc[1],
          Expression.eval env.toEnvironment input_var_state_pc[2], 0] :
        Word (ZMod p)) =
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
    rw [ep0, ep1, ep2]
  have ha1U :
      Word.isU64
        (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
            Expression.eval env.toEnvironment input_var_state_pc[1],
            Expression.eval env.toEnvironment input_var_state_pc[2], 0] :
          Word (ZMod p)) :=
    ha1eq ▸ h_pcU
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  have h4U :
      Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) :=
    Word.isU64_four
  have hcimm :
      Vector.map (Expression.eval env.toEnvironment)
          input_var_adapter_op_c_imm =
        input_adapter_op_c_imm := by
    rw [← CircuitType.eval_var_fields]
    exact h_input.2.1.2.2.2.2.2
  have hapv_map :
      Vector.map (Expression.eval env.toEnvironment)
          input_var_adapter_op_a_memory_prev_value =
        input_adapter_op_a_memory_prev_value := by
    rw [← CircuitType.eval_var_fields]
    exact h_input.2.1.2.1.1
  have hbpv_map :
      Vector.map (Expression.eval env.toEnvironment)
          input_var_adapter_op_b_memory_prev_value =
        input_adapter_op_b_memory_prev_value := by
    rw [← CircuitType.eval_var_fields]
    exact h_input.2.1.2.2.2.2.1.1
  have hcimmeq :
      (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_imm[0],
          Expression.eval env.toEnvironment input_var_adapter_op_c_imm[1],
          Expression.eval env.toEnvironment input_var_adapter_op_c_imm[2],
          Expression.eval env.toEnvironment input_var_adapter_op_c_imm[3]] :
        Word (ZMod p)) = input_adapter_op_c_imm := by
    rw [← hcimm]
    apply Vector.ext
    intro i hi
    simp only [Vector.getElem_map]
    interval_cases i <;> rfl
  have ec : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[i] =
        input_adapter_op_c_imm[i] := by
    intro i hi
    rw [← hcimm]
    simp only [Vector.getElem_map]
  have ec0 := ec 0 (by omega)
  have ec1 := ec 1 (by omega)
  have ec2 := ec 2 (by omega)
  have ec3 := ec 3 (by omega)
  have hrs1eq :
      (#v[Expression.eval env.toEnvironment
            input_var_adapter_op_a_memory_prev_value[0],
          Expression.eval env.toEnvironment
            input_var_adapter_op_a_memory_prev_value[1],
          Expression.eval env.toEnvironment
            input_var_adapter_op_a_memory_prev_value[2],
          Expression.eval env.toEnvironment
            input_var_adapter_op_a_memory_prev_value[3]] :
        Word (ZMod p)) =
        #v[input_adapter_op_a_memory_prev_value[0],
          input_adapter_op_a_memory_prev_value[1],
          input_adapter_op_a_memory_prev_value[2],
          input_adapter_op_a_memory_prev_value[3]] := by
    rw [← hapv_map]
    simp only [Vector.getElem_map]
  have hrs2eq :
      (#v[Expression.eval env.toEnvironment
            input_var_adapter_op_b_memory_prev_value[0],
          Expression.eval env.toEnvironment
            input_var_adapter_op_b_memory_prev_value[1],
          Expression.eval env.toEnvironment
            input_var_adapter_op_b_memory_prev_value[2],
          Expression.eval env.toEnvironment
            input_var_adapter_op_b_memory_prev_value[3]] :
        Word (ZMod p)) =
        #v[input_adapter_op_b_memory_prev_value[0],
          input_adapter_op_b_memory_prev_value[1],
          input_adapter_op_b_memory_prev_value[2],
          input_adapter_op_b_memory_prev_value[3]] := by
    rw [← hbpv_map]
    simp only [Vector.getElem_map]
  have hrs1U :
      Word.isU64
        (#v[Expression.eval env.toEnvironment
              input_var_adapter_op_a_memory_prev_value[0],
            Expression.eval env.toEnvironment
              input_var_adapter_op_a_memory_prev_value[1],
            Expression.eval env.toEnvironment
              input_var_adapter_op_a_memory_prev_value[2],
            Expression.eval env.toEnvironment
              input_var_adapter_op_a_memory_prev_value[3]] :
          Word (ZMod p)) :=
    hrs1eq ▸ h_rs1U
  have hrs2U :
      Word.isU64
        (#v[Expression.eval env.toEnvironment
              input_var_adapter_op_b_memory_prev_value[0],
            Expression.eval env.toEnvironment
              input_var_adapter_op_b_memory_prev_value[1],
            Expression.eval env.toEnvironment
              input_var_adapter_op_b_memory_prev_value[2],
            Expression.eval env.toEnvironment
              input_var_adapter_op_b_memory_prev_value[3]] :
          Word (ZMod p)) :=
    hrs2eq ▸ h_rs2U
  have hsumbin :
      (input_isBeq + input_isBne + input_isBlt +
          input_isBge + input_isBltu + input_isBgeu) *
          (input_isBeq + input_isBne + input_isBlt +
            input_isBge + input_isBltu +
              input_isBgeu - 1) = 0 := by
    rw [hsumreal]
    rcases h_bin with h | h <;> rw [h] <;> simp
  obtain ⟨h_sig_bin, hbg_gate⟩ :=
    signed_selector_valid fb0 fb1 fb2 fb3 fb4 fb5 h_bin
  have h_lt_spec : LtOperationSigned.Spec
      ⟨#v[Expression.eval env.toEnvironment
            input_var_adapter_op_a_memory_prev_value[0],
          Expression.eval env.toEnvironment
            input_var_adapter_op_a_memory_prev_value[1],
          Expression.eval env.toEnvironment
            input_var_adapter_op_a_memory_prev_value[2],
          Expression.eval env.toEnvironment
            input_var_adapter_op_a_memory_prev_value[3]],
        #v[Expression.eval env.toEnvironment
            input_var_adapter_op_b_memory_prev_value[0],
          Expression.eval env.toEnvironment
            input_var_adapter_op_b_memory_prev_value[1],
          Expression.eval env.toEnvironment
            input_var_adapter_op_b_memory_prev_value[2],
          Expression.eval env.toEnvironment
            input_var_adapter_op_b_memory_prev_value[3]],
        ⟨⟨⟨env.get (i₀)⟩,
            Vector.map (Expression.eval env.toEnvironment)
              (Vector.mapRange 4 fun i => var { index := i₀ + 1 + i }),
            env.get (i₀ + 5),
            Vector.map (Expression.eval env.toEnvironment)
              (Vector.mapRange 2 fun i => var { index := i₀ + 6 + i })⟩,
          ⟨env.get (i₀ + 8)⟩, ⟨env.get (i₀ + 9)⟩⟩,
        input_isBlt + input_isBge, input_is_real⟩ := by
    rw [he_lt, LtOperationSigned.populateFE_eval env
      #v[input_var_adapter_op_a_memory_prev_value[0], input_var_adapter_op_a_memory_prev_value[1],
         input_var_adapter_op_a_memory_prev_value[2], input_var_adapter_op_a_memory_prev_value[3]]
      #v[input_var_adapter_op_b_memory_prev_value[0], input_var_adapter_op_b_memory_prev_value[1],
         input_var_adapter_op_b_memory_prev_value[2], input_var_adapter_op_b_memory_prev_value[3]]
      _ _ _ _ rfl rfl hrs1U hrs2U]
    simp only [circuit_norm, h_input]
    exact LtOperationSigned.spec_populate hrs1U hrs2U h_sig_bin h_bin hbg_gate
  have he_dec := he_br
  have he_cmp := he_lt
  rw [LtOperationSigned.populateFE_eval env
    #v[input_var_adapter_op_a_memory_prev_value[0], input_var_adapter_op_a_memory_prev_value[1],
       input_var_adapter_op_a_memory_prev_value[2], input_var_adapter_op_a_memory_prev_value[3]]
    #v[input_var_adapter_op_b_memory_prev_value[0], input_var_adapter_op_b_memory_prev_value[1],
       input_var_adapter_op_b_memory_prev_value[2], input_var_adapter_op_b_memory_prev_value[3]]
    _ _ _ _ rfl rfl hrs1U hrs2U] at he_cmp
  simp only [circuit_norm, h_input] at he_cmp
  rw [hrs1eq, hrs2eq] at he_cmp
  have hdecision := congrArg (fun c : Circuits.Types.LtOperationSigned (ZMod p) =>
    branchDecision input_isBeq input_isBne input_isBlt input_isBge input_isBltu input_isBgeu
      c.result.u16_compare_operation.bit
      (c.result.u16_flags[0] + c.result.u16_flags[1] + c.result.u16_flags[2] + c.result.u16_flags[3])) he_cmp
  simp only [branchDecision, circuit_norm] at hdecision
  replace he_br := he_br.trans hdecision
  have brb : env.get (i₀ + 10) = 0 ∨ env.get (i₀ + 10) = 1 := he_br ▸ h_brbin
  have hnp0 :
      env.get (i₀ + 11) =
        env.get (i₀ + 10) *
            (AddOperation.populate
              #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
              input_adapter_op_c_imm)[0] +
          (input_is_real - env.get (i₀ + 10)) *
            (AddOperation.populate
              #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
              #v[4, 0, 0, 0])[0] := by
    have hcell := SP1Clean.BranchChip.nextPcIR_eval env
      #v[input_var_state_pc[0], input_var_state_pc[1], input_var_state_pc[2]]
      input_var_adapter_op_c_imm (var { index := i₀ + 10 }) input_var_is_real
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2]] input_adapter_op_c_imm
      (by simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
            List.getElem_cons_succ, ep0, ep1, ep2])
      hcimmeq h_pcU h_imm 0 (by omega)
    simp only [circuit_norm, h_real_eval] at hcell
    exact (he_np ⟨0, by omega⟩).trans hcell
  have hnp1 :
      env.get (i₀ + 12) =
        env.get (i₀ + 10) *
            (AddOperation.populate
              #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
              input_adapter_op_c_imm)[1] +
          (input_is_real - env.get (i₀ + 10)) *
            (AddOperation.populate
              #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
              #v[4, 0, 0, 0])[1] := by
    have hcell := SP1Clean.BranchChip.nextPcIR_eval env
      #v[input_var_state_pc[0], input_var_state_pc[1], input_var_state_pc[2]]
      input_var_adapter_op_c_imm (var { index := i₀ + 10 }) input_var_is_real
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2]] input_adapter_op_c_imm
      (by simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
            List.getElem_cons_succ, ep0, ep1, ep2])
      hcimmeq h_pcU h_imm 1 (by omega)
    simp only [circuit_norm, h_real_eval] at hcell
    exact (he_np ⟨1, by omega⟩).trans hcell
  have hnp2 :
      env.get (i₀ + 13) =
        env.get (i₀ + 10) *
            (AddOperation.populate
              #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
              input_adapter_op_c_imm)[2] +
          (input_is_real - env.get (i₀ + 10)) *
            (AddOperation.populate
              #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
              #v[4, 0, 0, 0])[2] := by
    have hcell := SP1Clean.BranchChip.nextPcIR_eval env
      #v[input_var_state_pc[0], input_var_state_pc[1], input_var_state_pc[2]]
      input_var_adapter_op_c_imm (var { index := i₀ + 10 }) input_var_is_real
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2]] input_adapter_op_c_imm
      (by simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
            List.getElem_cons_succ, ep0, ep1, ep2])
      hcimmeq h_pcU h_imm 2 (by omega)
    simp only [circuit_norm, h_real_eval] at hcell
    exact (he_np ⟨2, by omega⟩).trans hcell
  have hBranchSemantics :
      Word.isU64
          (AddOperation.populate
            #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
            input_adapter_op_c_imm) ∧
        Word.toBitVec64
            (AddOperation.populate
              #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
              input_adapter_op_c_imm) =
          Word.toBitVec64
              (#v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] :
                Word (ZMod p)) +
            Word.toBitVec64 input_adapter_op_c_imm :=
    AddOperation.spec_populate h_pcU h_imm (1 : ZMod p) rfl
  have hFallSemantics :
      Word.isU64
          (AddOperation.populate
            #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
            #v[4, 0, 0, 0]) ∧
        Word.toBitVec64
            (AddOperation.populate
              #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
              #v[4, 0, 0, 0]) =
          Word.toBitVec64
              (#v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] :
                Word (ZMod p)) +
            Word.toBitVec64 (#v[(4 : ZMod p), 0, 0, 0] :
              Word (ZMod p)) :=
    AddOperation.spec_populate h_pcU h4U (1 : ZMod p) rfl
  have hBranchAssert :
      AddOperation.AssertSpec
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
        input_adapter_op_c_imm
        (AddOperation.populate
          #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          input_adapter_op_c_imm) :=
    (AddOperation.carries_of_addSemantics h_pcU h_imm
      hBranchSemantics.1 hBranchSemantics.2).1
  have hFallAssert :
      AddOperation.AssertSpec
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
        #v[4, 0, 0, 0]
        (AddOperation.populate
          #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          #v[4, 0, 0, 0]) :=
    (AddOperation.carries_of_addSemantics h_pcU h4U
      hFallSemantics.1 hFallSemantics.2).1
  have nextEqBranch (hr1 : input_is_real = 1)
      (hbr1 : env.get (i₀ + 10) = 1) :
      (#v[env.get (i₀ + 11), env.get (i₀ + 12), env.get (i₀ + 13), 0] :
          Word (ZMod p)) =
        AddOperation.populate
          #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          input_adapter_op_c_imm := by
    apply Vector.ext
    intro i hi
    interval_cases i
    · simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero]
      rw [hnp0, hbr1, hr1]
      simp
    · simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_succ, List.getElem_cons_zero]
      rw [hnp1, hbr1, hr1]
      simp
    · simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_succ, List.getElem_cons_zero]
      rw [hnp2, hbr1, hr1]
      simp
    · simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_succ, List.getElem_cons_zero]
      exact h_bt3.symm
  have nextEqFall (hr1 : input_is_real = 1)
      (hbr0 : env.get (i₀ + 10) = 0) :
      (#v[env.get (i₀ + 11), env.get (i₀ + 12), env.get (i₀ + 13), 0] :
          Word (ZMod p)) =
        AddOperation.populate
          #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          #v[4, 0, 0, 0] := by
    apply Vector.ext
    intro i hi
    interval_cases i
    · simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_zero]
      rw [hnp0, hbr0, hr1]
      simp
    · simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_succ, List.getElem_cons_zero]
      rw [hnp1, hbr0, hr1]
      simp
    · simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_succ, List.getElem_cons_zero]
      rw [hnp2, hbr0, hr1]
      simp
    · simp only [Vector.getElem_mk, List.getElem_toArray,
        List.getElem_cons_succ, List.getElem_cons_zero]
      exact h_ft3.symm
  have branchCarries (hr1 : input_is_real = 1)
      (hbr1 : env.get (i₀ + 10) = 1) :
      AddOperation.AssertSpec
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
        input_adapter_op_c_imm
        #v[env.get (i₀ + 11), env.get (i₀ + 12), env.get (i₀ + 13), 0] := by
    rw [nextEqBranch hr1 hbr1]
    exact hBranchAssert
  have fallCarries (hr1 : input_is_real = 1)
      (hbr0 : env.get (i₀ + 10) = 0) :
      AddOperation.AssertSpec
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
        #v[4, 0, 0, 0]
        #v[env.get (i₀ + 11), env.get (i₀ + 12), env.get (i₀ + 13), 0] := by
    rw [nextEqFall hr1 hbr0]
    exact hFallAssert
  have real_of_branching (hbr1 : env.get (i₀ + 10) = 1) :
      input_is_real = 1 := by
    rcases h_bin with hr0 | hr1
    · have hbr0 : env.get (i₀ + 10) = 0 :=
        he_br.trans (h_brpad hr0)
      exfalso
      rw [hbr0] at hbr1
      exact zero_ne_one hbr1
    · exact hr1
  have mulPred_of_bool {x : ZMod p} (hx : x = 0 ∨ x = 1) :
      x * (x - 1) = 0 := by
    rcases hx with h | h <;> rw [h] <;> simp
  have branchPredicates (hr1 : input_is_real = 1)
      (hbr1 : env.get (i₀ + 10) = 1) :
      let c0 :=
        (input_state_pc[0] + input_adapter_op_c_imm[0] -
          env.get (i₀ + 11)) * (65536 : ZMod p)⁻¹
      let c1 :=
        (input_state_pc[1] + input_adapter_op_c_imm[1] -
          env.get (i₀ + 12) + c0) * (65536 : ZMod p)⁻¹
      let c2 :=
        (input_state_pc[2] + input_adapter_op_c_imm[2] -
          env.get (i₀ + 13) + c1) * (65536 : ZMod p)⁻¹
      let c3 :=
        (input_adapter_op_c_imm[3] + c2) * (65536 : ZMod p)⁻¹
      c0 * (c0 - 1) = 0 ∧ c1 * (c1 - 1) = 0 ∧
        c2 * (c2 - 1) = 0 ∧ c3 * (c3 - 1) = 0 := by
    have hc := branchCarries hr1 hbr1
    simp only [AddOperation.AssertSpec, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      zero_add, sub_zero] at hc ⊢
    exact
      ⟨mulPred_of_bool hc.1,
        mulPred_of_bool hc.2.1,
        mulPred_of_bool hc.2.2.1,
        mulPred_of_bool hc.2.2.2⟩
  have fallPredicates (hr1 : input_is_real = 1)
      (hbr0 : env.get (i₀ + 10) = 0) :
      let c0 :=
        (input_state_pc[0] + 4 - env.get (i₀ + 11)) *
          (65536 : ZMod p)⁻¹
      let c1 :=
        (input_state_pc[1] - env.get (i₀ + 12) + c0) *
          (65536 : ZMod p)⁻¹
      let c2 :=
        (input_state_pc[2] - env.get (i₀ + 13) + c1) *
          (65536 : ZMod p)⁻¹
      let c3 := c2 * (65536 : ZMod p)⁻¹
      c0 * (c0 - 1) = 0 ∧ c1 * (c1 - 1) = 0 ∧
        c2 * (c2 - 1) = 0 ∧ c3 * (c3 - 1) = 0 := by
    have hc := fallCarries hr1 hbr0
    simp only [AddOperation.AssertSpec, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ,
      zero_add, add_zero, sub_zero] at hc ⊢
    exact
      ⟨mulPred_of_bool hc.1,
        mulPred_of_bool hc.2.1,
        mulPred_of_bool hc.2.2.1,
        mulPred_of_bool hc.2.2.2⟩
  simp only [SP1Clean.BranchChip.committedNextPc,
    SP1Clean.BranchChip.branchTargetWord,
    SP1Clean.BranchChip.fallThroughWord, populateBranching, populateComparison,
    branchDecision, rs1WordInput, rs2WordInput, Inputs.is_real,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at h_ranges
  simp +instances only [main, branchDecision, circuit_norm, h_input, hpc, hcimm,
    hapv_map, hbpv_map, ep0, ep1, ep2, ec0, ec1, ec2, ec3]
  refine
    ⟨⟨⟨hrs1U, hrs2U, h_bin, h_sig_bin⟩,
        by simpa only [LtOperationSigned.circuit] using h_lt_spec⟩,
        ?_, ?_, ?_, ?_, ?_, ?_,
        hsumbin, ?_, ?_,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
        ⟨h_bin, by simpa only [Readers.CPUState.Spec] using h_cpu⟩,
        ⟨⟨h_bin, h_bin, h_clk⟩,
          by simpa only [Readers.ITypeReaderImmutable.Spec] using h_it⟩,
        ?_, ?_, ?_⟩
  · rcases fb0 with h | h <;> rw [h] <;> simp
  · rcases fb1 with h | h <;> rw [h] <;> simp
  · rcases fb2 with h | h <;> rw [h] <;> simp
  · rcases fb3 with h | h <;> rw [h] <;> simp
  · rcases fb4 with h | h <;> rw [h] <;> simp
  · rcases fb5 with h | h <;> rw [h] <;> simp
  · rcases brb with h | h <;> rw [h] <;> simp
  · rw [he_dec]
    simp
  · rcases brb with hbr0 | hbr1
    · rw [hbr0]
      simp
    · rw [hbr1, one_mul]
      exact (branchPredicates (real_of_branching hbr1) hbr1).1
  · rcases brb with hbr0 | hbr1
    · rw [hbr0]
      simp
    · rw [hbr1, one_mul]
      exact (branchPredicates (real_of_branching hbr1) hbr1).2.1
  · rcases brb with hbr0 | hbr1
    · rw [hbr0]
      simp
    · rw [hbr1, one_mul]
      exact (branchPredicates (real_of_branching hbr1) hbr1).2.2.1
  · rcases brb with hbr0 | hbr1
    · rw [hbr0]
      simp
    · rw [hbr1, one_mul]
      exact (branchPredicates (real_of_branching hbr1) hbr1).2.2.2
  · rcases h_bin with hr0 | hr1
    · have hbr0 : env.get (i₀ + 10) = 0 :=
        he_br.trans (h_brpad hr0)
      rw [hsumreal, hr0, hbr0]
      simp
    · rcases brb with hbr0 | hbr1
      · rw [hsumreal, hr1, hbr0]
        simpa using (fallPredicates hr1 hbr0).1
      · rw [hsumreal, hr1, hbr1]
        simp
  · rcases h_bin with hr0 | hr1
    · have hbr0 : env.get (i₀ + 10) = 0 :=
        he_br.trans (h_brpad hr0)
      rw [hsumreal, hr0, hbr0]
      simp
    · rcases brb with hbr0 | hbr1
      · rw [hsumreal, hr1, hbr0]
        simpa using (fallPredicates hr1 hbr0).2.1
      · rw [hsumreal, hr1, hbr1]
        simp
  · rcases h_bin with hr0 | hr1
    · have hbr0 : env.get (i₀ + 10) = 0 :=
        he_br.trans (h_brpad hr0)
      rw [hsumreal, hr0, hbr0]
      simp
    · rcases brb with hbr0 | hbr1
      · rw [hsumreal, hr1, hbr0]
        simpa using (fallPredicates hr1 hbr0).2.2.1
      · rw [hsumreal, hr1, hbr1]
        simp
  · rcases h_bin with hr0 | hr1
    · have hbr0 : env.get (i₀ + 10) = 0 :=
        he_br.trans (h_brpad hr0)
      rw [hsumreal, hr0, hbr0]
      simp
    · rcases brb with hbr0 | hbr1
      · rw [hsumreal, hr1, hbr0]
        simpa using (fallPredicates hr1 hbr0).2.2.2
      · rw [hsumreal, hr1, hbr1]
        simp
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have hranges := h_ranges hr1
    rw [← he_br] at hranges
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := Nat.cast_ofNat
    simp only [byteChannel, hnp0]
    rw [← c14]
    exact (byteRowSpec_range _ SP1Clean.BranchChip.h14p).mpr hranges.1
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have hranges := h_ranges hr1
    rw [← he_br] at hranges
    have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
    simp only [byteChannel, hnp1]
    rw [← c16]
    exact (byteRowSpec_range _ SP1Clean.sixteen_lt).mpr hranges.2.1
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have hranges := h_ranges hr1
    rw [← he_br] at hranges
    have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := Nat.cast_ofNat
    simp only [byteChannel, hnp2]
    rw [← c16]
    exact (byteRowSpec_range _ SP1Clean.sixteen_lt).mpr hranges.2.2

end SP1Clean.BranchChip
