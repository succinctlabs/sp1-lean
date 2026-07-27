import SP1Clean.Proofs.Chips.ShiftLeftChip.Defs
import SP1Clean.Proofs.Chips.ShiftLeftChip.Soundness.Sll
import SP1Clean.Proofs.Chips.ShiftLeftChip.Soundness.Sllw
import SP1Clean.Math.EvalVec
import Clean.Air.Circuit

/-! # `SP1Clean.ShiftLeftChip` — contract: soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance + the soundness
`Assumptions` live in the sibling `Defs` module (`Assumptions` there, not here, so the per-op
`Soundness/<Op>.lean` split files can import it without a cycle through `Formal`). This module holds the
`ProverAssumptions`, the soundness/completeness proofs, and the bundled `circuit`.

**Soundness** is assembled here from the two per-conjunct `Soundness/{Sll,Sllw}.lean` files — each its own
`GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy per-variant proofs
compile in parallel — plus the shared channel-requirement tail (the same in both variants, reused here from
`SoundSll`). `circuit_proof_start_core` only introduces the binders (no `simp`), so the sub-theorems' raw
`h_holds`/`h_input`/`h_assumptions` binders match directly.

**Completeness** is proven against `main`'s honest `Populate` witness closures (flags via the
`"shift_left_flags"` `ProverHint`): every witnessed cell is pinned to its populate projection, the
constraints close by the `Populate.lean` value-level bundles, and the nine byte-range pulls by the
populate bound lemmas. The closures themselves are conformance-checked cell-for-cell against SP1's real
`generate_trace` in `TraceGenTests/ShiftLeftChipTraceWitness.lean`. -/

namespace SP1Clean.ShiftLeftChip

open Circuit
open Extracted (ShiftLeftCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

-- `Assumptions` (the operand `isU64`/register-readback contract) lives in `Defs` so the per-op
-- `Soundness/<Op>.lean` split files can import it without a cycle through `Formal`.

/-- Prover-side row well-formedness: the operand `isU64`s, the `is_real` binary selector, the honest
`"shift_left_flags"` hint (each flag binary, the sum = `is_real` — required by the in-circuit
`is_real - (is_sll + is_sllw)` bind), `op_a_0 = 0`, the immediate-`c` machinery (`imm_c` boolean facts
+ the four `prev_value = op_c` pins, verbatim `ALUTypeReader.Spec` conjuncts), the CPUState clock
bounds, and the three register-access timestamp `Spec`s (op_c gated `is_real - imm_c`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  Word.isU64 input.op_b_val ∧
  Word.isU64 input.adapter.op_c_memory.prev_value ∧
  -- (W11 Option-B memory flip) the op_a register read-prior is `u64` on real rows — feeds the
  -- `ALUTypeReader` op_a/op_b `isU64` reader-`Spec` conjunct (op_a's half).
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (f[0] = 0 ∨ f[0] = 1) ∧ (f[1] = 0 ∨ f[1] = 1) ∧
  input.is_real = f[0] + f[1] ∧
  input.adapter.op_a_0 = 0 ∧
  (input.is_real - 1) * input.adapter.imm_c = 0 ∧
  (input.is_real - input.adapter.imm_c = 0 ∨ input.is_real - input.adapter.imm_c = 1) ∧
  (input.adapter.imm_c * (input.adapter.op_c_memory.prev_value[0] - input.adapter.op_c[0]) = 0 ∧
    input.adapter.imm_c * (input.adapter.op_c_memory.prev_value[1] - input.adapter.op_c[1]) = 0 ∧
    input.adapter.imm_c * (input.adapter.op_c_memory.prev_value[2] - input.adapter.op_c[2]) = 0 ∧
    input.adapter.imm_c * (input.adapter.op_c_memory.prev_value[3] - input.adapter.op_c[3]) = 0) ∧
  Readers.CPUState.Spec
    { cols := input.state,
      next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real - input.adapter.imm_c,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩ ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- G1: completeness of the reader's Memory pulls must exhibit the channel guarantee for each
  -- pulled prior record. These are honest-trace facts, not soundness assumptions. The op_c bound is
  -- needed only for a register shift (the `is_real - imm_c` pull is absent for an immediate).
  (input.is_real = 1 →
    input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24) ∧
  (input.is_real - input.adapter.imm_c = 1 →
    input.adapter.op_c_memory.access_timestamp.prev_low.val < 2 ^ 24)

set_option maxHeartbeats 4000000 in
/-- **Soundness.** The flag-gated RV64 `sll`/`sllw` identities on the result column `cols.a`. **Pieced
together** from the two per-conjunct `Soundness/{Sll,Sllw}.lean` files — each its own
`GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy per-variant proofs
compile in parallel — plus the shared channel-requirement tail (the same in both variants, reused here from
`SoundSll`). `circuit_proof_start_core` only introduces the binders (no `simp`), so the sub-theorems' raw
`h_holds`/`h_input`/`h_assumptions` binders match directly. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start_core
  refine ⟨fun hr => ⟨?_, ?_⟩, ?_⟩
  · exact (SoundSll.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSllw.soundness i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSll.soundness  i₀ env input_var input h_input h_assumptions h_holds).2

/-- Completeness: `main`'s honest `Populate` witness closures (flags from the `"shift_left_flags"`
hint) satisfy every constraint under `ProverAssumptions`. The chip-local assertion tail remains
folded behind `ShiftLeftCore.circuit`, avoiding the Lean 4.31 kernel-size cliff. -/
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start_core
  simp +instances only [circuit_norm] at h_input
  provable_struct_simp
  obtain ⟨hbU, hcU, ha_prev, hbin, hf0, hf1, hsum, hop_a_0, himmc, himmbin, hpins, h_cpu,
    hrac_a, hrac_b, hrac_c, hdec, hprev_ab, hprev_c⟩ := h_assumptions
  simp only [circuit_norm] at hbU hcU ha_prev hbin hsum hop_a_0 himmc himmbin hpins h_cpu
  simp only [circuit_norm] at hrac_a hrac_b hrac_c hdec hprev_ab hprev_c
  obtain ⟨-, h_env_a, h_env_cb, h_env_v, h_env_s, h_env_lo, h_env_hi, h_env_lr,
    h_env_msb, h_env_fl, -⟩ := h_env
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  have hpc := h_input.2.1.2.2.2
  have hbpv := h_input.2.2.2.2.2.2.1.1
  have hcpv := h_input.2.2.2.2.2.2.2.2.1.1
  have himm_eval := h_input.2.2.2.2.2.2.2.2.2
  have hbpv_map :
      Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_b_memory_prev_value =
        input_adapter_op_b_memory_prev_value := by
    rw [← CircuitType.eval_var_fields]
    exact hbpv
  have hapv := h_input.2.2.2.1.1
  have hopc := h_input.2.2.2.2.2.2.2.1
  have hapv_map :
      Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_a_memory_prev_value =
        input_adapter_op_a_memory_prev_value := by
    rw [← CircuitType.eval_var_fields]
    exact hapv
  have hopc_map :
      Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_c = input_adapter_op_c := by
    rw [← CircuitType.eval_var_fields]
    exact hopc
  have hcpv_map :
      Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_c_memory_prev_value =
        input_adapter_op_c_memory_prev_value := by
    rw [← CircuitType.eval_var_fields]
    exact hcpv
  have hpc_map :
      Vector.map (Expression.eval env.toEnvironment) input_var_state_pc = input_state_pc := by
    rw [← CircuitType.eval_var_fields]
    exact hpc
  have ec0 : Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[0]
      = input_adapter_op_c_memory_prev_value[0] := by
    rw [ProvableType.getElem_eval_fields, hcpv]
  have heb : ∀ (k : ℕ) (hk : k < 4),
      Expression.eval env.toEnvironment (input_var_adapter_op_b_memory_prev_value[k]'hk)
        = input_adapter_op_b_memory_prev_value[k]'hk := by
    intro k hk
    rw [ProvableType.getElem_eval_fields, hbpv]
  have heb0 := heb 0 (by norm_num)
  have heb1 := heb 1 (by norm_num)
  have heb2 := heb 2 (by norm_num)
  have heb3 := heb 3 (by norm_num)
  have epc0 : Expression.eval env.toEnvironment input_var_state_pc[0] = input_state_pc[0] := by
    rw [ProvableType.getElem_eval_fields, hpc]
  have epc1 : Expression.eval env.toEnvironment input_var_state_pc[1] = input_state_pc[1] := by
    rw [ProvableType.getElem_eval_fields, hpc]
  have epc2 : Expression.eval env.toEnvironment input_var_state_pc[2] = input_state_pc[2] := by
    rw [ProvableType.getElem_eval_fields, hpc]
  simp only [circuit_norm] at h_env_a h_env_cb h_env_v h_env_s h_env_lo h_env_hi h_env_lr
  simp only [circuit_norm] at h_env_msb h_env_fl
  simp only [vec4_eval, hbpv_map, ec0] at h_env_a h_env_cb h_env_v h_env_s h_env_lo h_env_hi
  simp only [vec4_eval, hbpv_map, ec0] at h_env_lr h_env_msb
  set B := input_adapter_op_b_memory_prev_value with hB
  set c0 := input_adapter_op_c_memory_prev_value[0] with hc0
  set F := hintFlags env.hint with hF
  have hA0 : env.get i₀ = (populateA B c0 F)[0] := by simpa using h_env_a 0
  have hA1 : env.get (i₀ + 1) = (populateA B c0 F)[1] := by simpa using h_env_a 1
  have hA2 : env.get (i₀ + 2) = (populateA B c0 F)[2] := by simpa using h_env_a 2
  have hA3 : env.get (i₀ + 3) = (populateA B c0 F)[3] := by simpa using h_env_a 3
  have hcb0 : env.get (i₀ + 4) = (cBits c0)[0] := by simpa using h_env_cb 0
  have hcb1 : env.get (i₀ + 4 + 1) = (cBits c0)[1] := by simpa using h_env_cb 1
  have hcb2 : env.get (i₀ + 4 + 2) = (cBits c0)[2] := by simpa using h_env_cb 2
  have hcb3 : env.get (i₀ + 4 + 3) = (cBits c0)[3] := by simpa using h_env_cb 3
  have hcb4 : env.get (i₀ + 4 + 4) = (cBits c0)[4] := by simpa using h_env_cb 4
  have hcb5 : env.get (i₀ + 4 + 5) = (cBits c0)[5] := by simpa using h_env_cb 5
  have hv0 : env.get (i₀ + 4 + 6) = (vPowers c0)[0] := by simpa using h_env_v 0
  have hv1 : env.get (i₀ + 4 + 6 + 1) = (vPowers c0)[1] := by simpa using h_env_v 1
  have hv2 : env.get (i₀ + 4 + 6 + 2) = (vPowers c0)[2] := by simpa using h_env_v 2
  have hs0 : env.get (i₀ + 4 + 6 + 3) = (shiftU16 c0 F)[0] := by simpa using h_env_s 0
  have hs1 : env.get (i₀ + 4 + 6 + 3 + 1) = (shiftU16 c0 F)[1] := by simpa using h_env_s 1
  have hs2 : env.get (i₀ + 4 + 6 + 3 + 2) = (shiftU16 c0 F)[2] := by simpa using h_env_s 2
  have hs3 : env.get (i₀ + 4 + 6 + 3 + 3) = (shiftU16 c0 F)[3] := by simpa using h_env_s 3
  have hlo0 : env.get (i₀ + 4 + 6 + 3 + 4) = (lowerLimb B c0)[0] := by simpa using h_env_lo 0
  have hlo1 : env.get (i₀ + 4 + 6 + 3 + 4 + 1) = (lowerLimb B c0)[1] := by
    simpa using h_env_lo 1
  have hlo2 : env.get (i₀ + 4 + 6 + 3 + 4 + 2) = (lowerLimb B c0)[2] := by
    simpa using h_env_lo 2
  have hlo3 : env.get (i₀ + 4 + 6 + 3 + 4 + 3) = (lowerLimb B c0)[3] := by
    simpa using h_env_lo 3
  have hhi0 : env.get (i₀ + 4 + 6 + 3 + 4 + 4) = (higherLimb B c0)[0] := by
    simpa using h_env_hi 0
  have hhi1 : env.get (i₀ + 4 + 6 + 3 + 4 + 4 + 1) = (higherLimb B c0)[1] := by
    simpa using h_env_hi 1
  have hhi2 : env.get (i₀ + 4 + 6 + 3 + 4 + 4 + 2) = (higherLimb B c0)[2] := by
    simpa using h_env_hi 2
  have hhi3 : env.get (i₀ + 4 + 6 + 3 + 4 + 4 + 3) = (higherLimb B c0)[3] := by
    simpa using h_env_hi 3
  have hlr0 : env.get (i₀ + 4 + 6 + 3 + 4 + 4 + 4) = (limbResult B c0)[0] := by
    simpa using h_env_lr 0
  have hlr1 : env.get (i₀ + 4 + 6 + 3 + 4 + 4 + 4 + 1) = (limbResult B c0)[1] := by
    simpa using h_env_lr 1
  have hlr2 : env.get (i₀ + 4 + 6 + 3 + 4 + 4 + 4 + 2) = (limbResult B c0)[2] := by
    simpa using h_env_lr 2
  have hlr3 : env.get (i₀ + 4 + 6 + 3 + 4 + 4 + 4 + 3) = (limbResult B c0)[3] := by
    simpa using h_env_lr 3
  have hmsbc : env.get (i₀ + 4 + 6 + 3 + 4 + 4 + 4 + 4) = sllwMsb B c0 F := h_env_msb
  have hfl0 : env.get (i₀ + 4 + 6 + 3 + 4 + 4 + 4 + 4 + 1) = F[0] := by
    simpa using h_env_fl 0
  have hfl1 : env.get (i₀ + 4 + 6 + 3 + 4 + 4 + 4 + 4 + 1 + 1) = F[1] := by
    simpa using h_env_fl 1
  have hfl2 : env.get (i₀ + 4 + 6 + 3 + 4 + 4 + 4 + 4 + 1 + 2)
      = F[1] * input_adapter_imm_c := by
    simpa only [circuit_norm, himm_eval] using h_env_fl 2
  have hsum01 : F[0] + F[1] = 0 ∨ F[0] + F[1] = 1 := by
    rw [← hsum]
    exact hbin
  have hbUw : Word.isU64 B := hbU
  obtain ⟨hc0v, -, -, -⟩ := Word.lt_cases_of_isU64 hcU
  obtain ⟨hcba0, hcba1, hcba2, hcba3, hcba4, hcba5⟩ := cBits_asserts c0
  simp only [← sub_eq_add_neg] at hcba0 hcba1 hcba2 hcba3 hcba4 hcba5
  obtain ⟨hsel0, hsb0, hsel1, hsb1, hsel2, hsb2, hsel3, hsb3, hone⟩ :=
    shiftU16_asserts c0 F hf0 hsum01
  simp only [← sub_eq_add_neg] at hsb0 hsel1 hsb1 hsel2 hsb2 hsel3 hsb3 hone
  obtain ⟨hva0, hva1, hva2⟩ := v_asserts c0
  simp only [← sub_eq_add_neg] at hva0 hva1 hva2
  obtain ⟨hsp0, hsp1, hsp2, hsp3⟩ := split_asserts B c0
  simp only [← sub_eq_add_neg] at hsp0 hsp1 hsp2 hsp3
  obtain ⟨hlra0, hlra1, hlra2, hlra3⟩ := limbResult_asserts B c0
  simp only [← sub_eq_add_neg] at hlra0 hlra1 hlra2 hlra3
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14,
    hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22⟩ :=
    place_asserts B c0 F hf0 hf1 hsum01
  simp only [← sub_eq_add_neg] at hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14
  simp only [← sub_eq_add_neg] at hp15 hp16 hp17 hp18 hp19 hp20 hp21 hp22
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by
    rw [hop_a_0, zero_mul]
  simp +instances only [main, circuit_norm, h_input]
  simp only [hA0, hA1, hA2, hA3, hcb0, hcb1, hcb2, hcb3, hcb4, hcb5, hv0, hv1, hv2,
    hlo0, hlo1, hlo2, hlo3, hhi0, hhi1, hhi2, hhi3, hmsbc, hfl0, hfl1, hfl2,
    hapv_map, hbpv_map, hopc_map, hcpv_map, hpc_map, ec0, epc0, epc1, epc2]
  refine ⟨⟨hbin, h_cpu⟩,
    ⟨⟨fun _ => populateA_val_lt B c0 F hbUw 1 (by norm_num), hf1⟩,
      sllwMsb_bool B c0 F hbUw, fun h1 => ?_⟩,
    ⟨⟨hsum01, hsum01, by simpa only [hsum] using h_clk⟩,
      ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0,
        by rw [← hsum]; exact himmc,
        by rw [← hsum]; exact himmbin,
        hpins,
        by rw [← hsum]; exact hrac_a,
        by rw [← hsum]; exact hrac_b,
        by rw [← hsum]; exact hrac_c,
        by rw [← hsum]; exact hdec,
        by rw [← hsum]; exact fun hr => ⟨ha_prev hr, hbU, (hprev_ab hr).1, (hprev_ab hr).2⟩,
        by rw [← hsum]; exact fun hc => ⟨hcU, hprev_c hc⟩⟩⟩,
    ⟨⟨hsum01, fun _ => ?_, by simpa only [hsum] using h_clk.at_four⟩, trivial⟩,
    by rcases hbin with h | h <;> rw [h] <;> simp,
    by rw [hsum, sub_self],
    by rcases hsum01 with h | h <;> rw [h] <;> simp,
    by rcases hf0 with h | h <;> rw [h] <;> simp,
    by rcases hf1 with h | h <;> rw [h] <;> simp,
    ⟨trivial, by
      simp only [ShiftLeftCore.circuit, ShiftLeftChip.CoreSpec, circuit_norm, Vector.getElem_map,
        Vector.getElem_mapRange, hA0, hA1, hA2, hA3, hcb0, hcb1, hcb2, hcb3, hcb4, hcb5,
        hs0, hs1, hs2, hs3, hlo0, hlo1, hlo2, hlo3, hhi0, hhi1, hhi2, hhi3, hlr0,
        hlr1, hlr2, hlr3]
      exact ⟨hcba0, hcba1, hcba2, hcba3, hcba4, hcba5,
        by simp only [sub_zero]; exact_mod_cast hsel0,
        hsb0, hsel1, hsb1, hsel2, hsb2, hsel3, hsb3, hone,
        by exact_mod_cast hva0, by exact_mod_cast hva1, by exact_mod_cast hva2,
        hsp0, hsp1, hsp2, hsp3,
        hlra0, hlra1, hlra2, hlra3,
        hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14,
        hp15, hp16, hp17, hp18, hp19, hp20, hp21, hp22,
        by simp, hop_a_0⟩⟩,
    fun _ => by
      change ByteRowSpec _
      convert byteRow_e32 c0 hc0v using 2
      rw [sub_eq_add_neg],
    fun _ => by
      change ByteRowSpec _
      convert byteRow_lower B c0 0 (by norm_num) using 2
      rw [sub_eq_add_neg],
    fun _ => by
      change ByteRowSpec _
      convert byteRow_higher B c0 hbUw 0 (by norm_num) using 2,
    fun _ => by
      change ByteRowSpec _
      convert byteRow_lower B c0 1 (by norm_num) using 2
      rw [sub_eq_add_neg],
    fun _ => by
      change ByteRowSpec _
      convert byteRow_higher B c0 hbUw 1 (by norm_num) using 2,
    fun _ => by
      change ByteRowSpec _
      convert byteRow_lower B c0 2 (by norm_num) using 2
      rw [sub_eq_add_neg],
    fun _ => by
      change ByteRowSpec _
      convert byteRow_higher B c0 hbUw 2 (by norm_num) using 2,
    fun _ => by
      change ByteRowSpec _
      convert byteRow_lower B c0 3 (by norm_num) using 2
      rw [sub_eq_add_neg],
    fun _ => by
      change ByteRowSpec _
      convert byteRow_higher B c0 hbUw 3 (by norm_num) using 2⟩
  · rw [show sllwMsb B c0 F = U16MSBOperation.populate_msb (populateA B c0 F)[1] by
      rw [sllwMsb, if_pos h1]]
    exact (U16MSBOperation.spec_populate (populateA_val_lt B c0 F hbUw 1 (by norm_num)) 1).2 rfl
  · refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
      simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm, hA0, hA1, hA2, hA3] <;>
      first
        | exact populateA_val_lt B c0 F hbUw 0 (by norm_num)
        | exact populateA_val_lt B c0 F hbUw 1 (by norm_num)
        | exact populateA_val_lt B c0 F hbUw 2 (by norm_num)
        | exact populateA_val_lt B c0 F hbUw 3 (by norm_num)

/-- Under the row's own constraints, the shallow parent glue
`is_real - (is_sll + is_sllw) = 0` identifies the exposed derived Program gate with the public
`is_real` selector without normalizing any nested arithmetic circuit. -/
theorem isReal_eq_exposedGate (input : Var Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (rowConstraints : ((main input).operations offset).ConstraintsHold env) :
    env input.is_real = env (exposedGate offset) := by
  have shallow := FlatOperation.shallowConstraints_of_constraintsHoldFlat
    (Circuit.constraintsHold_toFlat_iff.mpr rowConstraints)
  have allConstraints := (constraintsHold_shallow_iff_forall_mem.mp shallow).1
  have bindingMem : input.is_real - exposedGate offset ∈
      ((main input).operations offset).shallowConstraints := by
    change input.is_real - exposedGate offset ∈
      input.is_real * (input.is_real - 1) :: (input.is_real - exposedGate offset) :: _
    exact List.mem_cons_of_mem _ List.mem_cons_self
  have binding := allConstraints _ bindingMem
  have bindingZero : env input.is_real - env (exposedGate offset) = 0 := by
    simpa only [eval_sub] using binding
  exact sub_eq_zero.mp bindingZero

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in ShiftLeft's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (exposedGate offset)
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact (`exposedGate offset - imm_c`)-gated source-C pull occupies its declared slot in
ShiftLeft's exposed Memory list. -/
theorem opCPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (exposedGate offset - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- ShiftLeft's exposed channels: the State pair through the canonical `CPUState` child interface,
the Memory-channel closed form above, plus the Program-bus instruction fetch (descended from the
composed `ALUTypeReader`, gate = the reader's literal derived selector sum, opcode = the committed
flag encoding). -/
def stateExposure (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ExposedChannel (ZMod p)) :=
  Readers.CPUState.exposedState
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩ ++
  expose memoryChannel (exposedMemoryInteractions input offset) ++
  expose programChannel
    [ programChannel.pulledIf (exposedGate offset)
        ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], exposedOpcode offset,
         input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
         input.adapter.op_a_0, 0, input.adapter.imm_c⟩ ]

private theorem main_exposedChannelsLawful (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).ExposedChannelsLawful (stateExposure input offset) := by
  unfold Operations.ExposedChannelsLawful
  intro exposed exposedMem
  simp only [stateExposure, Readers.CPUState.exposedState, expose, List.mem_append,
    List.mem_singleton] at exposedMem
  rcases exposedMem with (rfl | rfl) | rfl
  · exact interactionsWith_main_state_eq input offset
  · exact interactionsWith_main_memory_eq input offset
  · exact interactionsWith_main_program_eq input offset

set_option maxHeartbeats 4000000 in
/-- The `ShiftLeft` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `sll`/`sllw` semantic contract;
output is the extracted `ShiftLeftCols` column struct. Soundness is proved (assembled from the two per-op
`Soundness/<Op>.lean` files); the explicitly deferred completeness seam is recorded above. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs ShiftLeftCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    -- `byteChannel` dropped from `channelsWithRequirements` (W11): the nine `gate`-gated byte pulls'
    -- off-gate `Requirements` are discharged locally via the shallow `(is_sll + is_sllw)` boolean gate
    -- (`off_gate_vacuous`), so `byteChannel` can later be *finished* in a Clean `SoundEnsemble`.
    channelsWithRequirements := [memoryChannel.toRaw],
    requirementsChannelsLawful := fun input_var i₀ =>
      requirementsChannelsLawful_main input_var i₀,
    -- W11 (A2): the State pair + Memory closed form + Program fetch, via `stateExposure` above;
    -- lawfulness is the standalone `main_exposedChannelsLawful` (also the axiom-clean seam for
    -- `interactionsWith_memory_eq` below while the completeness seam is open).
    exposedChannels := stateExposure,
    exposedChannels_eq := main_exposedChannelsLawful }

/-- Folded circuit projections used by whole-chip row codecs without unfolding the
proof-bearing `GeneralFormalCircuit` bundle. -/
@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 33 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 33 := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq]

/-- The completed ShiftLeft circuit exposes exactly the Memory interaction list above.  Stated via
the exposure-lawfulness theorem directly (not through `circuit`) so it stays axiom-clean while the
completeness seam is open. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact main_exposedChannelsLawful input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [stateExposure, Readers.CPUState.exposedState, expose])

end SP1Clean.ShiftLeftChip
