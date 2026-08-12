import SP1Clean.Proofs.Chips.ShiftRightChip.Defs
import SP1Clean.Proofs.Chips.ShiftRightChip.Soundness.Srl
import SP1Clean.Proofs.Chips.ShiftRightChip.Soundness.Sra
import SP1Clean.Proofs.Chips.ShiftRightChip.Soundness.Srlw
import SP1Clean.Proofs.Chips.ShiftRightChip.Soundness.Sraw
import SP1Clean.Math.EvalVec
import Clean.Air.Circuit

/-! # `SP1Clean.ShiftRightChip` — contract: soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance + the soundness
`Assumptions` live in the sibling `Defs` module (`Assumptions` there, not here, so the per-op
`Soundness/<Op>.lean` split files can import it without a cycle through `Formal`). This module holds the
`ProverAssumptions`, the soundness/completeness proofs, and the bundled `circuit`.

**Soundness** is assembled here from the four per-conjunct `Soundness/{Srl,Sra,Srlw,Sraw}.lean` files —
each its own `GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy
per-variant proofs compile in parallel — plus the shared `Operations.Requirements` tail (the same in every
variant, reused here from `SoundSrl`). `circuit_proof_start_core` only introduces the binders (no `simp`),
so the sub-theorems' raw `h_holds`/`h_input`/`h_assumptions` binders match directly.

**Completeness** is proven against `main`'s honest `Populate` witness closures (flags via the
`"shift_right_flags"` `ProverHint`), as `ShiftLeftChip`: cells pinned to their populate projections,
constraints closed by the `Populate.lean` value-level bundles, pulls by the populate bound lemmas. The
closures are conformance-checked against SP1's real `generate_trace` in
`TraceGenTests/ShiftRightChipTraceWitness.lean`. -/

namespace SP1Clean.ShiftRightChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

-- `Assumptions` (the soundness operand-`isU64` contract) lives in `Defs` so the per-op
-- `Soundness/<Op>.lean` split files can import it without a cycle through `Formal`.

/-- Prover-side row well-formedness: the register-read `isU64`s, the `is_real` binary selector, the
honest `"shift_right_flags"` hint (each flag binary, the sum = `is_real`), `op_a_0 = 0`, the
immediate-`c` machinery (verbatim `ALUTypeReader.Spec` conjuncts), the CPUState clock bounds, and the
three register-access timestamp `Spec`s (op_c gated `is_real - imm_c`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  Word.isU64 input.adapter.op_b_memory.prev_value ∧
  Word.isU64 input.adapter.op_c_memory.prev_value ∧
  -- (W11 memory flip) the op_a read-prior `isU64`, surfaced by the now-pure-read `ALUTypeReader` `Spec`.
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (f[0] = 0 ∨ f[0] = 1) ∧ (f[1] = 0 ∨ f[1] = 1) ∧
  (f[2] = 0 ∨ f[2] = 1) ∧ (f[3] = 0 ∨ f[3] = 1) ∧
  input.is_real = f[0] + f[1] + f[2] + f[3] ∧
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
  -- pulled prior record. These bounds are trace facts supplied by the honest prover; soundness derives
  -- them from the balanced Memory channel and never assumes them locally. The op_c pull is absent for
  -- an immediate, hence its narrower `is_real - imm_c` gate.
  (input.is_real = 1 →
    input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24) ∧
  (input.is_real - input.adapter.imm_c = 1 →
    input.adapter.op_c_memory.access_timestamp.prev_low.val < 2 ^ 24)

/-- **Soundness.** The flag-gated RV64 `srl`/`sra`/`srlw`/`sraw` identities on the result column `cols.a`.
**Pieced together** from the four per-conjunct `Soundness/{Srl,Sra,Srlw,Sraw}.lean` files — each its own
`GeneralFormalCircuit.Soundness` over a single-conjunct `Spec`, split out so the heavy per-variant proofs
compile in parallel — plus the shared `Operations.Requirements` tail (the same in every variant, reused
here from `SoundSrl`). `circuit_proof_start_core` only introduces the binders (no `simp`), so the
sub-theorems' raw `h_holds`/`h_input`/`h_assumptions` binders match directly.

The former 4M ceiling was ~100× over: the four per-conjunct proofs carry the cost in their own modules,
so this assembly clears ≤40000 against the plain default. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start_core
  refine ⟨fun hr => ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (SoundSrl.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSra.soundness  i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSrlw.soundness i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSraw.soundness i₀ env input_var input h_input h_assumptions h_holds).1 hr
  · exact (SoundSrl.soundness  i₀ env input_var input h_input h_assumptions h_holds).2

/-- Completeness: `main`'s honest `Populate` witness closures (flags from the `"shift_right_flags"`
hint) satisfy every constraint under `ProverAssumptions`. -/
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start_core
  simp +instances only [circuit_norm] at h_input
  provable_struct_simp
  obtain ⟨hbU, hcU, ha_prev, hbin, hf0, hf1, hf2, hf3, hsum, hop_a_0, himmc, himmbin, hpins, h_cpu,
    hrac_a, hrac_b, hrac_c, hdec, hprev_ab, hprev_c⟩ := h_assumptions
  simp only [circuit_norm] at hbU hcU ha_prev hbin hsum hop_a_0 himmc himmbin hpins h_cpu
  simp only [circuit_norm] at hrac_a hrac_b hrac_c hdec hprev_ab hprev_c
  -- SC Phase 2pre: the GFC `ALUTypeReader` (composed via `let _ ←`, after the 11 `witnessVector`s)
  -- appends its honest-witness/completeness conjunct to `h_env` as the trailing `h_env_alu`.
  -- (SC Phase 2c) the composed `CPUState` GFC now pushes its `StateTruth` guarantee, so its
  -- completeness-provided facts are the (discarded) prepended component of `h_env`.
  obtain ⟨-, h_env_a, h_env_bmsb, h_env_srwmsb, h_env_cb, h_env_sram, h_env_v, h_env_lo, h_env_hi,
    h_env_lr, h_env_s, h_env_fl, -⟩ := h_env
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  -- project (not destructure — rcases on `h_input` disturbs the bound `h_env_*` hypotheses)
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
  have heb1 := heb 1 (by norm_num); have heb3 := heb 3 (by norm_num)
  have epc0 : Expression.eval env.toEnvironment input_var_state_pc[0] = input_state_pc[0] := by
    rw [ProvableType.getElem_eval_fields, hpc]
  have epc1 : Expression.eval env.toEnvironment input_var_state_pc[1] = input_state_pc[1] := by
    rw [ProvableType.getElem_eval_fields, hpc]
  have epc2 : Expression.eval env.toEnvironment input_var_state_pc[2] = input_state_pc[2] := by
    rw [ProvableType.getElem_eval_fields, hpc]
  simp only [circuit_norm] at h_env_a h_env_bmsb h_env_srwmsb h_env_cb h_env_sram h_env_v
  simp only [circuit_norm] at h_env_lo h_env_hi h_env_lr h_env_s h_env_fl
  simp only [vec4_eval, hbpv_map, ec0] at h_env_a h_env_bmsb h_env_srwmsb h_env_cb h_env_sram h_env_v
  simp only [vec4_eval, hbpv_map, ec0] at h_env_lo h_env_hi h_env_lr h_env_s
  set B := input_adapter_op_b_memory_prev_value with hB
  set c0 := input_adapter_op_c_memory_prev_value[0] with hc0
  set F := hintFlags env.hint with hF
  have hA0 : env.get i₀ = (populateA B c0 F)[0] := by simpa using h_env_a 0
  have hA1 : env.get (i₀ + 1) = (populateA B c0 F)[1] := by simpa using h_env_a 1
  have hA2 : env.get (i₀ + 2) = (populateA B c0 F)[2] := by simpa using h_env_a 2
  have hA3 : env.get (i₀ + 3) = (populateA B c0 F)[3] := by simpa using h_env_a 3
  have hbm : env.get (i₀ + 4) = bMsb B F := by simpa using h_env_bmsb
  have hsw : env.get (i₀ + 4 + 1) = srwMsb B c0 F := by simpa using h_env_srwmsb
  have hcb0 : env.get (i₀ + 4 + 1 + 1) = (ShiftLeftChip.cBits c0)[0] := by simpa using h_env_cb 0
  have hcb1 : env.get (i₀ + 4 + 1 + 1 + 1) = (ShiftLeftChip.cBits c0)[1] := by
    simpa using h_env_cb 1
  have hcb2 : env.get (i₀ + 4 + 1 + 1 + 2) = (ShiftLeftChip.cBits c0)[2] := by
    simpa using h_env_cb 2
  have hcb3 : env.get (i₀ + 4 + 1 + 1 + 3) = (ShiftLeftChip.cBits c0)[3] := by
    simpa using h_env_cb 3
  have hcb4 : env.get (i₀ + 4 + 1 + 1 + 4) = (ShiftLeftChip.cBits c0)[4] := by
    simpa using h_env_cb 4
  have hcb5 : env.get (i₀ + 4 + 1 + 1 + 5) = (ShiftLeftChip.cBits c0)[5] := by
    simpa using h_env_cb 5
  have hsram : env.get (i₀ + 4 + 1 + 1 + 6) = sraMsbV0123 B c0 F := by simpa using h_env_sram
  have hv0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1) = (vPowersInv c0)[0] := by simpa using h_env_v 0
  have hv1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 1) = (vPowersInv c0)[1] := by
    simpa using h_env_v 1
  have hv2 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 2) = (vPowersInv c0)[2] := by
    simpa using h_env_v 2
  have hlo0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3) = (lowerLimb B c0 F)[0] := by
    simpa using h_env_lo 0
  have hlo1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 1) = (lowerLimb B c0 F)[1] := by
    simpa using h_env_lo 1
  have hlo2 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 2) = (lowerLimb B c0 F)[2] := by
    simpa using h_env_lo 2
  have hlo3 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 3) = (lowerLimb B c0 F)[3] := by
    simpa using h_env_lo 3
  have hhi0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4) = (higherLimb B c0 F)[0] := by
    simpa using h_env_hi 0
  have hhi1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 1) = (higherLimb B c0 F)[1] := by
    simpa using h_env_hi 1
  have hhi2 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 2) = (higherLimb B c0 F)[2] := by
    simpa using h_env_hi 2
  have hhi3 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 3) = (higherLimb B c0 F)[3] := by
    simpa using h_env_hi 3
  have hlr0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4) = (limbResult B c0 F)[0] := by
    simpa using h_env_lr 0
  have hlr1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 1) = (limbResult B c0 F)[1] := by
    simpa using h_env_lr 1
  have hlr2 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 2) = (limbResult B c0 F)[2] := by
    simpa using h_env_lr 2
  have hlr3 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 3) = (limbResult B c0 F)[3] := by
    simpa using h_env_lr 3
  have hs0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4) = (shiftU16 c0 F)[0] := by
    simpa using h_env_s 0
  have hs1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 1) = (shiftU16 c0 F)[1] := by
    simpa using h_env_s 1
  have hs2 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 2) = (shiftU16 c0 F)[2] := by
    simpa using h_env_s 2
  have hs3 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 3) = (shiftU16 c0 F)[3] := by
    simpa using h_env_s 3
  have hfl0 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4) = F[0] := by
    simpa using h_env_fl 0
  have hfl1 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 1) = F[1] := by
    simpa using h_env_fl 1
  have hfl2 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 2) = F[2] := by
    simpa using h_env_fl 2
  have hfl3 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 3) = F[3] := by
    simpa using h_env_fl 3
  have hfl4 : env.get (i₀ + 4 + 1 + 1 + 6 + 1 + 3 + 4 + 4 + 4 + 4 + 4)
      = (F[2] + F[3]) * input_adapter_imm_c := by
    simpa only [circuit_norm, himm_eval] using h_env_fl 4
  have hsum01 : F[0] + F[1] + F[2] + F[3] = 0 ∨ F[0] + F[1] + F[2] + F[3] = 1 := by
    rw [← hsum]; exact hbin
  obtain ⟨hc0v, -, -, -⟩ := Word.lt_cases_of_isU64 hcU
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  simp +instances only [main, circuit_norm, h_input]
  simp only [hA0, hA1, hA2, hA3, hbm, hsw, hcb0, hcb1, hcb2, hcb3, hcb4, hcb5, hsram, hv0, hv1,
    hv2, hlo0, hlo1, hlo2, hlo3, hhi0, hhi1, hhi2, hhi3,
    hfl0, hfl1, hfl2, hfl3, hfl4, hapv_map, hbpv_map, hopc_map, hcpv_map, hpc_map,
    heb1, heb3, ec0, epc0, epc1, epc2]
  have hbUw : Word.isU64 B := hbU
  obtain ⟨hbU0, hbU1, hbU2, hbU3⟩ := Word.lt_cases_of_isU64 hbUw
  obtain ⟨ho0, ho1, ho2, ho3⟩ := one_hot_resolve F hf0 hf1 hf2 hf3 hsum01
  have he14 : F[0] + F[1] = 0 ∨ F[0] + F[1] = 1 := by
    rcases hf0 with h0 | h0
    · rcases hf1 with h1 | h1
      · left; rw [h0, h1, add_zero]
      · right; rw [h0, h1, zero_add]
    · obtain ⟨h1z, -, -⟩ := ho0 h0
      right; rw [h0, h1z, add_zero]
  have he13 : F[2] + F[3] = 0 ∨ F[2] + F[3] = 1 := by
    rcases hf2 with h2 | h2
    · rcases hf3 with h3 | h3
      · left; rw [h2, h3, add_zero]
      · right; rw [h2, h3, zero_add]
    · obtain ⟨-, -, h3z⟩ := ho2 h2
      right; rw [h2, h3z, add_zero]
  have hbmB := bMsb_bool B F hbUw hf1 hf3 (fun h => (ho1 h).2.2)
  obtain ⟨hcba0, hcba1, hcba2, hcba3, hcba4, hcba5⟩ := ShiftLeftChip.cBits_asserts c0
  simp only [← sub_eq_add_neg] at hcba0 hcba1 hcba2 hcba3 hcba4 hcba5
  obtain ⟨hsel0, hsb0, hsel1, hsb1, hsel2, hsb2, hsel3, hsb3, hone⟩ :=
    shiftU16_asserts c0 F he14 hsum01
  simp only [← sub_eq_add_neg] at hsb0 hsel1 hsb1 hsel2 hsb2 hsel3 hsb3 hone
  obtain ⟨hva0, hva1, hva2⟩ := vInv_asserts c0
  simp only [← sub_eq_add_neg] at hva0 hva1 hva2
  obtain ⟨hsp0, hsp1, hsp2, hsp3⟩ := split_asserts B c0 F
  simp only [← sub_eq_add_neg] at hsp0 hsp1 hsp2 hsp3
  obtain ⟨hlra0, hlra1, hlra2, hlra3⟩ := limbResult_asserts B c0 F
  simp only [← sub_eq_add_neg] at hlra0 hlra1 hlra2 hlra3
  obtain ⟨hmsb1, hmsb2, hmsb3⟩ := msb_asserts B c0 F hf0 hf1 hf2 hf3 hsum01
  simp only [← sub_eq_add_neg] at hmsb2 hmsb3
  obtain ⟨hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15,
    hp16, hp17, hp18, hp19, hp20, hp21, hp22⟩ := place_asserts B c0 F hf0 hf1 hf2 hf3 hsum01
  simp only [← sub_eq_add_neg] at hp1 hp2 hp3 hp4 hp5 hp6 hp7 hp8 hp9 hp10 hp11 hp12 hp13 hp14 hp15
  simp only [← sub_eq_add_neg] at hp16 hp17 hp18 hp19 hp20 hp21 hp22
  refine ⟨⟨hbin, h_cpu⟩,
    ⟨⟨fun _ => hbU3, hf1⟩,
      hbmB, fun h1 => ?_⟩,
    ⟨⟨fun _ => hbU1, hf3⟩,
      hbmB, fun h3 => ?_⟩,
    ⟨⟨fun _ => populateA_val_lt B c0 F hbUw hf0 hf1 hf2 hf3 hsum01 1 (by norm_num), he13⟩,
      srwMsb_bool B c0 F hbUw hf0 hf1 hf2 hf3 hsum01, fun h13 => ?_⟩,
    ⟨⟨hbin, hbin, h_clk⟩, ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, himmc, himmbin, hpins,
      hrac_a, hrac_b, hrac_c, hdec,
      fun hr => ⟨ha_prev hr, hbU, (hprev_ab hr).1, (hprev_ab hr).2⟩,
      fun hc => ⟨hcU, hprev_c hc⟩⟩⟩,
    -- (W11 Option B) the op_a write `RegisterWrite` block: gate `sum` binary + the witnessed result `a`
    -- (`populateA`) is `U64` (`populateA_val_lt`, unconditional under the prover assumptions).
    ⟨⟨hsum01, fun _ => ?_, by simpa only [hsum] using h_clk.at_four⟩, trivial⟩,
    by rcases hbin with h | h <;> rw [h] <;> simp,
    by rw [hsum, sub_self],
    by rcases hf0 with h | h <;> rw [h] <;> simp,
    by rcases hf1 with h | h <;> rw [h] <;> simp,
    by rcases hf2 with h | h <;> rw [h] <;> simp,
    by rcases hf3 with h | h <;> rw [h] <;> simp,
    by rcases hsum01 with h | h <;> rw [h] <;> simp,
    ⟨trivial, by
      simp only [ShiftRightCore.circuit, ShiftRightChip.CoreSpec, circuit_norm, Vector.getElem_map,
        Vector.getElem_mapRange, hA0, hA1, hA2, hA3, hcb0, hcb1, hcb2, hcb3, hcb4, hcb5,
        hlo0, hlo1, hlo2, hlo3, hhi0, hhi1, hhi2, hhi3, hlr0, hlr1, hlr2, hlr3,
        hs0, hs1, hs2, hs3]
      exact ⟨by simp,
        hcba0, hcba1, hcba2, hcba3, hcba4, hcba5,
        by simp only [sub_zero]; exact_mod_cast hsel0,
        hsb0, hsel1, hsb1, hsel2, hsb2, hsel3, hsb3, hone,
        by exact_mod_cast hva0, by exact_mod_cast hva1, by exact_mod_cast hva2,
        hsp0, hsp1, hsp2, hsp3,
        hlra0, hlra1, hlra2, hlra3,
        hmsb1, hmsb2, hmsb3,
        hp1, hp2, hp3, hp4, hp5, hp6, hp7, hp8, hp9, hp10, hp11, hp12, hp13, hp14, hp15,
        hp16, hp17, hp18, hp19, hp20, hp21, hp22,
        hop_a_0⟩⟩,
    fun _ => by
      change ByteRowSpec _; convert ShiftLeftChip.byteRow_e32 c0 hc0v using 2; rw [sub_eq_add_neg],
    fun _ => by change ByteRowSpec _; convert byteRow_lower B c0 F 0 (by norm_num) using 2,
    fun _ => by
      change ByteRowSpec _; convert byteRow_higher B c0 F hbUw he14 0 (by norm_num) using 2
      rw [sub_eq_add_neg],
    fun _ => by change ByteRowSpec _; convert byteRow_lower B c0 F 1 (by norm_num) using 2,
    fun _ => by
      change ByteRowSpec _; convert byteRow_higher B c0 F hbUw he14 1 (by norm_num) using 2
      rw [sub_eq_add_neg],
    fun _ => by change ByteRowSpec _; convert byteRow_lower B c0 F 2 (by norm_num) using 2,
    fun _ => by
      change ByteRowSpec _; convert byteRow_higher B c0 F hbUw he14 2 (by norm_num) using 2
      rw [sub_eq_add_neg],
    fun _ => by change ByteRowSpec _; convert byteRow_lower B c0 F 3 (by norm_num) using 2,
    fun _ => by
      change ByteRowSpec _; convert byteRow_higher B c0 F hbUw he14 3 (by norm_num) using 2
      rw [sub_eq_add_neg]⟩
  · -- SRA: the sign witness is the high bit of `B[3]`
    rw [bMsb_eq_sra B F h1 (ho1 h1).2.2]
    exact (U16MSBOperation.spec_populate hbU3 1).2 rfl
  · -- SRAW: the sign witness is the high bit of `B[1]`
    rw [bMsb_eq_sraw B F h3 (ho3 h3).2.1]
    exact (U16MSBOperation.spec_populate hbU1 1).2 rfl
  · -- the word-variant sign witness is the high bit of the placed `a[1]`
    rw [show srwMsb B c0 F = U16MSBOperation.populate_msb (populateA B c0 F)[1] by
      rw [srwMsb, if_pos h13]]
    exact (U16MSBOperation.spec_populate
      (populateA_val_lt B c0 F hbUw hf0 hf1 hf2 hf3 hsum01 1 (by norm_num)) 1).2 rfl
  · -- `RegisterWrite` write value `a = populateA` is `U64` (each limb `< 2^16`, `populateA_val_lt`).
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
      simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm, hA0, hA1, hA2, hA3]
    · exact populateA_val_lt B c0 F hbUw hf0 hf1 hf2 hf3 hsum01 0 (by norm_num)
    · exact populateA_val_lt B c0 F hbUw hf0 hf1 hf2 hf3 hsum01 1 (by norm_num)
    · exact populateA_val_lt B c0 F hbUw hf0 hf1 hf2 hf3 hsum01 2 (by norm_num)
    · exact populateA_val_lt B c0 F hbUw hf0 hf1 hf2 hf3 hsum01 3 (by norm_num)

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in ShiftRight's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact (`is_real - imm_c`)-gated source-C pull occupies its declared slot in ShiftRight's
exposed Memory list. -/
theorem opCPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- ShiftRight's exposed channels: the State pair through the canonical `CPUState` child interface,
the Memory-channel closed form above, plus the Program-bus instruction fetch (descended from the
composed `ALUTypeReader`, gate `is_trusted = is_real`, opcode = the committed flag encoding). -/
def stateExposure (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ExposedChannel (ZMod p)) :=
  Readers.CPUState.exposedState
    ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      8, input.is_real⟩ ++
  expose memoryChannel (exposedMemoryInteractions input offset) ++
  expose programChannel (exposedProgramInteractions input offset)

private theorem main_stateInteractions_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith stateChannel.toRaw =
      (Readers.CPUState.stateInteractions
        ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
          8, input.is_real⟩).map ChannelInteraction.toRaw := by
  exact interactionsWith_main_state_eq input offset

/-- The ALU-type reader's five Memory interactions and `RegisterWrite`'s write push are the only
Memory interactions in `main`. Kept as its own opaque declaration to avoid a kernel proof-size cliff
when the three exposed-channel calculations are combined. -/
private theorem main_memoryInteractions_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact interactionsWith_main_memory_eq input offset

private theorem main_programInteractions_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith programChannel.toRaw =
      (exposedProgramInteractions input offset).map ChannelInteraction.toRaw := by
  exact interactionsWith_main_program_eq input offset

/-- The three channel calculations are opaque declarations above. This dispatcher therefore stays
small enough for the kernel to check without re-materializing all three expanded `main` proofs in one
term. -/
private theorem main_exposedChannelsLawful (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).ExposedChannelsLawful (stateExposure input offset) := by
  unfold Operations.ExposedChannelsLawful
  intro exposed exposedMem
  simp only [stateExposure, Readers.CPUState.exposedState, expose, List.mem_append,
    List.mem_singleton] at exposedMem
  rcases exposedMem with (rfl | rfl) | rfl
  · exact main_stateInteractions_eq input offset
  · exact main_memoryInteractions_eq input offset
  · exact main_programInteractions_eq input offset

/-- The `ShiftRight` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `srl`/`sra`/`srlw`/`sraw`
semantic contract; output is the native `Columns` row struct. Soundness is proved (assembled
from the four per-op `Soundness/<Op>.lean` files); completeness is proved above (the former
deferred seam is closed).

The former 4M ceiling was ~100× over: every field here is a reference to an already-elaborated theorem,
so the bundle clears ≤40000 against the plain default. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    -- `byteChannel` dropped from `channelsWithRequirements` (W11): the nine `gate`-gated byte pulls'
    -- off-gate `Requirements` are discharged locally via the shallow `sum` boolean gate
    -- (`off_gate_vacuous`), so `byteChannel` can later be *finished* in a Clean `SoundEnsemble`.
    channelsWithRequirements := [memoryChannel.toRaw],
    requirementsChannelsLawful := fun input_var i₀ =>
      requirementsChannelsLawful_main input_var i₀,
    -- W11 (A2): the State pair + Memory closed form + Program fetch, via `stateExposure` above;
    -- lawfulness is the standalone `main_exposedChannelsLawful` (which also backs
    -- `interactionsWith_memory_eq` below directly).
    exposedChannels := stateExposure,
    exposedChannels_eq := main_exposedChannelsLawful }

/-- Folded circuit projections used by whole-chip row codecs. -/
@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 37 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 37 := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq]

/-- The completed ShiftRight circuit exposes exactly the Memory interaction list above.  Stated via
the exposure-lawfulness theorem directly (not through `circuit`), keeping it independent of the
proof-bearing bundle. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact main_exposedChannelsLawful input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [stateExposure, Readers.CPUState.exposedState, expose])

end SP1Clean.ShiftRightChip
