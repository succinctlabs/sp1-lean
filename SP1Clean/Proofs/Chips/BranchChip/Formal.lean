import SP1Clean.Native.Chips.BranchChip.Defs
import SP1Clean.Proofs.Chips.BranchChip.Decision

/-! # `SP1Clean.BranchChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.BranchChip

open Circuit
open Extracted (BranchColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Operands `isU64`; `is_real`/flag/`is_branching`-binary are proven from the gates. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (#v[input.adapter.op_a_memory.prev_value[0], input.adapter.op_a_memory.prev_value[1],
    input.adapter.op_a_memory.prev_value[2], input.adapter.op_a_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64 (#v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
    input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p))

/-- Honest prover-side row well-formedness. The immediate + rs1/rs2 + pc words `isU64`, `is_real` binary,
the CPUState clock bounds + op_a/op_b register-access timestamp bounds, the two targets fitting in 48 bits
(`value[3] = 0`), and the `is_real`-gated next_pc 4-byte alignment + u16 limb ranges. -/
def ProverAssumptions (input : Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  let br := hintBranching hint
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (rs1WordInput input) ∧
  Word.isU64 (rs2WordInput input) ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := input.state.pc, clk_inc := 8, is_real := input.is_real } ∧
  Readers.ITypeReaderImmutable.Spec
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc, 0⟩ ∧
  (branchTargetWord input)[3] = 0 ∧
  (fallThroughWord input)[3] = 0 ∧
  (f[0] = 0 ∨ f[0] = 1) ∧ (f[1] = 0 ∨ f[1] = 1) ∧ (f[2] = 0 ∨ f[2] = 1) ∧
  (f[3] = 0 ∨ f[3] = 1) ∧ (f[4] = 0 ∨ f[4] = 1) ∧ (f[5] = 0 ∨ f[5] = 1) ∧
  (input.is_real = f[0] + f[1] + f[2] + f[3] + f[4] + f[5]) ∧
  -- honest `is_branching`: binary, zero on padding, and (on real rows) the per-opcode branch-taken
  -- decision as a pure function of the source words (mirrors `Spec`'s six-way condition).
  (br = 0 ∨ br = 1) ∧
  (input.is_real = 0 → br = 0) ∧
  (input.is_real = 1 →
    (f[0] = 1 → (br = 1 ↔
      Word.toBitVec64 (rs1WordInput input) = Word.toBitVec64 (rs2WordInput input))) ∧
    (f[1] = 1 → (br = 1 ↔
      Word.toBitVec64 (rs1WordInput input) ≠ Word.toBitVec64 (rs2WordInput input))) ∧
    (f[2] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).slt (Word.toBitVec64 (rs2WordInput input)) = true)) ∧
    (f[3] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).slt (Word.toBitVec64 (rs2WordInput input)) = false)) ∧
    (f[4] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).ult (Word.toBitVec64 (rs2WordInput input)) = true)) ∧
    (f[5] = 1 → (br = 1 ↔
      (Word.toBitVec64 (rs1WordInput input)).ult (Word.toBitVec64 (rs2WordInput input)) = false))) ∧
  -- the `is_real`-gated committed `next_pc` byte ranges (4-byte-aligned low limb + two u16 limbs).
  (input.is_real = 1 →
    ((committedNextPc input br)[0] * (4 : ZMod p)⁻¹).val < 2 ^ 14 ∧
    (committedNextPc input br)[1].val < 2 ^ 16 ∧
    (committedNextPc input br)[2].val < 2 ^ 16) ∧
  -- SC Phase 2c: the honest prover supplies the State pull's `StateTruth`.
  (input.is_real = 1 → SP1Clean.Semantics.StateTruth (Readers.CPUState.stateMsgOf input.state) data) ∧
  -- SC Phase 2a: the honest prover supplies the Program pull's `ProgTruth`. The immutable I-type reader
  -- carries the branch opcode as the one-hot-weighted flag sum (`f[i] * (40+i)`, mirroring `main`'s
  -- `opcode` let); `progMsgOf` copies the reader input verbatim (op_a is a source read).
  (input.is_real = 1 → SP1Clean.Semantics.ProgTruth
    (Readers.ITypeReaderImmutable.progMsgOf
      ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
        input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
        f[0] * 40 + f[1] * 41 + f[2] * 42 + f[3] * 43 + f[4] * 44 + f[5] * 45⟩) data)

-- The binary-element algebra (`zero_ne_one'`, `val_of_bool`, `one_hot6`) and the six-way decision
-- dispatch (`branch_conditions_of_decision_eq` / `branch_decision_eq_of_conditions`) live in the
-- sibling `Decision` module, so the heavy one-hot case analysis is elaborated once, in a small
-- context, rather than twice under the giant chip goal here.

set_option maxHeartbeats 8000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_imm, h_rs1U, h_rs2U, h_pcU⟩ := h_assumptions
  obtain ⟨h_lt, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_realsum, h_sumbin, h_isbr_bin,
    h_isbr, h_pad, h_cpustate, h_add1, h_add1z, h_add2, h_add2z, h_pc0, h_pc1, h_pc2, h_itype,
    h_byte1, h_byte2, h_byte3⟩ := h_holds
  obtain ⟨_h_ir, ⟨_h_ckh, _h_ck1, _h_ck0, hpc⟩, _h_a, ⟨h_amem_pv, _, _⟩, _h_a0, _h_b,
    ⟨h_bmem_pv, _, _⟩, hcimm⟩ := h_input
  -- the `is_real = Σ flags` gate is now the shallow `assertZero (is_real - sum)`; recover the eq form.
  replace h_realsum := add_neg_eq_zero.mp h_realsum
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := by
    rw [h_realsum]; exact bool_of_mul_pred h_sumbin
  have hbeq := bool_of_mul_pred h_beq
  have hbne := bool_of_mul_pred h_bne
  have hblt := bool_of_mul_pred h_blt
  have hbge := bool_of_mul_pred h_bge
  have hbltu := bool_of_mul_pred h_bltu
  have hbgeu := bool_of_mul_pred h_bgeu
  have hisbr := bool_of_mul_pred h_isbr_bin
  have hrs1eq : (#v[Expression.eval env input_var_adapter_op_a_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_a_memory_prev_value[0], input_adapter_op_a_memory_prev_value[1],
        input_adapter_op_a_memory_prev_value[2], input_adapter_op_a_memory_prev_value[3]] := by
    rw [← h_amem_pv]; simp only [Vector.getElem_map]
  have hrs2eq : (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] := by
    rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have hrs1U : Word.isU64 (#v[Expression.eval env input_var_adapter_op_a_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_a_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs1eq ▸ h_rs1U
  have hrs2U : Word.isU64 (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs2eq ▸ h_rs2U
  have hpceq : (#v[Expression.eval env input_var_state_pc[0], Expression.eval env input_var_state_pc[1],
      Expression.eval env input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have hpcU : Word.isU64 (#v[Expression.eval env input_var_state_pc[0],
      Expression.eval env input_var_state_pc[1], Expression.eval env input_var_state_pc[2], 0]
        : Word (ZMod p)) := hpceq ▸ h_pcU
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := Word.isU64_four
  have h_onehot := one_hot6 hbeq hbne hblt hbge hbltu hbgeu h_sumbin
  have h_sig_bin : env.get (i₀ + 2) + env.get (i₀ + 3) = 0 ∨ env.get (i₀ + 2) + env.get (i₀ + 3) = 1 := by
    rcases hblt with hl | hl <;> rcases hbge with hg | hg
    · left; rw [hl, hg]; simp
    · right; rw [hl, hg]; simp
    · right; rw [hl, hg]; simp
    · exfalso
      have := val_of_bool (h := hbeq); have := val_of_bool (h := hbne)
      have := val_of_bool (h := hbltu); have := val_of_bool (h := hbgeu)
      haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
      rw [hl, hg, ZMod.val_one] at h_onehot
      omega
  refine ⟨⟨?_, h_bin, ⟨hbeq, hbne, hblt, hbge, hbltu, hbgeu, hisbr⟩, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact h_itype ⟨h_bin, h_bin⟩
  · intro hr1 hbr1
    have hav := (h_add1 ⟨fun _ => ⟨hpcU, h_imm⟩, hisbr⟩ hbr1).2
    rw [hpceq] at hav
    have hn0 : env.get (i₀ + 6 + 1 + 4 + 4) = env.get (i₀ + 6 + 1) := by
      rw [h_pc0, hbr1, hr1]; ring
    have hn1 : env.get (i₀ + 6 + 1 + 4 + 4 + 1) = env.get (i₀ + 6 + 1 + 1) := by
      rw [h_pc1, hbr1, hr1]; ring
    have hn2 : env.get (i₀ + 6 + 1 + 4 + 4 + 2) = env.get (i₀ + 6 + 1 + 2) := by
      rw [h_pc2, hbr1, hr1]; ring
    rw [show Word.toBitVec64
          (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 6 + 1 + i }))
        = Word.toBitVec64
          (#v[env.get (i₀ + 6 + 1 + 4 + 4), env.get (i₀ + 6 + 1 + 4 + 4 + 1),
            env.get (i₀ + 6 + 1 + 4 + 4 + 2), 0] : Word (ZMod p)) from by
        congr 1; apply Vector.ext; intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        interval_cases i
        · exact hn0.symm
        · exact hn1.symm
        · exact hn2.symm
        · exact h_add1z] at hav
    simp only [nextPcWord, pcWord, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    exact hav
  · intro hr1 hbr0
    have hgate1 : input_is_real + -env.get (i₀ + 6) = 1 := by rw [hr1, hbr0]; ring
    have hav := (h_add2 ⟨fun _ => ⟨hpcU, h4U⟩, Or.inr hgate1⟩ hgate1).2
    rw [hpceq] at hav
    have hn0 : env.get (i₀ + 6 + 1 + 4 + 4) = env.get (i₀ + 6 + 1 + 4) := by
      rw [h_pc0, hbr0, hr1]; ring
    have hn1 : env.get (i₀ + 6 + 1 + 4 + 4 + 1) = env.get (i₀ + 6 + 1 + 4 + 1) := by
      rw [h_pc1, hbr0, hr1]; ring
    have hn2 : env.get (i₀ + 6 + 1 + 4 + 4 + 2) = env.get (i₀ + 6 + 1 + 4 + 2) := by
      rw [h_pc2, hbr0, hr1]; ring
    rw [show Word.toBitVec64
          (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 6 + 1 + 4 + i }))
        = Word.toBitVec64
          (#v[env.get (i₀ + 6 + 1 + 4 + 4), env.get (i₀ + 6 + 1 + 4 + 4 + 1),
            env.get (i₀ + 6 + 1 + 4 + 4 + 2), 0] : Word (ZMod p)) from by
        congr 1; apply Vector.ext; intro i hi
        simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        interval_cases i
        · exact hn0.symm
        · exact hn1.symm
        · exact hn2.symm
        · exact h_add2z] at hav
    simp only [nextPcWord, pcWord, Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    exact hav
  · intro hr1
    have h_lt_spec := LtOperationSigned.result_semantic hrs1U hrs2U hr1
      (h_lt ⟨hrs1U, hrs2U, h_bin, h_sig_bin⟩)
    obtain ⟨h_bit, h_eqf, -⟩ := h_lt_spec
    -- `result_semantic` returns the bit/flags through the (unreduced) `Inputs`-constructor projections;
    -- `circuit_norm` reduces them to the `env.get`/`mapRange` form that `h_isbr`/the `Decision` lemma use.
    simp only [circuit_norm] at h_bit h_eqf
    rw [hrs1eq, hrs2eq] at h_bit h_eqf
    -- `simp only [id_eq]` strips the `id (ZMod p)` field-type wrapper off the gate so it unifies
    -- with the `Decision` lemma's plain-`ZMod p` equation (the `id` blocks `linear_combination`'s
    -- ring synthesis — see PROOF_PATTERNS).
    rw [hr1, one_mul] at h_isbr
    simp only [id_eq] at h_isbr
    have hone : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
        + env.get (i₀ + 4) + env.get (i₀ + 5) = 1 := by rw [← h_realsum]; exact hr1
    simp only [rs1Word, rs2Word]
    exact branch_conditions_of_decision_eq h_rs1U h_rs2U hbeq hbne hblt hbge hbltu hbgeu hisbr hone
      h_bit h_eqf (by simp only [branchDecision]; linear_combination h_isbr)
  · -- 4-byte alignment of the branch target's low limb, from the in-circuit `÷4` byte-range pull
    -- `h_byte1` (`(next_pc[0] · 4⁻¹).val < 2^14 ⇒ next_pc[0].val % 4 = 0`). Lifted to the whole word
    -- at the Sail bridge. Mirrors `JalChip.soundness`.
    intro hr1
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := by norm_cast
    have hguar := h_byte1 (by rw [hr1])
    simp only [byteChannel] at hguar
    rw [← c14] at hguar
    exact val_mod_four_of_mul_inv_four_lt ((byteRowSpec_range _ h14p).mp hguar)
  · refine ⟨Or.inr ⟨hrs1U, hrs2U, h_bin, h_sig_bin⟩, h_bin, Or.inr ⟨fun _ => ⟨hpcU, h_imm⟩, hisbr⟩,
      Or.inr ⟨fun _ => ⟨hpcU, h4U⟩, ?_⟩, Or.inr ⟨h_bin, h_bin⟩,
      fun h1 h0 => off_gate_vacuous h_bin h1 h0, fun h1 h0 => off_gate_vacuous h_bin h1 h0,
      fun h1 h0 => off_gate_vacuous h_bin h1 h0⟩
    -- AddOp2 gate `is_real - is_branching` is binary: on padding `is_branching = 0` from `h_pad`.
    rcases h_bin with h0 | h1
    · have hbr0 : env.get (i₀ + 6) = 0 := by
        have hh : (input_is_real + -1) * env.get (i₀ + 6) = 0 := h_pad
        rw [h0] at hh
        linear_combination -hh
      left; rw [h0, hbr0]; simp
    · rcases hisbr with hb0 | hb1
      · right; rw [h1, hb0]; simp
      · left; rw [h1, hb1]; simp

set_option maxHeartbeats 4000000 in
/-- Completeness via honest `ProverHint` flag witnesses (`hintFlags`/`hintBranching`). The six-way
decision constraint is discharged by mirroring soundness's case analysis in reverse via `Decision`. -/
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_imm, h_rs1U, h_rs2U, h_pcU, h_bin, h_cpu, h_it, h_bt3, h_ft3,
    hf0, hf1, hf2, hf3, hf4, hf5, h_realsum, h_brbin, h_brpad, h_dec, h_ranges, h_st, h_prog⟩ :=
    h_assumptions
  -- `h_env` now bundles the six witness-gen equation groups with the GFC `ITypeReaderImmutable`
  -- subcircuit's completeness obligation (trailing conjunct, discarded — the reader slot is discharged below).
  obtain ⟨he_flags, he_br, he_bv, he_fv, he_np, he_lt, -, _⟩ := h_env
  simp only [branchTargetWord, fallThroughWord] at h_bt3 h_ft3 h_ranges
  have hg0 : env.get i₀ = (hintFlags env.hint)[0] := by simpa using he_flags 0
  have hg1 : env.get (i₀ + 1) = (hintFlags env.hint)[1] := by simpa using he_flags 1
  have hg2 : env.get (i₀ + 2) = (hintFlags env.hint)[2] := by simpa using he_flags 2
  have hg3 : env.get (i₀ + 3) = (hintFlags env.hint)[3] := by simpa using he_flags 3
  have hg4 : env.get (i₀ + 4) = (hintFlags env.hint)[4] := by simpa using he_flags 4
  have hg5 : env.get (i₀ + 5) = (hintFlags env.hint)[5] := by simpa using he_flags 5
  have fb0 : env.get i₀ = 0 ∨ env.get i₀ = 1 := hg0 ▸ hf0
  have fb1 : env.get (i₀ + 1) = 0 ∨ env.get (i₀ + 1) = 1 := hg1 ▸ hf1
  have fb2 : env.get (i₀ + 2) = 0 ∨ env.get (i₀ + 2) = 1 := hg2 ▸ hf2
  have fb3 : env.get (i₀ + 3) = 0 ∨ env.get (i₀ + 3) = 1 := hg3 ▸ hf3
  have fb4 : env.get (i₀ + 4) = 0 ∨ env.get (i₀ + 4) = 1 := hg4 ▸ hf4
  have fb5 : env.get (i₀ + 5) = 0 ∨ env.get (i₀ + 5) = 1 := hg5 ▸ hf5
  have brb : env.get (i₀ + 6) = 0 ∨ env.get (i₀ + 6) = 1 := he_br ▸ h_brbin
  have hsumreal : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
      + env.get (i₀ + 4) + env.get (i₀ + 5) = input_is_real := by
    rw [hg0, hg1, hg2, hg3, hg4, hg5]; exact h_realsum.symm
  have hpc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc = input_state_pc :=
    h_input.2.1.2.2.2
  have ep0 : Expression.eval env.toEnvironment input_var_state_pc[0] = input_state_pc[0] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep1 : Expression.eval env.toEnvironment input_var_state_pc[1] = input_state_pc[1] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep2 : Expression.eval env.toEnvironment input_var_state_pc[2] = input_state_pc[2] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ha1eq : (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
      Expression.eval env.toEnvironment input_var_state_pc[1],
      Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by rw [ep0, ep1, ep2]
  have ha1U : Word.isU64 (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
      Expression.eval env.toEnvironment input_var_state_pc[1],
      Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p)) := ha1eq ▸ h_pcU
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := Word.isU64_four
  have hcimm : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_c_imm
      = input_adapter_op_c_imm := h_input.2.2.2.2.2.2.2
  have hcimmeq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_imm[0],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[1],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[2],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[3]] : Word (ZMod p))
      = input_adapter_op_c_imm := by
    rw [← hcimm]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hrs1eq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_a_memory_prev_value[0], input_adapter_op_a_memory_prev_value[1],
        input_adapter_op_a_memory_prev_value[2], input_adapter_op_a_memory_prev_value[3]] := by
    rw [← h_input.2.2.2.1.1]; simp only [Vector.getElem_map]
  have hrs2eq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] := by
    rw [← h_input.2.2.2.2.2.2.1.1]; simp only [Vector.getElem_map]
  have hrs1U : Word.isU64 (#v[Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs1eq ▸ h_rs1U
  have hrs2U : Word.isU64 (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs2eq ▸ h_rs2U
  have hsumbin : (env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
      + env.get (i₀ + 4) + env.get (i₀ + 5)) * (env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2)
        + env.get (i₀ + 3) + env.get (i₀ + 4) + env.get (i₀ + 5) + -1) = 0 := by
    rw [hsumreal]; rcases h_bin with h | h <;> rw [h] <;> simp
  have h_onehot := one_hot6 fb0 fb1 fb2 fb3 fb4 fb5 hsumbin
  have h_sig_bin : env.get (i₀ + 2) + env.get (i₀ + 3) = 0 ∨ env.get (i₀ + 2) + env.get (i₀ + 3) = 1 := by
    rcases fb2 with hl | hl <;> rcases fb3 with hg | hg
    · left; rw [hl, hg]; simp
    · right; rw [hl, hg]; simp
    · right; rw [hl, hg]; simp
    · exfalso
      have := val_of_bool (h := fb0); have := val_of_bool (h := fb1)
      have := val_of_bool (h := fb4); have := val_of_bool (h := fb5)
      haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
      rw [hl, hg, ZMod.val_one] at h_onehot
      omega
  -- the `(is_real-1)·is_signed` gate: real rows kill `(is_real-1)`; on padding the six binary flags
  -- sum to `is_real = 0`, so each is `0` and `is_blt + is_bge = 0`.
  have hbg_gate : (input_is_real - 1) * (env.get (i₀ + 2) + env.get (i₀ + 3)) = 0 := by
    rcases h_bin with h | h
    · haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
      have hp : 2 ^ 17 < p := Fact.out
      have hsum0 : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
          + env.get (i₀ + 4) + env.get (i₀ + 5) = 0 := hsumreal.trans h
      have e : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
            + env.get (i₀ + 4) + env.get (i₀ + 5)
          = (((env.get i₀).val + (env.get (i₀ + 1)).val + (env.get (i₀ + 2)).val
            + (env.get (i₀ + 3)).val + (env.get (i₀ + 4)).val + (env.get (i₀ + 5)).val : ℕ) : ZMod p) := by
        push_cast [ZMod.natCast_zmod_val]; ring
      rw [e] at hsum0
      have b0 := val_of_bool fb0; have b1 := val_of_bool fb1; have b2 := val_of_bool fb2
      have b3 := val_of_bool fb3; have b4 := val_of_bool fb4; have b5 := val_of_bool fb5
      have hvsum : (env.get i₀).val + (env.get (i₀ + 1)).val + (env.get (i₀ + 2)).val
          + (env.get (i₀ + 3)).val + (env.get (i₀ + 4)).val + (env.get (i₀ + 5)).val = 0 := by
        have := congrArg ZMod.val hsum0
        rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_zero] at this
      have h2 : env.get (i₀ + 2) = 0 := (ZMod.val_eq_zero _).mp (by omega)
      have h3 : env.get (i₀ + 3) = 0 := (ZMod.val_eq_zero _).mp (by omega)
      rw [h, h2, h3]; ring
    · rw [h]; ring
  have hbv : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + 6 + 1 + i}) : Word (ZMod p))
      = AddOperation.populate #v[Expression.eval env.toEnvironment input_var_state_pc[0],
          Expression.eval env.toEnvironment input_var_state_pc[1],
          Expression.eval env.toEnvironment input_var_state_pc[2], 0] input_adapter_op_c_imm := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [he_bv ⟨i, hi⟩, hcimmeq]
  have hfv : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + 6 + 1 + 4 + i}) : Word (ZMod p))
      = AddOperation.populate #v[Expression.eval env.toEnvironment input_var_state_pc[0],
          Expression.eval env.toEnvironment input_var_state_pc[1],
          Expression.eval env.toEnvironment input_var_state_pc[2], 0] #v[4, 0, 0, 0] := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [he_fv ⟨i, hi⟩]
  have hbv3 : env.get (i₀ + 6 + 1 + 3)
      = (AddOperation.populate #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          input_adapter_op_c_imm)[3] := by
    have := congrArg (·[3]) hbv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hfv3 : env.get (i₀ + 6 + 1 + 4 + 3)
      = (AddOperation.populate #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          #v[4, 0, 0, 0])[3] := by
    have := congrArg (·[3]) hfv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have h_gate2 : input_is_real + -env.get (i₀ + 6) = 0 ∨ input_is_real + -env.get (i₀ + 6) = 1 := by
    rcases h_bin with h | h
    · have hbr0 : env.get (i₀ + 6) = 0 := by rw [he_br]; exact h_brpad h
      rw [h, hbr0]; simp
    · rcases brb with hb | hb <;> rw [h, hb] <;> simp
  have hbt0 : env.get (i₀ + 6 + 1) = (AddOperation.populate
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] input_adapter_op_c_imm)[0] := by
    have := congrArg (·[0]) hbv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hbt1 : env.get (i₀ + 6 + 1 + 1) = (AddOperation.populate
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] input_adapter_op_c_imm)[1] := by
    have := congrArg (·[1]) hbv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hbt2 : env.get (i₀ + 6 + 1 + 2) = (AddOperation.populate
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] input_adapter_op_c_imm)[2] := by
    have := congrArg (·[2]) hbv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hft0 : env.get (i₀ + 6 + 1 + 4) = (AddOperation.populate
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] #v[4, 0, 0, 0])[0] := by
    have := congrArg (·[0]) hfv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hft1 : env.get (i₀ + 6 + 1 + 4 + 1) = (AddOperation.populate
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] #v[4, 0, 0, 0])[1] := by
    have := congrArg (·[1]) hfv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hft2 : env.get (i₀ + 6 + 1 + 4 + 2) = (AddOperation.populate
      #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] #v[4, 0, 0, 0])[2] := by
    have := congrArg (·[2]) hfv
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  simp only [committedNextPc, branchTargetWord, fallThroughWord] at h_ranges
  have hnp0 : env.get (i₀ + 6 + 1 + 4 + 4) = hintBranching env.hint * (AddOperation.populate
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] input_adapter_op_c_imm)[0]
      + (input_is_real - hintBranching env.hint) * (AddOperation.populate
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] #v[4, 0, 0, 0])[0] := by
    have h := he_np ⟨0, by omega⟩
    simp only [Nat.add_zero, List.getElem_cons_zero] at h
    rw [he_br, hbt0, hft0] at h; exact h
  have hnp1 : env.get (i₀ + 6 + 1 + 4 + 4 + 1) = hintBranching env.hint * (AddOperation.populate
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] input_adapter_op_c_imm)[1]
      + (input_is_real - hintBranching env.hint) * (AddOperation.populate
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] #v[4, 0, 0, 0])[1] := by
    have h := he_np ⟨1, by omega⟩
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [he_br, hbt1, hft1] at h; exact h
  have hnp2 : env.get (i₀ + 6 + 1 + 4 + 4 + 2) = hintBranching env.hint * (AddOperation.populate
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] input_adapter_op_c_imm)[2]
      + (input_is_real - hintBranching env.hint) * (AddOperation.populate
        #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] #v[4, 0, 0, 0])[2] := by
    have h := he_np ⟨2, by omega⟩
    simp only [List.getElem_cons_succ, List.getElem_cons_zero] at h
    rw [he_br, hbt2, hft2] at h; exact h
  -- The composed `LtOperationSigned` `FormalAssertion`'s `Spec` at the witnessed `populate`d columns
  -- (offset `i₀+18 = i₀+6+1+4+4+3`); reused for both the obligation and the decision readout.
  have h_lt_spec : LtOperationSigned.circuit.Spec
      ⟨#v[Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[0],
          Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[1],
          Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[2],
          Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[3]],
        #v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]],
        ⟨⟨⟨env.get (i₀ + 6 + 1 + 4 + 4 + 3)⟩,
            Vector.map (Expression.eval env.toEnvironment)
              (Vector.mapRange 4 fun i => var { index := i₀ + 6 + 1 + 4 + 4 + 3 + 1 + i }),
            env.get (i₀ + 6 + 1 + 4 + 4 + 3 + 1 + 4),
            Vector.map (Expression.eval env.toEnvironment)
              (Vector.mapRange 2 fun i => var { index := i₀ + 6 + 1 + 4 + 4 + 3 + 1 + 4 + 1 + i })⟩,
          ⟨env.get (i₀ + 6 + 1 + 4 + 4 + 3 + 8)⟩, ⟨env.get (i₀ + 6 + 1 + 4 + 4 + 3 + 8 + 1)⟩⟩,
        env.get (i₀ + 2) + env.get (i₀ + 3), input_is_real⟩ := by
    convert LtOperationSigned.spec_populate
      (b := #v[Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[0],
          Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[1],
          Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[2],
          Expression.eval env.toEnvironment input_var_adapter_op_a_memory_prev_value[3]])
      (cc := #v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]])
      (is_signed := env.get (i₀ + 2) + env.get (i₀ + 3)) (is_real := input_is_real)
      hrs1U hrs2U h_sig_bin h_bin hbg_gate using 2
    refine (ProvableType.ext_iff _ _).mpr (fun i hi => ?_)
    refine Eq.trans ?_
      ((getElem_toElements_eval_varFromOffset env.toEnvironment (i₀ + 6 + 1 + 4 + 4 + 3) i hi).trans
        (he_lt ⟨i, hi⟩))
    simp [circuit_norm]
  refine ⟨⟨⟨hrs1U, hrs2U, h_bin, h_sig_bin⟩, h_lt_spec⟩, ?_, ?_, ?_, ?_, ?_, ?_,
    (by linear_combination -hsumreal), hsumbin, ?_, ?_, ?_,
    ⟨h_bin, h_cpu, h_st⟩, ⟨⟨fun _ => ⟨ha1U, h_imm⟩, brb⟩, ?_⟩, ?_, ⟨⟨fun _ => ⟨ha1U, h4U⟩, h_gate2⟩, ?_⟩, ?_,
    ?_, ?_, ?_, ⟨⟨h_bin, h_bin⟩, h_it, by
      rw [hg0, hg1, hg2, hg3, hg4, hg5]; exact h_prog⟩, ?_, ?_, ?_⟩
  · rcases fb0 with h | h <;> rw [h] <;> simp
  · rcases fb1 with h | h <;> rw [h] <;> simp
  · rcases fb2 with h | h <;> rw [h] <;> simp
  · rcases fb3 with h | h <;> rw [h] <;> simp
  · rcases fb4 with h | h <;> rw [h] <;> simp
  · rcases fb5 with h | h <;> rw [h] <;> simp
  · rcases brb with h | h <;> rw [h] <;> simp
  · -- `===` carrier is `id (ZMod p)`; `CommRing (id (ZMod p))` needed for `linear_combination`.
    haveI : CommRing (id (ZMod p)) := inferInstanceAs (CommRing (ZMod p))
    rcases h_bin with h | h
    · rw [h]; simp
    · rw [h, one_mul]
      obtain ⟨h_bit, h_eqf, h_eqbin⟩ := LtOperationSigned.result_semantic hrs1U hrs2U h h_lt_spec
      simp only [circuit_norm] at h_bit h_eqf h_eqbin
      rw [hrs1eq, hrs2eq] at h_bit h_eqf
      have hdec := h_dec h
      simp only [rs1WordInput, rs2WordInput] at hdec h_rs1U h_rs2U
      rw [← he_br, ← hg0, ← hg1, ← hg2, ← hg3, ← hg4, ← hg5] at hdec
      obtain ⟨hd0, hd1, hd2, hd3, hd4, hd5⟩ := hdec
      have hone : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
          + env.get (i₀ + 4) + env.get (i₀ + 5) = 1 := by rw [hsumreal]; exact h
      have key := branch_decision_eq_of_conditions h_rs1U h_rs2U fb0 fb1 fb2 fb3 fb4 fb5 brb hone
        h_bit h_eqf h_eqbin hd0 hd1 hd2 hd3 hd4 hd5
      simp only [branchDecision] at key
      linear_combination key
  · rcases h_bin with h | h
    · have hbr0 : env.get (i₀ + 6) = 0 := by rw [he_br]; exact h_brpad h
      rw [h, hbr0]; simp
    · rw [h]; simp
  · rw [hbv]; exact AddOperation.spec_populate ha1U h_imm (env.get (i₀ + 6))
  · rw [hbv3]; exact h_bt3
  · rw [hfv]; exact AddOperation.spec_populate ha1U h4U (input_is_real + -env.get (i₀ + 6))
  · rw [hfv3]; exact h_ft3
  · simpa [sub_eq_add_neg] using he_np 0
  · simpa [sub_eq_add_neg] using he_np 1
  · simpa [sub_eq_add_neg] using he_np 2
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := by norm_cast
    simp only [byteChannel, hnp0]
    rw [← c14]
    exact (byteRowSpec_range _ h14p).mpr (h_ranges hr1).1
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
    simp only [byteChannel, hnp1]
    rw [← c16]
    exact (byteRowSpec_range _ h16p).mpr (h_ranges hr1).2.1
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have c16 : ((16 : ℕ) : ZMod p) = (16 : ZMod p) := by norm_cast
    simp only [byteChannel, hnp2]
    rw [← c16]
    exact (byteRowSpec_range _ h16p).mpr (h_ranges hr1).2.2

/-- The BRANCH chip's `GeneralFormalCircuit`: conditional control flow via `LtOperationSigned` +
two `AddOperation` gadgets + `ITypeReaderImmutable`. Soundness and completeness are axiom-clean. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs BranchColumns :=
  -- `byteChannel` dropped (W11 Phase 0c): the three off-gate next_pc byte-range pulls are discharged by the
  -- inline `is_real = Σ flags` / `Σ flags ∈ {0,1}` shallow gates in `main`; residual buses are the readers'.
  { main, elaborated,
    channelsWithRequirements := [stateChannel.toRaw, memoryChannel.toRaw],
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, byteChannel, stateChannel, memoryChannel,
        AddOperation.circuit, LtOperationSigned.circuit, Readers.CPUState.circuit,
        Readers.ITypeReaderImmutable.circuit]; grind,
    -- W11: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair so the chip is a
    -- `VmTables` table. `next_pc` is the **witnessed** muxed branch target the chip feeds `CPUState`:
    -- the three selected limbs `next_pc[0..2]` (cells `offset+15..17`).
    exposedChannels := fun input offset =>
      stateChannel.expose
        [ stateChannel.pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             var ⟨offset + 6 + 1 + 4 + 4⟩, var ⟨offset + 6 + 1 + 4 + 4 + 1⟩,
             var ⟨offset + 6 + 1 + 4 + 4 + 2⟩⟩ ],
    exposedChannels_eq := by
      intro input offset
      simp only [Operations.ExposedChannelsLawful, VmChannel.expose, List.mem_singleton, forall_eq,
        List.map_cons, List.map_nil]
      simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
        Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
        Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
        Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        SP1Clean.AddOperation.circuit, SP1Clean.AddOperation.main,
        LtOperationSigned.circuit, LtOperationSigned.main,
        U16MSBOperation.circuit, U16MSBOperation.main,
        LtOperationUnsigned.circuit, LtOperationUnsigned.main,
        U16CompareOperation.circuit, U16CompareOperation.main,
        circuit_norm, FormalAssertion.toSubcircuit_interactions,
        GeneralFormalCircuit.toSubcircuit_interactions]
      simp [circuit_norm, Gadgets.Equality.main, VmChannel.pulledIf, VmChannel.pushedIf] }

end SP1Clean.BranchChip
