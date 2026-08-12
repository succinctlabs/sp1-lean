import SP1Clean.Native.Chips.JalrChip.Defs
import SP1Clean.Model.InteractionRecovery
import SP1Clean.Math.EvalVec
import Clean.Air.Circuit

/-! # `SP1Clean.JalrChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.JalrChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

-- `jalr_proof_start` is `circuit_proof_start` with its `provable_struct_simp` step **hoisted above**
-- the two `main`/`elaborated` unfolding steps.
--
-- Measured (2026-08-01): in the stock ordering `provable_struct_simp` runs its `simp … at *` fixpoint
-- *after* `dsimp only [main] at *` has expanded JALR's five-subcircuit tower (CPUState + two
-- `AddOperation`s + `ITypeReader` + `RegisterWrite`) into `h_holds` and the goal, and that one step
-- alone accounted for 2.90M of `soundness`'s 2.97M budget units — 98%. Every other step of the
-- thirteen is four orders of magnitude cheaper. Run on the still-folded context the same fixpoint costs
-- 2.16M *raw* heartbeats (≈2.2k budget units), a 1000x drop, and it destructures exactly the same
-- variables, because destructuring is driven by `h_input`/`h_assumptions`, not by `h_holds`.
--
-- The one thing the hoist gives up is that `provable_struct_simp`'s struct-eval set — which is
-- deliberately *not* a subset of `circuit_norm` (its `getElem` lemmas loop against `circuit_norm`'s
-- element-map spelling) — no longer reaches the unfolded `h_holds`. That is restored by the single
-- scoped pass below, which mirrors Clean's `ProvableStructSimp.structEvalSimpLemmas` verbatim and is
-- applied only `at h_holds ⊢` rather than `at *`. With that, both proof bodies go through byte for
-- byte. Keep the list in sync with Clean if that set changes.
--
-- `hygiene false` is required: the step list names the hypotheses `circuit_proof_start_core`
-- introduces (`h_input`, `h_holds`, `h_env`, …), exactly as Clean's own `circuit_proof_start` elab
-- does via `mkIdent`; under hygiene a macro's occurrences would not refer to them.
set_option hygiene false in
local macro "jalr_proof_start" : tactic => `(tactic| (
  circuit_proof_start_core
  try simp +instances only [circuit_norm] at input_var
  try simp +instances only [circuit_norm] at input
  try simp +instances only [circuit_norm] at h_input
  try dsimp only [Assumptions] at *
  try dsimp only [Spec] at *
  try dsimp only [ProverAssumptions] at *
  try dsimp only [ProverSpec] at *
  try dsimp only [ElaboratedCircuit.withData, ElaboratedCircuit.output]
  try dsimp only [field, id_eq, CircuitType.var_of_provableType,
    CircuitType.value_of_provableType, CircuitType.proverValue_of_provableType] at *
  -- hoisted: runs while `h_holds` and the goal are still the folded `main` application
  try provable_struct_simp
  try dsimp +instances only [elaborated] at *
  try dsimp +instances only [main] at *
  -- the scoped replacement for what the hoist gave up (mirrors Clean's `structEvalSimpLemmas`)
  try simp +instances only [ProvableStruct.eval_eq_eval, ProvableStruct.eval_eq_eval_prover,
    ProvableStruct.eval_var_eq_eval, ProvableStruct.eval_var_eq_eval_prover,
    ProvableStruct.eval_field_var_eq_eval, ProvableStruct.eval_field_var_eq_eval_prover,
    ProvableStruct.structEvalLiteralProc, ProvableStruct.structEvalProjectionProc,
    ProvableStruct.structEvalProjectionEvalProc, ProvableStruct.structEvalProjectionExpr,
    ProvableStruct.structEqSplit, ProvableStruct.components,
    ProvableType.eval_field, ProvableType.getElem_eval_fields,
    ProvableType.getElem_eval_fields_prover, getElem_eval_vector,
    CircuitType.eval_var_prover_to_verifier,
    CircuitType.eval_var_field, CircuitType.eval_var_field_prover,
    CircuitType.eval_expr, CircuitType.eval_expr_prover,
    CircuitType.value_of_provableType, CircuitType.proverValue_of_provableType,
    DerivedCircuitType.eval_verifier, DerivedCircuitType.eval_prover,
    CircuitType.evalVerifier, CircuitType.evalProver] at h_holds ⊢
  try simp +instances only [circuit_norm] at h_input
  try simp +instances only [circuit_norm] at h_assumptions
  try simp +instances only [circuit_norm, h_input] at h_holds
  try simp +instances only [circuit_norm, h_input] at h_env
  try simp +instances only [circuit_norm, h_input]
  try simp +instances only [circuit_norm] at h_spec
  try dsimp only [field, id_eq, CircuitType.var_of_provableType,
    CircuitType.value_of_provableType, CircuitType.proverValue_of_provableType] at *))

/-- Operands are 64-bit.  The pinned Rust padding gate and the
`is_real`/`lsb` boolean gates are represented in `main`, so none is assumed at
the verifier boundary. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (#v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
    input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p))

/-- Honest prover-side row well-formedness: operand `isU64`s, `is_real`/`lsb` binary, CPUState + op_a/op_b
timestamp bounds, `value[3] = 0` for both add results, and the `is_real`-gated cleared-target 4-byte
alignment (`(jump_target[0] - lsb) / 4 < 2^14`). Covers `rd ≠ x0` rows (`op_a_0 = 0`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_c_imm ∧
  Word.isU64 (#v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
    input.adapter.op_b_memory.prev_value[2], input.adapter.op_b_memory.prev_value[3]] : Word (ZMod p)) ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  -- (Option B pure-read ITypeReader) the op_a read-prior `isU64`, for the reader's op_a memory pull
  -- completeness (its `Spec` now derives + owes the read-prior `isU64` pair).
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := input.state.pc, clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  (jumpTargetWord input)[3] = 0 ∧
  (linkTargetWord input)[3] = 0 ∧
  (input.is_real = 1 →
    (((jumpTargetWord input)[0] - lsbBit input) * (4 : ZMod p)⁻¹).val < 2 ^ 14) ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧ input.state.pc[0].val < 2 ^ 16 ∧
    input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- G1: the two pulled prior records' 24-bit access clocks (`Channels.MemoryMsg.ClkBound`, the clock
  -- half of the memory channel's `Guarantees`). A pull's completeness must exhibit the guarantee it
  -- consumes; in a real trace each prior access sits at a genuine `< 2^24` timestamp. Soundness does
  -- *not* assume these — they are derived there from the pulls themselves.
  (input.is_real = 1 →
    input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24)

-- No ceiling. The former 8M one was ~120x over: opener + body together measure 65,581 budget units,
-- against the 200,000 default. The earlier ablation ("100% of the cost is the opener, the body is
-- free") was right about *where* the cost sat but not about *which* step. Exact per-step counts
-- (`#count_heartbeats` under `Elab.async false`) put 2.90M of the old 2.97M in
-- `provable_struct_simp` alone, purely because the stock ordering runs its
-- `at *` fixpoint after `main` has been unfolded into `h_holds` and the goal. `jalr_proof_start` hoists
-- that step above the unfolding; the proof body below is unchanged.
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  jalr_proof_start
  obtain ⟨h_imm, h_rs1U, h_pcU⟩ := h_assumptions
  obtain ⟨h_lsbgate, h_cpu, h_add1, h_av3, h_add2, h_oav3, h_it0,
    _h_regwrite, h_align, h_pad_gate, h_gate⟩ := h_holds
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := bool_of_mul_pred h_gate
  have h_pad (hr : input_is_real = 0) :
      input_adapter_op_a_0 = 0 := by
    rw [hr] at h_pad_gate
    simpa using h_pad_gate
  have h_lsb := bool_of_mul_pred h_lsbgate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's new `MemoryMsg.ClkBound` guarantee — `ITypeReader`'s op_b read-back push (`clk_low + 3`)
  -- and `RegisterWrite`'s op_a write push (`clk_low + 4`). The offset is left to unification, so this
  -- line never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  have h_it : Readers.ITypeReader.Spec _ :=
    h_it0 ⟨h_bin, h_bin, h_clk⟩
  have h_op_a_0 : input_adapter_op_a_0 = 0 ∨ input_adapter_op_a_0 = 1 := by
    rcases h_bin with h0 | h1
    · exact Or.inl (h_pad h0)
    · exact h_it.2.1 h1
  -- `h_input` flattened: `op_a/op_b_memory` are 3-leaf sub-groups `prev_value ∧ ts_prev_low ∧ ts_diff`.
  obtain ⟨_h_ir, ⟨_h_clkh, _h_clk1, _h_clk0, hpc⟩, _h_a, ⟨_h_amem_pv, _h_amem_pl, _h_amem_dl⟩,
    _h_a0, _h_b, ⟨h_bmem_pv, _h_bmem_pl, _h_bmem_dl⟩, _hcimm⟩ := h_input
  have erb : ∀ i (hi : i < 4), Expression.eval env input_var_adapter_op_b_memory_prev_value[i]
      = input_adapter_op_b_memory_prev_value[i] :=
    fun i hi => by rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have hrs1eq : (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] := by
    simp only [erb]
  have hrs1U : Word.isU64 (#v[Expression.eval env input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs1eq ▸ h_rs1U
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := Word.isU64_four
  have epc : ∀ i (hi : i < 3), Expression.eval env input_var_state_pc[i] = input_state_pc[i] :=
    fun i hi => by rw [← hpc]; simp only [Vector.getElem_map]
  have hpceq : (#v[Expression.eval env input_var_state_pc[0], Expression.eval env input_var_state_pc[1],
      Expression.eval env input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by simp only [epc]
  have hpcU : Word.isU64 (#v[Expression.eval env input_var_state_pc[0],
      Expression.eval env input_var_state_pc[1], Expression.eval env input_var_state_pc[2], 0]
        : Word (ZMod p)) := hpceq ▸ h_pcU
  -- `is_real - op_a_0` is binary: on real rows from `op_a_0 ∈ {0,1}`, on padding from `h_pad`.
  have h_gate2 : input_is_real - input_adapter_op_a_0 = 0 ∨ input_is_real - input_adapter_op_a_0 = 1 := by
    rcases h_bin with h | h
    · rw [h, h_pad h]; simp
    · rcases h_op_a_0 with h0 | h0 <;> rw [h, h0] <;> simp
  refine ⟨⟨h_it, h_bin, ?_, ?_, ?_, ?_⟩,
    Or.inr ⟨h_bin, h_bin, h_clk⟩,
    Or.inr ⟨h_bin, ?_, h_clk.at_four⟩,
    fun h1 h0 => off_gate_vacuous h_bin h1 h0⟩
  · intro hr1
    have := (h_add1 ⟨fun _ => ⟨hrs1U, h_imm⟩, h_bin⟩ hr1).2
    rw [hrs1eq] at this
    simpa only [rs1Word] using this
  · intro hr1 hop_a_0
    have hg1 : input_is_real - input_adapter_op_a_0 = 1 := by rw [hr1, hop_a_0]; simp
    have := (h_add2 ⟨fun _ => ⟨hpcU, h4U⟩, h_gate2⟩ hg1).2
    rw [hpceq] at this
    simpa only [pcWord] using this
  · -- 4-byte alignment of the cleared low limb, from the (otherwise-unused) byte-range pull `h_align`:
    -- `((add_value[0] - lsb) · 4⁻¹).val < 2^14 ⇒ (add_value[0] - lsb).val % 4 = 0`.
    intro hr1
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := Nat.cast_ofNat
    have hguar := h_align (by rw [hr1])
    simp only [byteChannel] at hguar
    rw [← c14] at hguar
    exact val_mod_four_of_mul_inv_four_lt ((byteRowSpec_range _ h14p).mp hguar)
  · -- LSB-clearing: the committed `nextPcWord` is `add_value` with bit 0 cleared (`~~~1#64 &&&`).
    -- The binary `lsb` gate + the `÷4` byte-range pin `lsb = bit0(add_value[0])`; with `add_value[3] = 0`
    -- this makes `toNat add_value = toNat nextPcWord + lsb`, so `ofNat64_clear_lsb_and` applies.
    intro hr1
    have hguar := h_align (by rw [hr1])
    simp only [byteChannel] at hguar
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := Nat.cast_ofNat
    rw [← c14] at hguar
    have hlt := (byteRowSpec_range _ h14p).mp hguar
    rw [sub_eq_add_neg] at hlt
    have hdlt : (env.get i₀ + -env.get (i₀ + 4 + 4)).val < 2 ^ 16 :=
      val_lt_65536_of_mul_inv_four_lt hlt
    have hdmod : (env.get i₀ + -env.get (i₀ + 4 + 4)).val % 4 = 0 :=
      val_mod_four_of_mul_inv_four_lt hlt
    have hlsble : (env.get (i₀ + 4 + 4)).val ≤ 1 := by
      rcases h_lsb with h | h <;> rw [h] <;> simp [ZMod.val_one]
    -- load-bearing for the `ZMod.val_add_of_lt` side goal's `omega` (the magnitude of `p`).
    have hp : 2 ^ 17 < p := Fact.out
    have hav0 : (env.get i₀).val
        = (env.get i₀ + -env.get (i₀ + 4 + 4)).val + (env.get (i₀ + 4 + 4)).val := by
      conv_lhs => rw [show env.get i₀
        = (env.get i₀ + -env.get (i₀ + 4 + 4)) + env.get (i₀ + 4 + 4) from by ring]
      rw [ZMod.val_add_of_lt (by omega)]
    have hav3 : (env.get (i₀ + 3)).val = 0 := by rw [h_av3]; simp
    simp only [JalrChip.nextPcWord, Word.toBitVec64, Word.toNat_def, Vector.getElem_map,
      Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, ZMod.val_zero, circuit_norm]
    -- goal: `ofNat 64 (toNat nextPcWord) = ~~~1#64 &&& ofNat 64 (toNat add_value)`; the two sums differ
    -- only by `lsb` in the low limb (`add_value[3] = 0`), so `ofNat64_clear_lsb_and` closes it.
    have hMeven : ((env.get i₀ + -env.get (i₀ + 4 + 4)).val + (env.get (i₀ + 1)).val * 2 ^ 16
        + (env.get (i₀ + 2)).val * 2 ^ 32 + 0 * 2 ^ 48) % 2 = 0 := by omega
    have hrel : (env.get i₀).val + (env.get (i₀ + 1)).val * 2 ^ 16 + (env.get (i₀ + 2)).val * 2 ^ 32
          + (env.get (i₀ + 3)).val * 2 ^ 48
        = ((env.get i₀ + -env.get (i₀ + 4 + 4)).val + (env.get (i₀ + 1)).val * 2 ^ 16
            + (env.get (i₀ + 2)).val * 2 ^ 32 + 0 * 2 ^ 48) + (env.get (i₀ + 4 + 4)).val := by
      rw [hav0, hav3]; ring
    rw [sub_eq_add_neg, hrel]
    exact ofNat64_clear_lsb_and hlsble hMeven
  · -- RegisterWrite op_a write push: `isU64` of the written link value `op_a_value`. On `rd ≠ x0`
    -- (`op_a_0 = 0`) it is the link add result `pc + 4` (`spec_populate.1`); on `rd = x0` (`op_a_0 = 1`)
    -- the `op_a_0` zeroing gates pin every limb to `0`.
    intro hr1
    replace hr1 : input_is_real = 1 := hr1
    rcases h_op_a_0 with h0 | h0
    · have hg1 : input_is_real - input_adapter_op_a_0 = 1 := by rw [hr1, h0]; simp
      exact (h_add2 ⟨fun _ => ⟨hpcU, h4U⟩, h_gate2⟩ hg1).1
    · obtain ⟨z0, z1, z2, z3⟩ := h_it.1
      rw [h0, one_mul] at z0 z1 z2 z3
      refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
        simp only [Vector.getElem_mapRange, circuit_norm] <;> simp_all

-- No ceiling (measures 24,475 budget units). Same mechanism and fix as `soundness` above: 2.98M of the
-- old 2.99M budget units were the un-hoisted `provable_struct_simp`. Here the scoped struct-eval pass inside
-- `jalr_proof_start` is a no-op (completeness has no `h_holds`); only the hoist matters.
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  jalr_proof_start
  obtain ⟨h_imm, h_rs1U, h_pcU, h_oap, h_bin, h_op_a_0, h_cpu, h_rac_a, h_rac_b, h_jt3, h_lt3,
    h_align_pa, hdec, hprevclk⟩ := h_assumptions
  -- G1: the *push* side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  -- op_b (rs1) read-prior `isU64` in the reader's **raw** `prev_value` form (from the reconstructed
  -- `h_rs1U`), for the pure-read `ITypeReader.Spec`'s memory-pull `isU64` pair.
  have hpb_raw : Word.isU64 input_adapter_op_b_memory_prev_value := by
    have he : (#v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]]
          : Word (ZMod p)) = input_adapter_op_b_memory_prev_value := by
      apply Vector.ext; intro i hi; interval_cases i <;> rfl
    rwa [he] at h_rs1U
  simp only [jumpTargetWord, linkTargetWord, lsbBit, rs1WordI] at h_jt3 h_lt3 h_align_pa
  -- `h_env` now bundles the two add-result + `lsb` witness-gen equations with the GFC `ITypeReader`
  -- subcircuit's completeness obligation (4th conjunct, discarded — the reader slot is discharged below).
  obtain ⟨he_av, he_oav, he_lsb, -, _⟩ := h_env
  obtain ⟨_h_ir, ⟨_h_clkh, _h_clk1, _h_clk0, hpc⟩, _h_a, ⟨_h_amem_pv, _h_amem_pl, _h_amem_dl⟩,
    _h_a0, _h_b, ⟨h_bmem_pv, _h_bmem_pl, _h_bmem_dl⟩, hcimm⟩ := h_input
  have erb : ∀ i (hi : i < 4),
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[i]
      = input_adapter_op_b_memory_prev_value[i] :=
    fun i hi => by rw [← h_bmem_pv]; simp only [Vector.getElem_map]
  have hrs1eq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
        input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] := by
    simp only [erb]
  have hrs1U : Word.isU64 (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p)) :=
    hrs1eq ▸ h_rs1U
  have hcimm_eq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_imm[0],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[1],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[2],
      Expression.eval env.toEnvironment input_var_adapter_op_c_imm[3]] : Word (ZMod p))
      = input_adapter_op_c_imm := (vec4_eval _ _).trans hcimm
  have epc : ∀ i (hi : i < 3),
      Expression.eval env.toEnvironment input_var_state_pc[i] = input_state_pc[i] :=
    fun i hi => by rw [← hpc]; simp only [Vector.getElem_map]
  have hpceq : (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
      Expression.eval env.toEnvironment input_var_state_pc[1],
      Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by simp only [epc]
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := Word.isU64_four
  have hval1 : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + i}) : Word (ZMod p))
      = AddOperation.populate #v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
          Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]]
          input_adapter_op_c_imm := by
    rw [← AddOperation.populateIR_eval env input_var_adapter_op_b_memory_prev_value
      input_var_adapter_op_c_imm _ _ rfl hcimm_eq hrs1U h_imm]
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    exact he_av ⟨i, hi⟩
  have hval2 : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + 4 + i}) : Word (ZMod p))
      = AddOperation.populate #v[Expression.eval env.toEnvironment input_var_state_pc[0],
          Expression.eval env.toEnvironment input_var_state_pc[1],
          Expression.eval env.toEnvironment input_var_state_pc[2], 0] #v[4, 0, 0, 0] := by
    rw [← AddOperation.populateIR_eval env
      #v[input_var_state_pc[0], input_var_state_pc[1], input_var_state_pc[2], 0]
      #v[4, 0, 0, 0] _ _ (by simp [circuit_norm]) (by simp [circuit_norm]) (hpceq ▸ h_pcU) h4U]
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    exact he_oav ⟨i, hi⟩
  have hav0 : env.get i₀
      = (AddOperation.populate #v[input_adapter_op_b_memory_prev_value[0],
          input_adapter_op_b_memory_prev_value[1], input_adapter_op_b_memory_prev_value[2],
          input_adapter_op_b_memory_prev_value[3]] input_adapter_op_c_imm)[0] := by
    have := congrArg (·[0]) hval1
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, hrs1eq, circuit_norm] using this
  have hav3 : env.get (i₀ + 3)
      = (AddOperation.populate #v[input_adapter_op_b_memory_prev_value[0],
          input_adapter_op_b_memory_prev_value[1], input_adapter_op_b_memory_prev_value[2],
          input_adapter_op_b_memory_prev_value[3]] input_adapter_op_c_imm)[3] := by
    have := congrArg (·[3]) hval1
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, hrs1eq, circuit_norm] using this
  have hoav3 : env.get (i₀ + 4 + 3)
      = (AddOperation.populate #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          #v[4, 0, 0, 0])[3] := by
    have := congrArg (·[3]) hval2
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, hpceq, circuit_norm] using this
  -- The lsb witness is u64-sorted, so its evaluation carries a `% 2 ^ 64` truncation. Binarity
  -- survives it untouched; the two places that need the *value* strip it via `hlsb_val` below.
  have hlsb_bin : env.get (i₀ + 4 + 4) = 0 ∨ env.get (i₀ + 4 + 4) = 1 := by
    rw [he_lsb]
    rcases Nat.mod_two_eq_zero_or_one ((env.get i₀).val % 2 ^ 64) with h | h <;> rw [h] <;> simp
  -- On a real row the add result is a `Word`, so its low limb is far below `2 ^ 64` and the
  -- truncation is the identity.
  have hlsb_val : input_is_real = 1 →
      env.get (i₀ + 4 + 4) = (((env.get i₀).val % 2 : ℕ) : ZMod p) := by
    intro hr1
    have hisu : Word.isU64 (AddOperation.populate
        #v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1],
           input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]]
        input_adapter_op_c_imm) :=
      hrs1eq ▸ (AddOperation.spec_populate hrs1U h_imm input_is_real hr1).1
    have h0 := (Word.lt_cases_of_isU64 hisu).1
    rw [he_lsb, hav0]
    congr 1
    omega
  have h_gate2 : input_is_real - input_adapter_op_a_0 = 0 ∨ input_is_real - input_adapter_op_a_0 = 1 := by
    rw [h_op_a_0]; simpa using h_bin
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [h_op_a_0, zero_mul]
  refine ⟨?_, ⟨h_bin, h_cpu⟩, ⟨⟨fun _ => ⟨hrs1U, h_imm⟩, h_bin⟩, ?_⟩, ?_, ⟨⟨fun _ => ⟨hpceq ▸ h_pcU, h4U⟩, h_gate2⟩, ?_⟩,
    ?_, ⟨⟨h_bin, h_bin, h_clk⟩,
      ⟨⟨hz _, hz _, hz _, hz _⟩, (fun _ => Or.inl h_op_a_0), h_rac_a, h_rac_b, hdec,
        fun hr => ⟨h_oap hr, hpb_raw, (hprevclk hr).1, (hprevclk hr).2⟩⟩⟩,
    ⟨⟨h_bin, ?_, h_clk.at_four⟩, trivial⟩, ?_, ?_, ?_⟩
  · rcases hlsb_bin with h | h <;> rw [h] <;> simp
  · rw [hval1]; exact AddOperation.spec_populate hrs1U h_imm input_is_real
  · rw [hav3]; exact h_jt3
  · rw [hval2]; exact AddOperation.spec_populate (hpceq ▸ h_pcU) h4U (input_is_real - input_adapter_op_a_0)
  · rw [hoav3]; exact h_lt3
  · -- RegisterWrite op_a write push: `isU64` of the link value `pc + 4` (completeness covers `op_a_0 = 0`).
    intro hr
    rw [hval2]
    exact (AddOperation.spec_populate (hpceq ▸ h_pcU) h4U (input_is_real - input_adapter_op_a_0)
      (by rw [h_op_a_0]; simpa using hr)).1
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := Nat.cast_ofNat
    simp only [byteChannel, hlsb_val hr1, hav0]
    rw [← c14]
    exact (byteRowSpec_range _ h14p).mpr (h_align_pa hr1)
  · rw [h_op_a_0]
    simp
  · rcases h_bin with h | h <;> rw [h] <;> simp

/-- Exact State-channel pair emitted by the composed CPU-state reader.  JALR's
successor PC is the witnessed jump target with its low bit cleared. -/
def exposedStateInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [ stateChannel.pulledIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536,
       input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
    stateChannel.pushedIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
       var ⟨offset⟩ - var ⟨offset + 8⟩,
       var ⟨offset + 1⟩, var ⟨offset + 2⟩⟩ ]

/-- Exact Byte-channel list emitted by the native JALR composition: CPU clock
checks, both add-result limb checks, the destination/source register timestamp
checks, and the cleared-target alignment check. -/
def exposedByteInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let clkLow := input.state.clk_0_16 + input.state.clk_16_24 * 65536
  let linkGate := input.is_real - input.adapter.op_a_0
  [ byteChannel.pulledIf input.is_real
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0, input.state.clk_16_24, 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, var ⟨offset⟩, Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, var ⟨offset + 1⟩, Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, var ⟨offset + 2⟩, Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, var ⟨offset + 3⟩, Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf linkGate
      ⟨6, var ⟨offset + 4⟩, Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf linkGate
      ⟨6, var ⟨offset + 5⟩, Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf linkGate
      ⟨6, var ⟨offset + 6⟩, Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf linkGate
      ⟨6, var ⟨offset + 7⟩, Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, input.adapter.op_a_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0,
       (clkLow + 4 - input.adapter.op_a_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_a_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, input.adapter.op_b_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨3, 0,
       (clkLow + 3 - input.adapter.op_b_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_b_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6,
       ((var ⟨offset⟩ : Expression (ZMod p)) - var ⟨offset + 8⟩) *
          Expression.const ((4 : ZMod p)⁻¹),
       Expression.const ((14 : ℕ) : ZMod p), 0⟩ ]

/-- Jalr's exact Memory-channel interaction list (I-type: no op_c register read — the second operand
is the immediate).  The op_a read-prior pull and the op_b (rs1) pull + read-back push descend from
the composed `ITypeReader`; the op_a write push from the composed `RegisterWrite`, carrying the
witnessed link address `op_a_value` (cells `offset+4..7`, after the jump target `add_value`).
Keeping this list beside `circuit` makes Clean's exposure interface the single structural source
consumed by both faithfulness and semantic grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, Vector.mapRange 4 fun i => var { index := offset + 4 + i }⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact rd read-prior pull occupies its declared slot in Jalr's exposed Memory list. -/
theorem opAPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B (rs1) pull occupies its declared slot in Jalr's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- Exact Program fetch emitted by the I-type adapter. -/
def exposedProgramInteractions (input : Var Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf input.is_real
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], 47,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0],
       input.adapter.op_c_imm, input.adapter.op_a_0, 0, 1⟩ ]

/-- The JALR chip row as a `GeneralFormalCircuit`: register-indirect jump with LSB clearing, composing the
two witnessed `AddOperation` gadgets and the I-type reader; output is the native `Columns` row. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  -- `byteChannel` dropped (W11 Phase 0c): the off-gate alignment byte-pull `Requirements` is discharged by
  -- the inline `is_real` boolean gate in `main`; the residual buses are the readers'/add-ops'.
  { main, elaborated,
    channelsWithRequirements := [stateChannel.toRaw, memoryChannel.toRaw],
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    requirementsChannelsLawful := fun input_var i₀ => by
      have h_byte : (byteChannel (p := p)).toRaw ∈
          (elaborated (p := p)).channelsWithGuarantees := by
        simp only [circuit_norm]
      dsimp only [Operations.RequirementsChannelsLawful]
      refine ⟨?_, ?_, ?_⟩
      · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorIR, witnessField,
          subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
        simp only [Operations.subcircuitChannelsWithRequirements_append,
          Operations.subcircuitChannelsWithRequirements_witness,
          Operations.subcircuitChannelsWithRequirements_subcircuit,
          Operations.subcircuitChannelsWithRequirements_assert,
          Operations.subcircuitChannelsWithRequirements_interact,
          Operations.subcircuitChannelsWithRequirements_nil,
          GeneralFormalCircuit.toSubcircuit_channelsWithRequirements,
          FormalAssertion.toSubcircuit_channelsWithRequirements,
          Readers.CPUState.channelsWithRequirements_eq,
          AddOperation.circuit, Readers.ITypeReader.circuit, Readers.RegisterWrite.circuit,
          Gadgets.Equality.channelsWithRequirements_eq, List.nil_append, List.append_nil]
        simp only [List.subset_def, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
        tauto
      · intro channel h_channel
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorIR, witnessField,
          subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength,
          Operations.shallowChannels_append, Operations.shallowChannels_witness,
          Operations.shallowChannels_subcircuit, Operations.shallowChannels_assert,
          Operations.shallowChannels_interact, Operations.shallowChannels_nil,
          List.nil_append] at h_channel
        simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at h_channel
        subst channel
        exact Or.inl h_byte
      · intro env h_constraints
        have hshallow := h_constraints
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorIR, witnessField,
          subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength,
          ConstraintsHold.Shallow, Operations.forAllNoOffset_append,
          Operations.forAllNoOffset, true_and, and_true, eval_sub,
          Expression.eval] at hshallow
        have h_gate : Expression.eval env input_var.is_real *
            (Expression.eval env input_var.is_real - 1) = 0 := hshallow.2
        have h_bool : Expression.eval env input_var.is_real = 0 ∨
            Expression.eval env input_var.is_real = 1 := bool_of_mul_pred h_gate
        have h_bool' : (ProvableStruct.eval env input_var).is_real = 0 ∨
            (ProvableStruct.eval env input_var).is_real = 1 := by
          simpa only [circuit_norm] using h_bool
        rw [Operations.inChannelsOrRequirements_iff_forall_mem]
        intro interaction h_interaction
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorIR, witnessField,
          subcircuitWithAssertion, assertion, assertZero, Channel.pullIf,
          HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength,
          Operations.shallowInteractions_append, Operations.shallowInteractions_witness,
          Operations.shallowInteractions_subcircuit, Operations.shallowInteractions_assert,
          Operations.shallowInteractions_interact, Operations.shallowInteractions_nil,
          List.nil_append] at h_interaction
        simp only [List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at h_interaction
        subst interaction
        right
        rw [ChannelInteraction.toRaw_requirements]
        intro h1 h0
        simp only [circuit_norm] at h1 h0
        exact off_gate_vacuous h_bool' h1 h0,
    -- W11: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair as chip-owned
    -- interactions (the Clean `VmTables` re-base that motivated the shape was investigated and deferred
    -- — roadmap W11). `next_pc` is the **witnessed** LSB-cleared jump target the chip feeds `CPUState`:
    -- low limb `add_value[0] - lsb` (cells `offset+0` minus `offset+8`), high limbs `add_value[1..2]`.
    exposedChannels := fun input offset =>
      expose stateChannel (exposedStateInteractions input offset) ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `ITypeReader`, gate
      -- `is_trusted = is_real`, opcode `JALR = 47`), consumed by `Soundness/TypedProgram.lean`.
      expose programChannel (exposedProgramInteractions input),
    exposedChannels_eq := by
      intro input offset
      unfold Operations.ExposedChannelsLawful
      intro exposed exposedMem
      simp only [expose, exposedStateInteractions, exposedProgramInteractions,
        List.mem_append, List.mem_singleton] at exposedMem
      rcases exposedMem with (rfl | rfl) | rfl
      · simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorIR, witnessField, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf, Operations.localLength]
        simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
          Readers.CPUState.interactionsWith_state_subcircuit,
          InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
          InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
          AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
          Readers.ITypeReader.circuit, Readers.ITypeReader.channelsWithGuarantees_eq,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
          FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
          Channels.stateChannel_eq_byteChannel_false, Channels.stateChannel_eq_programChannel_false,
          Channels.stateChannel_eq_memoryChannel_false, not_false_eq_true,
          Operations.interactionsWith_assert, Operations.interactionsWith_interact,
          Operations.interactionsWith_nil, List.nil_append]
        simp only [Operations.interactionsWith_subcircuit, FormalAssertion.toSubcircuit_interactions,
          Gadgets.Equality.main, circuit_norm, List.filter_nil, List.nil_append]
        simp only [Channels.byteChannel_eq_stateChannel_false, if_false, List.append_nil]
        simp [Readers.CPUState.stateInteractions, Readers.CPUState.currentMsg,
          Readers.CPUState.nextMsg]
        exact ⟨rfl, rfl⟩
      · -- Memory branch: compositional — the I-type reader keeps its three Memory interactions and
        -- `RegisterWrite` its write push via the reader-local `_subcircuit` lemmas; every other
        -- child is nil.
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorIR, witnessField, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf, Operations.localLength]
        simp only [Operations.interactionsWith_witness,
          Soundness.iTypeReader_memoryInteractions_subcircuit,
          Soundness.registerWrite_memoryInteractions_subcircuit,
          InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
          InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
          AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
          Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
          Gadgets.Equality.channelsWithGuarantees_eq,
          Gadgets.Equality.channelsWithRequirements_eq,
          FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
          Channels.memoryChannel_eq_byteChannel_false,
          Channels.memoryChannel_eq_stateChannel_false, not_false_eq_true,
          Operations.interactionsWith_assert, Operations.interactionsWith_interact,
          Operations.interactionsWith_nil, Soundness.iTypeMemoryInteractions,
          Soundness.registerWriteMemoryInteractions, List.cons_append, List.nil_append]
        simp only [circuit_norm]
        simp only [Channels.byteChannel_eq_memoryChannel_false, if_false,
          exposedMemoryInteractions, List.map_cons, List.map_nil]
        rfl
      · -- Program branch: compositional — the reader subcircuit keeps its fetch via the
        -- reader-local `_subcircuit` lemma; every other child is nil on the Program channel.
        simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
          witnessVectorIR, witnessField, subcircuitWithAssertion, assertion, assertZero,
          HasAssertEq.assert_eq, Expression.assertEquals, Channel.pullIf, Operations.localLength]
        simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
          InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
          InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
          Soundness.iTypeReader_programInteractions_subcircuit,
          Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
          AddOperation.circuit, AddOperation.channelsWithGuarantees_eq,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
          FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
          Channels.programChannel_eq_byteChannel_false,
          Channels.programChannel_eq_stateChannel_false,
          Channels.programChannel_eq_memoryChannel_false,
          not_false_eq_true, Operations.interactionsWith_assert,
          Operations.interactionsWith_interact, Operations.interactionsWith_nil,
          List.map_cons, List.map_nil, List.nil_append, Soundness.iTypeProgramMessage]
        simp only [Operations.interactionsWith_subcircuit,
          FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
          List.filter_nil, List.nil_append]
        simp only [Channels.byteChannel_eq_programChannel_false, if_false] }

/-- Folded circuit projections used by whole-chip row codecs without unfolding
the proof-bearing circuit bundle. -/
@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 9 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 9 := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq]

/-- The completed Jalr circuit exposes exactly its State interaction pair. -/
theorem interactionsWith_state_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith stateChannel.toRaw =
      (exposedStateInteractions input offset).map ChannelInteraction.toRaw :=
  circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨stateChannel.toRaw,
      (exposedStateInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

private def cpuByteInteractionsRaw
    (input : Var Readers.CPUState.Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  [ (byteChannel.pulledIf input.is_real
      ⟨6, (input.cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨3, 0, input.cols.clk_16_24, 0⟩).toRaw ]

omit [Fact (2 ^ 17 < p)] in
private theorem cpuByteInteractions_exact
    (input : Var Readers.CPUState.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.CPUState.main input).operations offset).interactionsWith byteChannel.toRaw =
      cpuByteInteractionsRaw input := by
  simp [Readers.CPUState.main, cpuByteInteractionsRaw, circuit_norm]

private theorem cpuByteInteractions_subcircuit
    (input : Var Readers.CPUState.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit ((Readers.CPUState.circuit (p := p)).toSubcircuit offset input) :: ops) =
      cpuByteInteractionsRaw input ++
        Operations.interactionsWith byteChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.CPUState.circuit byteChannel.toRaw input offset ops _
    (cpuByteInteractions_exact input offset)

private def addByteInteractionsRaw
    (input : Var AddOperation.Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  [ (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.value[0], Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.value[1], Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.value[2], Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.value[3], Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw ]

omit [Fact (2 ^ 17 < p)] in
private theorem addByteInteractions_exact
    (input : Var AddOperation.Inputs (ZMod p)) (offset : ℕ) :
    ((AddOperation.main input).operations offset).interactionsWith byteChannel.toRaw =
      addByteInteractionsRaw input := by
  simp [AddOperation.main, addByteInteractionsRaw, circuit_norm]

private theorem addByteInteractions_subcircuit
    (input : Var AddOperation.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit ((AddOperation.circuit (p := p)).toSubcircuit offset input) :: ops) =
      addByteInteractionsRaw input ++
        Operations.interactionsWith byteChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_assertionSubcircuit_of_main_exact
    AddOperation.circuit byteChannel.toRaw input offset ops _
    (addByteInteractions_exact input offset)

private def iTypeByteInteractionsRaw
    (input : Var Readers.ITypeReader.Inputs (ZMod p)) :
    List (AbstractInteraction (ZMod p)) :=
  [ (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.op_a_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨3, 0,
       (input.clk_low + 4 - input.cols.op_a_memory.access_timestamp.prev_low - 1 -
          input.cols.op_a_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨6, input.cols.op_b_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩).toRaw,
    (byteChannel.pulledIf input.is_real
      ⟨3, 0,
       (input.clk_low + 3 - input.cols.op_b_memory.access_timestamp.prev_low - 1 -
          input.cols.op_b_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩).toRaw ]

private theorem iTypeByteInteractions_exact
    (input : Var Readers.ITypeReader.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.ITypeReader.main input).operations offset).interactionsWith byteChannel.toRaw =
      iTypeByteInteractionsRaw input := by
  simp [Readers.ITypeReader.main, Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main, Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, iTypeByteInteractionsRaw,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    circuit_norm]

private theorem iTypeByteInteractions_subcircuit
    (input : Var Readers.ITypeReader.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit
          ((Readers.ITypeReader.circuit (p := p)).toSubcircuit offset input) :: ops) =
      iTypeByteInteractionsRaw input ++
        Operations.interactionsWith byteChannel.toRaw ops :=
  InteractionRecovery.interactionsWith_generalSubcircuit_of_main_exact_list
    Readers.ITypeReader.circuit byteChannel.toRaw input offset ops _
    (iTypeByteInteractions_exact input offset)

omit [Fact (2 ^ 17 < p)] in
private theorem registerWriteByteInteractions_exact
    (input : Var Readers.RegisterWrite.Inputs (ZMod p)) (offset : ℕ) :
    ((Readers.RegisterWrite.main input).operations offset).interactionsWith byteChannel.toRaw =
      [] := by
  simp [Readers.RegisterWrite.main, circuit_norm]

private theorem registerWriteByteInteractions_subcircuit
    (input : Var Readers.RegisterWrite.Inputs (ZMod p))
    (offset : ℕ) (ops : Operations (ZMod p)) :
    Operations.interactionsWith byteChannel.toRaw
        (.subcircuit
          ((Readers.RegisterWrite.circuit (p := p)).toSubcircuit offset input) :: ops) =
      Operations.interactionsWith byteChannel.toRaw ops := by
  simpa only [List.nil_append] using
    InteractionRecovery.interactionsWith_assertionSubcircuit_of_main_exact
      Readers.RegisterWrite.circuit byteChannel.toRaw input offset ops []
      (registerWriteByteInteractions_exact input offset)

private def jalrByteInteractionsRaw
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (AbstractInteraction (ZMod p)) :=
  let jumpValue : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + i }
  let linkValue : Word (Expression (ZMod p)) :=
    Vector.mapRange 4 fun i => var { index := offset + 4 + i }
  let lsb : Expression (ZMod p) := var { index := offset + 8 }
  let cpuInput : Var Readers.CPUState.Inputs (ZMod p) :=
    ⟨input.state, #v[jumpValue[0] - lsb, jumpValue[1], jumpValue[2]],
      8, input.is_real⟩
  let jumpAddInput : Var AddOperation.Inputs (ZMod p) :=
    ⟨#v[input.adapter.op_b_memory.prev_value[0],
        input.adapter.op_b_memory.prev_value[1],
        input.adapter.op_b_memory.prev_value[2],
        input.adapter.op_b_memory.prev_value[3]],
      input.adapter.op_c_imm, { value := jumpValue }, input.is_real⟩
  let linkAddInput : Var AddOperation.Inputs (ZMod p) :=
    ⟨#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0],
      #v[4, 0, 0, 0], { value := linkValue },
      input.is_real - input.adapter.op_a_0⟩
  let readerInput : Var Readers.ITypeReader.Inputs (ZMod p) :=
    ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536,
      input.state.pc, 47, linkValue[0], linkValue[1],
      linkValue[2], linkValue[3]⟩
  cpuByteInteractionsRaw cpuInput ++
    addByteInteractionsRaw jumpAddInput ++
    addByteInteractionsRaw linkAddInput ++
    iTypeByteInteractionsRaw readerInput ++
    [ (byteChannel.pulledIf input.is_real
        ⟨6, (jumpValue[0] - lsb) * (4 : ZMod p)⁻¹,
         Expression.const ((14 : ℕ) : ZMod p), 0⟩).toRaw ]

omit [Fact (2 ^ 17 < p)] in
private theorem jalrByteInteractionsRaw_eq_exposed
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    jalrByteInteractionsRaw input offset =
      (exposedByteInteractions input offset).map ChannelInteraction.toRaw := by
  simp only [jalrByteInteractionsRaw, exposedByteInteractions,
    cpuByteInteractionsRaw, addByteInteractionsRaw,
    iTypeByteInteractionsRaw, circuit_norm, List.cons_append,
    List.nil_append, Nat.add_assoc, Nat.reduceAdd]

private theorem jalrByteInteractions_exact
    (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith byteChannel.toRaw =
      jalrByteInteractionsRaw input offset := by
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p))
      (ops : Operations (ZMod p)) =>
    @InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil
      (ZMod p) _ (ProvablePair field field) ProvablePair.instance
      (Gadgets.Equality.circuit field) byteChannel.toRaw n inp ops
      List.not_mem_nil List.not_mem_nil
  simp only [main, Circuit.operations, Circuit.bind_def, Circuit.pure_def,
    witnessVectorIR, witnessField,
    subcircuitWithAssertion, assertion, assertZero,
    HasAssertEq.assert_eq, Expression.assertEquals,
    Operations.localLength]
  simp only [Operations.interactionsWith_append,
    Operations.interactionsWith_witness,
    cpuByteInteractions_subcircuit, addByteInteractions_subcircuit,
    iTypeByteInteractions_subcircuit,
    registerWriteByteInteractions_subcircuit, heq,
    Operations.interactionsWith_assert,
    Operations.interactionsWith_nil, List.nil_append]
  simp only [jalrByteInteractionsRaw, cpuByteInteractionsRaw,
    addByteInteractionsRaw, iTypeByteInteractionsRaw,
    circuit_norm, List.cons_append, List.nil_append]

/-- The completed Jalr circuit emits exactly its fifteen Byte interactions. -/
theorem interactionsWith_byte_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith byteChannel.toRaw =
      (exposedByteInteractions input offset).map ChannelInteraction.toRaw :=
  (jalrByteInteractions_exact input offset).trans
    (jalrByteInteractionsRaw_eq_exposed input offset)

/-- The completed Jalr circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw :=
  circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

/-- The completed Jalr circuit exposes exactly its Program fetch. -/
theorem interactionsWith_program_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith programChannel.toRaw =
      (exposedProgramInteractions input).map ChannelInteraction.toRaw :=
  circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨programChannel.toRaw,
      (exposedProgramInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.JalrChip
