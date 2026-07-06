import SP1Clean.Native.Chips.MulChip.Defs
import SP1Clean.Math.EvalVec

/-! # `SP1Clean.MulChip` — `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.MulChip

open Circuit
open Extracted (MulCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- No soundness-side assumption (Option B memory flip): the operand `isU64`s are **derived** in soundness
from the `RTypeReader` reader sub-`Spec`'s memory read-prior pulls (bridged to the operation's flag-sum gate
by the `is_real = sum` row gate), not assumed — mirroring `AddChip`. -/
def Assumptions (_ : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := True

/-- Prover-side row well-formedness, with the reader column blocks as *threaded inputs* (mirrors
`AddChip.ProverAssumptions`): the operand `isU64`s, the `is_real` binary selector, the honest
`"mul_flags"` hint (each flag binary, the sum = `is_real`, `is_mulw` only on real rows), the
`op_a_0 = 0` flag, and the `is_real`-gated CPUState clock bounds + per-operand register-access
timestamp bounds (the verifier commits a well-formed clock/timestamp row). Soundness never assumes
these. -/
def ProverAssumptions (input : Inputs (ZMod p)) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (f[0] = 0 ∨ f[0] = 1) ∧ (f[1] = 0 ∨ f[1] = 1) ∧ (f[2] = 0 ∨ f[2] = 1) ∧
  (f[3] = 0 ∨ f[3] = 1) ∧ (f[4] = 0 ∨ f[4] = 1) ∧
  input.is_real = f[0] + f[1] + f[2] + f[3] + f[4] ∧
  (f[4] = 1 → input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩ ∧
  -- (W11 flip) the decode bounds the `RTypeReader` program **pull** now *derives* into its `Spec`
  -- (destination index `< 32`, pc limbs `< 2^16`, on real rows) — completeness must provide them.
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- SC Phase 2c: the honest prover supplies the State pull's `StateTruth`.
  (input.is_real = 1 → SP1Clean.Semantics.StateTruth (Readers.CPUState.stateMsgOf input.state) data) ∧
  -- SC Phase 2a: the honest prover supplies the Program pull's `ProgTruth` (the flag-weighted MUL*/MULW
  -- opcode `is_mul·11 + … + is_mulw·24`; `progMsgOf` ignores the `wv` fields, so the `0` placeholders are
  -- defeq to the actual reader input which carries the ALU-result `a` limbs).
  (input.is_real = 1 → SP1Clean.Semantics.ProgTruth
    (Readers.RTypeReader.progMsgOf
      ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536, input.state.pc,
       f[0] * 11 + f[1] * 12 + f[2] * 13 + f[3] * 14 + f[4] * 24, 0, 0, 0, 0⟩) data)

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨_hcpu, h_mulop, ha0, ha1, ha2, ha3, gb_mul, gb_mulh, gb_mulhu, gb_mulhsu, gb_mulw,
    gb_sum, hopa0, hadapter, h_eq_rs, _h_regwrite, h_gate⟩ := h_holds
  have bmul := bool_of_mul_pred gb_mul
  have bmulh := bool_of_mul_pred gb_mulh
  have bmulhu := bool_of_mul_pred gb_mulhu
  have bmulhsu := bool_of_mul_pred gb_mulhsu
  have bmulw := bool_of_mul_pred gb_mulw
  have bsum := bool_of_mul_pred gb_sum
  have h_bin := bool_of_mul_pred h_gate
  -- **Option B cycle-break.** No operand `isU64` is assumed (chip `Assumptions = True`). Apply the
  -- `RTypeReader` sub-soundness to get its `Spec`; its 7th conjunct is the memory-pull-derived operand `isU64`
  -- trio (gated on `is_real`). The `is_real = sum` row gate (`h_eq_rs`) bridges that to the operation's
  -- flag-sum gate, so the reader's operand `isU64` discharges `MulOperation`'s `sum = 1 → isU64` precondition.
  have h_rspec := hadapter ⟨h_bin, h_bin⟩
  have h_trio := h_rspec.2.2.2.2.2.2
  have h_rs : input_is_real
      = env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3) + env.get (i₀ + 4) :=
    add_neg_eq_zero.mp h_eq_rs
  have hbc : input_is_real = 1 → Word.isU64 input_adapter_op_b_memory_prev_value
      ∧ Word.isU64 input_adapter_op_c_memory_prev_value := fun hr => ⟨(h_trio hr).2.1, (h_trio hr).2.2⟩
  -- `is_mulw = 1 → sum = 1` (gate = flag-sum, SP1 `alu/mul/mod.rs:234`): one-hot via `sum_eq_one`.
  have h_mw := fun (hmw : (env.get (i₀ + 4) : ZMod p) = 1) =>
    MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inr hmw))))
  -- `MulOperation.Assumptions`: operands `isU64` when the sum-gate is active, bridged `sum = 1 → is_real = 1`
  -- via `h_rs`; flag binaries; `is_mulw → sum`; sum-bound. Inlined so the operation input (incl. `cols`) is
  -- inferred from `h_mulop`/`result_semantic`/the goal rather than left ambiguous.
  have h_spec := h_mulop
    ⟨fun hsum => hbc (h_rs.trans hsum), bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩
  -- RegisterWrite owes `is_real = 1 → isU64 a`; on a real row `sum = 1` (via `h_rs`), so `a = resultWord`
  -- (`aSelector` linkage) is `isU64` from `result_semantic`.
  have h_a_isU64 : input_is_real = 1 →
      Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 50 + i })) := by
    intro hr
    have hsum1 : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3) + env.get (i₀ + 4) = 1 :=
      h_rs ▸ hr
    obtain ⟨hisU64, _, _, _, _, _⟩ := MulOperation.result_semantic
      ⟨fun hsum => hbc (h_rs.trans hsum), bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [show (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 50 + i }))
        = MulOperation.resultWord _ _ from ?_]
    · exact hisU64
    · rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
      apply Vector.ext; intro k hk; interval_cases k <;>
        simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
          Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
        first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  refine ⟨⟨h_rspec, h_bin, fun hr => ⟨?_, ?_, ?_, ?_, ?_⟩⟩, h_bin,
    Or.inr ⟨fun hsum => hbc (h_rs.trans hsum), bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩,
    Or.inr ⟨h_bin, h_bin⟩, Or.inr ⟨h_bin, h_a_isU64⟩⟩
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inl h1)
    obtain ⟨_hisU64, hmul, _hmulhu, _hmulh, _hmulhsu, _hmulw⟩ :=
      MulOperation.result_semantic ⟨fun hsum => hbc (h_rs.trans hsum), bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mul_eq, ← hmul h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inl h1))
    obtain ⟨_hisU64, _hmul, _hmulhu, hmulh, _hmulhsu, _hmulw⟩ :=
      MulOperation.result_semantic ⟨fun hsum => hbc (h_rs.trans hsum), bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mulh_eq, ← hmulh h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inl h1)))
    obtain ⟨_hisU64, _hmul, hmulhu, _hmulh, _hmulhsu, _hmulw⟩ :=
      MulOperation.result_semantic ⟨fun hsum => hbc (h_rs.trans hsum), bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mulhu_eq, ← hmulhu h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    obtain ⟨_hisU64, _hmul, _hmulhu, _hmulh, hmulhsu, _hmulw⟩ :=
      MulOperation.result_semantic ⟨fun hsum => hbc (h_rs.trans hsum), bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mulhsu_eq, ← hmulhsu h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inr h1))))
    obtain ⟨_hisU64, _hmul, _hmulhu, _hmulh, _hmulhsu, hmulw⟩ :=
      MulOperation.result_semantic ⟨fun hsum => hbc (h_rs.trans hsum), bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec hsum1
    rw [rv64_mulw_eq, ← hmulw h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    apply Vector.ext; intro k hk; interval_cases k <;>
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, Nat.reduceLT, dif_pos] <;>
      first | exact ha0 | exact ha1 | exact ha2 | exact ha3

set_option maxHeartbeats 40000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨hbU, hcU, ha_prev, hbin, hf0, hf1, hf2, hf3, hf4, hsum, hmulw_real, hop_a_0, h_cpu,
    hrac_a, hrac_b, hrac_c, hdec, h_st, h_prog⟩ := h_assumptions
  -- `h_env` now bundles the CPUState GFC obligation (SC Phase 2c, prepended) + the `flags`/`cols`/`a`
  -- witness-gen equations + the GFC `RTypeReader` subcircuit's completeness obligation (trailing).
  obtain ⟨-, h_env_flags, h_env_cols, h_env_a, -⟩ := h_env
  obtain ⟨-, ⟨-, -, -, hpc⟩, -, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩ := h_input
  -- the five variant flags are witnessed from the `"mul_flags"` hint
  have hflag0 : env.get i₀ = (hintFlags env.hint)[0] := by simpa using h_env_flags 0
  have hflag1 : env.get (i₀ + 1) = (hintFlags env.hint)[1] := by simpa using h_env_flags 1
  have hflag2 : env.get (i₀ + 2) = (hintFlags env.hint)[2] := by simpa using h_env_flags 2
  have hflag3 : env.get (i₀ + 3) = (hintFlags env.hint)[3] := by simpa using h_env_flags 3
  have hflag4 : env.get (i₀ + 4) = (hintFlags env.hint)[4] := by simpa using h_env_flags 4
  have hf0' : env.get i₀ = 0 ∨ env.get i₀ = 1 := by rw [hflag0]; exact hf0
  have hf1' : env.get (i₀ + 1) = 0 ∨ env.get (i₀ + 1) = 1 := by rw [hflag1]; exact hf1
  have hf2' : env.get (i₀ + 2) = 0 ∨ env.get (i₀ + 2) = 1 := by rw [hflag2]; exact hf2
  have hf3' : env.get (i₀ + 3) = 0 ∨ env.get (i₀ + 3) = 1 := by rw [hflag3]; exact hf3
  have hf4' : env.get (i₀ + 4) = 0 ∨ env.get (i₀ + 4) = 1 := by rw [hflag4]; exact hf4
  have hsumc : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
      + env.get (i₀ + 4) = input_is_real := by
    rw [hflag0, hflag1, hflag2, hflag3, hflag4]; exact hsum.symm
  have hsum01' : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
        + env.get (i₀ + 4) = 0
      ∨ env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3)
        + env.get (i₀ + 4) = 1 := by
    rw [hsumc]; exact hbin
  have hmw' : env.get (i₀ + 4) = 1 → env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2)
      + env.get (i₀ + 3) + env.get (i₀ + 4) = 1 := fun h => by
    rw [hsumc]; exact hmulw_real (by rw [← hflag4]; exact h)
  have epc : ∀ (i : ℕ) (hi : i < 3),
      Expression.eval env.toEnvironment input_var_state_pc[i] = input_state_pc[i] :=
    fun i hi => by rw [← hpc, Vector.getElem_map]
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have hbool : ∀ x : ZMod p, x = 0 ∨ x = 1 → x * (x + -1) = 0 := by
    rintro x (h | h) <;> rw [h] <;> simp
  -- fold the witness hint's `populate` operands to the evaluated input words
  simp only [Inputs.op_b_val, Inputs.op_c_val, vec4_eval, hob, hoc] at h_env_cols
  rw [← epc 0 (by norm_num), ← epc 1 (by norm_num), ← epc 2 (by norm_num)] at h_cpu
  refine ⟨⟨hbin, h_cpu, h_st⟩,
    ⟨⟨fun _ => ⟨hbU, hcU⟩, hsum01', hmw', hf0', hf1', hf2', hf3', hf4', hsum01'⟩, ?_⟩,
    by simpa using h_env_a 0, by simpa using h_env_a 1,
    by simpa using h_env_a 2, by simpa using h_env_a 3,
    hbool _ hf0', hbool _ hf1', hbool _ hf2', hbool _ hf3', hbool _ hf4', hbool _ hsum01',
    hop_a_0,
    ⟨⟨hbin, hbin⟩, ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c, hdec,
      fun hr => ⟨ha_prev hr, hbU, hcU⟩⟩, ?_⟩,
    ?_, ⟨⟨hbin, ?_⟩, trivial⟩, ?_⟩
  · -- the composed `MulOperation` `FormalAssertion`'s `Spec` at the witnessed `populate`d columns:
    -- `spec_populate` once the witnessed column struct equals `populate …` (each cell is
    -- `env.get (i₀+5+k)`, pinned by the normalised witness hint to `(toElements (populate …))[k]`).
    convert MulOperation.spec_populate (b := input_adapter_op_b_memory_prev_value)
      (c := input_adapter_op_c_memory_prev_value) hbU hcU
      (env.get i₀) (env.get (i₀ + 1)) (env.get (i₀ + 2)) (env.get (i₀ + 3)) (env.get (i₀ + 4))
      (env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3) + env.get (i₀ + 4))
      hf0' hf1' hf2' hf3' hf4' hsum01' using 2
    refine (ProvableType.ext_iff _ _).mpr (fun i hi => ?_)
    refine Eq.trans ?_
      ((getElem_toElements_eval_varFromOffset env.toEnvironment (i₀ + 5) i hi).trans
        (h_env_cols ⟨i, hi⟩))
    simp [circuit_norm]
  · -- Program pull `ProgTruth`: the dummy `progMsgOf` opcode uses the hint flags `(hintFlags env.hint)[k]`;
    -- the goal's opcode uses the witnessed flag columns `env.get (i₀+k)`. Bridge them via `hflag*` (the `wv`
    -- fields differ but `progMsgOf` ignores them, so `exact h_prog` closes up-to-defeq), then hand off `h_prog`.
    intro hr
    rw [hflag0, hflag1, hflag2, hflag3, hflag4]
    exact h_prog hr
  · -- the `is_real = sum` row gate: the prover sets `is_real = Σ flags` (`hsumc`).
    linear_combination -hsumc
  · -- RegisterWrite's `isU64 value` (op_a write push): on a real row the witnessed `a` equals the selected
    -- product slice = `resultWord (populate …)`, whose `isU64` is `spec_populate`'s `result_semantic`.
    intro hr
    have hsum1 : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3) + env.get (i₀ + 4) = 1 :=
      hsumc.trans hr
    have h_mulspec := MulOperation.spec_populate (b := input_adapter_op_b_memory_prev_value)
      (c := input_adapter_op_c_memory_prev_value) hbU hcU
      (env.get i₀) (env.get (i₀ + 1)) (env.get (i₀ + 2)) (env.get (i₀ + 3)) (env.get (i₀ + 4))
      (env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3) + env.get (i₀ + 4))
      hf0' hf1' hf2' hf3' hf4' hsum01'
    obtain ⟨hisU64, _, _, _, _, _⟩ := MulOperation.result_semantic
      ⟨fun _ => ⟨hbU, hcU⟩, hsum01', hmw', hf0', hf1', hf2', hf3', hf4', hsum01'⟩ h_mulspec hsum1
    rw [show (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var { index := i₀ + 5 + 45 + i }))
        = MulOperation.resultWord _ _ from ?_]
    · exact hisU64
    · -- The `a` slices (`h_env_a`) reference the witnessed product columns `env.get (i₀+5+16+j)`, while
      -- `aSelector (populate)` references `(populate).product[j]`; they agree because the chip witnesses the
      -- columns to `populate` (`h_env_cols` + `getElem_toElements_eval_varFromOffset`).
      have hprod : ∀ (j : ℕ) (hj : j < 16),
          (MulOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value
            (env.get (i₀ + 1)) (env.get (i₀ + 3)) (env.get (i₀ + 4))).product[j]'(by omega)
            = env.get (i₀ + 5 + 16 + j) := fun j hj => by
        have key : (MulOperation.populate input_adapter_op_b_memory_prev_value
              input_adapter_op_c_memory_prev_value
              (env.get (i₀ + 1)) (env.get (i₀ + 3)) (env.get (i₀ + 4))).product[j]'(by omega)
            = (ProvableType.toElements (MulOperation.populate input_adapter_op_b_memory_prev_value
                input_adapter_op_c_memory_prev_value
                (env.get (i₀ + 1)) (env.get (i₀ + 3)) (env.get (i₀ + 4))))[16 + j]'(by
              have : ProvableStruct.combinedSize Extracted.MulOperation = 45 := by decide
              show 16 + j < ProvableStruct.combinedSize Extracted.MulOperation; omega) := by
          simp only [circuit_norm, explicit_provable_type]
          rw [Vector.getElem_append_right (by omega) (by omega), Vector.getElem_append_left (by omega)]
          congr 1; omega
        rw [key]
        exact (h_env_cols ⟨16 + j, by omega⟩).symm.trans (by dsimp only; congr 1; omega)
      have hpmsb : (MulOperation.populate input_adapter_op_b_memory_prev_value
            input_adapter_op_c_memory_prev_value
            (env.get (i₀ + 1)) (env.get (i₀ + 3)) (env.get (i₀ + 4))).product_msb.msb
          = env.get (i₀ + 5 + 16 + 16 + 4 + 4 + 1 + 1) := by
        have key : (MulOperation.populate input_adapter_op_b_memory_prev_value
              input_adapter_op_c_memory_prev_value
              (env.get (i₀ + 1)) (env.get (i₀ + 3)) (env.get (i₀ + 4))).product_msb.msb
            = (ProvableType.toElements (MulOperation.populate input_adapter_op_b_memory_prev_value
                input_adapter_op_c_memory_prev_value
                (env.get (i₀ + 1)) (env.get (i₀ + 3)) (env.get (i₀ + 4))))[42]'(by
              show 42 < ProvableStruct.combinedSize Extracted.MulOperation; decide) := by
          simp only [circuit_norm, explicit_provable_type]
          rw [Vector.getElem_append_right (by decide) (by decide),
              Vector.getElem_append_right (by decide) (by decide),
              Vector.getElem_append_right (by decide) (by decide),
              Vector.getElem_append_right (by decide) (by decide),
              Vector.getElem_append_right (by decide) (by decide),
              Vector.getElem_append_right (by decide) (by decide),
              Vector.getElem_append_left (by decide)]
          rfl
        rw [key]; exact (h_env_cols ⟨42, by omega⟩).symm.trans (by congr 1)
      rw [← MulOperation.aSelector_eq_resultWord _ _ hf0' hf1' hf2' hf3' hf4' hsum1]
      apply Vector.ext; intro k hk; interval_cases k <;>
        simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
          Vector.getElem_mapRange, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
          List.getElem_cons_succ, Nat.reduceLT, dif_pos, hprod, hpmsb] <;>
        first | exact h_env_a 0 | exact h_env_a 1 | exact h_env_a 2 | exact h_env_a 3
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- The `Mul` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `mul`/`mulh`/`mulhu`/`mulhsu`/`mulw`
semantic contract; output is the extracted `MulCols` column struct. Soundness/completeness are proven
and axiom-clean (completeness via `MulOperation.spec_populate` on the witnessed columns). -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs MulCols :=
  { main, elaborated,
    -- `programChannel` dropped (W11 flip — now pulled via `RTypeReader`, a guarantee not a requirement).
    channelsWithRequirements := [stateChannel.toRaw, memoryChannel.toRaw],
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    -- W11 (A2): expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8)
    -- so the chip is a `VmTables` table; descends to the composed `CPUState` subcircuit's lone pull+push.
    exposedChannels := fun input _ =>
      stateChannel.expose
        [ stateChannel.pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ],
    exposedChannels_eq := by
      intro input offset
      simp only [Operations.ExposedChannelsLawful, VmChannel.expose, List.mem_singleton, forall_eq,
        List.map_cons, List.map_nil]
      simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
        Readers.RTypeReader.circuit, Readers.RTypeReader.main,
        Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
        Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
        Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        SP1Clean.MulOperation.circuit, SP1Clean.MulOperation.main,
        SP1Clean.U16toU8OperationSafe.circuit, SP1Clean.U16toU8OperationSafe.main,
        SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
        circuit_norm, FormalAssertion.toSubcircuit_interactions,
        GeneralFormalCircuit.toSubcircuit_interactions]
      simp [circuit_norm, Gadgets.Equality.main, VmChannel.pulledIf, VmChannel.pushedIf] }

end SP1Clean.MulChip
