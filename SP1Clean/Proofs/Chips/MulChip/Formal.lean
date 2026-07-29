import SP1Clean.Native.Chips.MulChip.Defs
import SP1Clean.Math.EvalVec
import SP1Clean.Proofs.Chips.MulChip.Structural
import Clean.Air.Circuit

/-! # `SP1Clean.MulChip` — `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.MulChip

open Circuit
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
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
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
  -- G1: the three pulled prior records' 24-bit access clocks (`Channels.MemoryMsg.ClkBound`, the clock
  -- half of the memory channel's `Guarantees`) — see `AddChip.ProverAssumptions`. Soundness does *not*
  -- assume these; there they are derived from the pulls themselves.
  (input.is_real = 1 →
    input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_c_memory.access_timestamp.prev_low.val < 2 ^ 24)

omit [Fact (2 ^ 24 < p)] in
/-- Four consecutive evaluated witness cells assemble the 4-limb word `#v[v0, v1, v2, v3]`. Applied
symbolically at the six sites in `soundness` that must identify the witnessed register-write word `a`
with `MulOperation.aSelector` — the flag-weighted product slice — one per RV64 variant plus the
`RegisterWrite` `isU64` obligation. -/
private lemma evalWord4_of_cells {env : Environment (ZMod p)} {o : ℕ} {v0 v1 v2 v3 : ZMod p}
    (h0 : env.get o = v0) (h1 : env.get (o + 1) = v1)
    (h2 : env.get (o + 2) = v2) (h3 : env.get (o + 3) = v3) :
    Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := o + i })
      = #v[v0, v1, v2, v3] := by
  apply Vector.ext; intro k hk
  interval_cases k <;>
    simp only [Vector.getElem_map, Vector.getElem_mapRange, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero, List.getElem_cons_succ] <;>
    assumption

-- Measured (W5/b8): the former 4M was ~50x over; floor bracket (60k, 80k] after the six
-- `aSelector` tails were factored through `evalWord4_of_cells` (it was (80k, 100k] before).
set_option maxHeartbeats 400000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_cpu, h_mulop, ha0, ha1, ha2, ha3, gb_mul, gb_mulh, gb_mulhu, gb_mulhsu, gb_mulw,
    gb_sum, hopa0, hadapter, h_eq_rs, _h_regwrite, h_gate⟩ := h_holds
  have ha0_real (hr : input_is_real = 1) := sub_eq_zero.mp (by simpa only [hr, one_mul] using ha0)
  have ha1_real (hr : input_is_real = 1) := sub_eq_zero.mp (by simpa only [hr, one_mul] using ha1)
  have ha2_real (hr : input_is_real = 1) := sub_eq_zero.mp (by simpa only [hr, one_mul] using ha2)
  have ha3_real (hr : input_is_real = 1) := sub_eq_zero.mp (by simpa only [hr, one_mul] using ha3)
  -- On a real row the witnessed word `a` (cells `i₀+50..53`) *is* `MulOperation.aSelector` — the
  -- flag-weighted product slice — spelled as the 4-limb literal. Shared by all six `resultWord` sites.
  have hA (hr : input_is_real = 1) :=
    evalWord4_of_cells (ha0_real hr) (ha1_real hr) (ha2_real hr) (ha3_real hr)
  have bmul := bool_of_mul_pred gb_mul
  have bmulh := bool_of_mul_pred gb_mulh
  have bmulhu := bool_of_mul_pred gb_mulhu
  have bmulhsu := bool_of_mul_pred gb_mulhsu
  have bmulw := bool_of_mul_pred gb_mulw
  have bsum := bool_of_mul_pred gb_sum
  have h_bin := bool_of_mul_pred h_gate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's `MemoryMsg.ClkBound` guarantee — `RTypeReader`'s two read-back pushes (`clk_low + 3` /
  -- `+ 2`) and `RegisterWrite`'s op_a write push (`clk_low + 4`). The offset is left to unification,
  -- so this line never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  -- No operand range is assumed by the chip: `MulOperation` derives both operand bounds from its
  -- own safe byte decompositions. The reader `Spec` remains the public register-read contract.
  have h_rspec := hadapter ⟨h_bin, h_bin, h_clk⟩
  have h_rs : input_is_real
      = env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3) + env.get (i₀ + 4) :=
    sub_eq_zero.mp h_eq_rs
  -- `is_mulw = 1 → sum = 1` (gate = flag-sum, SP1 `alu/mul/mod.rs:234`): one-hot via `sum_eq_one`.
  have h_mw := fun (hmw : (env.get (i₀ + 4) : ZMod p) = 1) =>
    MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inr hmw))))
  -- `MulOperation.Assumptions`: row/flag binaries, `is_mulw → sum`, and the sum bound. Inlined so
  -- the operation input (including `cols`) is inferred from `h_mulop`/`result_semantic`/the goal.
  have h_spec := h_mulop
    ⟨bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩
  -- The operation's semantic readout, awaiting only `sum = 1`. Its conjuncts, in order:
  -- `isU64 resultWord`, then the `MUL`, `MULHU`, `MULH`, `MULHSU`, `MULW` BitVec identities.
  have hsem := MulOperation.result_semantic
    ⟨bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec
  -- RegisterWrite owes `is_real = 1 → isU64 a`; on a real row `sum = 1` (via `h_rs`), so `a = resultWord`
  -- (`aSelector` linkage) is `isU64` from `result_semantic`.
  have h_a_isU64 : input_is_real = 1 →
      Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 50 + i })) := by
    intro hr
    have hsum1 : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3) + env.get (i₀ + 4) = 1 :=
      h_rs ▸ hr
    rw [show (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 50 + i }))
        = MulOperation.resultWord _ _ from ?_]
    · exact (hsem hsum1).1
    · rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Nat.reduceLT, dif_pos]
      exact hA hr
  refine ⟨⟨h_rspec, h_bin, fun hr => ⟨?_, ?_, ?_, ?_, ?_⟩,
      -- F-A4-01: the exported selector one-hot — the five boolean gates + `is_real = Σ flags`.
      fun hr => by simpa only [SelectorOneHot, selectors] using
        MulOperation.oneHot_of_sum_one bmul bmulh bmulhu bmulhsu bmulw (h_rs.symm.trans hr)⟩,
    Or.inr ⟨bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩,
    Or.inr ⟨h_bin, h_bin, h_clk⟩,
    Or.inr ⟨h_bin, h_a_isU64, h_clk.at_four⟩⟩
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inl h1)
    rw [rv64_mul_eq, ← (hsem hsum1).2.1 h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
      Vector.getElem_mapRange, Nat.reduceLT, dif_pos]
    exact hA (h_rs.trans hsum1)
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inl h1))
    rw [rv64_mulh_eq, ← (hsem hsum1).2.2.2.1 h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
      Vector.getElem_mapRange, Nat.reduceLT, dif_pos]
    exact hA (h_rs.trans hsum1)
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inl h1)))
    rw [rv64_mulhu_eq, ← (hsem hsum1).2.2.1 h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
      Vector.getElem_mapRange, Nat.reduceLT, dif_pos]
    exact hA (h_rs.trans hsum1)
  · intro h1
    have hsum1 :=
      MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    rw [rv64_mulhsu_eq, ← (hsem hsum1).2.2.2.2.1 h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
      Vector.getElem_mapRange, Nat.reduceLT, dif_pos]
    exact hA (h_rs.trans hsum1)
  · intro h1
    have hsum1 :=
      MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inr h1))))
    rw [rv64_mulw_eq, ← (hsem hsum1).2.2.2.2.2 h1]; congr 1
    rw [← MulOperation.aSelector_eq_resultWord _ _ bmul bmulh bmulhu bmulhsu bmulw hsum1]
    simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
      Vector.getElem_mapRange, Nat.reduceLT, dif_pos]
    exact hA (h_rs.trans hsum1)

-- Whole-chip completeness must normalize the 54-cell witness stream (5 flags + the 45-cell
-- `MulOperation` populate + the 4-cell result) against every composed reader/operation obligation
-- in one `circuit_proof_start` pass — the largest single witness closure in the tree, so the
-- ceiling is genuine. Measured (W5/b8): the former 128M was ~1600x over; floor bracket (60k, 80k].
set_option maxHeartbeats 400000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨hbU, hcU, ha_prev, hbin, hf0, hf1, hf2, hf3, hf4, hsum, hmw_real, hop_a_0, h_cpu,
    hrac_a, hrac_b, hrac_c, hdec, hprevclk⟩ := h_assumptions
  -- G1: the *push* side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩ := h_input
  -- `h_env` bundles the CPUState GFC obligation (discarded), the flags/`cols`/`a` witness-gen
  -- equations, and the trailing `RTypeReader` GFC obligation (discarded).
  obtain ⟨-, h_env_flags, h_env_cols, h_env_a, -⟩ := h_env
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
    rw [hsumc]; exact hmw_real (by rw [← hflag4]; exact h)
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have hbool : ∀ x : ZMod p, x = 0 ∨ x = 1 → x * (x - 1) = 0 := by
    rintro x (h | h) <;> rw [h] <;> simp
  -- fold the witness hint's `populate` operands to the evaluated input words
  simp only [Inputs.op_b_val, Inputs.op_c_val, vec4_eval] at h_env_cols
  -- Ascribe `h_env_cols`'s IR-native RHS into the plain `toElements (populate …)` form via a
  -- *definitional* `have` (the CHEAP reduction), then fold the prev-value operands via `hob`/`hoc` —
  -- the 4.31 `combinedSize'`/`nativeValue` fix (`docs/proposals/consolidation-progress.md`, "PATTERN
  -- FULLY PROVEN"). One reusable per-index fact serves both the `Spec` conversion below and the
  -- `RegisterWrite` `isU64` bullet's `product`/`product_msb` reads.
  have h_env_cols' : ∀ (i : ℕ) (hi : i < 45), env.toEnvironment.get (i₀ + 5 + i)
      = (toElements (MulOperation.populate input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value
          (env.get (i₀ + 1)) (env.get (i₀ + 3)) (env.get (i₀ + 4))))[i]'hi := fun i hi => by
    have hc : env.toEnvironment.get (i₀ + 5 + i)
        = (toElements (MulOperation.populate
            (Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_b_memory_prev_value)
            (Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_c_memory_prev_value)
            (env.get (i₀ + 1)) (env.get (i₀ + 3)) (env.get (i₀ + 4))))[i]'hi := h_env_cols ⟨i, hi⟩
    rwa [hob, hoc] at hc
  -- The full witnessed-`cols` struct equals `populate …` (per-cell, via `getElem_toElements_eval_
  -- varFromOffset` + `h_env_cols'`) — reused both by the `Spec` conversion below and by the
  -- `RegisterWrite` `isU64` bullet's `product`/`product_msb` field reads (sidesteps any manual
  -- `toElements`/`Vector.getElem_append_*`/cast reasoning about `MulOperation`'s 9-field layout).
  have hcols_eq : Eval.eval env.toEnvironment
      (ProvableStruct.varFromOffset Extracted.MulOperation (i₀ + 5) : Var Extracted.MulOperation (ZMod p))
      = MulOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value
          (env.get (i₀ + 1)) (env.get (i₀ + 3)) (env.get (i₀ + 4)) :=
    (ProvableType.ext_iff (α := Extracted.MulOperation) _ _).mpr (fun i hi =>
      (getElem_toElements_eval_varFromOffset env.toEnvironment (i₀ + 5) i hi).trans (h_env_cols' i hi))
  refine ⟨⟨hbin, h_cpu⟩,
    ⟨⟨hsum01', hmw', hf0', hf1', hf2', hf3', hf4', hsum01'⟩, ?_⟩,
    by rw [sub_eq_zero.mpr (by simpa using h_env_a 0), mul_zero],
    by rw [sub_eq_zero.mpr (by simpa using h_env_a 1), mul_zero],
    by rw [sub_eq_zero.mpr (by simpa using h_env_a 2), mul_zero],
    by rw [sub_eq_zero.mpr (by simpa using h_env_a 3), mul_zero],
    hbool _ hf0', hbool _ hf1', hbool _ hf2', hbool _ hf3', hbool _ hf4', hbool _ hsum01',
    hop_a_0,
    ⟨⟨hbin, hbin, h_clk⟩,
      ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c, hdec,
        fun hr => ⟨ha_prev hr, hbU, hcU, (hprevclk hr).1, (hprevclk hr).2.1, (hprevclk hr).2.2⟩⟩⟩,
    by linear_combination -hsumc,
    ⟨⟨hbin, ?_, h_clk.at_four⟩, trivial⟩,
    by rcases hbin with h | h <;> rw [h] <;> simp⟩
  · -- `MulOperation.circuit.Spec` at the witnessed columns: the structural `spec_populate` once the
    -- witnessed struct equals `populate …` (each cell is `env.get (i₀+5+k)`, pinned by `h_env_cols'`).
    convert MulOperation.spec_populate (b := input_adapter_op_b_memory_prev_value)
      (c := input_adapter_op_c_memory_prev_value) hbU hcU
      (env.get i₀) (env.get (i₀ + 1)) (env.get (i₀ + 2)) (env.get (i₀ + 3)) (env.get (i₀ + 4))
      (env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3) + env.get (i₀ + 4))
      hf0' hf1' hf2' hf3' hf4' hsum01' using 2
    rfl
    simpa only [circuit_norm] using hcols_eq
  · -- RegisterWrite's `isU64 value` (the op_a write push): on a real row the witnessed `a` equals the
    -- selected product slice `resultWord (populate …)`, whose `isU64` is `spec_populate`'s
    -- `result_semantic`.
    intro hr
    have hsum1 : env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3) + env.get (i₀ + 4) = 1 :=
      hsumc.trans hr
    have h_mulspec := MulOperation.spec_populate (b := input_adapter_op_b_memory_prev_value)
      (c := input_adapter_op_c_memory_prev_value) hbU hcU
      (env.get i₀) (env.get (i₀ + 1)) (env.get (i₀ + 2)) (env.get (i₀ + 3)) (env.get (i₀ + 4))
      (env.get i₀ + env.get (i₀ + 1) + env.get (i₀ + 2) + env.get (i₀ + 3) + env.get (i₀ + 4))
      hf0' hf1' hf2' hf3' hf4' hsum01'
    obtain ⟨hisU64, _, _, _, _, _⟩ := MulOperation.result_semantic
      ⟨hsum01', hmw', hf0', hf1', hf2', hf3', hf4', hsum01'⟩ h_mulspec hsum1
    rw [show (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var { index := i₀ + 5 + 45 + i }))
        = MulOperation.resultWord _ _ from ?_]
    · exact hisU64
    · -- The `a` slices (`h_env_a`) reference the witnessed product columns `env.get (i₀+5+16+j)`, while
      -- `aSelector (populate)` references `(populate).product[j]`; they agree because the chip witnesses
      -- the columns to `populate` (`h_env_cols'`).
      have hprod : ∀ (j : ℕ) (hj : j < 16),
          (MulOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value
            (env.get (i₀ + 1)) (env.get (i₀ + 3)) (env.get (i₀ + 4))).product[j]'(by omega)
            = env.get (i₀ + 5 + 16 + j) := fun j hj => by
        rw [← hcols_eq]; simp only [circuit_norm]
      have hpmsb : (MulOperation.populate input_adapter_op_b_memory_prev_value
            input_adapter_op_c_memory_prev_value
            (env.get (i₀ + 1)) (env.get (i₀ + 3)) (env.get (i₀ + 4))).product_msb.msb
          = env.get (i₀ + 5 + 16 + 16 + 4 + 4 + 1 + 1) := by
        rw [← hcols_eq]; simp only [circuit_norm]
      rw [← MulOperation.aSelector_eq_resultWord _ _ hf0' hf1' hf2' hf3' hf4' hsum1]
      simp only [MulOperation.aSelector, MulOperation.productVal, Nat.reduceLT, dif_pos,
        hprod, hpmsb]
      exact evalWord4_of_cells (h_env_a 0) (h_env_a 1) (h_env_a 2) (h_env_a 3)

/-- Exact State-channel pair emitted by the composed CPU-state reader. -/
def exposedStateInteractions (input : Var Inputs (ZMod p)) :
    List (ChannelInteraction (stateChannel (p := p))) :=
  [ stateChannel.pulledIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536,
       input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
    stateChannel.pushedIf input.is_real
      ⟨input.state.clk_high,
       input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
       input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ]

/-- Mul's exact Memory-channel interaction list.  The op_a write push carries the witnessed result
word `a` (cells `offset+50..53` — after the 5 variant flags and the 45 `MulOperation` columns).
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
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2,
       input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, Vector.mapRange 4 fun i => var { index := offset + 50 + i }⟩ ]

omit [Fact (2 ^ 24 < p)] in
/-- The exact source-B pull occupies its declared slot in Mul's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 24 < p)] in
/-- The exact source-C pull occupies its declared slot in Mul's exposed Memory list. -/
theorem opCPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c, 0, 0, input.adapter.op_c_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The Program-fetch opcode committed by the witnessed one-hot variant flags (cells `offset+0..4`):
`MUL·11 + MULH·12 + MULHU·13 + MULHSU·14 + MULW·24`.  Named so the exposed pull and
`Soundness/TypedProgram.lean` share one statement-level expression instead of raw witness indices. -/
def exposedOpcode (offset : ℕ) : Expression (ZMod p) :=
  var ⟨offset⟩ * 11 + var ⟨offset + 1⟩ * 12 + var ⟨offset + 2⟩ * 13 +
    var ⟨offset + 3⟩ * 14 + var ⟨offset + 4⟩ * 24

/-- Exact Program fetch emitted by the R-type adapter, with the instruction opcode reconstructed
from the five chip-owned variant flags. -/
def exposedProgramInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf input.is_real
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
       exposedOpcode offset, input.adapter.op_a,
       #v[input.adapter.op_b, 0, 0, 0],
       #v[input.adapter.op_c, 0, 0, 0],
       input.adapter.op_a_0, 0, 0⟩ ]

-- The tightest site in this file: measured (W5/b8) floor bracket (150k, 200k] — under 1.5x
-- headroom against the plain default — so the former 8M was only ~40x over, not removable.
set_option maxHeartbeats 800000 in
/-- The `Mul` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `mul`/`mulh`/`mulhu`/`mulhsu`/`mulw`
semantic contract; output is the native `Columns` row. Soundness is proved; completeness is
the explicitly disclosed 4.31 migration seam above. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  { main, elaborated,
    -- `programChannel` dropped (W11 flip — now pulled via `RTypeReader`, a guarantee not a requirement).
    channelsWithRequirements := [stateChannel.toRaw, memoryChannel.toRaw],
    requirementsChannelsLawful := requirementsChannelsLawful_main,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    -- W11 (A2): expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8)
    -- so the chip is a `VmTables` table; descends to the composed `CPUState` subcircuit's lone pull+push.
    exposedChannels := fun input offset =>
      expose stateChannel (exposedStateInteractions input) ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `RTypeReader`, gate
      -- `is_trusted = is_real`, opcode = the committed one-hot flag encoding), consumed by
      -- `Soundness/TypedProgram.lean`.
      expose programChannel (exposedProgramInteractions input offset),
    exposedChannels_eq := by
      intro input offset
      have h_byte := Channels.byteChannel_toRaw_ne_stateChannel (p := p)
      have h_program := Channels.programChannel_toRaw_ne_stateChannel (p := p)
      have h_memory := Channels.memoryChannel_toRaw_ne_stateChannel (p := p)
      unfold Operations.ExposedChannelsLawful
      intro exposed exposedMem
      simp only [expose, exposedStateInteractions, exposedProgramInteractions,
        List.mem_append, List.mem_singleton] at exposedMem
      rcases exposedMem with (rfl | rfl) | rfl
      -- Program branch first: compositional — the reader subcircuit keeps its fetch via the
      -- reader-local `_subcircuit` lemma; every other child is nil on the Program channel. The
      -- State and Memory branches then share one descent through the composed children.
      rotate_left 2
      · simp only [main, Circuit.operations, Circuit.bind_def,
          Circuit.pure_def, witnessVectorNative, witnessNative, subcircuitWithAssertion,
          assertion, assertZero, Operations.localLength]
        simp only [Operations.interactionsWith_append, Operations.interactionsWith_witness,
          InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
          InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
          Soundness.rTypeReader_programInteractions_subcircuit,
          Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
          SP1Clean.MulOperation.circuit, MulOperation.channelsWithGuarantees_eq,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
          FormalCircuitBase.channelsWithGuarantees_def,
          List.mem_cons, List.not_mem_nil, or_false,
          Channels.programChannel_eq_byteChannel_false,
          Channels.programChannel_eq_stateChannel_false,
          Channels.programChannel_eq_memoryChannel_false,
          not_false_eq_true, Operations.interactionsWith_assert,
          Operations.interactionsWith_nil, List.map_cons, List.map_nil, List.nil_append,
          Soundness.rTypeProgramMessage, exposedOpcode]
        simp only [circuit_norm, List.nil_append]
      all_goals
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
      · simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
          h_byte, h_program, h_memory, decide_false, decide_true, Bool.false_eq_true,
          if_true, List.nil_append]
      · simp [circuit_norm, Gadgets.Equality.main, exposedMemoryInteractions] }

/-- Folded circuit projections used by the whole-chip row codec. -/
@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 54 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 54 := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq]

/-- The completed Mul circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw :=
  circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩ (by simp [circuit, expose])

/-- The completed Mul circuit exposes exactly its State interaction pair. -/
theorem interactionsWith_state_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith stateChannel.toRaw =
      (exposedStateInteractions input).map ChannelInteraction.toRaw :=
  circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨stateChannel.toRaw, (exposedStateInteractions input).map ChannelInteraction.toRaw⟩ (by simp [circuit, expose])

/-- The completed Mul circuit exposes exactly its Program fetch. -/
theorem interactionsWith_program_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith programChannel.toRaw =
      (exposedProgramInteractions input offset).map ChannelInteraction.toRaw :=
  circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨programChannel.toRaw, (exposedProgramInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.MulChip
