import Clean.Air.FlatComponent
import ToClean.Circuit.SubcircuitProjection
import SP1Clean.Native.Chips.MulChip.Defs
import SP1Clean.Math.EvalVec
import SP1Clean.Proofs.Chips.MulChip.Structural
import Clean.Air.Circuit
import ToClean.Circuit.WitgenEval

/-! # `SP1Clean.MulChip` — `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.MulChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- Soundness needs no input assumption: the arithmetic and reader subcircuits derive the
operand bounds from their byte and memory channel contracts. -/
def Assumptions (_ : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop := True

/-- Witness construction requires bounded operands, binary selectors with a binary sum,
nonzero destination routing, and the clock, timestamp and decode bounds of the readers.
Soundness derives these obligations from the circuit and its channel contracts. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_hint : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.isMul = 0 ∨ input.isMul = 1) ∧
  (input.isMulh = 0 ∨ input.isMulh = 1) ∧
  (input.isMulhu = 0 ∨ input.isMulhu = 1) ∧
  (input.isMulhsu = 0 ∨ input.isMulhsu = 1) ∧
  (input.isMulw = 0 ∨ input.isMulw = 1) ∧
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
/-- Four consecutive evaluated witness cells assemble the word `#v[v0, v1, v2, v3]`.
Used in completeness to identify the generated register-write word with its selected product slice. -/
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

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Inputs.is_real]
  obtain ⟨h_cpu, h_mulop, gb_mul, gb_mulh, gb_mulhu, gb_mulhsu, gb_mulw,
    gb_sum, hopa0, hadapter, _h_regwrite⟩ := h_holds
  have bmul := bool_of_mul_pred gb_mul
  have bmulh := bool_of_mul_pred gb_mulh
  have bmulhu := bool_of_mul_pred gb_mulhu
  have bmulhsu := bool_of_mul_pred gb_mulhsu
  have bmulw := bool_of_mul_pred gb_mulw
  have bsum := bool_of_mul_pred gb_sum
  have h_bin := bsum
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's `MemoryMsg.ClkBound` guarantee — `RTypeReader`'s two read-back pushes (`clk_low + 3` /
  -- `+ 2`) and `RegisterWrite`'s op_a write push (`clk_low + 4`). The offset is left to unification,
  -- so this line never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  -- No operand range is assumed by the chip: `MulOperation` derives both operand bounds from its
  -- own safe byte decompositions. The reader `Spec` remains the public register-read contract.
  have h_rspec := hadapter ⟨h_bin, h_bin, h_clk⟩
  -- `is_mulw = 1 → sum = 1` (gate = flag-sum, SP1 `alu/mul/mod.rs:234`): one-hot via `sum_eq_one`.
  have h_mw := fun (hmw : (input_isMulw : ZMod p) = 1) =>
    MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inr hmw))))
  -- `MulOperation.Assumptions`: row/flag binaries, `is_mulw → sum`, and the sum bound. Inlined so
  -- the operation input (including `cols`) is inferred from `h_mulop`/`result_semantic`/the goal.
  have h_spec := h_mulop
    ⟨bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩
  -- The operation's semantic readout, awaiting only `sum = 1`. Its conjuncts, in order:
  -- `isU64 resultWord`, then the `MUL`, `MULHU`, `MULH`, `MULHSU`, `MULW` BitVec identities.
  have hsem := MulOperation.result_semantic
    ⟨bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩ h_spec.1
  -- RegisterWrite owes `is_real = 1 → isU64 a`; on a real row `sum = 1` (via `h_rs`), so `a = resultWord`
  -- (`aSelector` linkage) is `isU64` from `result_semantic`.
  have h_a_isU64 : (input_isMul + input_isMulh + input_isMulhu + input_isMulhsu + input_isMulw) = 1 →
      Word.isU64 (Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var { index := i₀ + 45 + i })) := by
    intro hr
    have hsum1 : input_isMul + input_isMulh + input_isMulhu + input_isMulhsu + input_isMulw = 1 :=
      hr
    have h_bound := (hsem hsum1).1
    rw [← h_spec.2 hsum1] at h_bound
    simpa only [Nat.add_assoc, Nat.reduceAdd] using h_bound
  refine ⟨⟨h_rspec, h_bin, fun hr => ⟨?_, ?_, ?_, ?_, ?_⟩,
      -- F-A4-01: the exported selector one-hot — the five boolean gates + `is_real = Σ flags`.
      fun hr => by simpa only [SelectorOneHot, selectors] using
        MulOperation.oneHot_of_sum_one bmul bmulh bmulhu bmulhsu bmulw hr⟩,
    Or.inr ⟨bsum, h_mw, bmul, bmulh, bmulhu, bmulhsu, bmulw, bsum⟩,
    Or.inr ⟨h_bin, h_bin, h_clk⟩,
    Or.inr ⟨h_bin, h_a_isU64, h_clk.at_four⟩⟩
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inl h1)
    rw [rv64_mul_eq, ← (hsem hsum1).2.1 h1]; congr 1
    exact h_spec.2 hsum1
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inl h1))
    rw [rv64_mulh_eq, ← (hsem hsum1).2.2.2.1 h1]; congr 1
    exact h_spec.2 hsum1
  · intro h1
    have hsum1 := MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inl h1)))
    rw [rv64_mulhu_eq, ← (hsem hsum1).2.2.1 h1]; congr 1
    exact h_spec.2 hsum1
  · intro h1
    have hsum1 :=
      MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inl h1))))
    rw [rv64_mulhsu_eq, ← (hsem hsum1).2.2.2.2.1 h1]; congr 1
    exact h_spec.2 hsum1
  · intro h1
    have hsum1 :=
      MulOperation.sum_eq_one bmul bmulh bmulhu bmulhsu bmulw bsum (Or.inr (Or.inr (Or.inr (Or.inr h1))))
    rw [rv64_mulw_eq, ← (hsem hsum1).2.2.2.2.2 h1]; congr 1
    exact h_spec.2 hsum1

-- Completeness normalizes the 45-cell multiplication witness and four-cell result against the
-- composed reader and operation contracts. Selectors are supplied by the input row.
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start [Inputs.is_real]
  obtain ⟨hbU, hcU, ha_prev, hbin, hf0, hf1, hf2, hf3, hf4, hop_a_0, h_cpu,
    hrac_a, hrac_b, hrac_c, hdec, hprevclk⟩ := h_assumptions
  -- G1: the *push* side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  obtain ⟨-, ⟨-, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩,
    hmul, hmulh, hmulhu, hmulhsu, hmulw⟩ := h_input
  obtain ⟨-, h_env_cols, h_env_a, -⟩ := h_env
  have hf0' := hf0
  have hf1' := hf1
  have hf2' := hf2
  have hf3' := hf3
  have hf4' := hf4
  have hsum01' := hbin
  have hmw' : input_isMulw = 1 →
      input_isMul + input_isMulh + input_isMulhu + input_isMulhsu + input_isMulw = 1 := by
    intro hmw
    exact MulOperation.sum_eq_one hf0 hf1 hf2 hf3 hf4 hbin
      (Or.inr (Or.inr (Or.inr (Or.inr hmw))))
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have hbool : ∀ x : ZMod p, x = 0 ∨ x = 1 → x * (x - 1) = 0 := by
    rintro x (h | h) <;> rw [h] <;> simp
  -- One-hot bound for the two signed-variant flags (`is_mulh`/`is_mulhsu`): the five-flag sum is
  -- `{0,1}`-bounded, so their `val`-sum is at most one (the `populateFE_eval` sign-selector premise).
  have hsum13 : (input_isMulh).val + (input_isMulhsu).val ≤ 1 := by
    have hp := Fact.out (p := 2 ^ 24 < p)
    have v0 : (input_isMul).val ≤ 1 := by rcases hf0' with h | h <;> simp [h, ZMod.val_one]
    have v1 : (input_isMulh).val ≤ 1 := by rcases hf1' with h | h <;> simp [h, ZMod.val_one]
    have v2 : (input_isMulhu).val ≤ 1 := by rcases hf2' with h | h <;> simp [h, ZMod.val_one]
    have v3 : (input_isMulhsu).val ≤ 1 := by rcases hf3' with h | h <;> simp [h, ZMod.val_one]
    have v4 : (input_isMulw).val ≤ 1 := by rcases hf4' with h | h <;> simp [h, ZMod.val_one]
    have hcast : input_isMul + input_isMulh + input_isMulhu + input_isMulhsu
        + input_isMulw
        = (((input_isMul).val + (input_isMulh).val + (input_isMulhu).val
            + (input_isMulhsu).val + (input_isMulw).val : ℕ) : ZMod p) := by
      push_cast [ZMod.natCast_zmod_val]; ring
    have hlt : (input_isMul).val + (input_isMulh).val + (input_isMulhu).val
        + (input_isMulhsu).val + (input_isMulw).val < p := by omega
    rcases hsum01' with h | h
    · rw [hcast] at h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hlt, ZMod.val_zero] at hv
      omega
    · rw [hcast] at h
      have hv := congrArg ZMod.val h
      rw [ZMod.val_natCast_of_lt hlt, ZMod.val_one] at hv
      omega
  -- fold the witness stream's `populateFE` operands to the evaluated input words
  simp only [Inputs.op_b_val, Inputs.op_c_val] at h_env_cols
  -- `circuit_norm` states the witness condition as one struct equation; read it cell by cell.
  replace h_env_cols := fun j : Fin 45 =>
    (ProvableStruct.get_of_eval_varFromOffset_eq (α := Circuits.Types.MulOperation) env.toEnvironment i₀ _
      (by simpa only [circuit_norm] using h_env_cols) j (by
        have h : size Circuits.Types.MulOperation = 45 := rfl
        have := j.isLt
        omega)).trans (Witgen.getElem_eval_toElements _ _ j (by
      have h : size Circuits.Types.MulOperation = 45 := rfl
      have := j.isLt
      omega)).symm
  -- The witness stream is the `populateFE` IR; `populateFE_eval_cell` evaluates each pinned cell to
  -- the value-level `populate` at the evaluated operands. One reusable per-index fact serves both
  -- the `Spec` conversion below and the `RegisterWrite` `isU64` bullet's `product`/`product_msb`
  -- reads.
  have h_env_cols' : ∀ (i : ℕ) (hi : i < 45), env.toEnvironment.get (i₀ + i)
      = (toElements (MulOperation.populate input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value
          (input_isMulh) (input_isMulhsu) (input_isMulw)))[i]'hi := fun i hi => by
    refine (h_env_cols ⟨i, hi⟩).trans ?_
    have hcell := MulOperation.populateFE_eval_cell env
      input_var_adapter_op_b_memory_prev_value input_var_adapter_op_c_memory_prev_value
      input_var_isMulh input_var_isMulhsu input_var_isMulw
      input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value
      (input_isMulh) (input_isMulhsu) (input_isMulw)
      ((vec4_eval env.toEnvironment _).trans hob) ((vec4_eval env.toEnvironment _).trans hoc)
      hmulh hmulhsu hmulw hbU hcU hf1' hf3' hsum13 i hi
    exact hcell
  -- The full witnessed-`cols` struct equals `populate …` (per-cell, via `getElem_toElements_eval_
  -- varFromOffset` + `h_env_cols'`) — reused both by the `Spec` conversion below and by the
  -- `RegisterWrite` `isU64` bullet's `product`/`product_msb` field reads (sidesteps any manual
  -- `toElements`/`Vector.getElem_append_*`/cast reasoning about `MulOperation`'s 9-field layout).
  have hcols_eq : Eval.eval env.toEnvironment
      (ProvableStruct.varFromOffset Circuits.Types.MulOperation i₀ : Var Circuits.Types.MulOperation (ZMod p))
      = MulOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value
          (input_isMulh) (input_isMulhsu) (input_isMulw) :=
    (ProvableType.ext_iff (α := Circuits.Types.MulOperation) _ _).mpr (fun i hi =>
      (getElem_toElements_eval_varFromOffset env.toEnvironment i₀ i hi).trans (h_env_cols' i hi))
  refine ⟨⟨hbin, h_cpu⟩,
    ⟨⟨hsum01', hmw', hf0', hf1', hf2', hf3', hf4', hsum01'⟩, ?_⟩,
    hbool _ hf0', hbool _ hf1', hbool _ hf2', hbool _ hf3', hbool _ hf4', hbool _ hsum01',
    hop_a_0,
    ⟨⟨hbin, hbin, h_clk⟩,
      ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c, hdec,
        fun hr => ⟨ha_prev hr, hbU, hcU, (hprevclk hr).1, (hprevclk hr).2.1, (hprevclk hr).2.2⟩⟩⟩,
    ⟨⟨hbin, ?_, h_clk.at_four⟩, trivial⟩⟩
  · -- The operation owns both the populated arithmetic evidence and the generated result.
    constructor
    · convert MulOperation.productSpec_populate (b := input_adapter_op_b_memory_prev_value)
        (c := input_adapter_op_c_memory_prev_value) hbU hcU
        (input_isMul) (input_isMulh) (input_isMulhu) (input_isMulhsu) (input_isMulw)
        (input_isMul + input_isMulh + input_isMulhu + input_isMulhsu + input_isMulw)
        hf0' hf1' hf2' hf3' hf4' hsum01' using 2
      -- 4.32: `convert … using 2` now leaves only the `cols` equality. The former `rfl` step closed a
      -- separate `circuit.Spec = Spec` goal that the congruence no longer emits (Clean `088a9287`).
      simpa only [circuit_norm] using hcols_eq
    · intro hsum1
      rw [← MulOperation.aSelector_eq_resultWord _ _ hf0' hf1' hf2' hf3' hf4' hsum1]
      simp only [MulOperation.aSelector, MulOperation.productVal, Vector.getElem_map,
        Vector.getElem_mapRange, Nat.reduceLT, dif_pos]
      simpa only [circuit_norm, Nat.reduceMod, Nat.add_zero, hmul, hmulh, hmulhu, hmulhsu, hmulw] using
        evalWord4_of_cells (h_env_a 0) (h_env_a 1) (h_env_a 2) (h_env_a 3)
  · -- RegisterWrite's `isU64 value` (the op_a write push): on a real row the witnessed `a` equals the
    -- selected product slice `resultWord (populate …)`, whose `isU64` is `productSpec_populate`'s
    -- `result_semantic`.
    intro hr
    have hsum1 : input_isMul + input_isMulh + input_isMulhu + input_isMulhsu + input_isMulw = 1 :=
      hr
    have h_mulspec := MulOperation.productSpec_populate
      (a := Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index := i₀ + 45 + i }))
      (b := input_adapter_op_b_memory_prev_value)
      (c := input_adapter_op_c_memory_prev_value) hbU hcU
      (input_isMul) (input_isMulh) (input_isMulhu) (input_isMulhsu) (input_isMulw)
      (input_isMul + input_isMulh + input_isMulhu + input_isMulhsu + input_isMulw)
      hf0' hf1' hf2' hf3' hf4' hsum01'
    obtain ⟨hisU64, _, _, _, _, _⟩ := MulOperation.result_semantic
      ⟨hsum01', hmw', hf0', hf1', hf2', hf3', hf4', hsum01'⟩ h_mulspec hsum1
    rw [show (Vector.map (Expression.eval env.toEnvironment)
          (Vector.mapRange 4 fun i => var { index := i₀ + 45 + i }))
        = MulOperation.resultWord _ _ from ?_]
    · exact hisU64
    · -- The `a` slices (`h_env_a`) reference the witnessed product columns `env.get (i₀+5+16+j)`, while
      -- `aSelector (populate)` references `(populate).product[j]`; they agree because the chip witnesses
      -- the columns to `populate` (`h_env_cols'`).
      have hprod : ∀ (j : ℕ) (hj : j < 16),
          (MulOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value
            (input_isMulh) (input_isMulhsu) (input_isMulw)).product[j]'(by omega)
            = env.get (i₀ + 16 + j) := fun j hj => by
        rw [← hcols_eq]; simp only [circuit_norm]
      have hpmsb : (MulOperation.populate input_adapter_op_b_memory_prev_value
            input_adapter_op_c_memory_prev_value
            (input_isMulh) (input_isMulhsu) (input_isMulw)).product_msb.msb
          = env.get (i₀ + 16 + 16 + 4 + 4 + 1 + 1) := by
        rw [← hcols_eq]; simp only [circuit_norm]
      rw [← MulOperation.aSelector_eq_resultWord _ _ hf0' hf1' hf2' hf3' hf4' hsum1]
      simp only [MulOperation.aSelector, MulOperation.productVal, Nat.reduceLT, dif_pos,
        hprod, hpmsb]
      simpa only [circuit_norm, Nat.reduceMod, Nat.add_zero, hmul, hmulh, hmulhu, hmulhsu, hmulw] using
        evalWord4_of_cells (h_env_a 0) (h_env_a 1) (h_env_a 2) (h_env_a 3)

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
word `a` (cells `offset+45..48`, after the 45 `MulOperation` columns).
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
       input.adapter.op_a, 0, 0, Vector.mapRange 4 fun i => var { index := offset + 45 + i }⟩ ]

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

/-- Program opcode encoded by the five committed input selectors. -/
def exposedOpcode (input : Var Inputs (ZMod p)) : Expression (ZMod p) :=
  input.isMul * 11 + input.isMulh * 12 + input.isMulhu * 13 +
    input.isMulhsu * 14 + input.isMulw * 24

/-- Exact Program fetch emitted by the R-type adapter, with the instruction opcode reconstructed
from the five chip-owned variant flags. -/
def exposedProgramInteractions (input : Var Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf input.is_real
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
       exposedOpcode input, input.adapter.op_a,
       #v[input.adapter.op_b, 0, 0, 0],
       #v[input.adapter.op_c, 0, 0, 0],
       input.adapter.op_a_0, 0, 0⟩ ]

/-- The `Mul` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `mul`/`mulh`/`mulhu`/`mulhsu`/`mulw`
semantic contract; output is the native `Columns` row. Soundness and completeness are both proved
above (the former 4.31-migration completeness seam is closed). -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  { name := "sp1.native.mul", main, elaborated,
    -- `programChannel` dropped (W11 flip — now pulled via `RTypeReader`, a guarantee not a requirement).
    channelsWithRequirements := [stateChannel.toRaw, memoryChannel.toRaw],
    requirementsChannelsLawful := requirementsChannelsLawful_main,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    -- W11 (A2): expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8)
    -- as chip-owned interactions (the Clean `VmTables` re-base that motivated the shape was investigated
    -- and deferred — roadmap W11); descends to the composed `CPUState` subcircuit's lone pull+push.
    exposedChannels := fun input offset =>
      expose stateChannel (exposedStateInteractions input) ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `RTypeReader`, gate
      -- `is_trusted = is_real`, opcode = the committed one-hot flag encoding), consumed by
      -- `Soundness/TypedProgram.lean`.
      expose programChannel (exposedProgramInteractions input),
    exposedChannels_eq := by
      preserve_tactic_target
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
          Circuit.pure_def, witnessVectorIR, Witnessable.witness, witnessIR,
          subcircuitWithAssertion,
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
        simp only [circuit_norm]
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
          List.nil_append]
      · simp [circuit_norm, Gadgets.Equality.main, exposedMemoryInteractions] }

/-- Folded circuit projections used by the whole-chip row codec. -/
@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 49 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 49 := by
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
      (exposedProgramInteractions input).map ChannelInteraction.toRaw :=
  circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨programChannel.toRaw, (exposedProgramInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

/-- The row contains no Clean lookup operations; cross-table checks use channels. -/
theorem lookups_empty :
    ({ circuit := MulChip.circuit (p := p) } :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq,
    Air.Flat.Component.rowOperations_mk, MulChip.circuit_main_eq]
  simp [MulChip.main, Readers.CPUState.circuit,
    Readers.CPUState.main, Readers.RTypeReader.circuit,
    Readers.RTypeReader.main, Readers.RegisterWrite.circuit,
    Readers.RegisterWrite.main, Readers.RegisterAccessCols.circuit,
    Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit,
    Readers.RegisterAccessTimestamp.main, MulOperation.circuit,
    MulOperation.main, U16toU8OperationSafe.circuit,
    U16toU8OperationSafe.main, U16MSBOperation.circuit,
    U16MSBOperation.main, Gadgets.Equality.main, circuit_norm]

end SP1Clean.MulChip
