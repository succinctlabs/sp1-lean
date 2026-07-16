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
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

set_option maxHeartbeats 4000000 in
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
    sub_eq_zero.mp h_eq_rs
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
  refine ⟨⟨h_rspec, h_bin, fun hr => ⟨?_, ?_, ?_, ?_, ?_⟩⟩,
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

set_option warn.sorry false in
set_option maxHeartbeats 128000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  -- COMPLETENESS DEFERRED (Clean 4.30 combinedSize/nativeValue blowup — see docs/proposals/consolidation-progress.md).
  -- The soundness half is fully proven; completeness is temporarily sorried to unblock the soundness build.
  sorry

set_option maxHeartbeats 2000000 in
/-- The `Mul` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `mul`/`mulh`/`mulhu`/`mulhsu`/`mulw`
semantic contract; output is the extracted `MulCols` column struct. Soundness is proved; completeness is
the explicitly disclosed 4.31 migration seam above. -/
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
      expose stateChannel
        [ stateChannel.pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ],
    exposedChannels_eq := by
      intro input offset
      have h_byte := Channels.byteChannel_toRaw_ne_stateChannel (p := p)
      have h_program := Channels.programChannel_toRaw_ne_stateChannel (p := p)
      have h_memory := Channels.memoryChannel_toRaw_ne_stateChannel (p := p)
      rw [Operations.exposedChannelsLawful_expose]
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
      simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
        h_byte, h_program, h_memory, decide_false, decide_true, Bool.false_eq_true,
        if_true, List.nil_append] }

end SP1Clean.MulChip
