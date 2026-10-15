import Clean.Air.FlatComponent
import ToClean.Circuit.SubcircuitProjection
import SP1Clean.Native.Chips.LtChip.Defs
import SP1Clean.Math.EvalVec
import Clean.Air.Circuit
import ToClean.Circuit.WitgenEval

/-! # `SP1Clean.LtChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.LtChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values; `is_real`-binary is proven from the in-circuit gate (so it lives in
`Spec`), not assumed. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- Honest operand bounds, boolean selectors/activity, the register or immediate row form,
CPU clock bounds and prior-access timestamps. No external selector hint is needed. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p))
    (_hint : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.isSlt = 0 ∨ input.isSlt = 1) ∧ (input.isSltu = 0 ∨ input.isSltu = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  (input.adapter.imm_c = 0 ∨ (input.is_real = 1 ∧ input.adapter.imm_c = 1)) ∧
  (input.adapter.imm_c *
      (input.adapter.op_c_memory.prev_value[0] - input.adapter.op_c[0]) = 0 ∧
    input.adapter.imm_c *
      (input.adapter.op_c_memory.prev_value[1] - input.adapter.op_c[1]) = 0 ∧
    input.adapter.imm_c *
      (input.adapter.op_c_memory.prev_value[2] - input.adapter.op_c[2]) = 0 ∧
    input.adapter.imm_c *
      (input.adapter.op_c_memory.prev_value[3] - input.adapter.op_c[3]) = 0) ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real - input.adapter.imm_c,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩ ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16) ∧
  -- G1: the three pulled prior records' 24-bit access clocks (`Channels.MemoryMsg.ClkBound`, the clock
  -- half of the memory channel's `Guarantees`). A pull's completeness must exhibit the guarantee it
  -- consumes; in a real trace each prior access sits at a genuine `< 2^24` timestamp. The op_c
  -- component is harmlessly stronger than its access gate on immediate rows (the honest builder puts
  -- literal zero there). Soundness does *not* assume these — they are derived from the pulls.
  (input.is_real = 1 →
    input.adapter.op_a_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_b_memory.access_timestamp.prev_low.val < 2 ^ 24 ∧
    input.adapter.op_c_memory.access_timestamp.prev_low.val < 2 ^ 24)

/-- The clean RV64 `slt` reduced to its `if`-form: `RV64.slt y x` is `1#64` iff `x <ₛ y`. -/
private lemma rv64_slt_eq (x y : BitVec 64) :
    RV64.slt y x = if x.toInt < y.toInt then 1#64 else 0#64 := by
  by_cases h : x.toInt < y.toInt <;> simp [RV64.slt, BitVec.slt, h]

/-- The clean RV64 `sltu` reduced to its `if`-form: `RV64.sltu y x` is `1#64` iff `x <ᵤ y`. -/
private lemma rv64_sltu_eq (x y : BitVec 64) :
    RV64.sltu y x = if x.toNat < y.toNat then 1#64 else 0#64 := by
  by_cases h : x.toNat < y.toNat <;> simp [RV64.sltu, BitVec.ult, h]

omit [Fact (2 ^ 17 < p)] in
set_option linter.unusedSectionVars false in
/-- The `resultWord` `#v[bit, 0, 0, 0]` packs to the 64-bit `0/1` indicator carried by its low limb:
when the compare `bit` is `if P then 1 else 0`, the word's `toBitVec64` is `if P then 1#64 else 0#64`. -/
private lemma toBitVec64_bitWord (bit : ZMod p) (P : Prop) [Decidable P]
    (h : bit = if P then 1 else 0) :
    Word.toBitVec64 (#v[bit, 0, 0, 0] : Word (ZMod p)) = if P then 1#64 else 0#64 := by
  subst h
  by_cases hP : P <;> simp [hP, Word.toBitVec64, Word.toNat, ZMod.val_one, ZMod.val_zero]

omit [Fact (2 ^ 17 < p)] in
set_option linter.unusedSectionVars false in
/-- A binary field element's `val` is a valid 16-bit limb. -/
private lemma val_lt_of_bool {b : ZMod p} (h : b = 0 ∨ b = 1) : b.val < 2 ^ 16 := by
  have := bool_val_le h; omega

omit [Fact (2 ^ 17 < p)] in
/-- The Lt result word `#v[bit, 0, 0, 0]` is a valid u64 whenever the compare `bit` is binary (the
op_a write push's `isU64 value` obligation). -/
private lemma isU64_bitWord {b : ZMod p} (h : b = 0 ∨ b = 1) :
    Word.isU64 (#v[b, 0, 0, 0] : Word (ZMod p)) :=
  Word.isU64_of_cases (val_lt_of_bool h) (val_lt_of_bool (Or.inl rfl))
    (val_lt_of_bool (Or.inl rfl)) (val_lt_of_bool (Or.inl rfl))

omit [Fact (2 ^ 17 < p)] in
set_option linter.unusedSectionVars false in
/-- A field element pinned to `if Q then 1 else 0` is binary (used in soundness to read the compare
`bit`'s binary-ness off `LtOperationSigned.result_semantic`). -/
private lemma bool_of_eq_ite {b : ZMod p} {Q : Prop} [Decidable Q]
    (h : b = if Q then 1 else 0) : b = 0 ∨ b = 1 := by
  split at h
  · exact Or.inr h
  · exact Or.inl h

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
set_option linter.unusedSectionVars false in
/-- Column 0 of a flattened `LtOperationSigned` column struct is its compare `bit` (peeling the
`ProvableStruct` `toComponents`/`cast`/`append` tower). Used by completeness to read the witnessed bit
out of the `populate`-pinned witness cell `env.get i₀`. -/
private lemma toElements_col0 {x : Circuits.Types.LtOperationSigned (ZMod p)}
    (hi : (0:ℕ) < size Circuits.Types.LtOperationSigned) :
    (toElements x)[0]'hi = x.result.u16_compare_operation.bit := by
  simp only [ProvableType.toElements, ProvableStruct.toComponents,
    ProvableStruct.componentsToElements, circuit_norm]
  refine ((Vector.getElem_append_left ?_).trans
    ((Vector.getElem_cast ?_).trans
      ((Vector.getElem_append_left ?_).trans (Vector.getElem_cast ?_)))) <;> decide

omit [Fact (2 ^ 17 < p)] in
/-- The witnessed compare `bit` of `LtOperationSigned.populate` (the `U16CompareOperation` strict-less-than
indicator on a real row) is binary. -/
private lemma populate_bit_bool {b cc : Word (ZMod p)} {s r : ZMod p} (hr : r = 1) :
    (LtOperationSigned.populate b cc s r).result.u16_compare_operation.bit = 0 ∨
    (LtOperationSigned.populate b cc s r).result.u16_compare_operation.bit = 1 := by
  rw [show (LtOperationSigned.populate b cc s r).result.u16_compare_operation.bit
        = (if r = 1 then LtOperationUnsigned.populate
              #v[b[0], b[1], b[2], b[3] + s * 32768 - 65536 * (s * U16MSBOperation.populate_msb b[3])]
              #v[cc[0], cc[1], cc[2], cc[3] + s * 32768 - 65536 * (s * U16MSBOperation.populate_msb cc[3])]
            else ⟨⟨0⟩, #v[0, 0, 0, 0], 0, #v[0, 0]⟩).u16_compare_operation.bit from rfl, if_pos hr,
      show (LtOperationUnsigned.populate _ _).u16_compare_operation.bit
        = U16CompareOperation.populate_bit _ _ from rfl]
  exact U16CompareOperation.populate_bit_bool _ _

omit [Fact (2 ^ 17 < p)] in
/-- The witnessed `LtOperationSigned` block's flattened cell 0 (the compare `bit`) is binary on a real
row — the form completeness uses after pinning the witness cell `env.get i₀` to `populate`. -/
private lemma witness_bit_bool {b cc : Word (ZMod p)} {s r : ZMod p} (hr : r = 1)
    (hi : (0:ℕ) < size Circuits.Types.LtOperationSigned) :
    (toElements (LtOperationSigned.populate b cc s r))[0]'hi = 0 ∨
    (toElements (LtOperationSigned.populate b cc s r))[0]'hi = 1 := by
  rw [toElements_col0]; exact populate_bit_bool hr

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Inputs.is_real]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨h_cpu, h_lt, h_adapter, _h_rw, h_gate,
    h_slt_bin, _h_sltu_bin, _h_op_a_0⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  have h_slt_bool := bool_of_mul_pred h_slt_bin
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's new `MemoryMsg.ClkBound` guarantee — `ALUTypeReader`'s two read-back pushes
  -- (`clk_low + 3` / `+ 2`) and `RegisterWrite`'s op_a write push (`clk_low + 4`). The offset is left
  -- to unification, so this line never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  refine ⟨⟨h_adapter ⟨h_bin, h_bin, h_clk⟩,
    h_bin, fun hr => ⟨fun hslt => ?_, fun hsltu => ?_⟩⟩, ?_⟩
  · -- `is_slt = 1` ⇒ `is_signed = 1`, so the gadget bit is the signed compare. The semantic
    -- `Spec` exposes the semantic bit via `result_semantic`.
    have h_lt_spec := (LtOperationSigned.result_semantic (h_lt ⟨ha, hb, h_bin, h_slt_bool⟩) hr).1
    rw [hslt] at h_lt_spec
    simp only [if_true] at h_lt_spec
    simp only [resultWord, rv64_slt_eq, toBitVec64_bitWord _ _ h_lt_spec]
  · -- `is_sltu = 1` with the sum-bound + booleans forces `is_slt = 0`
    have h_lt_spec := (LtOperationSigned.result_semantic (h_lt ⟨ha, hb, h_bin, h_slt_bool⟩) hr).1
    have h_slt0 : input_isSlt = 0 := by
      rcases h_slt_bool with h0 | h1
      · exact h0
      · exfalso
        rw [h1, hsltu] at h_gate
        exact (show (2 : ZMod p) ≠ 0 by simp [← ZMod.val_eq_zero, val_2_zmod_p])
          (by linear_combination h_gate)
    have h01 : (0 : ZMod p) ≠ 1 := zero_ne_one
    rw [h_slt0] at h_lt_spec
    simp only [if_neg h01] at h_lt_spec
    simp only [resultWord, rv64_sltu_eq, Word.toBitVec64_toNat ha,
      Word.toBitVec64_toNat hb, toBitVec64_bitWord _ _ h_lt_spec]
  -- The per-emitter channel-requirement tail: the bare `CPUState` `Assumptions` (the binary gate), the
  -- composed `LtOperationSigned`/`ALUTypeReader` requirements (bare or `[] ∨ Assumptions` disjuncts).
  · and_intros <;>
      first | exact h_bin | exact ⟨ha, hb, h_bin, h_slt_bool⟩
            | exact Or.inl rfl
            | exact Or.inr ⟨h_bin, h_bin, h_clk⟩
            | exact Or.inr ⟨h_bin, (fun hr => isU64_bitWord
                (bool_of_eq_ite (LtOperationSigned.result_semantic
                  (h_lt ⟨ha, hb, h_bin, h_slt_bool⟩) hr).1)),
                h_clk.at_four⟩

-- Keep populated comparison columns folded when transporting witness pins.
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start [Inputs.is_real]
  obtain ⟨ha, hb, ha_prev, hbin, hf0, hf1, hop_a_0, himm,
    himm_copy, h_cpu, hrac_a, hrac_b, hrac_c, hdec, hprevclk⟩ := h_assumptions
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  obtain ⟨-, h_env_cols, -⟩ := h_env
  have hflag0 : Expression.eval env.toEnvironment input_var_isSlt = input_isSlt := h_input.2.2.1
  have hflag1 : Expression.eval env.toEnvironment input_var_isSltu = input_isSltu := h_input.2.2.2
  have hbool : ∀ x : ZMod p, x = 0 ∨ x = 1 → x * (x - 1) = 0 := by
    rintro x (h | h) <;> rw [h] <;> simp
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have hpvb : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_b_memory_prev_value
      = input_adapter_op_b_memory_prev_value := h_input.2.1.2.2.2.2.1.1
  have hpvc : Vector.map (Expression.eval env.toEnvironment)
      input_var_adapter_op_c_memory_prev_value = input_adapter_op_c_memory_prev_value :=
    h_input.2.1.2.2.2.2.2.2.1.1
  have hreal : Expression.eval env.toEnvironment (input_var_isSlt + input_var_isSltu)
      = input_isSlt + input_isSltu := by
    simp only [circuit_norm, hflag0, hflag1]
  replace h_env_cols := fun j : Fin 10 =>
    (ProvableStruct.get_of_eval_varFromOffset_eq (α := Circuits.Types.LtOperationSigned) env.toEnvironment i₀ _
      (by simpa only [circuit_norm] using h_env_cols) j (by
        have h : size Circuits.Types.LtOperationSigned = 10 := rfl
        have := j.isLt
        omega)).trans (Witgen.getElem_eval_toElements _ _ j (by
      have h : size Circuits.Types.LtOperationSigned = 10 := rfl
      have := j.isLt
      omega)).symm
  have hcolsPop : ∀ j : Fin 10, env.get (i₀ + (j : ℕ))
      = (toElements (LtOperationSigned.populate input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value input_isSlt (input_isSlt + input_isSltu)))[(j : ℕ)]'(by
        have : size Circuits.Types.LtOperationSigned = 10 := rfl
        have := j.isLt
        omega) := by
    intro j
    refine (h_env_cols j).trans ?_
    have hcell := LtOperationSigned.populateFE_eval_cell env
      input_var_adapter_op_b_memory_prev_value input_var_adapter_op_c_memory_prev_value
      input_var_isSlt (input_var_isSlt + input_var_isSltu)
      input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value
      ((vec4_eval env.toEnvironment _).trans hpvb) ((vec4_eval env.toEnvironment _).trans hpvc)
      ha hb (j : ℕ) j.isLt
    rw [hflag0, hreal] at hcell
    exact hcell
  have himm_pad : ((input_isSlt + input_isSltu) - 1) * input_adapter_imm_c = 0 := by
    rcases himm with h0 | ⟨hr, h1⟩
    · rw [h0, mul_zero]
    · rw [hr, h1]
      simp
  have hcbin : (input_isSlt + input_isSltu) - input_adapter_imm_c = 0 ∨
      (input_isSlt + input_isSltu) - input_adapter_imm_c = 1 := by
    rcases himm with h0 | ⟨hr, h1⟩
    · rw [h0, sub_zero]
      exact hbin
    · rw [hr, h1]
      simp
  have hreal_of_c (hc : (input_isSlt + input_isSltu) - input_adapter_imm_c = 1) : (input_isSlt + input_isSltu) = 1 := by
    rcases himm with h0 | ⟨hr, h1⟩
    · rwa [h0, sub_zero] at hc
    · exact hr
  refine ⟨⟨hbin, h_cpu⟩,
    ⟨⟨ha, hb, hbin, hf0⟩, ?_⟩,
    ⟨⟨hbin, hbin, h_clk⟩,
      ⟨⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0,
      himm_pad, hcbin, himm_copy,
      hrac_a, hrac_b, hrac_c, hdec,
      (fun hr => ⟨ha_prev hr, ha, (hprevclk hr).1, (hprevclk hr).2.1⟩),
      fun hc => ⟨hb, (hprevclk (hreal_of_c hc)).2.2⟩⟩⟩,
    ⟨⟨hbin, ?_, h_clk.at_four⟩, trivial⟩,
    hbool _ hbin,
    hbool _ hf0,
    hbool _ hf1,
    hop_a_0⟩
  have hgate : ((input_isSlt + input_isSltu) - 1) * input_isSlt = 0 := by
    rcases hf0 with hs | hs
    · rw [hs, mul_zero]
    · rcases hf1 with hu | hu
      · rw [hs, hu]; ring
      · have impossible := hbool _ hbin
        rw [hs, hu] at impossible
        exact False.elim ((show (2 : ZMod p) ≠ 0 by
          simp [← ZMod.val_eq_zero, val_2_zmod_p]) (by linear_combination impossible))
  convert LtOperationSigned.spec_populate (b := input_adapter_op_b_memory_prev_value)
    (cc := input_adapter_op_c_memory_prev_value) (is_signed := input_isSlt)
    (is_real := (input_isSlt + input_isSltu))
    ha hb hf0 hbin hgate using 2
  refine (ProvableType.ext_iff (α := Circuits.Types.LtOperationSigned) _ _).mpr (fun i hi => ?_)
  refine Eq.trans ?_
    ((getElem_toElements_eval_varFromOffset env.toEnvironment i₀ i hi).trans
      (hcolsPop ⟨i, hi⟩))
  simp only [circuit_norm]
  simp [circuit_norm]
  intro hr
  have hc0 : env.get i₀
      = (toElements (LtOperationSigned.populate input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value input_isSlt (input_isSlt + input_isSltu)))[0]'(by
            have : size Circuits.Types.LtOperationSigned = 10 := rfl; omega) := hcolsPop 0
  refine isU64_bitWord ?_
  rw [hc0]
  exact witness_bit_bool hr _

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

/-- Exact Byte-channel list emitted by Lt: two CPU clock checks, the two signed-MSB checks,
the selected-limb comparison, and the ALU reader's six register-timestamp checks. The native
composition emits the CPU rows first; whole-chip faithfulness proves the permutation to Rust's
operation-first order. -/
def exposedByteInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (byteChannel (p := p))) :=
  let clkLow := input.state.clk_0_16 + input.state.clk_16_24 * 65536
  let opCGate := input.is_real - input.adapter.imm_c
  let isSlt := input.isSlt
  let bit := var ⟨offset⟩
  let comparison0 := var ⟨offset + 6⟩
  let comparison1 := var ⟨offset + 7⟩
  let bMsb := var ⟨offset + 8⟩
  let cMsb := var ⟨offset + 9⟩
  [ byteChannel.pulledIf input.is_real
      ⟨6, (input.state.clk_0_16 - 1) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real ⟨3, 0, input.state.clk_16_24, 0⟩,
    byteChannel.pulledIf isSlt
      ⟨6, (2 : Expression (ZMod p)) * input.op_b_val[3] - bMsb * 65536,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf isSlt
      ⟨6, (2 : Expression (ZMod p)) * input.op_c_val[3] - cMsb * 65536,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf input.is_real
      ⟨6, comparison0 - comparison1 + bit * 65536,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
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
    byteChannel.pulledIf opCGate
      ⟨6, input.adapter.op_c_memory.access_timestamp.diff_low_limb,
       Expression.const ((16 : ℕ) : ZMod p), 0⟩,
    byteChannel.pulledIf opCGate
      ⟨3, 0,
       (clkLow + 2 - input.adapter.op_c_memory.access_timestamp.prev_low - 1 -
          input.adapter.op_c_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹,
       0⟩ ]

/-- Lt's exact Memory-channel interaction list (ALU-type: the op_c register pull/read-back pair is
gated by **`is_real - imm_c`** — an immediate does no register read — and addressed by the low limb
`op_c[0]`).  The op_a write push carries the compare-bit word `[bit, 0, 0, 0]` (the witnessed
`LtOperationSigned` block's cell 0, at `offset`).  Keeping this list
beside `circuit` makes Clean's exposure interface the single structural source consumed by both
faithfulness and semantic grounding. -/
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
    memoryChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩,
    memoryChannel.pushedIf input.is_real
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0, #v[var { index := offset }, 0, 0, 0]⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in Lt's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf input.is_real
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact (`is_real - imm_c`)-gated source-C pull occupies its declared slot in Lt's exposed
Memory list. -/
theorem opCPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (input.is_real - input.adapter.imm_c)
      ⟨input.state.clk_high, input.adapter.op_c_memory.access_timestamp.prev_low,
       input.adapter.op_c[0], 0, 0, input.adapter.op_c_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The fetched opcode selected by the committed inputs: SLT = 9, SLTU = 10. -/
def exposedOpcode (input : Var Inputs (ZMod p)) : Expression (ZMod p) :=
  input.isSlt * 9 + input.isSltu * 10

/-- Exact Program fetch emitted by the ALU adapter, with the instruction opcode reconstructed from
the two chip-owned variant flags. -/
def exposedProgramInteractions (input : Var Inputs (ZMod p)) :
    List (ChannelInteraction (programChannel (p := p))) :=
  [ programChannel.pulledIf input.is_real
      ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2], exposedOpcode input,
       input.adapter.op_a, #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c,
       input.adapter.op_a_0, 0, input.adapter.imm_c⟩ ]

/-- The unified `Lt` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `slt`/`sltu` semantic contract,
composing the witnessed signed-compare gadget and the immediate-capable register reader; output is the
native `Columns` row. Soundness/completeness are proven and axiom-clean. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  { name := "sp1.native.lt", main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    -- W11 (A2): expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8)
    -- as chip-owned interactions (the Clean `VmTables` re-base that motivated the shape was investigated
    -- and deferred — roadmap W11); descends to the composed `CPUState` subcircuit's lone pull+push.
    exposedChannels := fun input offset =>
      expose stateChannel (exposedStateInteractions input) ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `ALUTypeReader`, gate
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
      · simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
          Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
          Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
          Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
          SP1Clean.LtOperationSigned.circuit, SP1Clean.LtOperationSigned.main,
          SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
          SP1Clean.LtOperationUnsigned.circuit, SP1Clean.LtOperationUnsigned.main,
          SP1Clean.U16CompareOperation.circuit, SP1Clean.U16CompareOperation.main,
          circuit_norm, FormalAssertion.toSubcircuit_interactions,
          GeneralFormalCircuit.toSubcircuit_interactions]
        simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
          h_byte, h_program, h_memory, decide_false, decide_true, Bool.false_eq_true,
          List.nil_append]
      · simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
          Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
          Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
          Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
          SP1Clean.LtOperationSigned.circuit, SP1Clean.LtOperationSigned.main,
          SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
          SP1Clean.LtOperationUnsigned.circuit, SP1Clean.LtOperationUnsigned.main,
          SP1Clean.U16CompareOperation.circuit, SP1Clean.U16CompareOperation.main,
          circuit_norm, FormalAssertion.toSubcircuit_interactions,
          GeneralFormalCircuit.toSubcircuit_interactions]
        simp [circuit_norm, Gadgets.Equality.main, exposedMemoryInteractions]
      · -- Program branch: compositional — the reader subcircuit keeps its fetch via the
        -- reader-local `_subcircuit` lemma; every other child is nil on the Program channel.
        simp only [main, Circuit.operations, Circuit.bind_def,
          Circuit.pure_def, subcircuitWithAssertion, assertion,
          assertZero, HasAssertEq.assert_eq, Expression.assertEquals, Operations.localLength]
        simp only [Operations.interactionsWith_append,
          InteractionRecovery.interactionsWith_generalSubcircuit_eq_nil,
          InteractionRecovery.interactionsWith_assertionSubcircuit_eq_nil,
          Soundness.aluTypeReader_programInteractions_subcircuit,
          Readers.CPUState.circuit, Readers.CPUState.channelsWithGuarantees_eq,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.channelsWithGuarantees_eq,
          SP1Clean.LtOperationSigned.circuit, SP1Clean.LtOperationSigned.elaborated,
          FormalCircuitBase.channelsWithGuarantees_def, List.mem_cons, List.not_mem_nil, or_false,
          Channels.programChannel_eq_byteChannel_false,
          Channels.programChannel_eq_stateChannel_false,
          Channels.programChannel_eq_memoryChannel_false,
          not_false_eq_true, Operations.interactionsWith_assert,
          Operations.interactionsWith_nil, List.map_cons, List.map_nil, List.nil_append,
          List.append_nil, Soundness.aluTypeProgramMessage, exposedOpcode]
        simp only [Operations.interactionsWith_subcircuit,
          FormalAssertion.toSubcircuit_interactions, Gadgets.Equality.main, circuit_norm,
          List.filter_nil, List.nil_append] }

/-- Folded circuit projections used by whole-chip row codecs without unfolding the proof bundle. -/
@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 10 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 10 := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq]

/-- The completed Lt circuit exposes exactly its State interaction pair. -/
theorem interactionsWith_state_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith stateChannel.toRaw =
      (exposedStateInteractions input).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨stateChannel.toRaw, (exposedStateInteractions input).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

/-- The completed Lt circuit emits exactly its eleven Byte interactions.
Runs at the plain default: the former 4000000 ceiling was ~100x over; measured floor <= 40000. -/
theorem interactionsWith_byte_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith byteChannel.toRaw =
      (exposedByteInteractions input offset).map ChannelInteraction.toRaw := by
  simp [main, exposedByteInteractions,
    Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    SP1Clean.LtOperationSigned.circuit, SP1Clean.LtOperationSigned.main,
    SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
    SP1Clean.LtOperationUnsigned.circuit, SP1Clean.LtOperationUnsigned.main,
    SP1Clean.U16CompareOperation.circuit, SP1Clean.U16CompareOperation.main,
    Gadgets.Equality.main, FormalAssertion.toSubcircuit_interactions,
    GeneralFormalCircuit.toSubcircuit_interactions, circuit_norm, Nat.add_assoc]

/-- The completed Lt circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

/-- The completed Lt circuit exposes exactly its Program fetch. -/
theorem interactionsWith_program_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith programChannel.toRaw =
      (exposedProgramInteractions input).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨programChannel.toRaw, (exposedProgramInteractions input).map
      ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

/-- The row contains no Clean lookup operations; cross-table checks use channels. -/
theorem lookups_empty :
    ({ circuit := LtChip.circuit (p := p) } :
      Air.Flat.Component (ZMod p)).operations.lookups = [] := by
  rw [Air.Flat.Component.lookups_eq, Air.Flat.Component.rowOperations_mk,
    LtChip.circuit_main_eq]
  simp [LtChip.main, Readers.CPUState.circuit, Readers.CPUState.main,
    Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
    Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
    Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
    Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
    LtOperationSigned.circuit, LtOperationSigned.main,
    LtOperationUnsigned.circuit, LtOperationUnsigned.main,
    U16MSBOperation.circuit, U16MSBOperation.main,
    U16CompareOperation.circuit, U16CompareOperation.main,
    Gadgets.Equality.main, circuit_norm]

end SP1Clean.LtChip
