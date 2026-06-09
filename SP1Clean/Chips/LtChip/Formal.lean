import SP1Clean.Chips.LtChip.Defs

/-! # `SP1Clean.LtChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.LtChip

open Circuit
open Extracted (LtCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values; `is_real`-binary is proven from the in-circuit gate (so it lives in
`Spec`), not assumed. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- Prover-side row well-formedness: operand `isU64`s, `is_real` binary, `op_a_0 = 0`,
`imm_c = 0` (SLT/SLTU are register-register), CPUState clock bounds, three timestamp `Spec`s
(op_c gated by `is_real - imm_c`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧ input.adapter.imm_c = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real - input.adapter.imm_c,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩

/-- Semantic contract, stated against the clean RV64 ISA functions (mirrors the R-type chip contract, here spelled
inline for the **two-variant** ALU adapter): the `ALUTypeReader` sub-`Spec` on the `state`/`adapter`
blocks (opcode `is_slt·9 + is_sltu·10`, `rd` write the result word), the proven `is_real`-binary fact, and
the `is_real`/flag-gated meaning — on real rows the result word is the RV64 `SLT` (when `is_slt = 1`) or
`SLTU` (when `is_sltu = 1`) of the operands (operand order matching the RV64 signature `f rs2_val rs1_val`
with `rs1 ↦ op_b_val`). Vacuous on padding. -/
def Spec (input : Inputs (ZMod p)) (cols : LtCols (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Readers.ALUTypeReader.Spec
    { cols := cols.adapter, is_real := input.is_real, is_trusted := input.is_real,
      clk_high := cols.state.clk_high,
      clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536,
      pc := cols.state.pc, opcode := cols.is_slt * 9 + cols.is_sltu * 10,
      wv0 := (resultWord cols)[0], wv1 := (resultWord cols)[1],
      wv2 := (resultWord cols)[2], wv3 := (resultWord cols)[3] } ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    (cols.is_slt = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.slt (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)) ∧
    (cols.is_sltu = 1 →
      Word.toBitVec64 (resultWord cols)
        = RV64.sltu (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val)))

/-- The clean RV64 `slt` reduced to its `if`-form: `RV64.slt y x` is `1#64` iff `x <ₛ y`. -/
private lemma rv64_slt_eq (x y : BitVec 64) :
    RV64.slt y x = if x.toInt < y.toInt then 1#64 else 0#64 := by
  by_cases h : x.toInt < y.toInt <;> simp [RV64.slt, BitVec.slt, h]

/-- The clean RV64 `sltu` reduced to its `if`-form: `RV64.sltu y x` is `1#64` iff `x <ᵤ y`. -/
private lemma rv64_sltu_eq (x y : BitVec 64) :
    RV64.sltu y x = if x.toNat < y.toNat then 1#64 else 0#64 := by
  by_cases h : x.toNat < y.toNat <;> simp [RV64.sltu, BitVec.ult, h]

/-- The `resultWord` `#v[bit, 0, 0, 0]` packs to the 64-bit `0/1` indicator carried by its low limb:
when the compare `bit` is `if P then 1 else 0`, the word's `toBitVec64` is `if P then 1#64 else 0#64`. -/
private lemma toBitVec64_bitWord (bit : ZMod p) (P : Prop) [Decidable P]
    (h : bit = if P then 1 else 0) :
    Word.toBitVec64 (#v[bit, 0, 0, 0] : Word (ZMod p)) = if P then 1#64 else 0#64 := by
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  subst h
  by_cases hP : P <;> simp [hP, Word.toBitVec64, Word.toNat, ZMod.val_one, ZMod.val_zero]

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Spec]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨_cpu, h_lt, h_adapter, h_gate, h_slt_bin, h_sltu_bin, h_sum⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  have h_slt_bool := bool_of_mul_pred h_slt_bin
  have h_sltu_bool := bool_of_mul_pred h_sltu_bin
  refine ⟨⟨h_adapter h_bin, h_bin, fun hr => ⟨fun hslt => ?_, fun hsltu => ?_⟩⟩,
    Or.inr h_bin, Or.inr ⟨ha, hb, h_bin, h_slt_bool⟩, Or.inr h_bin⟩
  · -- `is_slt = 1` ⇒ `is_signed = 1`, so the gadget bit is the signed compare. The structural
    -- `Spec` exposes the semantic bit via `result_semantic`.
    have h_lt_spec := (LtOperationSigned.result_semantic ha hb hr (h_lt ⟨ha, hb, h_bin, h_slt_bool⟩)).1
    rw [hslt] at h_lt_spec
    simp only [if_true] at h_lt_spec
    simp only [resultWord, rv64_slt_eq, toBitVec64_bitWord _ _ h_lt_spec]
  · -- `is_sltu = 1` with the sum-bound + booleans forces `is_slt = 0`
    have h_lt_spec := (LtOperationSigned.result_semantic ha hb hr (h_lt ⟨ha, hb, h_bin, h_slt_bool⟩)).1
    have h_slt0 : env.get i₀ = 0 := by
      rcases h_slt_bool with h0 | h1
      · exact h0
      · exfalso
        rw [h1, hsltu] at h_sum
        have h20 : (2 : ZMod p) = 0 := by
          have e : (2 : ZMod p) = (1 + 1) * (1 + 1 + -1) := by ring
          rw [e]; exact h_sum
        have hp := Fact.out (p := 2 ^ 17 < p)
        have h2 : ((2 : ℕ) : ZMod p) ≠ 0 := by
          rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
          intro hd
          have := Nat.le_of_dvd (by norm_num) hd
          omega
        exact h2 (by exact_mod_cast h20)
    have h01 : (0 : ZMod p) ≠ 1 := by
      haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
      intro h
      have := congrArg ZMod.val h
      rw [ZMod.val_zero, ZMod.val_one] at this
      exact absurd this (by norm_num)
    rw [h_slt0] at h_lt_spec
    simp only [if_neg h01] at h_lt_spec
    simp only [resultWord, rv64_sltu_eq, Word.toBitVec64_toNat ha,
      Word.toBitVec64_toNat hb, toBitVec64_bitWord _ _ h_lt_spec]

set_option linter.unusedSectionVars false in
/-- A length-4 `#v` of pointwise evaluations is the `Vector.map` of the evaluator (lets the witness
hint's `populate` operands, written `#v[env op_*_val[k]]` by the generator, be folded to `Vector.map`). -/
private lemma vec4_eval (e : Environment (ZMod p)) (v : Vector (Expression (ZMod p)) 4) :
    (#v[Expression.eval e v[0], Expression.eval e v[1], Expression.eval e v[2],
        Expression.eval e v[3]] : Vector (ZMod p) 4) = Vector.map (Expression.eval e) v := by
  ext k hk
  interval_cases k <;> simp [Vector.getElem_map]

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin, hop_a_0, himm, h_cpu, hrac_a, hrac_b, hrac_c⟩ := h_assumptions
  obtain ⟨h_env_flags, h_env_cols⟩ := h_env
  have hflag0 : env.get i₀ = 0 := by simpa using h_env_flags 0
  have hflag1 : env.get (i₀ + 1) = 0 := by simpa using h_env_flags 1
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  refine ⟨⟨hbin, h_cpu⟩,
    ⟨⟨ha, hb, hbin, Or.inl hflag0⟩, ?_⟩,
    ⟨hbin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0,
      by rw [himm, mul_zero], by rw [himm, sub_zero]; exact hbin,
      ⟨by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul]⟩,
      hrac_a, hrac_b, hrac_c⟩,
    by rcases hbin with h | h <;> rw [h] <;> simp,
    by rw [hflag0]; simp,
    by rw [hflag1]; simp,
    by rw [hflag0, hflag1]; simp⟩
  -- The composed `LtOperationSigned` `FormalAssertion`'s `Spec` at the witnessed `populate`d columns:
  -- `spec_populate` once the witnessed column struct equals `populate …` (each cell is `env.get (i₀+2+k)`,
  -- pinned by the normalised witness hint to `(toElements (populate …))[k]`).
  have hpvb : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_b_memory_prev_value
      = input_adapter_op_b_memory_prev_value := h_input.2.2.2.2.2.2.1.1
  have hpvc : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_c
      = input_adapter_op_c := h_input.2.2.2.2.2.2.2.1
  simp only [Inputs.op_b_val, Inputs.op_c_val, vec4_eval, hpvb, hpvc] at h_env_cols
  convert LtOperationSigned.spec_populate (b := input_adapter_op_b_memory_prev_value)
    (cc := input_adapter_op_c) (is_signed := env.get i₀) (is_real := input_is_real)
    ha hb (Or.inl hflag0) hbin (by rw [hflag0, mul_zero]) using 2
  refine (ProvableType.ext_iff _ _).mpr (fun i hi => ?_)
  refine Eq.trans ?_
    ((getElem_toElements_eval_varFromOffset env.toEnvironment (i₀ + 2) i hi).trans (h_env_cols ⟨i, hi⟩))
  simp [circuit_norm]

/-- The unified `Lt` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `slt`/`sltu` semantic contract,
composing the witnessed signed-compare gadget and the immediate-capable register reader; output is the
extracted `LtCols` column struct. Soundness/completeness are proven and axiom-clean. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs LtCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.LtChip
