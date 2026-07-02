import SP1Clean.Native.Chips.LtChip.Defs
import SP1Clean.Math.EvalVec

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

/-- Prover-side row well-formedness: operand `isU64`s (`op_b_val`/`op_c_val`), the op_a read-prior
`isU64` (op_a memory pull) and the op_c read-prior `isU64` (the `is_real - imm_c`-gated op_c memory pull —
distinct from `op_c_val = adapter.op_c` since `Lt`'s adapter is immediate-capable), `is_real` binary, the
honest `"lt_flags"` hint (each flag binary, the sum = `is_real`, `is_slt` only on real rows), `op_a_0 = 0`,
`imm_c = 0` (register-register rows), CPUState clock bounds, three timestamp `Spec`s
(op_c gated by `is_real - imm_c`). -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) : Prop :=
  let f := hintFlags hint
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 1 → Word.isU64 input.adapter.op_a_memory.prev_value) ∧
  (input.is_real - input.adapter.imm_c = 1 → Word.isU64 input.adapter.op_c_memory.prev_value) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (f[0] = 0 ∨ f[0] = 1) ∧ (f[1] = 0 ∨ f[1] = 1) ∧
  input.is_real = f[0] + f[1] ∧
  (f[0] = 1 → input.is_real = 1) ∧
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
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩ ∧
  (input.is_real = 1 → input.adapter.op_a.val < 32 ∧
    input.state.pc[0].val < 2 ^ 16 ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

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

/-- A binary field element's `val` is a valid 16-bit limb. -/
private lemma val_lt_of_bool {b : ZMod p} (h : b = 0 ∨ b = 1) : b.val < 2 ^ 16 := by
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rcases h with h | h <;> rw [h]
  · rw [ZMod.val_zero]; norm_num
  · rw [ZMod.val_one]; norm_num

/-- The Lt result word `#v[bit, 0, 0, 0]` is a valid u64 whenever the compare `bit` is binary (the
op_a write push's `isU64 value` obligation). -/
private lemma isU64_bitWord {b : ZMod p} (h : b = 0 ∨ b = 1) :
    Word.isU64 (#v[b, 0, 0, 0] : Word (ZMod p)) :=
  Word.isU64_of_cases (val_lt_of_bool h) (val_lt_of_bool (Or.inl rfl))
    (val_lt_of_bool (Or.inl rfl)) (val_lt_of_bool (Or.inl rfl))

set_option linter.unusedSectionVars false in
/-- A field element pinned to `if Q then 1 else 0` is binary (used in soundness to read the compare
`bit`'s binary-ness off `LtOperationSigned.result_semantic`). -/
private lemma bool_of_eq_ite {b : ZMod p} {Q : Prop} [Decidable Q]
    (h : b = if Q then 1 else 0) : b = 0 ∨ b = 1 := by
  split at h
  · exact Or.inr h
  · exact Or.inl h

set_option linter.unusedSectionVars false in
/-- Column 0 of a flattened `LtOperationSigned` column struct is its compare `bit` (peeling the
`ProvableStruct` `toComponents`/`cast`/`append` tower). Used by completeness to read the witnessed bit
out of the `populate`-pinned witness cell `env.get (i₀ + 2)`. -/
private lemma toElements_col0 {x : Extracted.LtOperationSigned (ZMod p)}
    (hi : (0:ℕ) < size Extracted.LtOperationSigned) :
    (toElements x)[0]'hi = x.result.u16_compare_operation.bit := by
  simp only [ProvableType.toElements, ProvableStruct.toComponents,
    ProvableStruct.componentsToElements, circuit_norm]
  rw [Vector.getElem_append_left (by decide), Vector.getElem_cast,
    Vector.getElem_append_left (by decide), Vector.getElem_cast]
  rfl

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

/-- The witnessed `LtOperationSigned` block's flattened cell 0 (the compare `bit`) is binary on a real
row — the form completeness uses after pinning the witness cell `env.get (i₀ + 2)` to `populate`. -/
private lemma witness_bit_bool {b cc : Word (ZMod p)} {s r : ZMod p} (hr : r = 1)
    (hi : (0:ℕ) < size Extracted.LtOperationSigned) :
    (toElements (LtOperationSigned.populate b cc s r))[0]'hi = 0 ∨
    (toElements (LtOperationSigned.populate b cc s r))[0]'hi = 1 := by
  rw [toElements_col0]; exact populate_bit_bool hr

set_option maxHeartbeats 800000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start [Spec]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨_cpu, h_lt, h_adapter, _h_rw, h_gate, h_slt_bin, h_sltu_bin, h_sum⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  have h_slt_bool := bool_of_mul_pred h_slt_bin
  have h_sltu_bool := bool_of_mul_pred h_sltu_bin
  refine ⟨⟨h_adapter ⟨h_bin, h_bin⟩, h_bin, fun hr => ⟨fun hslt => ?_, fun hsltu => ?_⟩⟩, ?_⟩
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
      exact zero_ne_one
    rw [h_slt0] at h_lt_spec
    simp only [if_neg h01] at h_lt_spec
    simp only [resultWord, rv64_sltu_eq, Word.toBitVec64_toNat ha,
      Word.toBitVec64_toNat hb, toBitVec64_bitWord _ _ h_lt_spec]
  -- The per-emitter channel-requirement tail: the bare `CPUState` `Assumptions` (the binary gate), the
  -- composed `LtOperationSigned`/`ALUTypeReader` requirements (bare or `[] ∨ Assumptions` disjuncts).
  · and_intros <;>
      first | exact h_bin | exact ⟨ha, hb, h_bin, h_slt_bool⟩ | exact ⟨h_bin, h_bin⟩
            | exact Or.inl rfl | exact Or.inr ⟨h_bin, h_bin⟩
            | exact Or.inr ⟨h_bin, fun hr => isU64_bitWord
                (bool_of_eq_ite (LtOperationSigned.result_semantic ha hb hr
                  (h_lt ⟨ha, hb, h_bin, h_slt_bool⟩)).1)⟩

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, ha_prev, hc_prev, hbin, hf0, hf1, hsum, hslt_real, hop_a_0, himm, h_cpu,
    hrac_a, hrac_b, hrac_c, hdec⟩ := h_assumptions
  obtain ⟨h_env_flags, h_env_cols⟩ := h_env
  have hflag0 : env.get i₀ = (hintFlags env.hint)[0] := by simpa using h_env_flags 0
  have hflag1 : env.get (i₀ + 1) = (hintFlags env.hint)[1] := by simpa using h_env_flags 1
  have hf0' : env.get i₀ = 0 ∨ env.get i₀ = 1 := by rw [hflag0]; exact hf0
  have hf1' : env.get (i₀ + 1) = 0 ∨ env.get (i₀ + 1) = 1 := by rw [hflag1]; exact hf1
  have hsum01' : env.get i₀ + env.get (i₀ + 1) = 0 ∨ env.get i₀ + env.get (i₀ + 1) = 1 := by
    rw [hflag0, hflag1, ← hsum]; exact hbin
  have hbool : ∀ x : ZMod p, x = 0 ∨ x = 1 → x * (x + -1) = 0 := by
    rintro x (h | h) <;> rw [h] <;> simp
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  refine ⟨⟨hbin, h_cpu⟩,
    ⟨⟨ha, hb, hbin, hf0'⟩, ?_⟩,
    ⟨⟨hbin, hbin⟩, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0,
      by rw [himm, mul_zero], by rw [himm, sub_zero]; exact hbin,
      ⟨by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul], by rw [himm, zero_mul]⟩,
      hrac_a, hrac_b, hrac_c, hdec, fun hr => ⟨ha_prev hr, ha⟩, hc_prev⟩,
    ⟨⟨hbin, ?_⟩, trivial⟩,
    by rcases hbin with h | h <;> rw [h] <;> simp,
    hbool _ hf0',
    hbool _ hf1',
    hbool _ hsum01'⟩
  -- The composed `LtOperationSigned` `FormalAssertion`'s `Spec` at the witnessed `populate`d columns:
  -- `spec_populate` once the witnessed column struct equals `populate …` (each cell is `env.get (i₀+2+k)`,
  -- pinned by the normalised witness hint to `(toElements (populate …))[k]`).
  have hpvb : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_b_memory_prev_value
      = input_adapter_op_b_memory_prev_value := h_input.2.2.2.2.2.2.1.1
  have hpvc : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_c
      = input_adapter_op_c := h_input.2.2.2.2.2.2.2.1
  simp only [Inputs.op_b_val, Inputs.op_c_val, vec4_eval, hpvb, hpvc] at h_env_cols
  have hgate : (input_is_real - 1) * env.get i₀ = 0 := by
    rw [hflag0]
    rcases hf0 with h | h
    · rw [h, mul_zero]
    · rw [hslt_real h, h]
      simp
  convert LtOperationSigned.spec_populate (b := input_adapter_op_b_memory_prev_value)
    (cc := input_adapter_op_c) (is_signed := env.get i₀) (is_real := input_is_real)
    ha hb hf0' hbin hgate using 2
  refine (ProvableType.ext_iff _ _).mpr (fun i hi => ?_)
  refine Eq.trans ?_
    ((getElem_toElements_eval_varFromOffset env.toEnvironment (i₀ + 2) i hi).trans (h_env_cols ⟨i, hi⟩))
  simp [circuit_norm]
  -- RegisterWrite's `isU64 #v[bit, 0, 0, 0]` (the op_a write push): the upper three limbs are literal
  -- `0`; the witnessed compare `bit` `env`-evaluates (via `h_env_cols`) to the `populate`d column 0,
  -- i.e. `U16CompareOperation.populate_bit …`, which is binary by `populate_bit_bool`.
  intro hr
  have h0 := h_env_cols 0
  simp only [Fin.val_zero, Nat.add_zero] at h0
  refine isU64_bitWord ?_
  rw [h0]
  exact witness_bit_bool hr _

/-- The unified `Lt` chip row as a `GeneralFormalCircuit`: flag-gated RV64 `slt`/`sltu` semantic contract,
composing the witnessed signed-compare gadget and the immediate-capable register reader; output is the
extracted `LtCols` column struct. Soundness/completeness are proven and axiom-clean. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs LtCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    -- W11 (A2): expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8)
    -- so the chip is a `VmTables` table; descends to the composed `CPUState` subcircuit's lone pull+push.
    exposedChannels := fun input _ =>
      expose stateChannel
        [ pulledIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          pushedIf input.is_real
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ],
    exposedChannels_eq := by
      intro input offset
      simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
        Readers.ALUTypeReader.circuit, Readers.ALUTypeReader.main,
        Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
        Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
        Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        SP1Clean.LtOperationSigned.circuit, SP1Clean.LtOperationSigned.main,
        SP1Clean.U16MSBOperation.circuit, SP1Clean.U16MSBOperation.main,
        SP1Clean.LtOperationUnsigned.circuit, SP1Clean.LtOperationUnsigned.main,
        SP1Clean.U16CompareOperation.circuit, SP1Clean.U16CompareOperation.main,
        circuit_norm, FormalAssertion.toSubcircuit_interactions]
      simp [circuit_norm, Gadgets.Equality.main] }

end SP1Clean.LtChip
