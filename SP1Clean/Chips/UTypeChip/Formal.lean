import SP1Clean.Chips.UTypeChip.Defs

/-! # `SP1Clean.UTypeChip` — contract: `Assumptions` / soundness / completeness / `circuit`

The chip `Spec` (J-type reader sub-`Spec` + `is_real`/`is_auipc`-binary + `RV64.lui`/`RV64.auipc`
identities) lives in `Specs/Chip.lean`. -/

namespace SP1Clean.UTypeChip

open Circuit
open Extracted (UTypeColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Operands `isU64`; the padding convention `is_real = 0 → op_a_0 = 0` ensures `is_real - op_a_0` is
binary. The decode fact `op_b_imm = RV64.lui (immOf adapter)` (the committed immediate is `sign_extend (imm
<< 12)`) is a trace/program-ROM guarantee. `is_real`/`is_auipc`-binary are proven from the gates. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_b_imm ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  (input.is_real = 0 → input.adapter.op_a_0 = 0) ∧
  Word.toBitVec64 input.adapter.op_b_imm = RV64.lui (immOf input.adapter)

/-- Honest prover-side row well-formedness. The immediate + program-counter words `isU64`, `is_real`/
`is_auipc` binary, `op_a_0 = 0` (the `rd ≠ x0` rows completeness covers), the CPUState clock bounds + op_a
register-access timestamp bounds, and the decode fact. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_b_imm ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_auipc = 0 ∨ input.is_auipc = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state,
      next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Word.toBitVec64 input.adapter.op_b_imm = RV64.lui (immOf input.adapter)

omit [Fact p.Prime] in
/-- `Word.toBitVec64 #v[0,0,0,0] = 0`. -/
lemma toBitVec64_zero_word : Word.toBitVec64 (#v[(0 : ZMod p), 0, 0, 0] : Word (ZMod p)) = 0 := by
  simp [Word.toBitVec64, Word.toNat_def]

/-- `RV64.auipc imm pc = pc + RV64.lui imm` (AUIPC's offset is `RV64.lui`'s value added to `pc`). -/
lemma auipc_eq_add_lui (imm : BitVec 20) (pcv : BitVec 64) :
    RV64.auipc imm pcv = pcv + RV64.lui imm := by
  rw [RV64.auipc, RV64.lui]; exact BitVec.add_comm _ _

set_option maxHeartbeats 2000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_imm, h_pcU, h_pad, h_dec⟩ := h_assumptions
  obtain ⟨_h_cpu, h_add, h_jt0, h_ad0, h_ad1, h_ad2, h_iaui_gate, h_real_gate⟩ := h_holds
  unfold id at *
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := bool_of_mul_pred h_real_gate
  have h_iaui : input_is_auipc = 0 ∨ input_is_auipc = 1 := bool_of_mul_pred h_iaui_gate
  have h_jt := h_jt0 h_bin
  have h_op_a_0 : input_adapter_op_a_0 = 0 ∨ input_adapter_op_a_0 = 1 := h_jt.2.1
  have hpc : Vector.map (Expression.eval env) input_var_state_pc = input_state_pc := h_input.2.1.2.2.2
  have ep0 : Expression.eval env input_var_state_pc[0] = input_state_pc[0] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep1 : Expression.eval env input_var_state_pc[1] = input_state_pc[1] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep2 : Expression.eval env input_var_state_pc[2] = input_state_pc[2] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ha0 : env.get i₀ = input_is_auipc * input_state_pc[0] := by
    rw [ep0] at h_ad0; exact add_neg_eq_zero.mp h_ad0
  have ha1 : env.get (i₀ + 1) = input_is_auipc * input_state_pc[1] := by
    rw [ep1] at h_ad1; exact add_neg_eq_zero.mp h_ad1
  have ha2 : env.get (i₀ + 2) = input_is_auipc * input_state_pc[2] := by
    rw [ep2] at h_ad2; exact add_neg_eq_zero.mp h_ad2
  have haddend0 : input_is_auipc = 0 →
      (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] : Word (ZMod p)) = #v[0, 0, 0, 0] := by
    intro h; rw [ha0, ha1, ha2, h]; simp
  have haddendpc : input_is_auipc = 1 →
      (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] : Word (ZMod p))
        = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
    intro h; rw [ha0, ha1, ha2, h]; simp
  have h_addendU : Word.isU64 (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] : Word (ZMod p)) := by
    rcases h_iaui with h | h
    · rw [haddend0 h]; refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;> simp
    · rw [haddendpc h]; exact h_pcU
  -- `is_real - op_a_0` is binary: on real rows from `op_a_0 ∈ {0,1}`, on padding from `h_pad`.
  have h_gate2 : input_is_real + -input_adapter_op_a_0 = 0 ∨ input_is_real + -input_adapter_op_a_0 = 1 := by
    rcases h_bin with h | h
    · rw [h, h_pad h]; simp
    · rcases h_op_a_0 with h0 | h0 <;> rw [h, h0] <;> simp
  have h_addspec := h_add ⟨fun _ => ⟨h_addendU, h_imm⟩, h_gate2⟩
  refine ⟨⟨h_jt, h_bin, h_iaui, ?_, ?_⟩, Or.inr h_bin, Or.inr ⟨fun _ => ⟨h_addendU, h_imm⟩, h_gate2⟩, Or.inr h_bin⟩
  · intro hr1 hop0 hiaui0
    have hg1 : input_is_real + -input_adapter_op_a_0 = 1 := by rw [hr1, hop0]; simp
    have hsem := (h_addspec hg1).2
    simp only [haddend0 hiaui0, toBitVec64_zero_word] at hsem
    rw [hsem]; simpa using h_dec
  · intro hr1 hop0 hiaui1
    have hg1 : input_is_real + -input_adapter_op_a_0 = 1 := by rw [hr1, hop0]; simp
    have hsem := (h_addspec hg1).2
    simp only [haddendpc hiaui1] at hsem
    rw [hsem, auipc_eq_add_lui, ← h_dec]
    simp only [pcWord]

set_option maxHeartbeats 2000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_imm, h_pcU, h_bin, h_iaui, h_op0, h_cpu, h_rac, _h_dec⟩ := h_assumptions
  obtain ⟨_, ⟨_, _, _, hpc⟩, ⟨_, _, _, hob, _⟩, _⟩ := h_input
  obtain ⟨he_addend, he_addval⟩ := h_env
  have ep0 : Expression.eval env.toEnvironment input_var_state_pc[0] = input_state_pc[0] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep1 : Expression.eval env.toEnvironment input_var_state_pc[1] = input_state_pc[1] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep2 : Expression.eval env.toEnvironment input_var_state_pc[2] = input_state_pc[2] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have hg0 : env.get i₀ = input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[0] := by
    simpa using he_addend 0
  have hg1 : env.get (i₀ + 1) = input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[1] := by
    simpa using he_addend 1
  have hg2 : env.get (i₀ + 2) = input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[2] := by
    simpa using he_addend 2
  have hAeq : (#v[input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[0],
        input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[1],
        input_is_auipc * Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] := by rw [hg0, hg1, hg2]
  have hbeq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_imm[0],
        Expression.eval env.toEnvironment input_var_adapter_op_b_imm[1],
        Expression.eval env.toEnvironment input_var_adapter_op_b_imm[2],
        Expression.eval env.toEnvironment input_var_adapter_op_b_imm[3]] : Word (ZMod p))
      = input_adapter_op_b_imm := by
    rw [← hob]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var { index := i₀ + 3 + i }) : Word (ZMod p))
      = AddOperation.populate #v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0]
          input_adapter_op_b_imm := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [he_addval ⟨i, hi⟩]
    simp only [hAeq, hbeq]
  have hA_U : Word.isU64 (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] : Word (ZMod p)) := by
    rcases h_iaui with h | h
    · have e : (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] : Word (ZMod p)) = #v[0, 0, 0, 0] := by
        rw [hg0, hg1, hg2, h]; simp
      rw [e]; refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;> simp
    · have e : (#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), 0] : Word (ZMod p))
          = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by
        rw [hg0, hg1, hg2, h, ep0, ep1, ep2]; simp
      rw [e]; exact h_pcU
  have h_gate2 : input_is_real + -input_adapter_op_a_0 = 0 ∨ input_is_real + -input_adapter_op_a_0 = 1 := by
    rw [h_op0]; simpa using h_bin
  refine ⟨⟨h_bin, h_cpu⟩, ⟨⟨fun _ => ⟨hA_U, h_imm⟩, h_gate2⟩, ?_⟩,
    ⟨h_bin, ⟨?_, ?_, ?_, ?_⟩, Or.inl h_op0, h_rac⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hval]; exact AddOperation.spec_populate hA_U h_imm (input_is_real + -input_adapter_op_a_0)
  · rw [h_op0, zero_mul]
  · rw [h_op0, zero_mul]
  · rw [h_op0, zero_mul]
  · rw [h_op0, zero_mul]
  · rw [hg0]; ring_nf
  · rw [hg1]; ring_nf
  · rw [hg2]; ring_nf
  · rcases h_iaui with h | h <;> rw [h] <;> simp
  · rcases h_bin with h | h <;> rw [h] <;> simp

/-- The U-type chip row as a `GeneralFormalCircuit`: the flag-gated `RV64.lui`/`RV64.auipc` semantics,
composing the witnessed `AddOperation` gadget and the J-type reader; output is the extracted `UTypeColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs UTypeColumns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.UTypeChip
