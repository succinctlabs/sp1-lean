import SP1Clean.Chips.AddChip.Defs

/-! # `SP1Clean.AddChip` — contract: `Assumptions` / soundness / completeness / `circuit` -/

namespace SP1Clean.AddChip

open Circuit
open Extracted (AddCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values (true on real and zero-padded rows). `is_real`-binary is NOT assumed
here — soundness *proves* it from the in-circuit binary gate (it lives in the `Spec`); only completeness
needs it as a prover precondition (see `ProverAssumptions`). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- The prover-side row well-formedness, with the reader column blocks as *threaded inputs*: the
operand `isU64`s, the `is_real` binary selector, the `op_a_0 = 0` flag (real Add rows write a non-`x0`
destination — the restriction the `op_a_0` flag imposes), and the
`is_real`-gated CPUState clock bounds + per-operand register-access timestamp bounds (the verifier commits a
well-formed clock/timestamp row). Soundness never assumes these — it derives the bounds from the byte bus. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]],
      clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_b_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3⟩ ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_c_memory, input.is_real, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 2⟩

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  -- `RTypeChipSpec` is fed to `circuit_proof_start` so it unfolds the shared Spec-builder def,
  -- re-normalizes `wv*` result-word fields, and drops the leading CPUState `True` fragment.
  circuit_proof_start [RTypeChipSpec]
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨_, h_add, h_adapter, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- `AddOperation` is a `FormalAssertion`; `h_add` is `Assumptions → Spec`. Feed `⟨ha, hb, h_bin⟩`
  -- inline (drives unification on the witnessed `value` field) and apply the gated add identity.
  refine ⟨⟨h_adapter h_bin, h_bin, fun hr => (h_add ⟨fun _ => ⟨ha, hb⟩, h_bin⟩ hr).2⟩, ?_⟩
  and_intros <;>
    first | exact Or.inl rfl | exact Or.inr h_bin | exact Or.inr ⟨fun _ => ⟨ha, hb⟩, h_bin⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hrac_c⟩ := h_assumptions
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩ := h_input
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have hbeq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_memory_prev_value[3]] : Word (ZMod p))
      = input_adapter_op_b_memory_prev_value := by
    rw [← hob]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hceq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[0],
      Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[1],
      Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[2],
      Expression.eval env.toEnvironment input_var_adapter_op_c_memory_prev_value[3]] : Word (ZMod p))
      = input_adapter_op_c_memory_prev_value := by
    rw [← hoc]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  -- The witnessed `value` is `populate op_b op_c` (`h_env` per-limb).
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + i}) : Word (ZMod p))
      = AddOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [h_env ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨fun _ => ⟨ha, hb⟩, hbin⟩, ?_⟩,
    ⟨hbin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c⟩, ?_⟩
  · rw [hval]; exact AddOperation.spec_populate ha hb input_is_real
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The Add chip row as a `GeneralFormalCircuit`: semantic contract, composing the
witnessed gadget; output is the extracted `AddCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs AddCols where
  main
  elaborated
  Assumptions := Assumptions
  Spec := Spec
  ProverAssumptions := ProverAssumptions
  ProverSpec := fun _ _ _ => True
  soundness := soundness
  completeness := completeness

end SP1Clean.AddChip
