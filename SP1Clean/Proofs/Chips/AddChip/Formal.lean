import SP1Clean.Native.Chips.AddChip.Defs
import SP1Clean.FormalModel.Contracts.ChipAssumptions

/-! # `SP1Clean.AddChip` — contract: `Assumptions` / soundness / completeness / `circuit`

This is the canonical "template" chip for the porting recipe (`docs/agents/porting-recipe.md`). When
golfing / cleaning proofs here or in any sibling chip, follow `docs/agents/proof-patterns.md` §
"Golf & cleanup discipline". -/

namespace SP1Clean.AddChip

open Circuit
open Extracted (AddCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- `Assumptions` / `ProverAssumptions` are on the audit surface in
`FormalModel/Contracts/ChipAssumptions.lean` (same `SP1Clean.AddChip` namespace). -/

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  -- The `Spec` is the inlined R-type-with-readers contract; `circuit_proof_start` unfolds it,
  -- re-normalizes `wv*` result-word fields, and drops the leading CPUState `True` fragment.
  circuit_proof_start
  obtain ⟨ha, hb⟩ := h_assumptions
  obtain ⟨_, h_add, h_adapter, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- `AddOperation` is a `FormalAssertion`; `h_add` is `Assumptions → Spec`. Feed `⟨ha, hb, h_bin⟩`
  -- inline (drives unification on the witnessed `value` field) and apply the gated add identity.
  refine ⟨⟨h_adapter h_bin, h_bin, fun hr => (h_add ⟨fun _ => ⟨ha, hb⟩, h_bin⟩ hr).2⟩, ?_⟩
  -- The sub-circuit `Assumptions` tail (post-Clean-`main`: each is a bare `Assumptions` or a
  -- `channelsWithRequirements = [] ∨ Assumptions` disjunct). All discharged by the binary gate + `ha`/`hb`.
  and_intros <;>
    first | exact h_bin | exact Or.inl rfl | exact Or.inr h_bin | exact Or.inr ⟨fun _ => ⟨ha, hb⟩, h_bin⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hrac_c⟩ := h_assumptions
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩ := h_input
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  have mapEq : ∀ (vv : Word (Expression (ZMod p))) (v : Word (ZMod p)),
      Vector.map (Expression.eval env.toEnvironment) vv = v →
      (#v[Expression.eval env.toEnvironment vv[0], Expression.eval env.toEnvironment vv[1],
        Expression.eval env.toEnvironment vv[2], Expression.eval env.toEnvironment vv[3]] : Word (ZMod p)) = v :=
    fun vv v h => by rw [← h]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hbeq := mapEq input_var_adapter_op_b_memory_prev_value _ hob
  have hceq := mapEq input_var_adapter_op_c_memory_prev_value _ hoc
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
  channelsWithRequirements :=
    [byteChannel.toRaw, stateChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw]

end SP1Clean.AddChip
