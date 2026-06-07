import SP1Clean.Chips.AddChip.Defs

/-! # The Add chip's `FormalCircuit` contract — `Assumptions` / soundness / completeness / `circuit`

The semantic contract for the Add chip row whose `main` + `ElaboratedCircuit` live in the sibling
`Defs` module: the prover/verifier `Assumptions`, the `soundness`/`completeness` proofs (routing the
add identity through `AddOperation`'s gadget `Spec`), and the bundled `GeneralFormalCircuit`. The Sail
bridge composing this `Spec` into the RISC-V spec is in `Bridge`. -/

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
  -- Pass `RTypeChipSpec` so `circuit_proof_start`'s goal `simp only [circuit_norm, …]` unfolds the shared
  -- `Spec`-builder def and re-normalizes its `wv* := resultWord[i]` fields (`(Vector.map eval v)[i]` →
  -- `eval v[i]`, matching the reader subcircuit's `h_adapter`) and drops the leading `True` (`true_and`).
  circuit_proof_start [RTypeChipSpec]
  obtain ⟨ha, hb⟩ := h_assumptions
  -- `h_holds` = the subcircuit results in emission order: CPUState reader, add gadget, RTypeReader
  -- reader, binary gate. The chip `Spec` is each sub-circuit's own `Spec` (direct sub-calls) + the
  -- proven `is_real`-binary gate + the gated add identity. The readers' `Assumptions` are now `True`
  -- (the byte/state/memory/program sends carry `Guarantees := True`), so no `isU64 wv` discharge is
  -- needed; the channel-requirement tail is trivial / sub-circuit `Or.inr trivial` disjuncts.
  -- `_` is the CPUState `assertion`'s contribution (its clk-bounds `Spec`, given `is_real` binary); the
  -- chip `Spec`'s CPUState conjunct is now `True` (simplified away by `circuit_proof_start`), so it is unused.
  obtain ⟨_, h_add, h_adapter, h_gate⟩ := h_holds
  -- `is_real` binary (from the chip's gate) — the chip `Spec`'s binary conjunct AND what discharges the
  -- readers'/operation's / the CPUState assertion's `is_real ∈ {0,1}` `Assumptions` (the gated design).
  have h_bin := bool_of_mul_pred h_gate
  -- `AddOperation` is now a `FormalAssertion` with `Assumptions = isU64 a ∧ isU64 b ∧ is_real∈{0,1}` and
  -- an `is_real`-gated semantic `Spec`; `h_add` is `Assumptions → Spec`, so feed `⟨ha, hb, h_bin⟩` (inline so
  -- the witnessed `value` field is driven by unification) and apply the resulting `is_real = 1 → …` under the
  -- chip's `is_real = 1` hypothesis (`.2` = the add identity).
  -- `Spec` is `RTypeChipSpec …`; `circuit_proof_start [RTypeChipSpec]` exposed it and `true_and` dropped the
  -- leading `True` (CPUState fragment), so the surfaced inner triple is reader-`Spec` / binary / gated-add.
  refine ⟨⟨h_adapter h_bin, h_bin, fun hr => (h_add ⟨fun _ => ⟨ha, hb⟩, h_bin⟩ hr).2⟩, ?_⟩
  -- the channel-requirement tail: per sub-circuit `<sub>.channelsWithRequirements = [] ∨ <sub>.Assumptions`
  -- — `CPUState`/`RTypeReader` carry the binary fact (`Or.inr h_bin`); `AddOperation` now emits the byte
  -- bus too, so its disjunct is `Or.inr ⟨ha, hb, h_bin⟩`.
  and_intros <;>
    first | exact Or.inl rfl | exact Or.inr h_bin | exact Or.inr ⟨fun _ => ⟨ha, hb⟩, h_bin⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  -- The threaded reader blocks are inputs now, so the composed obligations are discharged straight from
  -- `ProverAssumptions`: CPUState `⟨is_real binary, clk bounds⟩`, `AddOperation` `⟨isU64, isU64⟩`,
  -- RTypeReader `⟨is_real binary, ⟨zeroing (from op_a_0 = 0), op_a_0 binary, the three timestamp `Spec`s⟩⟩`,
  -- and the chip's own `is_real` binary gate.
  obtain ⟨ha, hb, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hrac_c⟩ := h_assumptions
  -- `op_b_val`/`op_c_val` are now the adapter's `op_b_memory`/`op_c_memory` register-read slots (no
  -- separate committed column), so their realisations are the `prev_value` leaves of the op_b/op_c groups
  -- of `h_input` (the adapter block).
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩ := h_input
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [hop_a_0, zero_mul]
  -- The `#v[eval op_*_memory.prev_value[i]]` literals the witnessVector feeds `populate` are the register
  -- read-back operand words.
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
  -- The witnessed `value` is `populate op_b op_c` (`h_env` per-limb), so its `AddOperation.Spec`
  -- obligation is exactly `spec_populate`. (`AddOperation` is now an `assertion`, so its completeness
  -- obligation is `Assumptions ∧ Spec`.)
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
