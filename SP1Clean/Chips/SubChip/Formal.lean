import SP1Clean.Chips.SubChip.Defs

/-! # `SP1Clean.SubChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance live in the
sibling `Defs` module, the Sail bridge (where present) in `Bridge`. This module holds the
prover/verifier `Assumptions`, any local `Spec`/helper lemmas, the soundness/completeness
proofs, and the bundled `circuit`. -/

namespace SP1Clean.SubChip

open Circuit
open Extracted (SubCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values (true on real and zero-padded rows). `is_real`-binary is NOT assumed
here — soundness *proves* it from the in-circuit binary gate (it lives in the `Spec`); only completeness
needs it as a prover precondition (see `ProverAssumptions`). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- The prover-side row well-formedness, with the reader column blocks as *threaded inputs*
(mirrors `AddChip.ProverAssumptions`): operand `isU64`s, `is_real` binary, `op_a_0 = 0`, and the
`is_real`-gated CPUState clock bounds + per-operand timestamp bounds. -/
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
  -- `Spec`-builder def and re-normalizes its `wv* := resultWord[i]` fields (matching the reader's
  -- `h_adapter`) and drops the leading `True` (`true_and`).
  circuit_proof_start [RTypeChipSpec]
  obtain ⟨ha, hb⟩ := h_assumptions
  -- `h_holds` = the subcircuit results in emission order: CPUState reader, sub gadget, RTypeReader
  -- reader, binary gate. The chip `Spec` is each sub-circuit's own `Spec` (direct sub-calls) + the
  -- proven `is_real`-binary gate + the gated sub identity.
  -- `_` is the CPUState `assertion`'s clk-bounds `Spec` (unused — the chip `Spec`'s CPUState conjunct is
  -- `True`, simplified away by `circuit_proof_start`).
  obtain ⟨_, h_sub, h_adapter, h_gate⟩ := h_holds
  -- `is_real` binary (from the chip's gate) — the chip `Spec`'s binary conjunct AND what discharges the
  -- readers'/operation's / the CPUState assertion's `is_real ∈ {0,1}` `Assumptions`.
  have h_bin := bool_of_mul_pred h_gate
  -- `SubOperation` is now a `FormalAssertion` with `Assumptions = isU64 a ∧ isU64 b ∧ is_real∈{0,1}` and an
  -- `is_real`-gated semantic `Spec`; `h_sub` is `Assumptions → Spec`, so feed `⟨ha, hb, h_bin⟩` (inline so
  -- the witnessed `value` field is driven by unification) and apply the resulting `is_real = 1 → …` under the
  -- chip's `is_real = 1` hypothesis (`.2` = the sub identity).
  refine ⟨⟨h_adapter h_bin, h_bin, fun hr => (h_sub ⟨ha, hb, h_bin⟩ hr).2⟩, ?_⟩
  -- the channel-requirement tail: `CPUState`/`RTypeReader` carry the binary fact (`Or.inr h_bin`);
  -- `SubOperation` now emits the byte bus too, so its disjunct is `Or.inr ⟨ha, hb, h_bin⟩`.
  and_intros <;>
    first | exact Or.inl rfl | exact Or.inr h_bin | exact Or.inr ⟨ha, hb, h_bin⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  -- Threaded reader blocks ⇒ all composed obligations come from `ProverAssumptions` (mirrors `AddChip`):
  -- CPUState `⟨is_real binary, clk bounds⟩`, `SubOperation` `⟨isU64, isU64⟩`, RTypeReader `⟨is_real binary,
  -- ⟨zeroing (op_a_0 = 0), op_a_0 binary, three timestamp `Spec`s⟩⟩`, and the chip's `is_real` binary gate.
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
  -- The witnessed `value` is `populate op_b op_c` (`h_env` per-limb), so its `SubOperation.Spec`
  -- obligation is exactly `spec_populate`. (`SubOperation` is now an `assertion`, so its completeness
  -- obligation is `Assumptions ∧ Spec`.)
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + i}) : Word (ZMod p))
      = SubOperation.populate input_adapter_op_b_memory_prev_value input_adapter_op_c_memory_prev_value := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [h_env ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨ha, hb, hbin⟩, ?_⟩,
    ⟨hbin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c⟩, ?_⟩
  · rw [hval]; exact SubOperation.spec_populate ha hb input_is_real
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The Sub chip row as a `GeneralFormalCircuit`: semantic contract, composing the witnessed
gadget + the two readers; output is the extracted `SubCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs SubCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.SubChip
