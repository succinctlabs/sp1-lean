import SP1Clean.Chips.SubwChip.Defs

/-! # `SP1Clean.SubwChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance live in the
sibling `Defs` module, the Sail bridge (where present) in `Bridge`. This module holds the
prover/verifier `Assumptions`, any local `Spec`/helper lemmas, the soundness/completeness
proofs, and the bundled `circuit`. -/

namespace SP1Clean.SubwChip

open Circuit
open Extracted (SubwCols)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values (true on real and zero-padded rows). `is_real`-binary is proven by
soundness from the in-circuit gate; only completeness needs it as a precondition. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_val

/-- Prover-side row well-formedness (mirrors `SubChip.ProverAssumptions`): operand `isU64`s, `is_real`
binary, `op_a_0 = 0`, and the `is_real`-gated CPUState clock bounds + per-operand timestamp bounds. -/
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

set_option maxRecDepth 4000 in
set_option maxHeartbeats 2000000 in
/-- **W-instruction soundness — the two `circuit_proof_start` landmines.** Composing the W-gadget threads
the sign-extended `op_a_write_value` `[v0, v1, msb·65535, msb·65535]` into the register reader, whose
`wv2`/`wv3` are the **nested** projection `(SubwOperation output).msb.msb * 65535` (Add/Sub use the flat
`(output).value[i]`). Two consequences vs Add/Sub, both avoided here:
1. **Don't `obtain ⟨…⟩ := h_holds`** — `rcases` builds a case-motive over `h_holds`'s whole type, which
   carries ~20 copies of that nested `.msb.msb` term (replicated across the reader's bus emits), and the
   motive forces the nested `ProvableStruct` `whnf` ~20× → blows past 16M heartbeats. Use `.2.1`/`.2.2.1`/
   `.2.2.2` (`And.right`/`And.left` projections — no motive, no deep `whnf`).
2. **Don't pass `[RTypeChipSpec]`** to `circuit_proof_start` — that unfolds the builder and lets
   `circuit_norm` churn on `RV64.subw` (`signExtend`/`setWidth`, unlike defeq-trivial `RV64.add`). Keeping
   it opaque hides `RV64.subw`; the arith goes through `rv64_subw_eq` by hand.
`maxHeartbeats 2000000` covers `circuit_proof_start`'s own (finite) normalization; `maxRecDepth` past 512
for the `#v[…]` resultWord. -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  -- **Use `.1`/`.2` projections everywhere — NEVER `obtain`/`rcases`/`cases` here.** Any of those builds a
  -- case-motive `fun _ => <goal>`, and the goal carries the unreduced nested `(output).msb.msb * 65535`
  -- projections (the W sign-fill, in the `RTypeChipSpec` resultWord + the reader-`Assumptions` tail);
  -- abstracting the goal forces that doubly-nested `ProvableStruct` `whnf` and blows past 16M heartbeats.
  -- `And.left`/`And.right` are plain function applications — no motive, no deep `whnf`. (Add/Sub's flat
  -- `.value[i]` is cheap, so their `obtain` is fine; only the W-gadget's nested `.msb` triggers this.)
  have h_subw := h_holds.2.1
  have h_adapter := h_holds.2.2.1
  have h_bin := bool_of_mul_pred h_holds.2.2.2
  have ha := h_assumptions.1
  have hb := h_assumptions.2
  -- `SubwOperation` is now a `FormalAssertion`; feed `⟨ha, hb, h_bin⟩` (explicit struct, since the witnessed
  -- `value`/`msb` are driven by the assertion input). Keep `.1`/`.2` projections — see the docstring.
  have h_as : SubwOperation.circuit.Assumptions
      { a := input_adapter_op_b_memory_prev_value, b := input_adapter_op_c_memory_prev_value,
        cols := ⟨Vector.map (Expression.eval env) (Vector.mapRange 2 fun i => var { index := i₀ + i }),
          ⟨env.get (i₀ + 2)⟩⟩, is_real := input_is_real } := ⟨ha, hb, h_bin⟩
  -- `RTypeChipSpec` is opaque (NOT passed to `circuit_proof_start`, so `RV64.subw` never reaches
  -- `circuit_norm`); the anonymous constructor whnf's it to `True ∧ reader ∧ binary ∧ arith`.
  refine ⟨⟨trivial, ?_, h_bin, fun hr => ?_⟩, ?_⟩
  · -- reader conjunct: `wv* := resultWord[i]` reduce to the four limbs `main` passed (`Vector.getElem_map`).
    simpa only [Vector.getElem_map] using h_adapter h_bin
  · -- the `is_real`-gated W arith: bridge the gadget's `signExtend` equation to `RV64.subw`.
    refine trans ?_ (rv64_subw_eq _ _).symm
    simpa only [SubwOperation.resultWord, Vector.getElem_map] using
      ((h_subw h_as).2 hr).2
  · -- channel-requirement tail (the readers carry the binary fact; `SubwOperation` now emits the byte bus).
    and_intros <;> first | exact Or.inl rfl | exact Or.inr h_bin | exact Or.inr h_as

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hbin, hop_a_0, h_cpu, hrac_a, hrac_b, hrac_c⟩ := h_assumptions
  -- `op_b_val`/`op_c_val` are now the adapter's `op_b_memory`/`op_c_memory` register-read slots; their
  -- realisations are the `prev_value` leaves of the op_b/op_c groups of `h_input` (the adapter block).
  obtain ⟨-, -, -, -, -, -, ⟨hob, -, -⟩, -, hoc, -, -⟩ := h_input
  obtain ⟨h_env_val, h_env_msb⟩ := h_env
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
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 2 fun i => var { index := i₀ + i }) : Vector (ZMod p) 2)
      = SubwOperation.subwValueWitness input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [h_env_val ⟨i, hi⟩]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  have hmsbeq : env.get (i₀ + 2)
      = SubwOperation.subwMsbWitness input_adapter_op_b_memory_prev_value
          input_adapter_op_c_memory_prev_value := by
    rw [h_env_msb]
    simp only [Inputs.op_b_val, Inputs.op_c_val]
    rw [hbeq, hceq]
  refine ⟨⟨hbin, h_cpu⟩, ⟨⟨ha, hb, hbin⟩, ?_⟩,
    ⟨hbin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl hop_a_0, hrac_a, hrac_b, hrac_c⟩, ?_⟩
  · rw [hval, hmsbeq]; exact SubwOperation.spec_populate ha hb input_is_real
  rcases hbin with h | h <;> rw [h] <;> simp

/-- The SUBW chip row as a `GeneralFormalCircuit`: semantic contract, composing the witnessed gadget +
the two readers; output is the extracted `SubwCols` column struct. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs SubwCols :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.SubwChip
