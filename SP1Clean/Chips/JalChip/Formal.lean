import SP1Clean.Chips.JalChip.Defs

/-! # `SP1Clean.JalChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance live in the
sibling `Defs` module, the Sail bridge (where present) in `Bridge`. This module holds the
prover/verifier `Assumptions`, any local `Spec`/helper lemmas, the soundness/completeness
proofs, and the bundled `circuit`. -/

namespace SP1Clean.JalChip

open Circuit
open Extracted (JalColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel binary_gate_req_vacuous)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Received-fact row well-formedness: the immediate word and the program counter are 64-bit (`pc` is a
received fact — the previous row's range-checked `next_pc` / the program ROM, never range-checked locally),
and the **padding convention** `is_real = 0 → op_a_0 = 0` (so the additive `is_real - op_a_0` gate of the
link `AddOperation` is binary on every row — on real rows from `op_a_0 ∈ {0,1}`, on padding from this).
`is_real`-binary is NOT assumed — soundness proves it from the in-circuit gate. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_b_imm ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  (input.is_real = 0 → input.adapter.op_a_0 = 0)

/-- The jump-target word the chip witnesses for `add_operation.value` (`pc + op_b_imm`, base-2^16). -/
def jumpTargetWord (input : Inputs (ZMod p)) : Word (ZMod p) :=
  AddOperation.populate
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] input.adapter.op_b_imm

/-- The link-address word the chip witnesses for `op_a_operation.value` (`pc + 4`, base-2^16). -/
def linkTargetWord (input : Inputs (ZMod p)) : Word (ZMod p) :=
  AddOperation.populate
    #v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] #v[4, 0, 0, 0]

/-- Honest prover-side row well-formedness. The immediate + program-counter words `isU64` (`pc` is a
received fact), `is_real` binary, the CPUState clock bounds (`next_pc` is irrelevant to `CPUState.Spec`,
so any value works) + op_a register-access timestamp bounds, the jump/link targets fitting in 48 bits
(`value[3] = 0`), and the `is_real`-gated next_pc 4-byte alignment (`jump_target[0] / 4 < 2^14`, SP1's
`Range` check). Completeness covers the `rd ≠ x0` rows (`op_a_0 = 0`) — the `op_a_0 = 1` (`jal x0`) case
would need a conditional `op_a_operation` witness (write `0`, not `pc + 4`); soundness handles both. This
mirrors `AddChip.ProverAssumptions`, which likewise fixes `op_a_0 = 0`. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p))
    (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.adapter.op_b_imm ∧
  Word.isU64 (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p)) ∧
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  input.adapter.op_a_0 = 0 ∧
  Readers.CPUState.Spec
    { cols := input.state, next_pc := input.state.pc, clk_inc := 8, is_real := input.is_real } ∧
  Readers.RegisterAccessCols.Spec
    ⟨input.adapter.op_a_memory, input.is_real,
      input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4⟩ ∧
  (jumpTargetWord input)[3] = 0 ∧
  (linkTargetWord input)[3] = 0 ∧
  (input.is_real = 1 → ((jumpTargetWord input)[0] * (4 : ZMod p)⁻¹).val < 2 ^ 14)

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_imm, h_pcU, h_pad⟩ := h_assumptions
  obtain ⟨h_cpu, h_add1, h_av3, h_add2, h_oav3, h_jt0, h_align, h_gate⟩ := h_holds
  -- `is_real` binary, from the chip's own gate.
  have h_bin : input_is_real = 0 ∨ input_is_real = 1 := bool_of_mul_pred h_gate
  -- the J-type reader sub-`Spec` (its `Assumptions` is exactly `is_real` binary).
  have h_jt : Readers.JTypeReader.Spec _ := h_jt0 h_bin
  have h_op_a_0 : input_adapter_op_a_0 = 0 ∨ input_adapter_op_a_0 = 1 := h_jt.2.1
  -- eval-of-pc rewrites: the circuit's `a` operand `#v[eval pc[i], 0]` is the concrete `pcWord`.
  have hpc : Vector.map (Expression.eval env) input_var_state_pc = input_state_pc := h_input.2.1.2.2.2
  have ep0 : Expression.eval env input_var_state_pc[0] = input_state_pc[0] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep1 : Expression.eval env input_var_state_pc[1] = input_state_pc[1] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep2 : Expression.eval env input_var_state_pc[2] = input_state_pc[2] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ha1eq : (#v[Expression.eval env input_var_state_pc[0], Expression.eval env input_var_state_pc[1],
      Expression.eval env input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by rw [ep0, ep1, ep2]
  have ha1U : Word.isU64 (#v[Expression.eval env input_var_state_pc[0],
      Expression.eval env input_var_state_pc[1], Expression.eval env input_var_state_pc[2], 0]
        : Word (ZMod p)) := ha1eq ▸ h_pcU
  -- `#v[4,0,0,0]` is a 64-bit word.
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := by
    have h4lt : (4 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by norm_cast,
        ZMod.val_natCast_of_lt h4lt, ZMod.val_zero] <;> norm_num
  -- the link gate `is_real - op_a_0` is binary on every row (real: `op_a_0` binary; padding: `op_a_0 = 0`).
  have h_gate2 : input_is_real + -input_adapter_op_a_0 = 0 ∨ input_is_real + -input_adapter_op_a_0 = 1 := by
    rcases h_bin with h | h
    · rw [h, h_pad h]; simp
    · rcases h_op_a_0 with h0 | h0 <;> rw [h, h0] <;> simp
  refine ⟨⟨h_jt, h_bin, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · -- jump identity: `is_real = 1 → add_operation.value = pc + op_b_imm`.
    intro hr1
    have := (h_add1 ⟨fun _ => ⟨ha1U, h_imm⟩, h_bin⟩ hr1).2
    rw [ha1eq] at this
    simpa only [pcWord] using this
  · -- link identity: `is_real = 1 → op_a_0 = 0 → op_a_operation.value = pc + 4`.
    intro hr1 hop_a_0
    have hg1 : input_is_real + -input_adapter_op_a_0 = 1 := by rw [hr1, hop_a_0]; simp
    have := (h_add2 ⟨fun _ => ⟨ha1U, h4U⟩, h_gate2⟩ hg1).2
    rw [ha1eq] at this
    simpa only [pcWord] using this
  -- the requirement tail (each sub's `channelsWithRequirements = [] ∨ Assumptions`, then the
  -- alignment padding guarantee). The new Clean shapes each sub's requirement as a disjunction —
  -- supply the `Assumptions` proof under `Or.inr`.
  · exact Or.inr h_bin
  · exact Or.inr ⟨fun _ => ⟨ha1U, h_imm⟩, h_bin⟩
  · exact Or.inr ⟨fun _ => ⟨ha1U, h4U⟩, h_gate2⟩
  · exact Or.inr h_bin
  · -- alignment byte pull padding requirement: vacuous for the binary gate (`toRawGated`).
    exact binary_gate_req_vacuous h_bin _

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_imm, h_pcU, h_bin, h_op_a_0, h_cpu, h_rac, h_jt3, h_lt3, h_align_pa⟩ := h_assumptions
  simp only [jumpTargetWord, linkTargetWord] at h_jt3 h_lt3 h_align_pa
  obtain ⟨he_av, he_oav⟩ := h_env
  -- eval-of-input rewrites.
  have hpc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc = input_state_pc :=
    h_input.2.1.2.2.2
  have hob : Vector.map (Expression.eval env.toEnvironment) input_var_adapter_op_b_imm
      = input_adapter_op_b_imm := h_input.2.2.2.2.2.1
  have ep0 : Expression.eval env.toEnvironment input_var_state_pc[0] = input_state_pc[0] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep1 : Expression.eval env.toEnvironment input_var_state_pc[1] = input_state_pc[1] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ep2 : Expression.eval env.toEnvironment input_var_state_pc[2] = input_state_pc[2] := by
    rw [← hpc]; simp only [Vector.getElem_map]
  have ha1eq : (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
      Expression.eval env.toEnvironment input_var_state_pc[1],
      Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p))
      = #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0] := by rw [ep0, ep1, ep2]
  have ha1U : Word.isU64 (#v[Expression.eval env.toEnvironment input_var_state_pc[0],
      Expression.eval env.toEnvironment input_var_state_pc[1],
      Expression.eval env.toEnvironment input_var_state_pc[2], 0] : Word (ZMod p)) := ha1eq ▸ h_pcU
  have h4U : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0] : Word (ZMod p)) := by
    have h4lt : (4 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ, show (4 : ZMod p) = ((4 : ℕ) : ZMod p) from by norm_cast,
        ZMod.val_natCast_of_lt h4lt, ZMod.val_zero] <;> norm_num
  have hb1eq : (#v[Expression.eval env.toEnvironment input_var_adapter_op_b_imm[0],
      Expression.eval env.toEnvironment input_var_adapter_op_b_imm[1],
      Expression.eval env.toEnvironment input_var_adapter_op_b_imm[2],
      Expression.eval env.toEnvironment input_var_adapter_op_b_imm[3]] : Word (ZMod p))
      = input_adapter_op_b_imm := by
    rw [← hob]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  -- the two witnessed add-result vectors are the corresponding `populate`s.
  have hval1 : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + i}) : Word (ZMod p))
      = AddOperation.populate #v[Expression.eval env.toEnvironment input_var_state_pc[0],
          Expression.eval env.toEnvironment input_var_state_pc[1],
          Expression.eval env.toEnvironment input_var_state_pc[2], 0] input_adapter_op_b_imm := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [he_av ⟨i, hi⟩, hb1eq]
  have hval2 : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 4 fun i => var {index := i₀ + 4 + i}) : Word (ZMod p))
      = AddOperation.populate #v[Expression.eval env.toEnvironment input_var_state_pc[0],
          Expression.eval env.toEnvironment input_var_state_pc[1],
          Expression.eval env.toEnvironment input_var_state_pc[2], 0] #v[4, 0, 0, 0] := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [he_oav ⟨i, hi⟩]
  -- per-limb witnessed values (for the two `value[3] = 0` asserts and the alignment pull).
  have hav0 : env.get i₀
      = (AddOperation.populate #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          input_adapter_op_b_imm)[0] := by
    have := congrArg (·[0]) hval1
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hav3 : env.get (i₀ + 3)
      = (AddOperation.populate #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          input_adapter_op_b_imm)[3] := by
    have := congrArg (·[3]) hval1
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  have hoav3 : env.get (i₀ + 4 + 3)
      = (AddOperation.populate #v[input_state_pc[0], input_state_pc[1], input_state_pc[2], 0]
          #v[4, 0, 0, 0])[3] := by
    have := congrArg (·[3]) hval2
    simpa only [Vector.getElem_map, Vector.getElem_mapRange, ha1eq, circuit_norm] using this
  -- the link gate `is_real - op_a_0` reduces to `is_real` (op_a_0 = 0 on the rd ≠ x0 rows completeness covers).
  have h_gate2 : input_is_real + -input_adapter_op_a_0 = 0 ∨ input_is_real + -input_adapter_op_a_0 = 1 := by
    rw [h_op_a_0]; simpa using h_bin
  have hz : ∀ w : ZMod p, input_adapter_op_a_0 * w = 0 := fun w => by rw [h_op_a_0, zero_mul]
  refine ⟨⟨h_bin, h_cpu⟩, ⟨⟨fun _ => ⟨ha1U, h_imm⟩, h_bin⟩, ?_⟩, ?_, ⟨⟨fun _ => ⟨ha1U, h4U⟩, h_gate2⟩, ?_⟩, ?_,
    ⟨h_bin, ⟨hz _, hz _, hz _, hz _⟩, Or.inl h_op_a_0, h_rac⟩, ?_, ?_⟩
  · -- AddOp1.Spec
    rw [hval1]; exact AddOperation.spec_populate ha1U h_imm input_is_real
  · -- add_operation.value[3] = 0
    rw [hav3]; exact h_jt3
  · -- AddOp2.Spec
    rw [hval2]; exact AddOperation.spec_populate ha1U h4U (input_is_real + -input_adapter_op_a_0)
  · -- op_a_operation.value[3] = 0
    rw [hoav3]; exact h_lt3
  · -- alignment byte pull (fires on real rows, `is_real = 1`).
    intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have c14 : ((14 : ℕ) : ZMod p) = (14 : ZMod p) := by norm_cast
    simp only [byteChannel, hav0]
    rw [← c14]
    exact (byteRowSpec_range _ h14p).mpr (h_align_pa hr1)
  · -- the `is_real` binary gate.
    rcases h_bin with h | h <;> rw [h] <;> simp

/-- The JAL chip row as a `GeneralFormalCircuit`: the data-dependent jump/link semantics, composing the
two witnessed `AddOperation` gadgets and the J-type reader; output is the extracted `JalColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs JalColumns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.JalChip
