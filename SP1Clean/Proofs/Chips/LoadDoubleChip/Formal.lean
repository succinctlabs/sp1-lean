import SP1Clean.Native.Chips.LoadDoubleChip.Defs

/-! # `SP1Clean.LoadDoubleChip` — contract: `Assumptions` / soundness / completeness / `circuit`

Split from the monolithic chip file: `main` + the `ElaboratedCircuit` instance live in the
sibling `Defs` module, the Sail bridge (where present) in `Bridge`. This module holds the
prover/verifier `Assumptions`, any local `Spec`/helper lemmas, the soundness/completeness
proofs, and the bundled `circuit`. -/

namespace SP1Clean.LoadDoubleChip

open Circuit
open Extracted (LoadDoubleColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values and the load targets a **valid, aligned, non-reserved** address: the
sum fits in 48 bits, is non-reserved (`≥ 2^16`), and is 8-byte aligned (`addr mod 8 = 0`, since LD's
offset bits are `0`). The address conditions are the "prover commits a valid LD address"
preconditions that `AddressOperation` needs (its inverse gate + offset range check). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 = 0

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_align⟩ := h_assumptions
  obtain ⟨_h_cpu, h_addr, h_mem, h_itype, h_op_a_0, h_gate⟩ := h_holds
  -- the proven `is_real`-binary gate discharges the readers'/`MemoryAccess`'s `Assumptions`; the
  -- `AddressOperation` gadget takes the operand `isU64`s + the address-fits bound.
  have h_bin := bool_of_mul_pred h_gate
  -- bridge the loaded-word `wv*` (the `ITypeReader` write value) from `eval` to value form: it is the
  -- nested `memory_access.prev_value` (which `ITypeReader.Spec`'s zeroing gates reference).
  have hmap : Vector.map (Expression.eval env) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.1
  have ev : ∀ i (hi : i < 4), Expression.eval env input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap]; simp only [Vector.getElem_map]
  have h_it := h_itype h_bin
  rw [ev 0 (by omega), ev 1 (by omega), ev 2 (by omega), ev 3 (by omega)] at h_it
  -- the `AddressOperation` Assumptions: operand `isU64`s + fits, the offset bits boolean (literal `0`),
  -- and the address-validity (non-reserved + 8-aligned, so the inverse gate / offset range check hold).
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, 0, 0⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, Or.inl rfl, Or.inl rfl, h_ge, by simp only [ZMod.val_zero]; omega⟩
  -- the per-subcircuit channel-requirement tail (`channels = [] ∨ <sub>.Assumptions`).
  exact ⟨⟨h_addr h_addr_as, h_mem h_bin, h_it, h_op_a_0, h_bin⟩,
    h_bin, Or.inr h_addr_as, Or.inr h_bin, Or.inr h_bin⟩

/-- Prover-side row well-formedness: operand `isU64`s + address-fits bound plus the `is_real` binary selector. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 = 0 ∧
    (input.is_real = 0 ∨ input.is_real = 1) ∧
    input.adapter.op_a_0 = 0 ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.memory_access.prev_value, input.is_real⟩ ∧
    Readers.ITypeReader.Spec
      ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high, clkLow input.state,
        input.state.pc, 35,
        input.memory_access.prev_value[0], input.memory_access.prev_value[1],
        input.memory_access.prev_value[2], input.memory_access.prev_value[3]⟩

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_align, hbin, h_op_a_0, h_cpu, h_mem, h_it⟩ := h_assumptions
  -- eval→value bridges for the nested vector fields the reader `Spec`s reference (`pc`, the loaded word).
  have hmap_pv : Vector.map (Expression.eval env.toEnvironment) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.1
  have hmap_pc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc
      = input_state_pc := h_input.2.1.2.2.2
  have epv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, 0, 0⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, Or.inl rfl, Or.inl rfl, h_ge, by simp only [ZMod.val_zero]; omega⟩
  refine ⟨⟨hbin, ?_⟩, h_addr_as, ⟨hbin, h_mem⟩, ⟨hbin, ?_⟩, h_op_a_0, ?_⟩
  · simp only [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]; exact h_cpu
  · simp only [epv 0 (by omega), epv 1 (by omega), epv 2 (by omega), epv 3 (by omega)]; exact h_it
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- The `LoadDouble` chip row as a `GeneralFormalCircuit`; output is the extracted `LoadDoubleColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs LoadDoubleColumns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    channelsWithRequirements :=
      [byteChannel.toRaw, stateChannel.toRaw, memoryChannel.toRaw, programChannel.toRaw],
    soundness := soundness, completeness := completeness }

end SP1Clean.LoadDoubleChip
