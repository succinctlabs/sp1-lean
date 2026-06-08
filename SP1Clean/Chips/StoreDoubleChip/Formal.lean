import SP1Clean.Chips.StoreDoubleChip.Defs

/-! # `SP1Clean.StoreDoubleChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.StoreDoubleChip

open Circuit
open Extracted (StoreDoubleColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values and the store targets a **valid, aligned, non-reserved** address: the
sum fits in 48 bits, is non-reserved (`≥ 2^16`), and is 8-byte aligned (`addr mod 8 = 0`, since SD's
offset bits are `0`). The address conditions are the "prover commits a valid SD address"
preconditions that `AddressOperation` needs (its inverse gate + offset range check). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 = 0

theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨ha, hb, hfit, h_ge, h_align⟩ := h_assumptions
  obtain ⟨_h_cpu, h_addr, h_mem, h_itype, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  have h_it := h_itype h_bin
  -- the `AddressOperation` Assumptions: operand `isU64`s + fits, the offset bits boolean (literal `0`),
  -- and the address-validity (non-reserved + 8-aligned, so the inverse gate / offset range check hold).
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_op_b_val, input_op_c_imm, 0, 0, 0⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, Or.inl rfl, Or.inl rfl, h_ge, by simp only [ZMod.val_zero]; omega⟩
  refine ⟨⟨h_addr h_addr_as, h_mem h_bin, h_it, h_bin⟩, ?_⟩
  -- the per-subcircuit channel-requirement tail (`channels = [] ∨ <sub>.Assumptions`).
  exact ⟨Or.inr h_bin, Or.inr h_addr_as, Or.inr h_bin, Or.inr h_bin⟩

/-- Prover-side row well-formedness (3-arg form): operand `isU64`s + address-fits bound + the reader
clock/timestamp `Spec`s + `is_real` binary. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 = 0 ∧
    (input.is_real = 0 ∨ input.is_real = 1) ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, input.is_real⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.adapter.op_a_memory.prev_value, input.is_real⟩ ∧
    Readers.ITypeReaderImmutable.Spec
      ⟨input.adapter, input.is_real, input.is_real, input.state.clk_high, clkLow input.state,
        input.state.pc, 39⟩

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨ha, hb, hfit, h_ge, h_align, hbin, h_cpu, h_mem, h_it⟩ := h_assumptions
  -- eval→value bridge for the nested `pc` vector the CPUState `Spec` references.
  have hmap_pc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc
      = input_state_pc := h_input.2.2.2.1.2.2.2
  have epc0 : Expression.eval env.toEnvironment input_var_state_pc[0]
      = input_state_pc[0] := by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have epc1 : Expression.eval env.toEnvironment input_var_state_pc[1]
      = input_state_pc[1] := by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have epc2 : Expression.eval env.toEnvironment input_var_state_pc[2]
      = input_state_pc[2] := by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_op_b_val, input_op_c_imm, 0, 0, 0⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, Or.inl rfl, Or.inl rfl, h_ge, by simp only [ZMod.val_zero]; omega⟩
  refine ⟨⟨?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · exact hbin
  · simp only [epc0, epc1, epc2]; exact h_cpu
  · exact hbin
  · exact h_mem
  · exact hbin
  · exact h_it
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- The `StoreDouble` chip row as a `GeneralFormalCircuit`; output is the extracted `StoreDoubleColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs StoreDoubleColumns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness }

end SP1Clean.StoreDoubleChip
