import SP1Clean.Native.Chips.StoreDoubleChip.Defs

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
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_align⟩ := h_assumptions
  obtain ⟨_h_cpu, h_addr, h_mem, h_itype, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  -- the `AddressOperation` Assumptions: operand `isU64`s + fits, the offset bits boolean (literal `0`),
  -- and the address-validity (non-reserved + 8-aligned, so the inverse gate / offset range check hold).
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, 0, 0⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, Or.inl rfl, Or.inl rfl, h_ge, by simp only [ZMod.val_zero]; omega⟩
  have h_it := h_itype ⟨h_bin, h_bin⟩
  -- (W11 memory flip) the pushed `new_value` for SD is the rs2 read (`op_a_memory.prev_value`), whose
  -- `isU64` is exposed by the immutable I-type adapter's `Spec` on a real row — no new assumption needed.
  have h_new : input_is_real = 1 → Word.isU64 input_adapter_op_a_memory_prev_value :=
    fun hr => (h_it.2.2.2.2.2 hr).1
  -- the per-subcircuit channel-requirement tail. `CPUState`'s requirement is now a bare
  -- `Assumptions` (`is_real` binary); the rest stay `channels = [] ∨ <sub>.Assumptions` disjuncts.
  exact ⟨⟨h_addr h_addr_as, h_mem ⟨h_bin, h_new⟩, h_it, h_bin⟩,
    h_bin, Or.inr h_addr_as, Or.inr ⟨h_bin, h_new⟩, Or.inr ⟨h_bin, h_bin⟩⟩

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
        input.state.pc, 39⟩ ∧
    (input.is_real = 1 → input.adapter.op_a.val < 32 ∧ input.state.pc[0].val < 2 ^ 16
      ∧ input.state.pc[1].val < 2 ^ 16 ∧ input.state.pc[2].val < 2 ^ 16)

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_align, hbin, h_cpu, h_mem, h_it, hdec⟩ := h_assumptions
  -- eval→value bridge for the nested `pc` vector the CPUState `Spec` references.
  have hmap_pc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc
      = input_state_pc := h_input.2.1.2.2.2
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, 0, 0⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, Or.inl rfl, Or.inl rfl, Or.inl rfl, h_ge, by simp only [ZMod.val_zero]; omega⟩
  refine ⟨⟨hbin, ?_⟩, h_addr_as, ⟨⟨hbin, fun hr => (h_it.2.2.2.2.2 hr).1⟩, h_mem⟩,
    ⟨⟨hbin, hbin⟩, h_it⟩, ?_⟩
  · simp only [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]; exact h_cpu
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- The `StoreDouble` chip row as a `GeneralFormalCircuit`; output is the extracted `StoreDoubleColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs StoreDoubleColumns :=
  { main, elaborated,
    channelsWithRequirements := [stateChannel.toRaw, memoryChannel.toRaw],
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    soundness := soundness, completeness := completeness,
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
        AddressOperation.circuit, AddressOperation.main,
        AddrAddOperation.circuit, AddrAddOperation.main,
        Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
        Readers.ITypeReaderImmutable.circuit, Readers.ITypeReaderImmutable.main,
        Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
        Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
        circuit_norm, FormalAssertion.toSubcircuit_interactions]
      simp [circuit_norm, Gadgets.Equality.main] }

end SP1Clean.StoreDoubleChip
