import SP1Clean.Native.Chips.LoadWordChip.Defs
import Clean.Air.Circuit

/-! # `SP1Clean.LoadWordChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.LoadWordChip

open Circuit
open Extracted (LoadWordColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The register/immediate operands and RAM word are genuine 64-bit values. Address validity,
non-reservation, four-byte alignment, and the bit-two offset interpretation follow from
`AddressOperation` together with this chip's two literal zero offset bits. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    Word.isU64 input.memory_access.prev_value

set_option maxHeartbeats 4000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  -- `op_b_val`/`op_c_imm` are reducible adapter projections (`adapter.op_b_memory.prev_value` /
  -- `adapter.op_c_imm`), not committed columns — unfold them to the destructured adapter binders.
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, h_pv_isu64⟩ := h_assumptions
  obtain ⟨hpv0, hpv1, hpv2, hpv3⟩ := Word.lt_cases_of_isU64 h_pv_isu64
  obtain ⟨h_cpu, h_addr, h_mem, h_msb, h_itype, _h_regwrite, hsel0, hsel1, hsel2, hsel3, h_op_a_0,
    h_msbgate, h_lw_gate, h_lwu_gate, h_gate⟩ := h_holds
  -- the proven `is_real`-binary gate discharges the readers'/`MemoryAccess`'s `Assumptions`.
  have h_bin := bool_of_mul_pred h_gate
  have h_lw_bin := bool_of_mul_pred h_lw_gate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's new `MemoryMsg.ClkBound` guarantee. Three distinct offsets: `MemoryAccess`'s RAM effect
  -- slot `clk_low + 1`, `ITypeReader`'s op_b read-back `clk_low + 3`, and `RegisterWrite`'s op_a write
  -- `clk_low + 4`. The offset is left to unification, so this never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  -- eval→value bridges for the nested vector fields the sub-`Spec`s / selection gates reference.
  have hmap_sw : Vector.map (Expression.eval env) input_var_selected_word = input_selected_word :=
    h_input.2.2.2.2.2.2.1
  have hmap_pv : Vector.map (Expression.eval env) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.2.1.1
  have esw : ∀ i (hi : i < 2), Expression.eval env input_var_selected_word[i]
      = input_selected_word[i] := fun i hi => by rw [← hmap_sw]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  simp only [esw 0 (by omega), esw 1 (by omega), epv 0 (by omega), epv 1 (by omega),
    epv 2 (by omega), epv 3 (by omega)] at hsel0 hsel1 hsel2 hsel3
  rw [esw 1 (by omega)] at h_msb
  have h_it := h_itype ⟨h_bin, h_bin, h_clk⟩
  simp only [esw 0 (by omega), esw 1 (by omega)] at h_it
  have h_addr_as : AddressOperation.SoundnessAssumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, 0,
        input_offset_bit, input_is_lw + input_is_lwu⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, h_bin⟩
  simp only [AddressOperation.circuit] at h_addr
  have h_addr_spec := h_addr h_addr_as
  simp only [circuit_norm] at h_addr_spec
  have h_off_bin : input_offset_bit = 0 ∨ input_offset_bit = 1 := by
    exact h_addr_spec.2.2.1
  -- `selected_word[1] < 2^16` on a real `is_lw` row: it equals `prev_value[1]` (offset 0) or
  -- `prev_value[3]` (offset 1), both genuine 16-bit memory limbs.
  have h_sel1_lt : input_selected_word[1].val < 2 ^ 16 := by
    rcases h_off_bin with h0 | h1
    · -- offset 0: gate B forces `selected_word[1] = prev_value[1]`.
      have hne : input_offset_bit - 1 ≠ 0 := by rw [h0, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
      have heq := sub_eq_zero.mp ((mul_eq_zero.mp hsel1).resolve_right hne)
      rw [heq]; exact hpv1
    · -- offset 1: gate D forces `selected_word[1] = prev_value[3]`.
      have hne : input_offset_bit ≠ 0 := by rw [h1]; exact one_ne_zero
      have heq := sub_eq_zero.mp ((mul_eq_zero.mp hsel3).resolve_right hne)
      rw [heq]; exact hpv3
  -- eval-form variant of the 16-bit bound, for the `U16MSBOperation` channel-requirement tail.
  have h_sel1_lt_eval : (Expression.eval env input_var_selected_word[1]).val < 2 ^ 16 := by
    rw [esw 1 (by omega)]; exact h_sel1_lt
  -- `selected_word[0] < 2^16` (value + eval form): it equals `prev_value[0]` (offset 0) or `prev_value[2]`
  -- (offset 1), both genuine 16-bit memory limbs — needed for the `RegisterWrite` loaded-word `isU64`.
  have h_sel0_lt : input_selected_word[0].val < 2 ^ 16 := by
    rcases h_off_bin with h0 | h1
    · have hne : input_offset_bit - 1 ≠ 0 := by rw [h0, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
      rw [sub_eq_zero.mp ((mul_eq_zero.mp hsel0).resolve_right hne)]; exact hpv0
    · have hne : input_offset_bit ≠ 0 := by rw [h1]; exact one_ne_zero
      rw [sub_eq_zero.mp ((mul_eq_zero.mp hsel2).resolve_right hne)]; exact hpv2
  have h_sel0_lt_eval : (Expression.eval env input_var_selected_word[0]).val < 2 ^ 16 := by
    rw [esw 0 (by omega)]; exact h_sel0_lt
  have h_msb_as : U16MSBOperation.circuit.Assumptions
      (⟨input_selected_word[1], ⟨input_msb⟩, input_is_lw⟩ : U16MSBOperation.Inputs (ZMod p)) :=
    ⟨fun _ => h_sel1_lt, h_lw_bin⟩
  have h_msb_spec := h_msb h_msb_as
  -- `msb` is binary (from `U16MSBOperation.Spec`), so the sign-fill limb `65535·msb ∈ {0, 65535} < 2^16`.
  have h_msb_val : (65535 * input_msb : ZMod p).val < 2 ^ 16 := by
    have hp65535 : (65535 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h_msb_bin : input_msb = 0 ∨ input_msb = 1 := h_msb_spec.1
    rcases h_msb_bin with h | h
    · rw [h, mul_zero, ZMod.val_zero]; norm_num
    · rw [h, mul_one, show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) by norm_cast,
        ZMod.val_natCast_of_lt hp65535]; norm_num
  -- the loaded word `#v[sw[0], sw[1], 65535·msb, 65535·msb]` (op_a write value) is `isU64` — from the
  -- selected memory limbs (`h_sel*_lt_eval`) + the binary `msb` fill (`h_msb_val`).
  have h_load_isu64 : Word.isU64
      (#v[Expression.eval env input_var_selected_word[0], Expression.eval env input_var_selected_word[1],
          65535 * input_msb, 65535 * input_msb] : Word (ZMod p)) :=
    Word.isU64_of_cases h_sel0_lt_eval h_sel1_lt_eval h_msb_val h_msb_val
  refine ⟨⟨h_addr_spec,
    h_mem ⟨h_bin, fun _ => h_pv_isu64, h_clk⟩, h_msb_spec, h_it,
    ⟨hsel0, hsel1, hsel2, hsel3⟩, h_op_a_0,
    h_msbgate, h_lw_bin, bool_of_mul_pred h_lwu_gate, h_bin⟩, ?_⟩
  -- The per-subcircuit channel-requirement tail: `MemoryAccess`'s read push owes `isU64 prev_value`,
  -- and `RegisterWrite`'s op_a write push owes `isU64 <loaded word>`. The MSB gadget exposes its empty
  -- requirement list canonically, so its local semantic assumption does not leak into this tail.
  -- G1: each also gained a `MemoryMsg.ClkBound` conjunct at its own push offset — `MemoryAccess` at the
  -- RAM `+1` slot, `ITypeReader` at op_b's `+3`, `RegisterWrite` at op_a's `+4`.
  refine ⟨Or.inr h_addr_as,
    Or.inr ⟨h_bin, fun _ => h_pv_isu64, h_clk⟩,
    Or.inr ⟨h_bin, h_bin, h_clk⟩,
    Or.inr ⟨h_bin, fun _ => h_load_isu64, h_clk.at_four⟩⟩

/-- Prover-side row well-formedness (3-arg form): operand `isU64`s + address-fits/alignment + the
`offset_bit` decomposition + the selected-limb 16-bit bounds + the reader/gadget `Spec`s + the selector
binaries + `op_a_0 = 0` + the offset-selection equations + the `(is_lw-1)·msb` zero-extension gate. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 4 = 0 ∧
    4 * input.offset_bit.val = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    Word.isU64 input.memory_access.prev_value ∧
    (input.is_lw = 0 ∨ input.is_lw = 1) ∧ (input.is_lwu = 0 ∨ input.is_lwu = 1) ∧
    (isReal input = 0 ∨ isReal input = 1) ∧
    input.adapter.op_a_0 = 0 ∧
    ((input.selected_word[0] - input.memory_access.prev_value[0]) * (input.offset_bit - 1) = 0 ∧
      (input.selected_word[1] - input.memory_access.prev_value[1]) * (input.offset_bit - 1) = 0 ∧
      (input.selected_word[0] - input.memory_access.prev_value[2]) * input.offset_bit = 0 ∧
      (input.selected_word[1] - input.memory_access.prev_value[3]) * input.offset_bit = 0) ∧
    input.msb * (input.is_lw - 1) = 0 ∧
    U16MSBOperation.Spec ⟨input.selected_word[1], ⟨input.msb⟩, input.is_lw⟩ ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, isReal input⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.memory_access.prev_value, isReal input⟩ ∧
    Readers.ITypeReader.Spec
      ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
        input.state.pc, input.is_lw * 31 + input.is_lwu * 34,
        input.selected_word[0], input.selected_word[1], 65535 * input.msb, 65535 * input.msb⟩

set_option maxHeartbeats 4000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_align, h_off, h_pv_isu64, h_lw_bin, h_lwu_bin, hbin, h_op_a_0,
    ⟨hsel0, hsel1, hsel2, hsel3⟩, h_msbgate, h_msb_spec, h_cpu, h_mem, h_it⟩ :=
    h_assumptions
  obtain ⟨hpv0, hpv1, hpv2, hpv3⟩ := Word.lt_cases_of_isU64 h_pv_isu64
  simp only [isReal] at hbin
  -- G1: the *push* side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  -- eval→value bridges for the nested vectors the reader/gadget `Spec`s reference.
  have hmap_pc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc
      = input_state_pc := h_input.2.2.1.2.2.2
  have hmap_sw : Vector.map (Expression.eval env.toEnvironment) input_var_selected_word
      = input_selected_word := h_input.2.2.2.2.2.2.1
  have hmap_pv : Vector.map (Expression.eval env.toEnvironment) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.2.1.1
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have esw : ∀ i (hi : i < 2), Expression.eval env.toEnvironment input_var_selected_word[i]
      = input_selected_word[i] := fun i hi => by rw [← hmap_sw]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  -- the `AddressOperation` subcircuit `Assumptions`.
  have h_off' : (0 : ZMod p).val + 2 * (0 : ZMod p).val + 4 * input_offset_bit.val
      = (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 := by
    simp only [ZMod.val_zero]; omega
  have h_off_bin : input_offset_bit = 0 ∨ input_offset_bit = 1 := by
    have h8 : (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 < 8 :=
      Nat.mod_lt _ (by norm_num)
    have hv : input_offset_bit.val = 0 ∨ input_offset_bit.val = 1 := by omega
    rcases hv with h | h
    · left; exact (ZMod.val_eq_zero _).mp h
    · right; have := ZMod.natCast_zmod_val input_offset_bit; rw [h, Nat.cast_one] at this; exact this.symm
  have h_addr_as : AddressOperation.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, 0,
        input_offset_bit, input_is_lw + input_is_lwu⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hbin, hfit, Or.inl rfl, Or.inl rfl, h_off_bin, h_ge, h_off'⟩
  -- `selected_word[1] < 2^16` (value + eval form), for the `U16MSBOperation` assertion `Assumptions`.
  have h_sel1_lt : input_selected_word[1].val < 2 ^ 16 := by
    rcases h_off_bin with h0 | h1
    · have hne : input_offset_bit - 1 ≠ 0 := by rw [h0, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
      rw [sub_eq_zero.mp ((mul_eq_zero.mp hsel1).resolve_right hne)]; exact hpv1
    · have hne : input_offset_bit ≠ 0 := by rw [h1]; exact one_ne_zero
      rw [sub_eq_zero.mp ((mul_eq_zero.mp hsel3).resolve_right hne)]; exact hpv3
  have h_sel1_lt_eval : (Expression.eval env.toEnvironment input_var_selected_word[1]).val < 2 ^ 16 := by
    rw [esw 1 (by omega)]; exact h_sel1_lt
  -- `selected_word[0] < 2^16` (value + eval form), for the `RegisterWrite` loaded-word `isU64`.
  have h_sel0_lt : input_selected_word[0].val < 2 ^ 16 := by
    rcases h_off_bin with h0 | h1
    · have hne : input_offset_bit - 1 ≠ 0 := by rw [h0, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
      rw [sub_eq_zero.mp ((mul_eq_zero.mp hsel0).resolve_right hne)]; exact hpv0
    · have hne : input_offset_bit ≠ 0 := by rw [h1]; exact one_ne_zero
      rw [sub_eq_zero.mp ((mul_eq_zero.mp hsel2).resolve_right hne)]; exact hpv2
  have h_sel0_lt_eval : (Expression.eval env.toEnvironment input_var_selected_word[0]).val < 2 ^ 16 := by
    rw [esw 0 (by omega)]; exact h_sel0_lt
  -- `msb` binary (from the `U16MSBOperation.Spec` prover assumption) → `65535·msb ∈ {0, 65535} < 2^16`.
  have h_msb_val : (65535 * input_msb : ZMod p).val < 2 ^ 16 := by
    have hp65535 : (65535 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h_msb_bin : input_msb = 0 ∨ input_msb = 1 := h_msb_spec.1
    rcases h_msb_bin with h | h
    · rw [h, mul_zero, ZMod.val_zero]; norm_num
    · rw [h, mul_one, show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) by norm_cast,
        ZMod.val_natCast_of_lt hp65535]; norm_num
  have h_load_isu64 : Word.isU64
      (#v[Expression.eval env.toEnvironment input_var_selected_word[0],
          Expression.eval env.toEnvironment input_var_selected_word[1],
          65535 * input_msb, 65535 * input_msb] : Word (ZMod p)) :=
    Word.isU64_of_cases h_sel0_lt_eval h_sel1_lt_eval h_msb_val h_msb_val
  refine ⟨⟨?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ⟨⟨fun _ => h_sel1_lt_eval, h_lw_bin⟩, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, h_op_a_0, ?_, ?_, ?_, ?_⟩
  · exact hbin
  · simp only [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]; exact h_cpu
  · exact ⟨hbin, fun _ => h_pv_isu64, h_clk⟩
  · exact h_mem
  · simp only [esw 1 (by omega)]; exact h_msb_spec
  · exact ⟨hbin, hbin, h_clk⟩
  · simp only [esw 0 (by omega), esw 1 (by omega)]; exact h_it
  · exact ⟨hbin, fun _ => h_load_isu64, h_clk.at_four⟩
  · trivial
  · simp only [esw 0 (by omega), epv 0 (by omega)]; exact hsel0
  · simp only [esw 1 (by omega), epv 1 (by omega)]; exact hsel1
  · simp only [esw 0 (by omega), epv 2 (by omega)]; exact hsel2
  · simp only [esw 1 (by omega), epv 3 (by omega)]; exact hsel3
  · exact h_msbgate
  · rcases h_lw_bin with h | h <;> rw [h] <;> simp
  · rcases h_lwu_bin with h | h <;> rw [h] <;> simp
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- LoadWord's exact Memory-channel interaction list — the RAM-access family shape: the composed
`MemoryAccess` RAM pull/push pair at the computed 48-bit address (`var ⟨offset..offset+2⟩` are the
`AddressOperation` sub-circuit's witnessed address limbs), then the I-type register entries (op_a
read-prior pull, op_b pull + read-back push) and `RegisterWrite`'s op_a write push carrying the
sign/zero-extended word `#v[selected_word[0], selected_word[1], 65535·msb, 65535·msb]`.  Keeping
this list beside `circuit` makes Clean's exposure interface the single structural source consumed by
both faithfulness and semantic grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨input.memory_access.access_timestamp.prev_high,
       input.memory_access.access_timestamp.prev_low,
       var { index := offset } - (4 : Expression (ZMod p)) * input.offset_bit -
         (2 : Expression (ZMod p)) * 0 - 0,
       var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩,
    memoryChannel.pushedIf (input.is_lw + input.is_lwu)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 1,
       var { index := offset } - (4 : Expression (ZMod p)) * input.offset_bit -
         (2 : Expression (ZMod p)) * 0 - 0,
       var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩,
    memoryChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf (input.is_lw + input.is_lwu)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf (input.is_lw + input.is_lwu)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0,
       #v[input.selected_word[0], input.selected_word[1], 65535 * input.msb,
          65535 * input.msb]⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact RAM-access pull occupies its declared slot in LoadWord's exposed Memory list. -/
theorem ramPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨input.memory_access.access_timestamp.prev_high,
       input.memory_access.access_timestamp.prev_low,
       var { index := offset } - (4 : Expression (ZMod p)) * input.offset_bit -
         (2 : Expression (ZMod p)) * 0 - 0,
       var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in LoadWord's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (input.is_lw + input.is_lwu)
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The `LoadWord` chip row as a `GeneralFormalCircuit`; output is the extracted `LoadWordColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs LoadWordColumns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    soundness := soundness, completeness := completeness,
    -- A2: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8); the
    -- enabled flag is the **derived** selector sum `is_lw + is_lwu` (SP1's `is_real`).
    exposedChannels := fun input offset =>
      expose stateChannel
        [ stateChannel.pulledIf (input.is_lw + input.is_lwu)
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf (input.is_lw + input.is_lwu)
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ] ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `ITypeReader`, gate
      -- `is_trusted = is_lw + is_lwu`, opcode `LW·31 + LWU·34`), consumed by
      -- `Soundness/TypedProgram.lean`.
      expose programChannel
        [ programChannel.pulledIf (input.is_lw + input.is_lwu)
            ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
             input.is_lw * 31 + input.is_lwu * 34, input.adapter.op_a,
             #v[input.adapter.op_b, 0, 0, 0], input.adapter.op_c_imm,
             input.adapter.op_a_0, 0, 1⟩ ],
    exposedChannels_eq := by
      intro input offset
      have h_byte := Channels.byteChannel_toRaw_ne_stateChannel (p := p)
      have h_program := Channels.programChannel_toRaw_ne_stateChannel (p := p)
      have h_memory := Channels.memoryChannel_toRaw_ne_stateChannel (p := p)
      unfold Operations.ExposedChannelsLawful
      intro exposed exposedMem
      simp only [expose, List.mem_append, List.mem_singleton] at exposedMem
      rcases exposedMem with (rfl | rfl) | rfl
      all_goals
        simp only [main, Readers.CPUState.circuit, Readers.CPUState.main,
          AddressOperation.circuit, AddressOperation.main,
          AddrAddOperation.circuit, AddrAddOperation.main,
          Readers.MemoryAccess.circuit, Readers.MemoryAccess.main,
          U16MSBOperation.circuit, U16MSBOperation.main,
          Readers.ITypeReader.circuit, Readers.ITypeReader.main,
          Readers.RegisterWrite.circuit, Readers.RegisterWrite.main,
          Readers.RegisterAccessCols.circuit, Readers.RegisterAccessCols.main,
          Readers.RegisterAccessTimestamp.circuit, Readers.RegisterAccessTimestamp.main,
          circuit_norm, FormalAssertion.toSubcircuit_interactions,
          GeneralFormalCircuit.toSubcircuit_interactions]
      · simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
          h_byte, h_program, h_memory, decide_false, decide_true, Bool.false_eq_true,
          if_true, List.nil_append]
      · simp [circuit_norm, Gadgets.Equality.main, exposedMemoryInteractions]
      · simp only [circuit_norm, Gadgets.Equality.main, List.filter_cons, List.filter_nil,
          Channels.byteChannel_eq_programChannel_false,
          Channels.stateChannel_eq_programChannel_false,
          Channels.memoryChannel_eq_programChannel_false,
          decide_false, decide_true, Bool.false_eq_true, if_true, List.nil_append] }

/-- Folded circuit projections used by the whole-chip row codec. -/
@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 4 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 4 := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq]

/-- The completed LoadWord circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.LoadWordChip
