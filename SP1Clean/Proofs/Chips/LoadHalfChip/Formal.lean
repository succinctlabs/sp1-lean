import SP1Clean.Native.Chips.LoadHalfChip.Defs
import Clean.Air.Circuit

/-! # `SP1Clean.LoadHalfChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.LoadHalfChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The register/immediate operands and RAM word are genuine 64-bit values. Address validity,
non-reservation, two-byte alignment, and offset decomposition follow from `AddressOperation`
together with this chip's literal zero low-offset bit. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    Word.isU64 input.memory_access.prev_value

omit [Fact (2 ^ 17 < p)] in
/-- The offset-selected half is 16-bit: the four corner gates pin it to one of the four 16-bit
memory limbs. Shared verbatim by soundness and completeness. -/
private lemma sel_lt_of_corners {s b0 b1 v0 v1 v2 v3 : ZMod p}
    (hb0 : b0 = 0 ∨ b0 = 1) (hb1 : b1 = 0 ∨ b1 = 1)
    (h0 : (s - v0) * (b0 - 1) * (b1 - 1) = 0) (h1 : (s - v1) * b0 * (b1 - 1) = 0)
    (h2 : (s - v2) * (b0 - 1) * b1 = 0) (h3 : (s - v3) * b0 * b1 = 0)
    (hv0 : v0.val < 2 ^ 16) (hv1 : v1.val < 2 ^ 16) (hv2 : v2.val < 2 ^ 16) (hv3 : v3.val < 2 ^ 16) :
    s.val < 2 ^ 16 := by
  have hz : ∀ x : ZMod p, x = 0 → x - 1 ≠ 0 :=
    fun x hx => by rw [hx, zero_sub]; exact neg_ne_zero.mpr one_ne_zero
  have hn : ∀ x : ZMod p, x = 1 → x ≠ 0 := fun x hx => by rw [hx]; exact one_ne_zero
  rcases hb0 with e0 | e0 <;> rcases hb1 with e1 | e1
  · rw [sub_eq_zero.mp
      ((mul_eq_zero.mp ((mul_eq_zero.mp h0).resolve_right (hz _ e1))).resolve_right (hz _ e0))]
    exact hv0
  · rw [sub_eq_zero.mp
      ((mul_eq_zero.mp ((mul_eq_zero.mp h2).resolve_right (hn _ e1))).resolve_right (hz _ e0))]
    exact hv2
  · rw [sub_eq_zero.mp
      ((mul_eq_zero.mp ((mul_eq_zero.mp h1).resolve_right (hz _ e1))).resolve_right (hn _ e0))]
    exact hv1
  · rw [sub_eq_zero.mp
      ((mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right (hn _ e1))).resolve_right (hn _ e0))]
    exact hv3

-- Both proofs read `h_assumptions` / `h_holds` through `.1`/`.2` projections instead of a wide
-- `obtain`: an `And.casesOn` motive re-abstracts the (very large) goal once per component, which is
-- Clean's `doc/performance-problems.md` pattern 7. Neither proof carries an elaboration budget any
-- more (they were stamped at 2000000 / 1500000, and 16M before that).
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  have ha := h_assumptions.1
  have hb := h_assumptions.2.1
  have h_pv_isu64 := h_assumptions.2.2
  have hpv := Word.lt_cases_of_isU64 h_pv_isu64
  have hpv0 := hpv.1
  have hpv1 := hpv.2.1
  have hpv2 := hpv.2.2.1
  have hpv3 := hpv.2.2.2
  have h_cpu := h_holds.1
  have hh1 := h_holds.2
  have h_addr := hh1.1
  have hh2 := hh1.2
  have h_mem := hh2.1
  have hh3 := hh2.2
  have h_msb := hh3.1
  have hh4 := hh3.2
  have h_itype := hh4.1
  have hh5 := hh4.2.2
  have hsel0 := hh5.1
  have hh6 := hh5.2
  have hsel1 := hh6.1
  have hh7 := hh6.2
  have hsel2 := hh7.1
  have hh8 := hh7.2
  have hsel3 := hh8.1
  have hh9 := hh8.2
  have h_op_a_0 := hh9.1
  have hh10 := hh9.2
  have h_msbgate := hh10.1
  have hh11 := hh10.2
  have h_lh_gate := hh11.1
  have hh12 := hh11.2
  have h_lhu_gate := hh12.1
  have h_gate := hh12.2
  have h_bin := bool_of_mul_pred h_gate
  have h_lh_bin := bool_of_mul_pred h_lh_gate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's new `MemoryMsg.ClkBound` guarantee. Three distinct offsets: `MemoryAccess`'s RAM effect
  -- slot `clk_low + 1`, `ITypeReader`'s op_b read-back `clk_low + 3`, and `RegisterWrite`'s op_a write
  -- `clk_low + 4`. The offset is left to unification, so this never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  -- eval→value bridges for the nested vector fields the sub-`Spec`s / selection gates reference.
  have hmap_ob : Vector.map (Expression.eval env) input_var_offset_bit = input_offset_bit :=
    h_input.2.2.2.2.2.1
  have hmap_pv : Vector.map (Expression.eval env) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.2.1.1
  have eob : ∀ i (hi : i < 2), Expression.eval env input_var_offset_bit[i] = input_offset_bit[i] :=
    fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  simp only [eob, epv] at hsel0 hsel1 hsel2 hsel3
  have h_it := h_itype ⟨h_bin, h_bin, h_clk⟩
  have h_addr_as : AddressOperation.SoundnessAssumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, Expression.eval env input_var_offset_bit[0],
          Expression.eval env input_var_offset_bit[1],
          input_is_lh + input_is_lhu⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, h_bin⟩
  simp only [AddressOperation.circuit] at h_addr
  have h_addr_spec := h_addr h_addr_as
  simp only [circuit_norm, eob] at h_addr_spec
  have hob0 : input_offset_bit[0] = 0 ∨ input_offset_bit[0] = 1 := h_addr_spec.2.1
  have hob1 : input_offset_bit[1] = 0 ∨ input_offset_bit[1] = 1 := h_addr_spec.2.2.1
  -- `selected_half < 2^16` on a real row: it equals one of the four 16-bit limbs by the offset corner.
  have h_sel_lt : input_selected_half.val < 2 ^ 16 :=
    sel_lt_of_corners hob0 hob1 hsel0 hsel1 hsel2 hsel3 hpv0 hpv1 hpv2 hpv3
  have h_msb_as : U16MSBOperation.circuit.Assumptions
      (⟨input_selected_half, ⟨input_msb⟩, input_is_lh⟩ : U16MSBOperation.Inputs (ZMod p)) :=
    ⟨fun _ => h_sel_lt, h_lh_bin⟩
  have h_msb_spec := h_msb h_msb_as
  -- `msb` binary (from `U16MSBOperation.Spec`) → sign-fill limb `65535·msb ∈ {0, 65535} < 2^16`.
  have h_msb_val : (65535 * input_msb : ZMod p).val < 2 ^ 16 := by
    have h_msb_bin : input_msb = 0 ∨ input_msb = 1 := h_msb_spec.1
    rcases h_msb_bin with h | h <;> simp [h]
  -- the loaded word `#v[selected_half, 65535·msb, 65535·msb, 65535·msb]` (op_a write value) is `isU64` —
  -- from the selected memory limb (`h_sel_lt`) + the binary `msb` sign fill (`h_msb_val`).
  have h_load_isu64 : Word.isU64
      (#v[input_selected_half, 65535 * input_msb, 65535 * input_msb, 65535 * input_msb] : Word (ZMod p)) :=
    Word.isU64_of_cases h_sel_lt h_msb_val h_msb_val h_msb_val
  refine ⟨⟨h_addr_spec,
    h_mem ⟨h_bin, fun _ => h_pv_isu64, h_clk⟩, h_msb_spec, h_it,
    ⟨hsel0, hsel1, hsel2, hsel3⟩, h_op_a_0,
    h_msbgate, h_lh_bin, bool_of_mul_pred h_lhu_gate, h_bin⟩, ?_⟩
  -- G1: each push-owning sub-circuit's `Assumptions` gained a `MemoryMsg.ClkBound` conjunct at its own
  -- offset — `MemoryAccess` at the RAM `+1` slot, `ITypeReader` at op_b's `+3`, `RegisterWrite` at
  -- op_a's `+4`.
  refine ⟨Or.inr h_addr_as,
    Or.inr ⟨h_bin, fun _ => h_pv_isu64, h_clk⟩,
    Or.inr ⟨h_bin, h_bin, h_clk⟩,
    Or.inr ⟨h_bin, fun _ => h_load_isu64, h_clk.at_four⟩⟩

/-- Prover-side row well-formedness: the address facts + the reader/gadget `Spec`s + the selector
binaries + `op_a_0 = 0` + the offset-selection equations + the `is_lhu·msb` zero-extension gate. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    (isReal input = 1 →
      2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48) ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 2 = 0 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    2 * input.offset_bit[0].val + 4 * input.offset_bit[1].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    input.memory_access.prev_value[0].val < 2 ^ 16 ∧ input.memory_access.prev_value[1].val < 2 ^ 16 ∧
    input.memory_access.prev_value[2].val < 2 ^ 16 ∧ input.memory_access.prev_value[3].val < 2 ^ 16 ∧
    (input.is_lh = 0 ∨ input.is_lh = 1) ∧ (input.is_lhu = 0 ∨ input.is_lhu = 1) ∧
    (isReal input = 0 ∨ isReal input = 1) ∧
    input.adapter.op_a_0 = 0 ∧
    ((input.selected_half - input.memory_access.prev_value[0])
        * (input.offset_bit[0] - 1) * (input.offset_bit[1] - 1) = 0 ∧
      (input.selected_half - input.memory_access.prev_value[1])
        * input.offset_bit[0] * (input.offset_bit[1] - 1) = 0 ∧
      (input.selected_half - input.memory_access.prev_value[2])
        * (input.offset_bit[0] - 1) * input.offset_bit[1] = 0 ∧
      (input.selected_half - input.memory_access.prev_value[3])
        * input.offset_bit[0] * input.offset_bit[1] = 0) ∧
    input.is_lhu * input.msb = 0 ∧
    U16MSBOperation.Spec ⟨input.selected_half, ⟨input.msb⟩, input.is_lh⟩ ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, isReal input⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.memory_access.prev_value, isReal input⟩ ∧
    Readers.ITypeReader.Spec
      ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
        input.state.pc, input.is_lh * 30 + input.is_lhu * 33,
        input.selected_half, 65535 * input.msb, 65535 * input.msb, 65535 * input.msb⟩

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  have ha := h_assumptions.1
  have hp1 := h_assumptions.2
  have hb := hp1.1
  have hp2 := hp1.2
  have hfit := hp2.1
  have hp3 := hp2.2
  have h_ge := hp3.1
  have hp4 := hp3.2
  have h_align := hp4.1
  have hp5 := hp4.2
  have hob0 := hp5.1
  have hp6 := hp5.2
  have hob1 := hp6.1
  have hp7 := hp6.2
  have h_off := hp7.1
  have hp8 := hp7.2
  have hpv0 := hp8.1
  have hp9 := hp8.2
  have hpv1 := hp9.1
  have hp10 := hp9.2
  have hpv2 := hp10.1
  have hp11 := hp10.2
  have hpv3 := hp11.1
  have hp12 := hp11.2
  have h_lh_bin := hp12.1
  have hp13 := hp12.2
  have h_lhu_bin := hp13.1
  have hp14 := hp13.2
  have hbin := hp14.1
  have hp15 := hp14.2
  have h_op_a_0 := hp15.1
  have hp16 := hp15.2
  have hsel0 := hp16.1.1
  have hsel1 := hp16.1.2.1
  have hsel2 := hp16.1.2.2.1
  have hsel3 := hp16.1.2.2.2
  have hp17 := hp16.2
  have h_msbgate := hp17.1
  have hp18 := hp17.2
  have h_msb_spec := hp18.1
  have hp19 := hp18.2
  have h_cpu := hp19.1
  have hp20 := hp19.2
  have h_mem := hp20.1
  have h_it := hp20.2
  simp only [isReal] at hbin
  -- G1: the *push* side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  -- eval→value bridges for the nested vectors the reader/gadget `Spec`s reference.
  have hmap_pc : Vector.map (Expression.eval env.toEnvironment) input_var_state_pc
      = input_state_pc := h_input.2.2.1.2.2.2
  have hmap_ob : Vector.map (Expression.eval env.toEnvironment) input_var_offset_bit
      = input_offset_bit := h_input.2.2.2.2.2.1
  have hmap_pv : Vector.map (Expression.eval env.toEnvironment) input_var_memory_access_prev_value
      = input_memory_access_prev_value := h_input.2.2.2.2.1.1
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have eob : ∀ i (hi : i < 2), Expression.eval env.toEnvironment input_var_offset_bit[i]
      = input_offset_bit[i] := fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have h_addr_as : AddressOperation.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, 0, Expression.eval env.toEnvironment input_var_offset_bit[0],
          Expression.eval env.toEnvironment input_var_offset_bit[1],
          input_is_lh + input_is_lhu⟩ : AddressOperation.Inputs (ZMod p)) := by
    simp only [eob]
    exact ⟨ha, hb, hbin, hfit, Or.inl rfl, hob0, hob1, h_ge, by simpa using h_off⟩
  have h_sel_lt : input_selected_half.val < 2 ^ 16 :=
    sel_lt_of_corners hob0 hob1 hsel0 hsel1 hsel2 hsel3 hpv0 hpv1 hpv2 hpv3
  -- `isU64 prev_value` (from the four 16-bit limbs) for `MemoryAccess`'s read push; the loaded-word `isU64`
  -- (`h_load_isu64`) for `RegisterWrite`'s op_a write push.
  have h_pv_isu64 : Word.isU64 input_memory_access_prev_value := Word.isU64_of_cases hpv0 hpv1 hpv2 hpv3
  have h_msb_val : (65535 * input_msb : ZMod p).val < 2 ^ 16 := by
    have h_msb_bin : input_msb = 0 ∨ input_msb = 1 := h_msb_spec.1
    rcases h_msb_bin with h | h <;> simp [h]
  have h_load_isu64 : Word.isU64
      (#v[input_selected_half, 65535 * input_msb, 65535 * input_msb, 65535 * input_msb] : Word (ZMod p)) :=
    Word.isU64_of_cases h_sel_lt h_msb_val h_msb_val h_msb_val
  refine ⟨⟨?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ⟨⟨fun _ => h_sel_lt, h_lh_bin⟩, ?_⟩,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, h_op_a_0, ?_, ?_, ?_, ?_⟩
  · exact hbin
  · simp only [epc]; exact h_cpu
  · exact ⟨hbin, fun _ => h_pv_isu64, h_clk⟩
  · exact h_mem
  · exact h_msb_spec
  · exact ⟨hbin, hbin, h_clk⟩
  · exact h_it
  · exact ⟨hbin, fun _ => h_load_isu64, h_clk.at_four⟩
  · trivial
  · simp only [eob, epv]; exact hsel0
  · simp only [eob, epv]; exact hsel1
  · simp only [eob, epv]; exact hsel2
  · simp only [eob, epv]; exact hsel3
  · exact h_msbgate
  · rcases h_lh_bin with h | h <;> rw [h] <;> simp
  · rcases h_lhu_bin with h | h <;> rw [h] <;> simp
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- LoadHalf's exact Memory-channel interaction list — the RAM-access family shape: the composed
`MemoryAccess` RAM pull/push pair at the computed 48-bit address (`var ⟨offset..offset+2⟩` are the
`AddressOperation` sub-circuit's witnessed address limbs), then the I-type register entries (op_a
read-prior pull, op_b pull + read-back push) and `RegisterWrite`'s op_a write push carrying the
sign/zero-extended half `#v[selected_half, 65535·msb, 65535·msb, 65535·msb]`.  Keeping this list
beside `circuit` makes Clean's exposure interface the single structural source consumed by both
faithfulness and semantic grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨input.memory_access.access_timestamp.prev_high,
       input.memory_access.access_timestamp.prev_low,
       var { index := offset } - (4 : Expression (ZMod p)) * input.offset_bit[1] -
         (2 : Expression (ZMod p)) * input.offset_bit[0] - 0,
       var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩,
    memoryChannel.pushedIf (input.is_lh + input.is_lhu)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 1,
       var { index := offset } - (4 : Expression (ZMod p)) * input.offset_bit[1] -
         (2 : Expression (ZMod p)) * input.offset_bit[0] - 0,
       var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩,
    memoryChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf (input.is_lh + input.is_lhu)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf (input.is_lh + input.is_lhu)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0,
       #v[input.selected_half, 65535 * input.msb, 65535 * input.msb, 65535 * input.msb]⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact RAM-access pull occupies its declared slot in LoadHalf's exposed Memory list. -/
theorem ramPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨input.memory_access.access_timestamp.prev_high,
       input.memory_access.access_timestamp.prev_low,
       var { index := offset } - (4 : Expression (ZMod p)) * input.offset_bit[1] -
         (2 : Expression (ZMod p)) * input.offset_bit[0] - 0,
       var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in LoadHalf's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (input.is_lh + input.is_lhu)
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The `LoadHalf` chip row as a `GeneralFormalCircuit`; output is the extracted `Columns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    soundness := soundness, completeness := completeness,
    -- A2: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8); the
    -- enabled flag is the **derived** selector sum `is_lh + is_lhu` (SP1's `is_real`).
    exposedChannels := fun input offset =>
      expose stateChannel
        [ stateChannel.pulledIf (input.is_lh + input.is_lhu)
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf (input.is_lh + input.is_lhu)
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ] ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `ITypeReader`, gate
      -- `is_trusted = is_lh + is_lhu`, opcode `LH·30 + LHU·33`), consumed by
      -- `Soundness/TypedProgram.lean`.
      expose programChannel
        [ programChannel.pulledIf (input.is_lh + input.is_lhu)
            ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
             input.is_lh * 30 + input.is_lhu * 33, input.adapter.op_a,
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

/-- The completed LoadHalf circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.LoadHalfChip
