import SP1Clean.Native.Chips.LoadByteChip.Defs

/-! # `SP1Clean.LoadByteChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.LoadByteChip

open Circuit
open Extracted (LoadByteColumns)
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Operands are 64-bit values; the load targets a non-reserved, in-range address (no alignment for byte
loads). The offset bits are bits 0–2 of the address and boolean. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    input.offset_bit[0].val + 2 * input.offset_bit[1].val + 4 * input.offset_bit[2].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    (input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1) ∧
    Word.isU64 input.memory_access.prev_value

set_option maxHeartbeats 16000000 in
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  obtain ⟨ha, hb, hfit, h_ge, h_off, hob0, hob1, hob2, h_pv_isu64⟩ := h_assumptions
  obtain ⟨h_cpu, h_addr, h_mem, hu8, hmsb_rcv, h_itype, _h_regwrite, hsel0, hsel1, hsel2, hsel3, hmux,
    h_op_a_0, h_msbgate, h_lb_gate, h_lbu_gate, h_gate⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  have h_lb_bin := bool_of_mul_pred h_lb_gate
  have h_lbu_bin := bool_of_mul_pred h_lbu_gate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's new `MemoryMsg.ClkBound` guarantee. Three distinct offsets: `MemoryAccess`'s RAM effect
  -- slot `clk_low + 1`, `ITypeReader`'s op_b read-back `clk_low + 3`, and `RegisterWrite`'s op_a write
  -- `clk_low + 4`. The offset is left to unification, so this never names the destructured state columns.
  have h_clk : ∀ (delta : ZMod p) (k : ℕ), delta.val = k → k ≤ 4 →
      input_is_lb + input_is_lbu = 1 →
      (input_state_clk_0_16 + input_state_clk_16_24 * 65536 + delta).val < 2 ^ 24 :=
    fun _ k hk hk4 hr => Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ k hk hk4
      (h_cpu h_bin hr).1 (h_cpu h_bin hr).2
  -- the RAM effect slot's offset is the literal `1`, whose `val` needs `Fact (1 < p)` (kept local so the
  -- instance does not leak into the surrounding heavy `simp` sets).
  have hv1 : (1 : ZMod p).val = 1 := by
    haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    exact ZMod.val_one p
  simp only [circuit_norm, byteChannel] at hu8 hmsb_rcv
  -- eval→value bridges (extracted directly from `h_input`; `tauto` over this context is too slow).
  obtain ⟨_, _, _, _, ⟨hmap_pv, _, _, _, _, _⟩, hmap_ob, _, _, _, _⟩ := h_input
  have eob : ∀ i (hi : i < 3), Expression.eval env input_var_offset_bit[i] = input_offset_bit[i] :=
    fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  simp only [eob 1 (by omega), eob 2 (by omega), epv 0 (by omega), epv 1 (by omega),
    epv 2 (by omega), epv 3 (by omega)] at hsel0 hsel1 hsel2 hsel3
  simp only [eob 0 (by omega)] at hmux
  -- the byte-mux equation in value form.
  have hmux_eq : input_selected_byte = input_offset_bit[0]
      * ((input_selected_limb - input_selected_limb_low_byte) * (256 : ZMod p)⁻¹)
      + ((1 : ZMod p) - input_offset_bit[0]) * input_selected_limb_low_byte := sub_eq_zero.mp hmux
  -- the real-row byte bounds, from the inline U8Range-pair receive.
  have h_u8 : input_is_lb + input_is_lbu = 1 →
      input_selected_limb_low_byte.val < 256
        ∧ ((input_selected_limb - input_selected_limb_low_byte) * (256 : ZMod p)⁻¹).val < 256 := by
    intro h1
    have hneg : -(input_is_lb + input_is_lbu) = -1 := by rw [h1]
    have G := hu8 hneg
    have hb := (byteRowSpec_u8range_pair _ _).mp G
    rw [show (2:ℕ)^8 = 256 from by norm_num] at hb
    exact hb
  -- `selected_byte < 256`, by the byte-mux + the offset-bit-0 case split.
  have h_byte_lt : input_is_lb + input_is_lbu = 1 → input_selected_byte.val < 256 := by
    intro h1
    obtain ⟨hlo, hhi⟩ := h_u8 h1
    rw [hmux_eq]
    rcases hob0 with h0 | h0
    · rw [h0]; simp only [zero_mul, zero_add, sub_zero, one_mul]; exact hlo
    · rw [h0]; simp only [one_mul, sub_self, zero_mul, add_zero]; exact hhi
  -- the LB-row sign-bit fact, from the inline MSB receive.
  have h_msb_fact : input_is_lb = 1 →
      (input_msb = 0 ∨ input_msb = 1) ∧ (input_msb = 1 ↔ 128 ≤ input_selected_byte.val) := by
    intro h1
    have hneg : - input_is_lb = -1 := by rw [h1]
    have G := hmsb_rcv hneg
    have := (byteRowSpec_msb _ _).mp G
    exact ⟨this.2.1, this.2.2⟩
  -- the `AddressOperation` Assumptions (eval form).
  have hob0' : Expression.eval env input_var_offset_bit[0] = 0
      ∨ Expression.eval env input_var_offset_bit[0] = 1 := by rw [eob 0 (by omega)]; exact hob0
  have hob1' : Expression.eval env input_var_offset_bit[1] = 0
      ∨ Expression.eval env input_var_offset_bit[1] = 1 := by rw [eob 1 (by omega)]; exact hob1
  have hob2' : Expression.eval env input_var_offset_bit[2] = 0
      ∨ Expression.eval env input_var_offset_bit[2] = 1 := by rw [eob 2 (by omega)]; exact hob2
  have h_off' : (Expression.eval env input_var_offset_bit[0]).val
        + 2 * (Expression.eval env input_var_offset_bit[1]).val
        + 4 * (Expression.eval env input_var_offset_bit[2]).val
      = (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 := by
    rw [eob 0 (by omega), eob 1 (by omega), eob 2 (by omega)]; exact h_off
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, Expression.eval env input_var_offset_bit[0],
          Expression.eval env input_var_offset_bit[1], Expression.eval env input_var_offset_bit[2]⟩
        : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, hob0', hob1', hob2', h_ge, h_off'⟩
  simp only [AddressOperation.circuit] at h_addr
  have h_addr_spec := h_addr h_addr_as
  simp only [circuit_norm, eob 0 (by omega), eob 1 (by omega), eob 2 (by omega)] at h_addr_spec
  have h_it := h_itype ⟨h_bin, h_bin, fun hr => h_clk 3 3 (by simp) (by norm_num) hr⟩
  -- `msb` is binary on any real row: LB rows get it from the inline MSB byte-pull; LBU rows have `msb = 0`
  -- (the `is_lbu·msb = 0` gate with `is_lbu = 1`).
  have h_msb_bin_real : input_is_lb + input_is_lbu = 1 → (input_msb = 0 ∨ input_msb = 1) := by
    intro h1
    rcases h_lb_bin with hlb | hlb
    · have hlbu : input_is_lbu = 1 := by rw [hlb, zero_add] at h1; exact h1
      left; rw [hlbu, one_mul] at h_msbgate; exact h_msbgate
    · exact (h_msb_fact hlb).1
  have hp65536 : (65536 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  -- the loaded word `#v[selected_byte + 65280·msb, 65535·msb, 65535·msb, 65535·msb]` (op_a write value) is
  -- `isU64` on real rows: limb 0 = the byte-sign-extended low limb (`selected_byte < 256` + `65280·msb`), the
  -- high limbs the sign fill `65535·msb` — all `< 2^16` since `selected_byte < 256` and `msb ∈ {0,1}`.
  have h_msb_val : input_is_lb + input_is_lbu = 1 → (65535 * input_msb : ZMod p).val < 2 ^ 16 := by
    intro h1
    rcases h_msb_bin_real h1 with h | h
    · rw [h, mul_zero, ZMod.val_zero]; norm_num
    · rw [h, mul_one, show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) by norm_cast,
        ZMod.val_natCast_of_lt (by omega)]; norm_num
  have h_limb0_lt : input_is_lb + input_is_lbu = 1 →
      (input_selected_byte + 65280 * input_msb : ZMod p).val < 2 ^ 16 := by
    intro h1
    have hbyte := h_byte_lt h1
    rcases h_msb_bin_real h1 with h | h
    · rw [h, mul_zero, add_zero]; omega
    · rw [h, mul_one]
      have h65280 : (65280 : ZMod p).val = 65280 := by
        rw [show (65280 : ZMod p) = ((65280 : ℕ) : ZMod p) by norm_cast, ZMod.val_natCast_of_lt (by omega)]
      have hval : (input_selected_byte + 65280 : ZMod p).val = input_selected_byte.val + 65280 := by
        rw [ZMod.val_add, h65280, Nat.mod_eq_of_lt (by omega)]
      rw [hval]; omega
  have h_load_isu64 : input_is_lb + input_is_lbu = 1 → Word.isU64
      (#v[input_selected_byte + 65280 * input_msb, 65535 * input_msb, 65535 * input_msb,
          65535 * input_msb] : Word (ZMod p)) :=
    fun h1 => Word.isU64_of_cases (h_limb0_lt h1) (h_msb_val h1) (h_msb_val h1) (h_msb_val h1)
  -- G1: each push-owning sub-circuit's `Assumptions` gained a `MemoryMsg.ClkBound` conjunct at its own
  -- offset — `MemoryAccess` at the RAM `+1` slot, `ITypeReader` at op_b's `+3`, `RegisterWrite` at
  -- op_a's `+4`.
  refine ⟨⟨h_addr_spec,
      h_mem ⟨h_bin, fun _ => h_pv_isu64, fun hr => h_clk 1 1 hv1 (by norm_num) hr⟩, h_it,
      fun h1 => ⟨(h_u8 h1).1, (h_u8 h1).2, h_byte_lt h1⟩, h_msb_fact,
      ⟨hsel0, hsel1, hsel2, hsel3⟩, hmux_eq, h_op_a_0, h_msbgate, h_lb_bin, h_lbu_bin, h_bin⟩,
    Or.inr h_addr_as,
    Or.inr ⟨h_bin, fun _ => h_pv_isu64, fun hr => h_clk 1 1 hv1 (by norm_num) hr⟩,
    fun h1 h0 => off_gate_vacuous h_bin h1 h0,
    fun h1 h0 => off_gate_vacuous h_lb_bin h1 h0,
    Or.inr ⟨h_bin, h_bin, fun hr => h_clk 3 3 (by simp) (by norm_num) hr⟩,
    Or.inr ⟨h_bin, h_load_isu64, fun hr => h_clk 4 4 (by simp) (by norm_num) hr⟩⟩

/-- Prover-side row well-formedness: the address facts + selector binaries + `op_a_0 = 0` + the byte
value bounds + the sign-bit fact + the limb-selection / byte-mux equations + the reader `Spec`s. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 ∧
    input.offset_bit[0].val + 2 * input.offset_bit[1].val + 4 * input.offset_bit[2].val
      = (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48 % 8 ∧
    (input.offset_bit[0] = 0 ∨ input.offset_bit[0] = 1) ∧
    (input.offset_bit[1] = 0 ∨ input.offset_bit[1] = 1) ∧
    (input.offset_bit[2] = 0 ∨ input.offset_bit[2] = 1) ∧
    Word.isU64 input.memory_access.prev_value ∧
    (input.is_lb = 0 ∨ input.is_lb = 1) ∧ (input.is_lbu = 0 ∨ input.is_lbu = 1) ∧
    (isReal input = 0 ∨ isReal input = 1) ∧
    input.adapter.op_a_0 = 0 ∧
    input.selected_limb_low_byte.val < 256 ∧ (highByte input).val < 256 ∧ input.selected_byte.val < 256 ∧
    (input.msb = 0 ∨ input.msb = 1) ∧ (input.msb = 1 ↔ 128 ≤ input.selected_byte.val) ∧
    input.is_lbu * input.msb = 0 ∧
    ((input.selected_limb - input.memory_access.prev_value[0])
        * (input.offset_bit[1] - 1) * (input.offset_bit[2] - 1) = 0 ∧
      (input.selected_limb - input.memory_access.prev_value[1])
        * input.offset_bit[1] * (input.offset_bit[2] - 1) = 0 ∧
      (input.selected_limb - input.memory_access.prev_value[2])
        * (input.offset_bit[1] - 1) * input.offset_bit[2] = 0 ∧
      (input.selected_limb - input.memory_access.prev_value[3])
        * input.offset_bit[1] * input.offset_bit[2] = 0) ∧
    input.selected_byte = input.offset_bit[0] * highByte input
        + (1 - input.offset_bit[0]) * input.selected_limb_low_byte ∧
    Readers.CPUState.Spec
      ⟨input.state, #v[input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]], 8, isReal input⟩ ∧
    Readers.MemoryAccess.Spec
      ⟨input.memory_access, input.state.clk_high, clkLow input.state, 0, 0, 0,
        input.memory_access.prev_value, isReal input⟩ ∧
    Readers.ITypeReader.Spec
      ⟨input.adapter, isReal input, isReal input, input.state.clk_high, clkLow input.state,
        input.state.pc, input.is_lb * 29 + input.is_lbu * 32,
        input.selected_byte + 65280 * input.msb, 65535 * input.msb, 65535 * input.msb,
        65535 * input.msb⟩

set_option maxHeartbeats 16000000 in
theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  haveI : AddGroup (id (ZMod p)) := inferInstanceAs (AddGroup (ZMod p))
  obtain ⟨ha, hb, hfit, h_ge, h_off, hob0, hob1, hob2, h_pv_isu64, h_lb_bin, h_lbu_bin, hbin, h_op_a_0,
    hlo_pa, hhi_pa, hbyte_pa, h_msb_bin, h_msb_iff, h_msbgate, ⟨hsel0, hsel1, hsel2, hsel3⟩,
    hmux_pa, h_cpu, h_mem, h_it⟩ := h_assumptions
  obtain ⟨_, _, ⟨_, _, _, hmap_pc⟩, _, ⟨hmap_pv, _, _, _, _, _⟩, hmap_ob, _, _, _, _⟩ := h_input
  simp only [isReal] at hbin
  haveI : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- G1: the *push* side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk : ∀ (delta : ZMod p) (k : ℕ), delta.val = k → k ≤ 4 →
      input_is_lb + input_is_lbu = 1 →
      (input_state_clk_0_16 + input_state_clk_16_24 * 65536 + delta).val < 2 ^ 24 :=
    fun _ k hk hk4 hr => Channels.MemoryMsg.clkBound_of_cpuState_bounds _ _ _ k hk hk4
      (h_cpu hr).1 (h_cpu hr).2
  have hv1 : (1 : ZMod p).val = 1 := ZMod.val_one p
  have h_msb_lt : input_msb.val < 256 := by
    rcases h_msb_bin with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have eob : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_offset_bit[i]
      = input_offset_bit[i] := fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have hob0' : Expression.eval env.toEnvironment input_var_offset_bit[0] = 0
      ∨ Expression.eval env.toEnvironment input_var_offset_bit[0] = 1 := by rw [eob 0 (by omega)]; exact hob0
  have hob1' : Expression.eval env.toEnvironment input_var_offset_bit[1] = 0
      ∨ Expression.eval env.toEnvironment input_var_offset_bit[1] = 1 := by rw [eob 1 (by omega)]; exact hob1
  have hob2' : Expression.eval env.toEnvironment input_var_offset_bit[2] = 0
      ∨ Expression.eval env.toEnvironment input_var_offset_bit[2] = 1 := by rw [eob 2 (by omega)]; exact hob2
  have h_off' : (Expression.eval env.toEnvironment input_var_offset_bit[0]).val
        + 2 * (Expression.eval env.toEnvironment input_var_offset_bit[1]).val
        + 4 * (Expression.eval env.toEnvironment input_var_offset_bit[2]).val
      = (Word.toNat input_adapter_op_b_memory_prev_value + Word.toNat input_adapter_op_c_imm) % 2 ^ 48 % 8 := by
    rw [eob 0 (by omega), eob 1 (by omega), eob 2 (by omega)]; exact h_off
  have h_addr_as : AddressOperation.circuit.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, Expression.eval env.toEnvironment input_var_offset_bit[0],
          Expression.eval env.toEnvironment input_var_offset_bit[1],
          Expression.eval env.toEnvironment input_var_offset_bit[2]⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, hfit, hob0', hob1', hob2', h_ge, h_off'⟩
  -- the loaded word `#v[selected_byte + 65280·msb, 65535·msb, 65535·msb, 65535·msb]` (op_a write value) is
  -- `isU64`: `selected_byte < 256` (prover) + `msb ∈ {0,1}` (prover) bound every limb `< 2^16`.
  have hp65536 : (65536 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have h_msb_val : (65535 * input_msb : ZMod p).val < 2 ^ 16 := by
    rcases h_msb_bin with h | h
    · rw [h, mul_zero, ZMod.val_zero]; norm_num
    · rw [h, mul_one, show (65535 : ZMod p) = ((65535 : ℕ) : ZMod p) by norm_cast,
        ZMod.val_natCast_of_lt (by omega)]; norm_num
  have h_limb0_lt : (input_selected_byte + 65280 * input_msb : ZMod p).val < 2 ^ 16 := by
    rcases h_msb_bin with h | h
    · rw [h, mul_zero, add_zero]; omega
    · rw [h, mul_one]
      have h65280 : (65280 : ZMod p).val = 65280 := by
        rw [show (65280 : ZMod p) = ((65280 : ℕ) : ZMod p) by norm_cast, ZMod.val_natCast_of_lt (by omega)]
      have hval : (input_selected_byte + 65280 : ZMod p).val = input_selected_byte.val + 65280 := by
        rw [ZMod.val_add, h65280, Nat.mod_eq_of_lt (by omega)]
      rw [hval]; omega
  have h_load_isu64 : Word.isU64
      (#v[input_selected_byte + 65280 * input_msb, 65535 * input_msb, 65535 * input_msb,
          65535 * input_msb] : Word (ZMod p)) :=
    Word.isU64_of_cases h_limb0_lt h_msb_val h_msb_val h_msb_val
  refine ⟨⟨?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbin
  · simp only [epc 0 (by omega), epc 1 (by omega), epc 2 (by omega)]; exact h_cpu
  · exact ⟨hbin, fun _ => h_pv_isu64, fun hr => h_clk 1 1 hv1 (by norm_num) hr⟩
  · exact h_mem
  · -- U8Range-pair receive obligation (real row); value is raw (`toRaw` (gated post-#398)).
    intro _
    simp only [byteChannel]
    exact (byteRowSpec_u8range_pair _ _).mpr ⟨hlo_pa, hhi_pa⟩
  · -- MSB receive obligation (real LB row); value is raw (`toRaw` (gated post-#398)).
    intro _
    simp only [byteChannel]
    exact (byteRowSpec_msb _ _).mpr ⟨⟨h_msb_lt, hbyte_pa⟩, h_msb_bin, h_msb_iff⟩
  · exact ⟨hbin, hbin, fun hr => h_clk 3 3 (by simp) (by norm_num) hr⟩
  · exact h_it
  · exact ⟨hbin, fun _ => h_load_isu64, fun hr => h_clk 4 4 (by simp) (by norm_num) hr⟩
  · trivial
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 0 (by omega)]; exact hsel0
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 1 (by omega)]; exact hsel1
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 2 (by omega)]; exact hsel2
  · simp only [eob 1 (by omega), eob 2 (by omega), epv 3 (by omega)]; exact hsel3
  · simp only [eob 0 (by omega)]; exact sub_eq_zero_of_eq hmux_pa
  · exact h_op_a_0
  · exact h_msbgate
  · rcases h_lb_bin with h | h <;> rw [h] <;> simp
  · rcases h_lbu_bin with h | h <;> rw [h] <;> simp
  · rcases hbin with h | h <;> rw [h] <;> simp

/-- LoadByte's exact Memory-channel interaction list — the RAM-access family shape: the composed
`MemoryAccess` RAM pull/push pair at the computed 48-bit address (`var ⟨offset..offset+2⟩` are the
`AddressOperation` sub-circuit's witnessed address limbs), then the I-type register entries (op_a
read-prior pull, op_b pull + read-back push) and `RegisterWrite`'s op_a write push carrying the
sign/zero-extended byte `#v[selected_byte + 65280·msb, 65535·msb, 65535·msb, 65535·msb]`.  Keeping
this list beside `circuit` makes Clean's exposure interface the single structural source consumed by
both faithfulness and semantic grounding. -/
def exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    List (ChannelInteraction (memoryChannel (p := p))) :=
  [ memoryChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨input.memory_access.access_timestamp.prev_high,
       input.memory_access.access_timestamp.prev_low,
       var { index := offset }, var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩,
    memoryChannel.pushedIf (input.is_lb + input.is_lbu)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 1,
       var { index := offset }, var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩,
    memoryChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨input.state.clk_high, input.adapter.op_a_memory.access_timestamp.prev_low,
       input.adapter.op_a, 0, 0, input.adapter.op_a_memory.prev_value⟩,
    memoryChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf (input.is_lb + input.is_lbu)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 3,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩,
    memoryChannel.pushedIf (input.is_lb + input.is_lbu)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 4,
       input.adapter.op_a, 0, 0,
       #v[input.selected_byte + 65280 * input.msb, 65535 * input.msb, 65535 * input.msb,
          65535 * input.msb]⟩ ]

omit [Fact (2 ^ 17 < p)] in
/-- The exact RAM-access pull occupies its declared slot in LoadByte's exposed Memory list. -/
theorem ramPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨input.memory_access.access_timestamp.prev_high,
       input.memory_access.access_timestamp.prev_low,
       var { index := offset }, var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

omit [Fact (2 ^ 17 < p)] in
/-- The exact source-B pull occupies its declared slot in LoadByte's exposed Memory list. -/
theorem opBPull_mem_exposedMemoryInteractions (input : Var Inputs (ZMod p)) (offset : ℕ) :
    memoryChannel.pulledIf (input.is_lb + input.is_lbu)
      ⟨input.state.clk_high, input.adapter.op_b_memory.access_timestamp.prev_low,
       input.adapter.op_b, 0, 0, input.adapter.op_b_memory.prev_value⟩ ∈
      exposedMemoryInteractions input offset := by
  simp [exposedMemoryInteractions]

/-- The `LoadByte` chip row as a `GeneralFormalCircuit`; output is the extracted `LoadByteColumns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs LoadByteColumns :=
  -- `byteChannel` dropped (W11 Phase 0c): the two off-gate byte pulls (`is_real`-gated U8 pair +
  -- `is_lb`-gated MSB) are discharged by the inline `is_real`/`is_lb` boolean gates in `main`; the
  -- residual buses are the readers'.
  { main, elaborated,
    Assumptions := Assumptions, Spec := Spec,
    ProverAssumptions := ProverAssumptions, ProverSpec := fun _ _ _ => True,
    channelsWithRequirements :=
      [stateChannel.toRaw, memoryChannel.toRaw],
    soundness := soundness, completeness := completeness,
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, byteChannel, stateChannel, memoryChannel, programChannel,
        AddressOperation.circuit, Readers.CPUState.circuit, Readers.ITypeReader.circuit,
        Readers.MemoryAccess.circuit, Readers.RegisterWrite.circuit]; grind,
    -- A2: expose the State-bus `[pulledIf is_real cur, pushedIf is_real next]` pair (pc+4, clk+8); the
    -- enabled flag is the **derived** selector sum `is_lb + is_lbu` (SP1's `is_real`).
    exposedChannels := fun input offset =>
      expose stateChannel
        [ stateChannel.pulledIf (input.is_lb + input.is_lbu)
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536,
             input.state.pc[0], input.state.pc[1], input.state.pc[2]⟩,
          stateChannel.pushedIf (input.is_lb + input.is_lbu)
            ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 8,
             input.state.pc[0] + 4, input.state.pc[1], input.state.pc[2]⟩ ] ++
      expose memoryChannel (exposedMemoryInteractions input offset) ++
      -- The Program-bus instruction fetch (descended from the composed `ITypeReader`, gate
      -- `is_trusted = is_lb + is_lbu`, opcode `LB·29 + LBU·32`), consumed by
      -- `Soundness/TypedProgram.lean`.
      expose programChannel
        [ programChannel.pulledIf (input.is_lb + input.is_lbu)
            ⟨input.state.pc[0], input.state.pc[1], input.state.pc[2],
             input.is_lb * 29 + input.is_lbu * 32, input.adapter.op_a,
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

/-- The completed LoadByte circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.LoadByteChip
