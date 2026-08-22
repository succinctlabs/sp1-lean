import SP1Clean.Native.Chips.LoadByteChip.Defs
import Clean.Air.Circuit

/-! # `SP1Clean.LoadByteChip` — `Assumptions` / soundness / completeness / `circuit`

`Assumptions`, soundness, completeness, and the bundled `circuit`. (`main` + `ElaboratedCircuit`
in `Defs`; Sail bridge in `Bridge`.) -/

namespace SP1Clean.LoadByteChip

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The register/immediate operands and RAM word are genuine 64-bit values. Address validity,
non-reservation, and offset decomposition are conclusions of the composed `AddressOperation` AIR. -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    Word.isU64 input.memory_access.prev_value

/-- The byte sign-extension low limb `byte + 65280·msb` is 16-bit whenever the byte is 8-bit and
`msb` is binary. Shared by soundness and completeness, which both build the loaded word
`#v[byte + 65280·msb, 65535·msb, 65535·msb, 65535·msb]`. -/
private lemma sext_limb0_lt {b m : ZMod p} (hb : b.val < 256) (hm : m = 0 ∨ m = 1) :
    (b + 65280 * m : ZMod p).val < 2 ^ 16 := by
  have hp65536 : (65536 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  rcases hm with h | h
  · rw [h, mul_zero, add_zero]; omega
  · have h65280 : (65280 : ZMod p).val = 65280 := val_65280_zmod_p
    rw [h, mul_one, ZMod.val_add, h65280, Nat.mod_eq_of_lt (by omega)]; omega

-- Both proofs read `h_holds` / `h_assumptions` / `h_input` through `.1`/`.2` projections instead of a
-- wide `obtain`: an `And.casesOn` motive re-abstracts the (very large) goal once per component, which is
-- Clean's `doc/performance-problems.md` pattern 7 and was two thirds of this file's elaboration cost.
-- Measured floors fell from (300000, 350000] to (150000, 160000] (soundness) and from (250000, 300000]
-- to (150000, 160000] (completeness) — both now clear Lean's plain default, so neither carries a scoped
-- elaboration budget any more (they were stamped at 2M / 1.5M, and 16M before that).
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  have ha := h_assumptions.1
  have hb := h_assumptions.2.1
  have h_pv_isu64 := h_assumptions.2.2
  have h_cpu := h_holds.1
  have hh1 := h_holds.2
  have h_addr := hh1.1
  have hh2 := hh1.2
  have h_mem := hh2.1
  have hh3 := hh2.2
  have hu8 := hh3.1
  have hh4 := hh3.2
  have hmsb_rcv := hh4.1
  have hh5 := hh4.2
  have h_itype := hh5.1
  have hh6 := hh5.2
  have hh7 := hh6.2
  have hsel0 := hh7.1
  have hh8 := hh7.2
  have hsel1 := hh8.1
  have hh9 := hh8.2
  have hsel2 := hh9.1
  have hh10 := hh9.2
  have hsel3 := hh10.1
  have hh11 := hh10.2
  have hmux := hh11.1
  have hh12 := hh11.2
  have h_op_a_0 := hh12.1
  have hh13 := hh12.2
  have h_msbgate := hh13.1
  have hh14 := hh13.2
  have h_lb_gate := hh14.1
  have hh15 := hh14.2
  have h_lbu_gate := hh15.1
  have hh16 := hh15.2
  have h_gate := hh16
  have h_bin := bool_of_mul_pred h_gate
  have h_lb_bin := bool_of_mul_pred h_lb_gate
  have h_lbu_bin := bool_of_mul_pred h_lbu_gate
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's new `MemoryMsg.ClkBound` guarantee. Three distinct offsets: `MemoryAccess`'s RAM effect
  -- slot `clk_low + 1`, `ITypeReader`'s op_b read-back `clk_low + 3`, and `RegisterWrite`'s op_a write
  -- `clk_low + 4`. The offset is left to unification, so this never names the destructured state columns.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec (h_cpu h_bin)
  simp only [circuit_norm, byteChannel] at hu8 hmsb_rcv
  -- eval→value bridges (extracted directly from `h_input`; `tauto` over this context is too slow).
  have hmap_pv := h_input.2.2.2.2.1.1
  have hmap_ob := h_input.2.2.2.2.2.1
  have eob : ∀ i (hi : i < 3), Expression.eval env input_var_offset_bit[i] = input_offset_bit[i] :=
    fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have h_addr_as : AddressOperation.SoundnessAssumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm,
        Expression.eval env input_var_offset_bit[0], Expression.eval env input_var_offset_bit[1],
        Expression.eval env input_var_offset_bit[2],
        input_is_lb + input_is_lbu⟩ : AddressOperation.Inputs (ZMod p)) :=
    ⟨ha, hb, h_bin⟩
  simp only [AddressOperation.circuit] at h_addr
  have h_addr_spec := h_addr h_addr_as
  simp only [circuit_norm, eob] at h_addr_spec
  have hob0 : input_offset_bit[0] = 0 ∨ input_offset_bit[0] = 1 := h_addr_spec.1
  simp only [eob, epv] at hsel0 hsel1 hsel2 hsel3
  simp only [eob] at hmux
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
  have h_it := h_itype ⟨h_bin, h_bin, h_clk⟩
  -- `msb` is binary on any real row: LB rows get it from the inline MSB byte-pull; LBU rows have `msb = 0`
  -- (the `is_lbu·msb = 0` gate with `is_lbu = 1`).
  have h_msb_bin_real : input_is_lb + input_is_lbu = 1 → (input_msb = 0 ∨ input_msb = 1) := by
    intro h1
    rcases h_lb_bin with hlb | hlb
    · have hlbu : input_is_lbu = 1 := by rw [hlb, zero_add] at h1; exact h1
      left; rw [hlbu, one_mul] at h_msbgate; exact h_msbgate
    · exact (h_msb_fact hlb).1
  -- the loaded word `#v[selected_byte + 65280·msb, 65535·msb, 65535·msb, 65535·msb]` (op_a write value) is
  -- `isU64` on real rows: limb 0 = the byte-sign-extended low limb (`selected_byte < 256` + `65280·msb`), the
  -- high limbs the sign fill `65535·msb` — all `< 2^16` since `selected_byte < 256` and `msb ∈ {0,1}`.
  have h_msb_val : input_is_lb + input_is_lbu = 1 → (65535 * input_msb : ZMod p).val < 2 ^ 16 :=
    fun h1 => by rcases h_msb_bin_real h1 with h | h <;> simp [h]
  have h_load_isu64 : input_is_lb + input_is_lbu = 1 → Word.isU64
      (#v[input_selected_byte + 65280 * input_msb, 65535 * input_msb, 65535 * input_msb,
          65535 * input_msb] : Word (ZMod p)) :=
    fun h1 => Word.isU64_of_cases (sext_limb0_lt (h_byte_lt h1) (h_msb_bin_real h1))
      (h_msb_val h1) (h_msb_val h1) (h_msb_val h1)
  -- G1: each push-owning sub-circuit's `Assumptions` gained a `MemoryMsg.ClkBound` conjunct at its own
  -- offset — `MemoryAccess` at the RAM `+1` slot, `ITypeReader` at op_b's `+3`, `RegisterWrite` at
  -- op_a's `+4`.
  refine ⟨⟨h_addr_spec,
      h_mem ⟨h_bin, fun _ => h_pv_isu64, h_clk⟩, h_it,
      fun h1 => ⟨(h_u8 h1).1, (h_u8 h1).2, h_byte_lt h1⟩, h_msb_fact,
      ⟨hsel0, hsel1, hsel2, hsel3⟩, hmux_eq, h_op_a_0, h_msbgate, h_lb_bin, h_lbu_bin, h_bin⟩,
    Or.inr h_addr_as,
    Or.inr ⟨h_bin, fun _ => h_pv_isu64, h_clk⟩,
    fun h1 h0 => off_gate_vacuous h_bin h1 h0,
    fun h1 h0 => off_gate_vacuous h_lb_bin h1 h0,
    Or.inr ⟨h_bin, h_bin, h_clk⟩,
    Or.inr ⟨h_bin, h_load_isu64, h_clk.at_four⟩⟩

/-- Prover-side row well-formedness: the address facts + selector binaries + `op_a_0 = 0` + the byte
value bounds + the branch-correct signed/unsigned byte facts + the limb-selection / byte-mux
equations + the reader `Spec`s. The non-reserved-address lower bound is real-row-gated, matching
`AddressOperation`'s inverse gate; `LB` alone ties `msb` to the selected byte's high bit, while
`LBU` requires `msb = 0`. -/
def ProverAssumptions (input : Inputs (ZMod p)) (_data : ProverData (ZMod p)) (_ : ProverHint (ZMod p)) : Prop :=
  Word.isU64 input.op_b_val ∧ Word.isU64 input.op_c_imm ∧
    (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 64 < 2 ^ 48 ∧
    (isReal input = 1 →
      2 ^ 16 ≤ (Word.toNat input.op_b_val + Word.toNat input.op_c_imm) % 2 ^ 48) ∧
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
    (input.msb = 0 ∨ input.msb = 1) ∧
    (input.is_lb = 1 → (input.msb = 1 ↔ 128 ≤ input.selected_byte.val)) ∧
    (input.is_lbu = 1 → input.msb = 0) ∧
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

theorem completeness :
    GeneralFormalCircuit.Completeness (ZMod p) main ProverAssumptions (fun _ _ _ => True) := by
  circuit_proof_start
  simp only [Inputs.op_b_val, Inputs.op_c_imm] at h_assumptions ⊢
  haveI : AddGroup (id (ZMod p)) := inferInstanceAs (AddGroup (ZMod p))
  have ha := h_assumptions.1
  have hp1 := h_assumptions.2
  have hb := hp1.1
  have hp2 := hp1.2
  have hfit := hp2.1
  have hp3 := hp2.2
  have h_ge := hp3.1
  have hp4 := hp3.2
  have h_off := hp4.1
  have hp5 := hp4.2
  have hob0 := hp5.1
  have hp6 := hp5.2
  have hob1 := hp6.1
  have hp7 := hp6.2
  have hob2 := hp7.1
  have hp8 := hp7.2
  have h_pv_isu64 := hp8.1
  have hp9 := hp8.2
  have h_lb_bin := hp9.1
  have hp10 := hp9.2
  have h_lbu_bin := hp10.1
  have hp11 := hp10.2
  have hbin := hp11.1
  have hp12 := hp11.2
  have h_op_a_0 := hp12.1
  have hp13 := hp12.2
  have hlo_pa := hp13.1
  have hp14 := hp13.2
  have hhi_pa := hp14.1
  have hp15 := hp14.2
  have hbyte_pa := hp15.1
  have hp16 := hp15.2
  have h_msb_bin := hp16.1
  have hp17 := hp16.2
  have h_msb_iff := hp17.1
  have hp18 := hp17.2
  have h_lbu_msb := hp18.1
  have hp19 := hp18.2
  have hsel0 := hp19.1.1
  have hsel1 := hp19.1.2.1
  have hsel2 := hp19.1.2.2.1
  have hsel3 := hp19.1.2.2.2
  have hp20 := hp19.2
  have hmux_pa := hp20.1
  have hp21 := hp20.2
  have h_cpu := hp21.1
  have hp22 := hp21.2
  have h_mem := hp22.1
  have hp23 := hp22.2
  have h_it := hp23
  have hmap_pc := h_input.2.2.1.2.2.2
  have hmap_pv := h_input.2.2.2.2.1.1
  have hmap_ob := h_input.2.2.2.2.2.1
  simp only [isReal] at hbin
  -- G1: the *push* side clock bounds, from the prover-supplied CPUState clock byte bounds.
  have h_clk := Readers.ClkDiscipline.of_cpuState_spec h_cpu
  have h_msb_lt : input_msb.val < 256 := by
    rcases h_msb_bin with h | h <;> rw [h] <;> simp [ZMod.val_one]
  have epc : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_state_pc[i]
      = input_state_pc[i] := fun i hi => by rw [← hmap_pc]; simp only [Vector.getElem_map]
  have eob : ∀ i (hi : i < 3), Expression.eval env.toEnvironment input_var_offset_bit[i]
      = input_offset_bit[i] := fun i hi => by rw [← hmap_ob]; simp only [Vector.getElem_map]
  have epv : ∀ i (hi : i < 4), Expression.eval env.toEnvironment input_var_memory_access_prev_value[i]
      = input_memory_access_prev_value[i] := fun i hi => by rw [← hmap_pv]; simp only [Vector.getElem_map]
  have h_addr_as : AddressOperation.Assumptions
      (⟨input_adapter_op_b_memory_prev_value, input_adapter_op_c_imm, Expression.eval env.toEnvironment input_var_offset_bit[0],
          Expression.eval env.toEnvironment input_var_offset_bit[1],
          Expression.eval env.toEnvironment input_var_offset_bit[2],
          input_is_lb + input_is_lbu⟩ : AddressOperation.Inputs (ZMod p)) := by
    simp only [eob]; exact ⟨ha, hb, hbin, hfit, hob0, hob1, hob2, h_ge, h_off⟩
  -- the loaded word `#v[selected_byte + 65280·msb, 65535·msb, 65535·msb, 65535·msb]` (op_a write value) is
  -- `isU64`: `selected_byte < 256` (prover) + `msb ∈ {0,1}` (prover) bound every limb `< 2^16`.
  have h_msb_val : (65535 * input_msb : ZMod p).val < 2 ^ 16 := by
    rcases h_msb_bin with h | h <;> simp [h]
  have h_load_isu64 : Word.isU64
      (#v[input_selected_byte + 65280 * input_msb, 65535 * input_msb, 65535 * input_msb,
          65535 * input_msb] : Word (ZMod p)) :=
    Word.isU64_of_cases (sext_limb0_lt hbyte_pa h_msb_bin) h_msb_val h_msb_val h_msb_val
  refine ⟨⟨?_, ?_⟩, h_addr_as, ⟨?_, ?_⟩, ?_, ?_, ⟨?_, ?_⟩, ⟨?_, ?_⟩,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hbin
  · simp only [epc]; exact h_cpu
  · exact ⟨hbin, fun _ => h_pv_isu64, h_clk⟩
  · exact h_mem
  · -- U8Range-pair receive obligation (real row); value is raw (`toRaw` (gated post-#398)).
    intro _
    simp only [byteChannel]
    exact (byteRowSpec_u8range_pair _ _).mpr ⟨hlo_pa, hhi_pa⟩
  · -- MSB receive obligation (real LB row); value is raw (`toRaw` (gated post-#398)).
    intro hneg
    have hlb : input_is_lb = 1 := neg_inj.mp hneg
    simp only [byteChannel]
    exact (byteRowSpec_msb _ _).mpr ⟨⟨h_msb_lt, hbyte_pa⟩, h_msb_bin, h_msb_iff hlb⟩
  · exact ⟨hbin, hbin, h_clk⟩
  · exact h_it
  · exact ⟨hbin, fun _ => h_load_isu64, h_clk.at_four⟩
  · trivial
  · simp only [eob, epv]; exact hsel0
  · simp only [eob, epv]; exact hsel1
  · simp only [eob, epv]; exact hsel2
  · simp only [eob, epv]; exact hsel3
  · simp only [eob]; exact sub_eq_zero_of_eq hmux_pa
  · exact h_op_a_0
  · rcases h_lbu_bin with hzero | hone
    · rw [hzero, zero_mul]
    · rw [hone, one_mul]
      exact h_lbu_msb hone
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
       var { index := offset } - (4 : Expression (ZMod p)) * input.offset_bit[2] -
         (2 : Expression (ZMod p)) * input.offset_bit[1] - input.offset_bit[0],
       var { index := offset + 1 }, var { index := offset + 2 },
       input.memory_access.prev_value⟩,
    memoryChannel.pushedIf (input.is_lb + input.is_lbu)
      ⟨input.state.clk_high, input.state.clk_0_16 + input.state.clk_16_24 * 65536 + 1,
       var { index := offset } - (4 : Expression (ZMod p)) * input.offset_bit[2] -
         (2 : Expression (ZMod p)) * input.offset_bit[1] - input.offset_bit[0],
       var { index := offset + 1 }, var { index := offset + 2 },
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
       var { index := offset } - (4 : Expression (ZMod p)) * input.offset_bit[2] -
         (2 : Expression (ZMod p)) * input.offset_bit[1] - input.offset_bit[0],
       var { index := offset + 1 }, var { index := offset + 2 },
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

/-- The `LoadByte` chip row as a `GeneralFormalCircuit`; output is the extracted `Columns`. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Columns :=
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

/-- Folded circuit projections used by the whole-chip row codec. -/
@[circuit_norm] theorem circuit_main_eq : (circuit (p := p)).main = main := rfl

@[circuit_norm] theorem circuit_localLength_eq (input : Var Inputs (ZMod p)) :
    (circuit (p := p)).localLength input = 4 := rfl

@[circuit_norm] theorem circuit_size_eq :
    (circuit (p := p)).size = size Inputs + 4 := by
  rw [GeneralFormalCircuit.size_eq, circuit_localLength_eq]

/-- The completed LoadByte circuit exposes exactly the Memory interaction list above. -/
theorem interactionsWith_memory_eq (input : Var Inputs (ZMod p)) (offset : ℕ) :
    ((main input).operations offset).interactionsWith memoryChannel.toRaw =
      (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw := by
  exact circuit.interactionsWith_eq_of_mem_exposedChannels input offset
    ⟨memoryChannel.toRaw, (exposedMemoryInteractions input offset).map ChannelInteraction.toRaw⟩
    (by simp [circuit, expose])

end SP1Clean.LoadByteChip
