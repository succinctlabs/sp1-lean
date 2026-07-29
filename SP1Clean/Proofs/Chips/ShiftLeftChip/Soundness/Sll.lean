import SP1Clean.Proofs.Chips.ShiftLeftChip.Defs
import SP1Clean.Proofs.Chips.ShiftLeftChip.Core
import SP1Clean.Proofs.CircuitProofStart

/-! # `ShiftLeftChip` — sll conjunct soundness (split out for parallel compilation)

The logical left-shift (SLL) conjunct, proved as its own `GeneralFormalCircuit.Soundness` over a
single-conjunct local `Spec`. Re-running `circuit_proof_start` regenerates the monolithic proof's context
(unfolding the local `Spec` and `Assumptions`), so the shared `have a1_bound_cond` setup, the SLL branch,
and the channel-requirement tail are verbatim slices of the monolith. Kept in a child namespace with the
local `Spec` named exactly `Spec` (so `circuit_proof_start` reduces it). -/

namespace SP1Clean.ShiftLeftChip.SoundSll

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- `RV64.sll` as a shift by the low six bits of the shift source. Lifted to a top-level lemma so the
`BitVec`/`2 ^ 64` reduction is kernel-checked once here rather than inline in `soundness` — avoids the
`2 ^ N` deep-recursion landmine (see `docs/PROOF_PATTERNS.md`). -/
lemma sll_rv64_eq (c b : BitVec 64) : RV64.sll c b = b <<< (c.toNat % 64) := by
  simp only [RV64.sll]; rw [BitVec.shiftLeft_eq']; congr 1

/-- The `sll` conjunct of `ShiftLeftChip.Spec`, as a standalone single-conjunct spec. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  input.is_real = 1 →
    (cols.is_sll = 1 →
      Word.toBitVec64 cols.a = RV64.sll (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

-- Genuinely binding (a `whnf`-bound elaboration tower): the former 4M ceiling was ~10× over, measured
-- floor bracket (200000, 400000]; sized at 4× the bracket top.
set_option maxHeartbeats 1600000 in
/-- Soundness of the `sll` conjunct (verbatim slice of the monolithic proof + the shared tail). -/
theorem soundness : GeneralFormalCircuit.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start_early_struct
  -- `op_b_val`/`op_c_val` are reducible projections of the physical ALU read-backs.
  simp only [Inputs.op_b_val, Inputs.op_c_val] at h_assumptions ⊢
  obtain ⟨hb_u64, hc_u64⟩ := h_assumptions
  obtain ⟨h_cpu, hmsb, _halu, _hregwrite, _hrealbin, hrealeq,
    _hE2, _hE4, _hE6, h_core,
    hbyte1, hbyte2, hbyte3, hbyte4, hbyte5, hbyte6, hbyte7, hbyte8, hbyte9⟩ := h_holds
  have h_core' := h_core trivial
  simp only [ShiftLeftCore.circuit, ShiftLeftChip.CoreSpec, Vector.getElem_map,
    Vector.getElem_mapRange, circuit_norm] at h_core'
  obtain ⟨
    hcb0b, hcb1b, hcb2b, hcb3b, hcb4b, hcb5b,
    hsu0sel, hsu0b, hsu1sel, hsu1b, hsu2sel, hsu2b, hsu3sel, hsu3b, hsusum,
    hv01e, hv012e, hv0123e,
    hsplit0, hsplit1, hsplit2, hsplit3,
    hreass0, hreass1, hreass2, hreass3,
    hp00, hp01, hp02, hp03, hp10, hp11, hp12, hp13,
    hp20, hp21, hp22, hp23, hp30, hp31, hp32, hp33,
    hw00, hw01, hw10, hw11, hwmsb2, hwmsb3,
    _himm, _hopa0⟩ := h_core'
  -- The variant flags are now **witnessed columns** (`flags[0..2]` at offsets `i₀+30..32`), not `Inputs`
  -- fields; `set` them under their old names so the proof body is unchanged.
  set input_is_sll := env.get (i₀ + 30) with hsll_def
  set input_is_sllw := env.get (i₀ + 31) with hsllw_def
  -- The shared power encoding of the shift amount (`v0123 = 2 ^ S`, `S = cb0 + 2cb1 + 4cb2 + 8cb3`)
  -- together with the two width normalizations every byte-range bound below is stated at. Derived once
  -- here; `a1_bound_cond`, `a_isU64` and the SLL branch each used to re-derive it verbatim.
  have hp17 : 131072 < p := by have := Fact.out (p := (2:ℕ)^17 < p); omega
  have hv01 : env.get (i₀+4+6) = (env.get (i₀+4) + 1) * (env.get (i₀+4+1) * 3 + 1) := by
    linear_combination hv01e
  have hv012 : env.get (i₀+4+6+1) = env.get (i₀+4+6) * (env.get (i₀+4+2) * 15 + 1) := by
    linear_combination hv012e
  have hv0123 : env.get (i₀+4+6+2) = env.get (i₀+4+6+1) * (env.get (i₀+4+3) * 255 + 1) := by
    linear_combination hv0123e
  obtain ⟨S, hSle, hv0123val, h_inner⟩ := ShiftLeftCore.v0123_pow
    (bool_of_mul_pred hcb0b) (bool_of_mul_pred hcb1b) (bool_of_mul_pred hcb2b) (bool_of_mul_pred hcb3b)
    hv01 hv012 hv0123
  have hwidth_hl : (env.get (i₀+4)*1 + env.get (i₀+4+1)*2 + env.get (i₀+4+2)*4 + env.get (i₀+4+3)*8 : ZMod p)
      = ((S : ℕ) : ZMod p) := by
    have hi := h_inner; push_cast at hi ⊢; linear_combination hi
  have hwidth_ll : (16 - (env.get (i₀+4)*1 + env.get (i₀+4+1)*2 + env.get (i₀+4+2)*4 + env.get (i₀+4+3)*8) : ZMod p)
      = (((16 - S) : ℕ) : ZMod p) := by
    push_cast [Nat.cast_sub (show S ≤ 16 by omega)]; linear_combination -hwidth_hl
  -- The SLLW result limb 1 (`a[1] = env.get (i₀+1)`) is 16-bit whenever `is_sllw = 1`. Proved once here
  -- (self-contained from the byte guarantees + placement), reused for the U16MSB sub-assertion's operand
  -- bound in both the SLLW branch and the channel-requirement tail.
  have a1_bound_cond : input_is_sllw = 1 → (env.get (i₀+1)).val < 2 ^ 16 := by
    intro hsllw1
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h; have hv := val_2_zmod_p (p := p); rw [h, ZMod.val_zero] at hv; omega
    have hsll0 : input_is_sll = 0 := by
      have e2 := _hE2; rw [hsllw1] at e2
      exact ShiftLeftCore.eq_zero_of_mul_const h2ne (by linear_combination e2 - _hE4)
    have hgate1 : (input_is_sll + input_is_sllw : ZMod p) = 1 := by rw [hsll0, hsllw1, zero_add]
    have hneg : -(input_is_sll + input_is_sllw) = -1 := by rw [hgate1]
    have hll0 : (env.get (i₀+4+6+3+4)).val < 2 ^ (16 - S) := by
      have hb := hbyte2 hneg; rw [hwidth_ll] at hb
      exact (byteRowSpec_range _ (show 16 - S < p by omega)).mp hb
    have hhl0 : (env.get (i₀+4+6+3+4+4)).val < 2 ^ S := by
      have hb := hbyte3 hneg; rw [hwidth_hl] at hb
      exact (byteRowSpec_range _ (show S < p by omega)).mp hb
    have hll1 : (env.get (i₀+4+6+3+4+1)).val < 2 ^ (16 - S) := by
      have hb := hbyte4 hneg; rw [hwidth_ll] at hb
      exact (byteRowSpec_range _ (show 16 - S < p by omega)).mp hb
    have hs0sel : env.get (i₀+4+6+3) * (env.get (i₀+4+4) - 0) = 0 := by
      rw [hsll0] at hsu0sel; linear_combination hsu0sel
    have hs1sel : env.get (i₀+4+6+3+1) * (env.get (i₀+4+4) - 1) = 0 := by
      rw [hsll0] at hsu1sel; linear_combination hsu1sel
    have hs2sel : env.get (i₀+4+6+3+2) * (env.get (i₀+4+4) - 2) = 0 := by
      rw [hsll0] at hsu2sel; linear_combination hsu2sel
    have hs3sel : env.get (i₀+4+6+3+3) * (env.get (i₀+4+4) - 3) = 0 := by
      rw [hsll0] at hsu3sel; linear_combination hsu3sel
    have hssum : env.get (i₀+4+6+3) + env.get (i₀+4+6+3+1) + env.get (i₀+4+6+3+2) + env.get (i₀+4+6+3+3) = 1 := by
      rw [hgate1, one_mul] at hsusum; linear_combination hsusum
    have hlr0 : env.get (i₀+4+6+3+4+4+4) = env.get (i₀+4+6+3+4) * env.get (i₀+4+6+2) := by
      linear_combination hreass0
    have hlr1 : env.get (i₀+4+6+3+4+4+4+1) = env.get (i₀+4+6+3+4+1) * env.get (i₀+4+6+2) + env.get (i₀+4+6+3+4+4) := by
      linear_combination hreass1
    rw [hsllw1, one_mul] at hw01 hw11
    rw [show (2:ℕ)^16 = 65536 from by norm_num]
    exact ShiftLeftCore.sllw_a1_bound (2^S) (2^(16-S))
      (by rw [← pow_add, Nat.add_sub_cancel' (show S ≤ 16 by omega)]; norm_num)
      hv0123val (bool_of_mul_pred hcb4b) hs0sel hs1sel hs2sel hs3sel hssum hlr0 hlr1 hll0 hhl0 hll1 hw01 hw11
  -- The placed result word `a` is a `u64` on every real (gate = 1) row — the `RegisterWrite` op_a write
  -- push's `isU64` requirement (W11 Option-B memory flip). Self-contained from the byte ranges (the
  -- `lower/higher_limb` pulls bound the `limb_result` entries) + the placement asserts (each `a_i` is `0`,
  -- a `limb_result` entry, or `msb·65535`); reused in the channel-requirement tail.
  have a_isU64 : (input_is_sll + input_is_sllw : ZMod p) = 1 →
      (env.get i₀).val < 2 ^ 16 ∧ (env.get (i₀+1)).val < 2 ^ 16 ∧
      (env.get (i₀+2)).val < 2 ^ 16 ∧ (env.get (i₀+3)).val < 2 ^ 16 := by
    intro hgate1
    have hneg : -(input_is_sll + input_is_sllw) = -1 := by rw [hgate1]
    have hll0 : (env.get (i₀+4+6+3+4)).val < 2 ^ (16 - S) := by
      have hb := hbyte2 hneg; rw [hwidth_ll] at hb
      exact (byteRowSpec_range _ (show 16 - S < p by omega)).mp hb
    have hhl0 : (env.get (i₀+4+6+3+4+4)).val < 2 ^ S := by
      have hb := hbyte3 hneg; rw [hwidth_hl] at hb
      exact (byteRowSpec_range _ (show S < p by omega)).mp hb
    have hll1 : (env.get (i₀+4+6+3+4+1)).val < 2 ^ (16 - S) := by
      have hb := hbyte4 hneg; rw [hwidth_ll] at hb
      exact (byteRowSpec_range _ (show 16 - S < p by omega)).mp hb
    have hhl1 : (env.get (i₀+4+6+3+4+4+1)).val < 2 ^ S := by
      have hb := hbyte5 hneg; rw [hwidth_hl] at hb
      exact (byteRowSpec_range _ (show S < p by omega)).mp hb
    have hll2 : (env.get (i₀+4+6+3+4+2)).val < 2 ^ (16 - S) := by
      have hb := hbyte6 hneg; rw [hwidth_ll] at hb
      exact (byteRowSpec_range _ (show 16 - S < p by omega)).mp hb
    have hhl2 : (env.get (i₀+4+6+3+4+4+2)).val < 2 ^ S := by
      have hb := hbyte7 hneg; rw [hwidth_hl] at hb
      exact (byteRowSpec_range _ (show S < p by omega)).mp hb
    have hll3 : (env.get (i₀+4+6+3+4+3)).val < 2 ^ (16 - S) := by
      have hb := hbyte8 hneg; rw [hwidth_ll] at hb
      exact (byteRowSpec_range _ (show 16 - S < p by omega)).mp hb
    have hhl3 : (env.get (i₀+4+6+3+4+4+3)).val < 2 ^ S := by
      have hb := hbyte9 hneg; rw [hwidth_hl] at hb
      exact (byteRowSpec_range _ (show S < p by omega)).mp hb
    have hlr0 : env.get (i₀+4+6+3+4+4+4) = env.get (i₀+4+6+3+4) * env.get (i₀+4+6+2) := by
      linear_combination hreass0
    have hlr1 : env.get (i₀+4+6+3+4+4+4+1) = env.get (i₀+4+6+3+4+1) * env.get (i₀+4+6+2) + env.get (i₀+4+6+3+4+4) := by
      linear_combination hreass1
    have hlr2 : env.get (i₀+4+6+3+4+4+4+2) = env.get (i₀+4+6+3+4+2) * env.get (i₀+4+6+2) + env.get (i₀+4+6+3+4+4+1) := by
      linear_combination hreass2
    have hlr3 : env.get (i₀+4+6+3+4+4+4+3) = env.get (i₀+4+6+3+4+3) * env.get (i₀+4+6+2) + env.get (i₀+4+6+3+4+4+2) := by
      linear_combination hreass3
    have hMN : 2 ^ S * 2 ^ (16 - S) = 65536 := by
      rw [← pow_add, Nat.add_sub_cancel' (show S ≤ 16 by omega)]; norm_num
    have hMpos : 0 < 2 ^ S := pow_pos (by norm_num) _
    have hb0 : (env.get (i₀+4+6+3+4+4+4)).val < 2 ^ 16 := by
      rw [hlr0]; exact lr0_val_lt hMN hMpos hv0123val hll0
    have hb1 : (env.get (i₀+4+6+3+4+4+4+1)).val < 2 ^ 16 := by
      rw [hlr1]; exact lr_val_lt hMN hv0123val hll1 hhl0
    have hb2 : (env.get (i₀+4+6+3+4+4+4+2)).val < 2 ^ 16 := by
      rw [hlr2]; exact lr_val_lt hMN hv0123val hll2 hhl1
    have hb3 : (env.get (i₀+4+6+3+4+4+4+3)).val < 2 ^ 16 := by
      rw [hlr3]; exact lr_val_lt hMN hv0123val hll3 hhl2
    have hssum : env.get (i₀+4+6+3) + env.get (i₀+4+6+3+1) + env.get (i₀+4+6+3+2)
        + env.get (i₀+4+6+3+3) = 1 := by
      rw [hgate1, one_mul] at hsusum; linear_combination hsusum
    rcases bool_of_mul_pred _hE4 with hsll0 | hsll1
    · -- is_sll = 0 ⇒ is_sllw = 1 (SLLW): low two limbs placed, high two `= msb·65535`.
      have hsllw1 : input_is_sllw = 1 := by rw [hsll0, zero_add] at hgate1; exact hgate1
      have hs0sel : env.get (i₀+4+6+3) * (env.get (i₀+4+4) - 0) = 0 := by
        rw [hsll0] at hsu0sel; linear_combination hsu0sel
      have hs1sel : env.get (i₀+4+6+3+1) * (env.get (i₀+4+4) - 1) = 0 := by
        rw [hsll0] at hsu1sel; linear_combination hsu1sel
      have hs2sel : env.get (i₀+4+6+3+2) * (env.get (i₀+4+4) - 2) = 0 := by
        rw [hsll0] at hsu2sel; linear_combination hsu2sel
      have hs3sel : env.get (i₀+4+6+3+3) * (env.get (i₀+4+4) - 3) = 0 := by
        rw [hsll0] at hsu3sel; linear_combination hsu3sel
      have a1_bound := a1_bound_cond hsllw1
      have h_msb_a1 := (hmsb ⟨fun _ => a1_bound, Or.inr hsllw1⟩).2 hsllw1
      have hmsbb : env.get (i₀+4+6+3+4+4+4+4) = 0 ∨ env.get (i₀+4+6+3+4+4+4+4) = 1 := by
        rw [show env.get (i₀+4+6+3+4+4+4+4)
            = if (env.get (i₀+1)).val ≥ 32768 then 1 else 0 from h_msb_a1]
        split
        · exact Or.inr rfl
        · exact Or.inl rfl
      rw [hsllw1, one_mul] at hw00 hw01 hw10 hw11 hwmsb2 hwmsb3
      have ha2 : env.get (i₀+2) = env.get (i₀+4+6+3+4+4+4+4) * 65535 := by linear_combination -hwmsb2
      have ha3 : env.get (i₀+3) = env.get (i₀+4+6+3+4+4+4+4) * 65535 := by linear_combination -hwmsb3
      exact sllw_a_isU64 (bool_of_mul_pred hcb4b) hs0sel hs1sel hs2sel hs3sel hssum hb0 hb1 hmsbb
        hw00 hw01 hw10 hw11 ha2 ha3
    · -- is_sll = 1 (SLL): a permutation/placement of the four `limb_result` entries.
      rw [hsll1, one_mul] at hp00 hp01 hp02 hp03 hp10 hp11 hp12 hp13 hp20 hp21 hp22 hp23 hp30 hp31 hp32 hp33
      exact sll_a_isU64 (bool_of_mul_pred hsu0b) (bool_of_mul_pred hsu1b) (bool_of_mul_pred hsu2b)
        hssum hb0 hb1 hb2 hb3 hp00 hp01 hp02 hp03 hp10 hp11 hp12 hp13 hp20 hp21 hp22 hp23
        hp30 hp31 hp32 hp33
  -- G1: the CPUState sub-`Spec`'s two clock byte bounds discharge the *push* side of the memory
  -- channel's `MemoryMsg.ClkBound` guarantee — `ALUTypeReader`'s two read-back pushes (`clk_low + 3` /
  -- `+ 2`) and `RegisterWrite`'s op_a write push (`clk_low + 4`). The offset is left to unification, so
  -- this line never names the destructured state columns. ShiftLeft composes both children at the
  -- *derived* gate `is_sll + is_sllw`, while `CPUState` runs at the public `is_real`; the binding
  -- constraint `hrealeq` identifies the two, so the bound is stated at the gate.
  have h_clk : Readers.ClkDiscipline (input_state_clk_0_16 + input_state_clk_16_24 * 65536)
      (input_is_sll + input_is_sllw) :=
    (Readers.ClkDiscipline.of_cpuState_spec (h_cpu (bool_of_mul_pred _hrealbin))).of_gate
      fun hgate => by linear_combination hrealeq + hgate
  refine ⟨fun hreal => ?_, ?_⟩
  · intro hsll
    -- Witnessed columns evaluate into `id (ZMod p)`; normalize to `ZMod p` so the native ring tactics
    -- fire with the standard instance (AGENTS.md `id (ZMod p)` note) and the kernel term stays shallow.
    have hgate1 : (input_is_sll + input_is_sllw : ZMod p) = 1 := by
      have h : (input_is_real - (input_is_sll + input_is_sllw) : ZMod p) = 0 := hrealeq
      rw [hreal] at h
      exact (sub_eq_zero.mp h).symm
    have hsllw0 : input_is_sllw = 0 := by
      have h : input_is_sll + input_is_sllw = input_is_sll + 0 := by rw [add_zero, hgate1, hsll]
      exact add_left_cancel h
    -- Remaining SLL assembly (all `ShiftLeftCore` lemmas + the `hcb*`/`hsplit*`/`hreass*`/`hp*`/`hbyte*`
    -- hypotheses above are in hand; `hgate1` fires every `hbyte*` guarantee via `by rw [hgate1]`):
    --   a. `v0123_pow hcb0b' … hv01e' hv012e' hv0123e'` (after `bool_of_mul_pred` on `hcb0b..hcb3b` and
    --      moving `hv*e` to `v = …` form) → `S`, `v0123.val = 2^S`, the inner-bits equation; `M := 2^S`,
    --      `N := 2^(16-S)`.
    --   b. From `hbyte2..hbyte9` + `byteRowSpec_range`: the `lower/higher_limb` range bounds (width
    --      `16-bitShift` / `bitShift`; massage `cb_i*1`/`((k:ℕ):ZMod p)` to the `sll_close_*` width form).
    --   c. `hbyte1` + `is_mod_64` → `op_c_memory.prev_value[0].val % 64 = (cb-sum).val`, i.e. the low-6-bit
    --      shift amount; bridge `RV64.sll` to `… <<< ((toBitVec64 c).toNat % 64)`.
    --   d. Case-split `byteShift = cb4 + cb5*2` (here `is_sll = 1`) into 0/1/2/3 via `hsu*sel`/`hsu*b`/
    --      `hsusum` one-hot; in each, the `is_sll`-gated `hp*` collapse `a` to `limb_result`, and `hreass*`
    --      put it in `ll*v0123 (+hl)` form; feed the matching `sll_close_cb4cb5_{zero,one_zero,zero_one,
    --      one_one}_case` (its `h_b*_dec` are `hsplit*` after `op_b_val = op_b_memory.prev_value` via `hb_eq`).
    --   e. Read both physical operands from the ALU reader; conclude the `RV64.sll` identity.
    obtain ⟨_, _, _, _, _, _, ⟨hbmem, _, _⟩, _, ⟨hcmem, _, _⟩, _⟩ := h_input
    -- Operand evaluations: the constraint columns read back the physical ALU reader values.
    have heb0 : Expression.eval env input_var_adapter_op_b_memory_prev_value[0] = input_adapter_op_b_memory_prev_value[0] := by
      rw [← hbmem, Vector.getElem_map]
    have heb1 : Expression.eval env input_var_adapter_op_b_memory_prev_value[1] = input_adapter_op_b_memory_prev_value[1] := by
      rw [← hbmem, Vector.getElem_map]
    have heb2 : Expression.eval env input_var_adapter_op_b_memory_prev_value[2] = input_adapter_op_b_memory_prev_value[2] := by
      rw [← hbmem, Vector.getElem_map]
    have heb3 : Expression.eval env input_var_adapter_op_b_memory_prev_value[3] = input_adapter_op_b_memory_prev_value[3] := by
      rw [← hbmem, Vector.getElem_map]
    have heval_c0 : Expression.eval env input_var_adapter_op_c_memory_prev_value[0] =
        input_adapter_op_c_memory_prev_value[0] := by
      rw [← hcmem, Vector.getElem_map]
    -- Fire and convert the nine byte-range guarantees (gate = 1 on the real `is_sll` row).
    have hneg : -(input_is_sll + input_is_sllw) = -1 := by rw [hgate1]
    have hll0 : (env.get (i₀+4+6+3+4)).val < 2 ^ (16 - S) := by
      have hb := hbyte2 hneg; rw [hwidth_ll] at hb
      exact (byteRowSpec_range _ (show 16 - S < p by omega)).mp hb
    have hhl0 : (env.get (i₀+4+6+3+4+4)).val < 2 ^ S := by
      have hb := hbyte3 hneg; rw [hwidth_hl] at hb
      exact (byteRowSpec_range _ (show S < p by omega)).mp hb
    have hll1 : (env.get (i₀+4+6+3+4+1)).val < 2 ^ (16 - S) := by
      have hb := hbyte4 hneg; rw [hwidth_ll] at hb
      exact (byteRowSpec_range _ (show 16 - S < p by omega)).mp hb
    have hhl1 : (env.get (i₀+4+6+3+4+4+1)).val < 2 ^ S := by
      have hb := hbyte5 hneg; rw [hwidth_hl] at hb
      exact (byteRowSpec_range _ (show S < p by omega)).mp hb
    have hll2 : (env.get (i₀+4+6+3+4+2)).val < 2 ^ (16 - S) := by
      have hb := hbyte6 hneg; rw [hwidth_ll] at hb
      exact (byteRowSpec_range _ (show 16 - S < p by omega)).mp hb
    have hhl2 : (env.get (i₀+4+6+3+4+4+2)).val < 2 ^ S := by
      have hb := hbyte7 hneg; rw [hwidth_hl] at hb
      exact (byteRowSpec_range _ (show S < p by omega)).mp hb
    have hll3 : (env.get (i₀+4+6+3+4+3)).val < 2 ^ (16 - S) := by
      have hb := hbyte8 hneg; rw [hwidth_ll] at hb
      exact (byteRowSpec_range _ (show 16 - S < p by omega)).mp hb
    have hhl3 : (env.get (i₀+4+6+3+4+4+3)).val < 2 ^ S := by
      have hb := hbyte9 hneg; rw [hwidth_hl] at hb
      exact (byteRowSpec_range _ (show S < p by omega)).mp hb
    -- The shift-amount width-10 bound (feeds `is_mod_64` inside `sll_assembly`).
    have h_diff : ((input_adapter_op_c_memory_prev_value[0] - (env.get (i₀+4) + env.get (i₀+4+1)*2 + env.get (i₀+4+2)*4
        + env.get (i₀+4+3)*8 + env.get (i₀+4+4)*16 + env.get (i₀+4+5)*32)) * (64:ZMod p)⁻¹).val < 1024 := by
      have hb := hbyte1 hneg
      have hbd := (byteRowSpec_range _ (show (10:ℕ) < p by omega)).mp hb
      rw [show (2:ℕ)^10 = 1024 from by norm_num] at hbd
      convert hbd using 3
      rw [heval_c0]; ring
    -- Bit-split decompositions, `limb_result` reassembly, and the `is_sll`-collapsed placements.
    have hb0dec : input_adapter_op_b_memory_prev_value[0] * env.get (i₀+4+6+2)
        = env.get (i₀+4+6+3+4+4) * ((65536:ℕ):ZMod p) + env.get (i₀+4+6+3+4) * env.get (i₀+4+6+2) := by
      push_cast; linear_combination hsplit0
    have hb1dec : input_adapter_op_b_memory_prev_value[1] * env.get (i₀+4+6+2)
        = env.get (i₀+4+6+3+4+4+1) * ((65536:ℕ):ZMod p) + env.get (i₀+4+6+3+4+1) * env.get (i₀+4+6+2) := by
      push_cast; linear_combination hsplit1
    have hb2dec : input_adapter_op_b_memory_prev_value[2] * env.get (i₀+4+6+2)
        = env.get (i₀+4+6+3+4+4+2) * ((65536:ℕ):ZMod p) + env.get (i₀+4+6+3+4+2) * env.get (i₀+4+6+2) := by
      push_cast; linear_combination hsplit2
    have hb3dec : input_adapter_op_b_memory_prev_value[3] * env.get (i₀+4+6+2)
        = env.get (i₀+4+6+3+4+4+3) * ((65536:ℕ):ZMod p) + env.get (i₀+4+6+3+4+3) * env.get (i₀+4+6+2) := by
      push_cast; linear_combination hsplit3
    have hlr0 : env.get (i₀+4+6+3+4+4+4) = env.get (i₀+4+6+3+4) * env.get (i₀+4+6+2) := by
      linear_combination hreass0
    have hlr1 : env.get (i₀+4+6+3+4+4+4+1) = env.get (i₀+4+6+3+4+1) * env.get (i₀+4+6+2) + env.get (i₀+4+6+3+4+4) := by
      linear_combination hreass1
    have hlr2 : env.get (i₀+4+6+3+4+4+4+2) = env.get (i₀+4+6+3+4+2) * env.get (i₀+4+6+2) + env.get (i₀+4+6+3+4+4+1) := by
      linear_combination hreass2
    have hlr3 : env.get (i₀+4+6+3+4+4+4+3) = env.get (i₀+4+6+3+4+3) * env.get (i₀+4+6+2) + env.get (i₀+4+6+3+4+4+2) := by
      linear_combination hreass3
    rw [hsll, one_mul] at hp00 hp01 hp02 hp03 hp10 hp11 hp12 hp13 hp20 hp21 hp22 hp23 hp30 hp31 hp32 hp33
    -- Selector facts (one-hot, `is_sll`-substituted byte-shift = `cb4 + 2·cb5`).
    have hs0sel : env.get (i₀+4+6+3) * (env.get (i₀+4+4) + env.get (i₀+4+5)*2 - 0) = 0 := by
      rw [hsll] at hsu0sel; linear_combination hsu0sel
    have hs1sel : env.get (i₀+4+6+3+1) * (env.get (i₀+4+4) + env.get (i₀+4+5)*2 - 1) = 0 := by
      rw [hsll] at hsu1sel; linear_combination hsu1sel
    have hs2sel : env.get (i₀+4+6+3+2) * (env.get (i₀+4+4) + env.get (i₀+4+5)*2 - 2) = 0 := by
      rw [hsll] at hsu2sel; linear_combination hsu2sel
    have hs3sel : env.get (i₀+4+6+3+3) * (env.get (i₀+4+4) + env.get (i₀+4+5)*2 - 3) = 0 := by
      rw [hsll] at hsu3sel; linear_combination hsu3sel
    have hssum : env.get (i₀+4+6+3) + env.get (i₀+4+6+3+1) + env.get (i₀+4+6+3+2) + env.get (i₀+4+6+3+3) = 1 := by
      rw [hgate1, one_mul] at hsusum; linear_combination hsusum
    have h_c0_lt : input_adapter_op_c_memory_prev_value[0].val < 65536 := by
      have h := hc_u64 0; norm_num at h ⊢; exact h
    -- Reduce the goal and apply the native assembly.
    have hLHS : Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var {index := i₀+ i})
        = (#v[env.get i₀, env.get (i₀+1), env.get (i₀+2), env.get (i₀+3)] : Word (ZMod p)) := by
      apply Vector.ext; intro i hi
      simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
      interval_cases i <;> rfl
    have hbword : Word.toBitVec64 input_adapter_op_b_memory_prev_value
        = Word.toBitVec64 (#v[input_adapter_op_b_memory_prev_value[0], input_adapter_op_b_memory_prev_value[1], input_adapter_op_b_memory_prev_value[2], input_adapter_op_b_memory_prev_value[3]] : Word (ZMod p)) := by
      congr 1; apply Vector.ext; intro i hi; interval_cases i <;> rfl
    rw [hLHS, sll_rv64_eq, ShiftLeftCore.toBitVec64_toNat_mod64 hc_u64, hbword]
    exact ShiftLeftCore.sll_assembly S hSle (2^S) (2^(16-S))
      (by rw [← pow_add, Nat.add_sub_cancel' (show S ≤ 16 by omega)]; norm_num) (by positivity) rfl rfl
      hv0123val h_inner (bool_of_mul_pred hcb4b) (bool_of_mul_pred hcb5b) h_c0_lt
      (ShiftLeftCore.cb_sum6_val_lt_64 (bool_of_mul_pred hcb0b) (bool_of_mul_pred hcb1b)
        (bool_of_mul_pred hcb2b) (bool_of_mul_pred hcb3b) (bool_of_mul_pred hcb4b) (bool_of_mul_pred hcb5b))
      h_diff hs0sel hs1sel hs2sel hs3sel hssum hb0dec hb1dec hb2dec hb3dec hlr0 hlr1 hlr2 hlr3
      hll0 hhl0 hll1 hhl1 hll2 hhl2 hll3 hhl3
      hp00 hp01 hp02 hp03 hp10 hp11 hp12 hp13 hp20 hp21 hp22 hp23 hp30 hp31 hp32 hp33
  · -- The MSB gadget exposes its empty requirement list canonically. The remaining reader/write
    -- assumptions are followed by the nine gate-gated byte pulls, all vacuous off-gate.
    exact ⟨Or.inr ⟨bool_of_mul_pred _hE2, bool_of_mul_pred _hE2, h_clk⟩,
      Or.inr ⟨bool_of_mul_pred _hE2, (fun hr => by
        obtain ⟨hq0, hq1, hq2, hq3⟩ := a_isU64 hr
        refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
          simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
        exacts [hq0, hq1, hq2, hq3]),
        h_clk.at_four⟩,
      fun h1 h0 => off_gate_vacuous (bool_of_mul_pred _hE2) h1 h0,
      fun h1 h0 => off_gate_vacuous (bool_of_mul_pred _hE2) h1 h0,
      fun h1 h0 => off_gate_vacuous (bool_of_mul_pred _hE2) h1 h0,
      fun h1 h0 => off_gate_vacuous (bool_of_mul_pred _hE2) h1 h0,
      fun h1 h0 => off_gate_vacuous (bool_of_mul_pred _hE2) h1 h0,
      fun h1 h0 => off_gate_vacuous (bool_of_mul_pred _hE2) h1 h0,
      fun h1 h0 => off_gate_vacuous (bool_of_mul_pred _hE2) h1 h0,
      fun h1 h0 => off_gate_vacuous (bool_of_mul_pred _hE2) h1 h0,
      fun h1 h0 => off_gate_vacuous (bool_of_mul_pred _hE2) h1 h0⟩

end SP1Clean.ShiftLeftChip.SoundSll
