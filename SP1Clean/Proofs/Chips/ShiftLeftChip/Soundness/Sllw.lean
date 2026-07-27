import SP1Clean.Proofs.Chips.ShiftLeftChip.Defs
import SP1Clean.Proofs.Chips.ShiftLeftChip.Core
import SP1Clean.Proofs.CircuitProofStart

/-! # `ShiftLeftChip` — sllw conjunct soundness (split out for parallel compilation)

The logical word left-shift (SLLW) conjunct, proved as its own `GeneralFormalCircuit.Soundness` over a
single-conjunct local `Spec`. Re-running `circuit_proof_start` regenerates the monolithic proof's context
(unfolding the local `Spec` and `Assumptions`), so the shared `have a1_bound_cond` setup, the SLLW branch,
and the channel-requirement tail are verbatim slices of the monolith. Kept in a child namespace with the
local `Spec` named exactly `Spec` (so `circuit_proof_start` reduces it). -/

namespace SP1Clean.ShiftLeftChip.SoundSllw

open Circuit
open SP1Clean.Channels (stateChannel byteChannel memoryChannel programChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- `RV64.sllw` bridged to the `HWord` 32-bit shift + sign-extension form that `ShiftLeftCore.sllw_assembly`
concludes. Lifted to a top-level lemma (the `2 ^ N`/`signExtend` reductions kernel-checked once here, off
the inline `soundness` path). -/
lemma sllw_rv64_eq {b c : Word (ZMod p)} (hb : Word.isU64 b) (hc : Word.isU64 c) :
    RV64.sllw (Word.toBitVec64 c) (Word.toBitVec64 b)
      = BitVec.signExtend 64 (HWord.toBitVec32 #v[b[0], b[1]] <<<
          BitVec.setWidth 5 (HWord.toBitVec32 #v[c[0], c[1]])) := by
  simp only [RV64.sllw, ShiftLeftCore.extractLsb32_toBitVec64 hb, ShiftLeftCore.extractLsb5_toBitVec64 hc]

/-- The `sllw` conjunct of `ShiftLeftChip.Spec`, as a standalone single-conjunct spec. -/
def Spec (input : Inputs (ZMod p)) (cols : Columns (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  input.is_real = 1 →
    (cols.is_sllw = 1 →
      Word.toBitVec64 cols.a = RV64.sllw (Word.toBitVec64 input.op_c_val) (Word.toBitVec64 input.op_b_val))

-- term-intrinsic: elaboration exceeds the 200k default (doc "72 heartbeats" was stale); needs a raised
-- ceiling. Candidate for structural masking, not a Phase-1 ratchet.
set_option maxHeartbeats 4000000 in
/-- Soundness of the `sllw` conjunct (verbatim slice of the monolithic proof + the shared tail). -/
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
  -- The SLLW result limb 1 (`a[1] = env.get (i₀+1)`) is 16-bit whenever `is_sllw = 1`. Proved once here
  -- (self-contained from the byte guarantees + placement), reused for the U16MSB sub-assertion's operand
  -- bound in both the SLLW branch and the channel-requirement tail.
  have a1_bound_cond : input_is_sllw = 1 → (env.get (i₀+1)).val < 2 ^ 16 := by
    intro hsllw1
    have hp17 : 131072 < p := by have := Fact.out (p := (2:ℕ)^17 < p); omega
    have h2ne : (2 : ZMod p) ≠ 0 := by
      intro h; have hv := val_2_zmod_p (p := p); rw [h, ZMod.val_zero] at hv; omega
    have hsll0 : input_is_sll = 0 := by
      have e2 := _hE2; rw [hsllw1] at e2
      exact ShiftLeftCore.eq_zero_of_mul_const h2ne (by linear_combination e2 - _hE4)
    have hgate1 : (input_is_sll + input_is_sllw : ZMod p) = 1 := by rw [hsll0, hsllw1, zero_add]
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
  · intro hsllw
    -- branch over a 2-limb (32-bit) word with sign extension (limbs 2,3 = `msb·65535`).
    have hgate1 : (input_is_sll + input_is_sllw : ZMod p) = 1 := by
      have h : (input_is_real - (input_is_sll + input_is_sllw) : ZMod p) = 0 := hrealeq
      rw [hreal] at h
      exact (sub_eq_zero.mp h).symm
    have hsll0 : input_is_sll = 0 := by
      have h : input_is_sll + input_is_sllw = 0 + input_is_sllw := by rw [zero_add, hgate1, hsllw]
      exact add_right_cancel h
    obtain ⟨_, _, _, _, _, _, ⟨hbmem, _, _⟩, _, ⟨hcmem, _, _⟩, _⟩ := h_input
    have heb0 : Expression.eval env input_var_adapter_op_b_memory_prev_value[0] = input_adapter_op_b_memory_prev_value[0] := by
      rw [← hbmem, Vector.getElem_map]
    have heb1 : Expression.eval env input_var_adapter_op_b_memory_prev_value[1] = input_adapter_op_b_memory_prev_value[1] := by
      rw [← hbmem, Vector.getElem_map]
    have heval_c0 : Expression.eval env input_var_adapter_op_c_memory_prev_value[0] =
        input_adapter_op_c_memory_prev_value[0] := by
      rw [← hcmem, Vector.getElem_map]
    have hp17 : 131072 < p := by have := Fact.out (p := (2:ℕ)^17 < p); omega
    -- Power encoding.
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
    have h_diff : ((input_adapter_op_c_memory_prev_value[0] - (env.get (i₀+4) + env.get (i₀+4+1)*2 + env.get (i₀+4+2)*4
        + env.get (i₀+4+3)*8 + env.get (i₀+4+4)*16 + env.get (i₀+4+5)*32)) * (64:ZMod p)⁻¹).val < 1024 := by
      have hb := hbyte1 hneg
      have hbd := (byteRowSpec_range _ (show (10:ℕ) < p by omega)).mp hb
      rw [show (2:ℕ)^10 = 1024 from by norm_num] at hbd
      convert hbd using 3
      rw [heval_c0]; ring
    -- Bit-split (limbs 0,1) + limb_result reassembly + selector reads.
    have hb0dec : input_adapter_op_b_memory_prev_value[0] * env.get (i₀+4+6+2)
        = env.get (i₀+4+6+3+4+4) * ((65536:ℕ):ZMod p) + env.get (i₀+4+6+3+4) * env.get (i₀+4+6+2) := by
      push_cast; linear_combination hsplit0
    have hb1dec : input_adapter_op_b_memory_prev_value[1] * env.get (i₀+4+6+2)
        = env.get (i₀+4+6+3+4+4+1) * ((65536:ℕ):ZMod p) + env.get (i₀+4+6+3+4+1) * env.get (i₀+4+6+2) := by
      push_cast; linear_combination hsplit1
    have hlr0 : env.get (i₀+4+6+3+4+4+4) = env.get (i₀+4+6+3+4) * env.get (i₀+4+6+2) := by
      linear_combination hreass0
    have hlr1 : env.get (i₀+4+6+3+4+4+4+1) = env.get (i₀+4+6+3+4+1) * env.get (i₀+4+6+2) + env.get (i₀+4+6+3+4+4) := by
      linear_combination hreass1
    -- Selectors (byte-shift = `cb4`, since `is_sll = 0`).
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
    -- SLLW placement asserts (gate `is_sllw = 1`).
    rw [hsllw, one_mul] at hw00 hw01 hw10 hw11 hwmsb2 hwmsb3
    -- Bounds for the operand limbs.
    have h_c0_lt : input_adapter_op_c_memory_prev_value[0].val < 65536 := by
      have h := hc_u64 0
      norm_num at h ⊢
      exact h
    have h_c1_lt : input_adapter_op_c_memory_prev_value[1].val < 65536 := by
      have h := hc_u64 1
      norm_num at h ⊢
      exact h
    have h_b0_lt : input_adapter_op_b_memory_prev_value[0].val < 65536 := by have h := hb_u64 0; norm_num at h ⊢; exact h
    have h_b1_lt : input_adapter_op_b_memory_prev_value[1].val < 65536 := by have h := hb_u64 1; norm_num at h ⊢; exact h
    -- The U16MSB operand bound on `a[1]` (reused from `a1_bound_cond`) and the resulting `msb` spec.
    have a1_bound : (env.get (i₀+1)).val < 2 ^ 16 := a1_bound_cond hsllw
    have h_msb_a1 := (hmsb ⟨fun _ => a1_bound, Or.inr hsllw⟩).2 hsllw
    -- Reduce the goal and apply the SLLW assembly.
    have hLHS : Vector.map (Expression.eval env) (Vector.mapRange 4 fun i => var {index := i₀+ i})
        = (#v[env.get i₀, env.get (i₀+1), env.get (i₀+2), env.get (i₀+3)] : Word (ZMod p)) := by
      apply Vector.ext; intro i hi
      simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
      interval_cases i <;> rfl
    rw [hLHS, sllw_rv64_eq hb_u64 hc_u64]
    exact ShiftLeftCore.sllw_assembly S hSle (2^S) (2^(16-S))
      (by rw [← pow_add, Nat.add_sub_cancel' (show S ≤ 16 by omega)]; norm_num) (by positivity) rfl rfl
      hv0123val h_inner (bool_of_mul_pred hcb4b) (bool_of_mul_pred hcb5b)
      h_c0_lt h_c1_lt h_b0_lt h_b1_lt
      (ShiftLeftCore.cb_sum6_val_lt_64 (bool_of_mul_pred hcb0b) (bool_of_mul_pred hcb1b)
        (bool_of_mul_pred hcb2b) (bool_of_mul_pred hcb3b) (bool_of_mul_pred hcb4b) (bool_of_mul_pred hcb5b))
      h_diff hs0sel hs1sel hs2sel hs3sel hssum hb0dec hb1dec hlr0 hlr1
      hll0 hhl0 hll1 hhl1 hw00 hw01 hw10 hw11 h_msb_a1
      (by linear_combination -hwmsb2) (by linear_combination -hwmsb3)
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

end SP1Clean.ShiftLeftChip.SoundSllw
