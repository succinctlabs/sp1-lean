import SP1Clean.Chips.ALU.ShiftRightChip.Lemmas
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import SP1Foundations.ByteOpcode
import SP1Clean.ByteOpcodeTable
import SP1Clean.SP1Lookup
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Operations.U16MSBOperation
import SP1Clean.MemoryAccess
import RISCV.Instructions

/-! # `ShiftRightChip` Clean circuit + `FormalAssertion`

Structural (witness-aware) `main` mirroring `_root_.ShiftRight.allHold_constraints_iff`
conjunct-by-conjunct — the same inline-gate discipline as `ShiftLeftChip`, extended
to the 4-variant right shift (`srl`/`sra`/`srlw`/`sraw`): 3 embedded U16MSB sign
witnesses, the inverse shift-power chain, SRA high-limb propagation gating, and
sign-extension. The shift has no upstream sub-operation, so gates are inline. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftRight

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Extract a `Range` bound from a (real-row) gated byte-opcode lookup.
Mirrors `SP1Clean.ShiftLeft.range_gated_bound`. -/
private lemma range_gated_bound {x bnd mult : ZMod p}
    (h : SP1Lookup.ByteOpcodeGated.Spec ⟨#v[(6 : ZMod p), x, bnd, 0], mult⟩)
    (hmult : mult ≠ 0) :
    x.val < 2 ^ bnd.val := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  rcases h with h0 | ⟨bop, hbop, hconstr⟩
  · exact absurd h0 hmult
  · have h_eq : bop = .Range := by
      have h6 : (6 : ZMod p) = ((6 : ℕ) : ZMod p) := by push_cast; rfl
      simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at hbop
      rw [h6] at hbop
      apply_fun ZMod.val at hbop
      have h_lt : bop.toNat < 7 := by cases bop <;> simp [ByteOpcode.toNat]
      rw [ZMod.val_natCast, ZMod.val_natCast,
          Nat.mod_eq_of_lt (by omega : bop.toNat < p),
          Nat.mod_eq_of_lt (by omega : (6 : ℕ) < p)] at hbop
      cases bop <;> simp [ByteOpcode.toNat] at hbop
      rfl
    subst h_eq
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
               List.getElem_cons_zero, ByteOpcode.constrain_Range] at hconstr
    exact hconstr

omit [Fact (2 ^ 17 < p)] in
/-- Reverse of `range_gated_bound`: build the gated byte-opcode `Spec` from the
`Range` bound. Used for completeness. Mirrors `SP1Clean.ShiftLeft.range_gated_spec`. -/
private lemma range_gated_spec {x bnd mult : ZMod p}
    (h : mult ≠ 0 → x.val < 2 ^ bnd.val) :
    SP1Lookup.ByteOpcodeGated.Spec ⟨#v[(6 : ZMod p), x, bnd, 0], mult⟩ := by
  by_cases hm : mult = 0
  · exact Or.inl hm
  · refine Or.inr ⟨.Range, ?_, ?_⟩
    · simp only [ByteOpcode.toNat, Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, Nat.cast_ofNat]
    · simp only [ByteOpcode.constrain_Range, Vector.getElem_mk, List.getElem_toArray,
                 List.getElem_cons_zero, List.getElem_cons_succ]
      exact h hm

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var ShiftRightCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter, op_a_write_value,
       b_msb, srw_msb, c_bits, sra_msb_v0123, v_0123, v_012, v_01,
       lower_limb, higher_limb, limb_result, shift_u16,
       is_srl, is_sra, is_srlw, is_sraw, is_w_imm, adapter_cols⟩ := cols
  -- Bind vector elements to named locals (lets the binop elaborator coerce
  -- numeral literals to `Expression (ZMod p)` — it does not anchor through `getElem`).
  let cb0 := c_bits[0]; let cb1 := c_bits[1]; let cb2 := c_bits[2]
  let cb3 := c_bits[3]; let cb4 := c_bits[4]; let cb5 := c_bits[5]
  let r0 := op_a_write_value[0]; let r1 := op_a_write_value[1]
  let r2 := op_a_write_value[2]; let r3 := op_a_write_value[3]
  let s0 := shift_u16[0]; let s1 := shift_u16[1]; let s2 := shift_u16[2]; let s3 := shift_u16[3]
  let ll0 := lower_limb[0]; let ll1 := lower_limb[1]
  let ll2 := lower_limb[2]; let ll3 := lower_limb[3]
  let hl0 := higher_limb[0]; let hl1 := higher_limb[1]
  let hl2 := higher_limb[2]; let hl3 := higher_limb[3]
  let lr0 := limb_result[0]; let lr1 := limb_result[1]
  let lr2 := limb_result[2]; let lr3 := limb_result[3]
  let ob0 := adapter.op_b_memory.prev_value[0]; let ob1 := adapter.op_b_memory.prev_value[1]
  let ob2 := adapter.op_b_memory.prev_value[2]; let ob3 := adapter.op_b_memory.prev_value[3]
  let oc0 := adapter.op_c_memory.prev_value[0]
  let bmsb := b_msb.msb
  let smsb := srw_msb.msb
  let is_real : Expression (ZMod p) := is_srl + is_sra + is_srlw + is_sraw
  let opcode_e : Expression (ZMod p) := is_srl * 7 + is_sra * 8 + is_srlw * 22 + is_sraw * 23
  let clk_low : Expression (ZMod p) := clk_0_16 + clk_16_24 * 65536
  let c6 : Expression (ZMod p) := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
  let c4 : Expression (ZMod p) := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8
  let sel : Expression (ZMod p) := cb4 + cb5 * 2 * (is_srl + is_sra)
  -- 1. U16MSB sign witness: SRA on op_b high limb (ob3), gate is_sra.
  is_sra * (is_sra - 1) === 0
  bmsb * (bmsb - 1) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), 2 * ob3 - bmsb * 65536, 16, 0], is_sra⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  -- 2. U16MSB sign witness: SRAW on op_b mid limb (ob1), gate is_sraw.
  is_sraw * (is_sraw - 1) === 0
  bmsb * (bmsb - 1) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), 2 * ob1 - bmsb * 65536, 16, 0], is_sraw⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  -- 3. U16MSB sign witness: SRLW/SRAW on result high limb (r1), gate is_srlw+is_sraw.
  (is_srlw + is_sraw) * ((is_srlw + is_sraw) - 1) === 0
  smsb * (smsb - 1) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), 2 * r1 - smsb * 65536, 16, 0], is_srlw + is_sraw⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  -- CPUState + ALUTypeReader (gated readers).
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, #v[pc[0] + 4, pc[1], pc[2]], 8, is_real⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.Gated.assertion
    (⟨clk_high, clk_low, opcode_e, pc, op_a_write_value, adapter, is_real,
      adapter_cols.is_trusted⟩ :
      Var SP1Clean.ALUTypeReader.Gated.Inputs (ZMod p))
  -- Selector binaries.
  is_srl * (is_srl - 1) === 0
  is_sra * (is_sra - 1) === 0
  is_srlw * (is_srlw - 1) === 0
  is_sraw * (is_sraw - 1) === 0
  is_real * (is_real - 1) === 0
  -- is_w_imm bridge.
  (is_w_imm - (is_srlw + is_sraw) * adapter.imm_c) === 0
  -- 6-bit shift decomposition binaries.
  cb0 * (cb0 - 1) === 0
  cb1 * (cb1 - 1) === 0
  cb2 * (cb2 - 1) === 0
  cb3 * (cb3 - 1) === 0
  cb4 * (cb4 - 1) === 0
  cb5 * (cb5 - 1) === 0
  -- Within-shift bound: (c0 - low6)·64⁻¹ < 2^10 (gated Range).
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), (oc0 - c6) * Expression.const (64 : ZMod p)⁻¹, 10, 0], is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  -- 4-way byte-shift one-hot selector (product gates) + binaries + sum.
  s0 * sel === 0
  s0 * (s0 - 1) === 0
  s1 * (sel - 1) === 0
  s1 * (s1 - 1) === 0
  s2 * (sel - 2) === 0
  s2 * (s2 - 1) === 0
  s3 * (sel - 3) === 0
  s3 * (s3 - 1) === 0
  is_real * (s0 + s1 + s2 + s3 - 1) === 0
  -- Shift-power chain (inverse: uses `1 - cb_i`).
  (v_01 - (1 - cb0 + 1) * 2 * ((1 - cb1) * 3 + 1)) === 0
  (v_012 - v_01 * ((1 - cb2) * 15 + 1)) === 0
  (v_0123 - v_012 * ((1 - cb3) * 255 + 1)) === 0
  -- Per-limb shift decompositions + bounds (gated Range); limbs 2,3 carry the
  -- `(is_srl + is_sra)` SRA-propagation factor on the op_b identity.
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), ll0, c4, 0], is_real⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), hl0, 16 - c4, 0], is_real⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  (ob0 * v_0123 - (hl0 * 65536 + ll0 * v_0123)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), ll1, c4, 0], is_real⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), hl1, 16 - c4, 0], is_real⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  (ob1 * v_0123 - (hl1 * 65536 + ll1 * v_0123)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), ll2, c4, 0], is_real⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), hl2, 16 - c4, 0], is_real⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  (ob2 * v_0123 * (is_srl + is_sra) - (hl2 * 65536 + ll2 * v_0123)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), ll3, c4, 0], is_real⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), hl3, 16 - c4, 0], is_real⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  (ob3 * v_0123 * (is_srl + is_sra) - (hl3 * 65536 + ll3 * v_0123)) === 0
  -- limb_result wiring.
  (lr0 - (hl0 + ll1 * v_0123)) === 0
  (lr1 - (hl1 + ll2 * v_0123)) === 0
  (lr2 - (hl2 + ll3 * v_0123)) === 0
  (lr3 - hl3) === 0
  -- Sign-witness gates.
  (is_srl + is_srlw) * bmsb === 0
  (sra_msb_v0123 - bmsb * v_0123) === 0
  ((is_srlw + is_sraw) - 1) * smsb === 0
  -- 16 SR (srl/sra) gated output equations: gated by (is_srl + is_sra) × shift_u16.
  (is_srl + is_sra) * (s0 * (r0 - lr0)) === 0
  (is_srl + is_sra) * (s0 * (r1 - lr1)) === 0
  (is_srl + is_sra) * (s0 * (r2 - lr2)) === 0
  (is_srl + is_sra) * (s0 * (r3 - (lr3 + (bmsb * 65536 - sra_msb_v0123)))) === 0
  (is_srl + is_sra) * (s1 * (r0 - lr1)) === 0
  (is_srl + is_sra) * (s1 * (r1 - lr2)) === 0
  (is_srl + is_sra) * (s1 * (r2 - (lr3 + (bmsb * 65536 - sra_msb_v0123)))) === 0
  (is_srl + is_sra) * (s1 * (r3 - bmsb * 65535)) === 0
  (is_srl + is_sra) * (s2 * (r0 - lr2)) === 0
  (is_srl + is_sra) * (s2 * (r1 - (lr3 + (bmsb * 65536 - sra_msb_v0123)))) === 0
  (is_srl + is_sra) * (s2 * (r2 - bmsb * 65535)) === 0
  (is_srl + is_sra) * (s2 * (r3 - bmsb * 65535)) === 0
  (is_srl + is_sra) * (s3 * (r0 - (lr3 + (bmsb * 65536 - sra_msb_v0123)))) === 0
  (is_srl + is_sra) * (s3 * (r1 - bmsb * 65535)) === 0
  (is_srl + is_sra) * (s3 * (r2 - bmsb * 65535)) === 0
  (is_srl + is_sra) * (s3 * (r3 - bmsb * 65535)) === 0
  -- 6 SRW (srlw/sraw) gated output equations.
  (is_srlw + is_sraw) * (s0 * (r0 - lr0)) === 0
  (is_srlw + is_sraw) * (s0 * (r1 - (lr1 + (bmsb * 65536 - sra_msb_v0123)))) === 0
  (is_srlw + is_sraw) * (s1 * (r0 - (lr1 + (bmsb * 65536 - sra_msb_v0123)))) === 0
  (is_srlw + is_sraw) * (s1 * (r1 - bmsb * 65535)) === 0
  (is_srlw + is_sraw) * (r2 - smsb * 65535) === 0
  (is_srlw + is_sraw) * (r3 - smsb * 65535) === 0
  -- op_a_0.
  adapter.op_a_0 === 0

set_option maxHeartbeats 2000000 in
-- ~90 inline gates + 2 readers + 17 gated lookups; consistency synthesis
-- exceeds default cap (precedent: ShiftLeft scaffold, scaled up).
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) ShiftRightCols unit where
  name := "SP1Clean.ShiftRight"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp (config := { arith := true, maxSteps := 1000000 }) only [main, circuit_norm]

def Assumptions (cols : ShiftRightCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted =
    cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw ∧
  cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw = 1

set_option maxHeartbeats 2000000 in
-- 78-conjunct refine over the ~75-conjunct structural FormalSpec (3 U16MSB
-- blocks + 2 gated readers + ~70 inline gates) exceeds the default cap.
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e_ckh, e_c1624, e_c016, e_pc⟩,
      ⟨e_opa, ⟨e_opapv, e_opapl, e_opadll⟩, e_opa0, e_opb,
        ⟨e_opbpv, e_opbpl, e_opbdll⟩, e_opc, ⟨e_opcpv, e_opcpl, e_opcdll⟩, e_immc⟩,
      e_oawv, e_bmsb, e_smsb, e_cbits, e_srav, e_v0123, e_v012, e_v01,
      e_lower, e_higher, e_limbresult, e_shiftu16,
      e_issrl, e_issra, e_issrlw, e_issraw, e_iswimm, e_istrusted⟩ := h_input
  subst_eqs
  obtain ⟨h_trusted, h_sum⟩ := h_assumptions
  simp only [FormalSpec, Vector.getElem_map]
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  haveI : Fact (p > 65536) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_sra_bin1, h_bmsb1, h_u16rng1, h_sraw_bin1, h_bmsb2, h_u16rng2,
    h_srw_bin, h_smsb, h_u16rng3, h_cpu, h_alu,
    h_srlbin, h_srabin, h_srlwbin, h_srawbin, h_realbin, h_iswimm,
    h_cb0, h_cb1, h_cb2, h_cb3, h_cb4, h_cb5, h_within,
    h_s0sel, h_s0bin, h_s1sel, h_s1bin, h_s2sel, h_s2bin, h_s3sel, h_s3bin, h_ssum,
    h_v01, h_v012, h_v0123, h_ll0, h_hl0, h_ob0, h_ll1, h_hl1, h_ob1,
    h_ll2, h_hl2, h_ob2, h_ll3, h_hl3, h_ob3, h_lr0, h_lr1, h_lr2, h_lr3,
    h_bmsbgate, h_sramsb, h_srwgate,
    h_o0, h_o1, h_o2, h_o3, h_o4, h_o5, h_o6, h_o7, h_o8, h_o9, h_o10, h_o11,
    h_o12, h_o13, h_o14, h_o15, h_w0, h_w1, h_w2, h_w3, h_w4, h_w5,
    h_opa0⟩ := h_holds
  unfold id at *
  refine ⟨⟨by linear_combination h_sra_bin1, by linear_combination h_bmsb1,
      fun h_ne => ?_⟩,
    ⟨by linear_combination h_sraw_bin1, by linear_combination h_bmsb2,
      fun h_ne => ?_⟩,
    ⟨by linear_combination h_srw_bin, by linear_combination h_smsb,
      fun h_ne => ?_⟩,
    h_cpu trivial, h_alu trivial,
    (mul_add_neg_one_eq_zero_iff _).mp h_srlbin,
    (mul_add_neg_one_eq_zero_iff _).mp h_srabin,
    (mul_add_neg_one_eq_zero_iff _).mp h_srlwbin,
    (mul_add_neg_one_eq_zero_iff _).mp h_srawbin,
    (mul_add_neg_one_eq_zero_iff _).mp h_realbin,
    by linear_combination h_iswimm,
    (mul_add_neg_one_eq_zero_iff _).mp h_cb0,
    (mul_add_neg_one_eq_zero_iff _).mp h_cb1,
    (mul_add_neg_one_eq_zero_iff _).mp h_cb2,
    (mul_add_neg_one_eq_zero_iff _).mp h_cb3,
    (mul_add_neg_one_eq_zero_iff _).mp h_cb4,
    (mul_add_neg_one_eq_zero_iff _).mp h_cb5,
    fun h_ne => ?_,
    mul_eq_zero.mp h_s0sel,
    (mul_add_neg_one_eq_zero_iff _).mp h_s0bin,
    (mul_eq_zero.mp h_s1sel).imp id (fun h => by linear_combination h),
    (mul_add_neg_one_eq_zero_iff _).mp h_s1bin,
    (mul_eq_zero.mp h_s2sel).imp id (fun h => by linear_combination h),
    (mul_add_neg_one_eq_zero_iff _).mp h_s2bin,
    (mul_eq_zero.mp h_s3sel).imp id (fun h => by linear_combination h),
    (mul_add_neg_one_eq_zero_iff _).mp h_s3bin,
    (mul_eq_zero.mp h_ssum).imp id (fun h => by linear_combination h),
    by linear_combination h_v01,
    by linear_combination h_v012,
    by linear_combination h_v0123,
    fun h_ne => ?_,
    fun h_ne => ?_,
    by push_cast; linear_combination h_ob0,
    fun h_ne => ?_,
    fun h_ne => ?_,
    by push_cast; linear_combination h_ob1,
    fun h_ne => ?_,
    fun h_ne => ?_,
    by push_cast; linear_combination h_ob2,
    fun h_ne => ?_,
    fun h_ne => ?_,
    by push_cast; linear_combination h_ob3,
    by linear_combination h_lr0,
    by linear_combination h_lr1,
    by linear_combination h_lr2,
    by linear_combination h_lr3,
    mul_eq_zero.mp h_bmsbgate,
    by linear_combination h_sramsb,
    (mul_eq_zero.mp h_srwgate).imp (fun h => by linear_combination h) id,
    (mul_eq_zero.mp h_o0).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o1).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o2).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o3).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o4).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o5).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o6).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o7).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o8).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o9).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o10).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o11).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o12).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o13).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o14).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o15).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_w0).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_w1).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_w2).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_w3).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_w4).imp id (fun h => by linear_combination h),
    (mul_eq_zero.mp h_w5).imp id (fun h => by linear_combination h),
    h_opa0⟩
  · -- block1 range (SRA, ob3, bound 16)
    have hb := range_gated_bound (h_u16rng1 trivial) h_ne
    have h16 : (16 : ZMod p).val = 16 := by
      rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
    rw [h16] at hb
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using hb
  · -- block2 range (SRAW, ob1, bound 16)
    have hb := range_gated_bound (h_u16rng2 trivial) h_ne
    have h16 : (16 : ZMod p).val = 16 := by
      rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
    rw [h16] at hb
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using hb
  · -- block3 range (SRLW/SRAW, r1, bound 16)
    have hb := range_gated_bound (h_u16rng3 trivial) h_ne
    have h16 : (16 : ZMod p).val = 16 := by
      rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
    rw [h16] at hb
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using hb
  · -- within-shift bound
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_within trivial) h_ne
  · -- lower_limb[0]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_ll0 trivial) h_ne
  · -- higher_limb[0]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_hl0 trivial) h_ne
  · -- lower_limb[1]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_ll1 trivial) h_ne
  · -- higher_limb[1]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_hl1 trivial) h_ne
  · -- lower_limb[2]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_ll2 trivial) h_ne
  · -- higher_limb[2]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_hl2 trivial) h_ne
  · -- lower_limb[3]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_ll3 trivial) h_ne
  · -- higher_limb[3]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_hl3 trivial) h_ne

set_option maxHeartbeats 2000000 in
-- 78-conjunct refine reconstructing the inline gates from the structural
-- FormalSpec; exceeds the default cap (same scale as `soundness`).
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e_ckh, e_c1624, e_c016, e_pc⟩,
      ⟨e_opa, ⟨e_opapv, e_opapl, e_opadll⟩, e_opa0, e_opb,
        ⟨e_opbpv, e_opbpl, e_opbdll⟩, e_opc, ⟨e_opcpv, e_opcpl, e_opcdll⟩, e_immc⟩,
      e_oawv, e_bmsb, e_smsb, e_cbits, e_srav, e_v0123, e_v012, e_v01,
      e_lower, e_higher, e_limbresult, e_shiftu16,
      e_issrl, e_issra, e_issrlw, e_issraw, e_iswimm, e_istrusted⟩ := h_input
  subst_eqs
  obtain ⟨h_trusted, h_sum⟩ := h_assumptions
  unfold id at *
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  haveI : Fact (p > 65536) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [FormalSpec, Vector.getElem_map] at h_spec
  obtain ⟨⟨h_sra_bin_s, h_bmsb_bin_s, h_range1_s⟩,
    ⟨h_sraw_bin_s, h_bmsb_bin2_s, h_range2_s⟩,
    ⟨h_srw_bin_s, h_smsb_bin_s, h_range3_s⟩, h_cpu_s, h_alu_s,
    h_srl_or, h_sra_or, h_srlw_or, h_sraw_or, h_real_or, h_iswimm_s,
    h_cb0_or, h_cb1_or, h_cb2_or, h_cb3_or, h_cb4_or, h_cb5_or, h_within_s,
    h_s0sel_s, h_s0_or, h_s1sel_s, h_s1_or, h_s2sel_s, h_s2_or, h_s3sel_s, h_s3_or,
    h_ssum_s, h_v01_s, h_v012_s, h_v0123_s, h_ll0_s, h_hl0_s, h_ob0_s,
    h_ll1_s, h_hl1_s, h_ob1_s, h_ll2_s, h_hl2_s, h_ob2_s, h_ll3_s, h_hl3_s, h_ob3_s,
    h_lr0_s, h_lr1_s, h_lr2_s, h_lr3_s, h_bmsbgate_s, h_sramsb_s, h_srwgate_s,
    h_o0_s, h_o1_s, h_o2_s, h_o3_s, h_o4_s, h_o5_s, h_o6_s, h_o7_s, h_o8_s, h_o9_s,
    h_o10_s, h_o11_s, h_o12_s, h_o13_s, h_o14_s, h_o15_s,
    h_w0_s, h_w1_s, h_w2_s, h_w3_s, h_w4_s, h_w5_s, h_opa0_s⟩ := h_spec
  refine ⟨by linear_combination h_sra_bin_s, by linear_combination h_bmsb_bin_s,
    ⟨trivial, range_gated_spec (fun hm => by
      have hh := h_range1_s hm
      have h16 : (16 : ZMod p).val = 16 := by
        rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
      rw [h16]
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using hh)⟩,
    by linear_combination h_sraw_bin_s, by linear_combination h_bmsb_bin2_s,
    ⟨trivial, range_gated_spec (fun hm => by
      have hh := h_range2_s hm
      have h16 : (16 : ZMod p).val = 16 := by
        rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
      rw [h16]
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using hh)⟩,
    by linear_combination h_srw_bin_s, by linear_combination h_smsb_bin_s,
    ⟨trivial, range_gated_spec (fun hm => by
      have hh := h_range3_s hm
      have h16 : (16 : ZMod p).val = 16 := by
        rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
      rw [h16]
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using hh)⟩,
    ⟨trivial, h_cpu_s⟩, ⟨trivial, h_alu_s⟩,
    by rcases h_srl_or with h | h <;> rw [h] <;> ring,
    by rcases h_sra_or with h | h <;> rw [h] <;> ring,
    by rcases h_srlw_or with h | h <;> rw [h] <;> ring,
    by rcases h_sraw_or with h | h <;> rw [h] <;> ring,
    by rcases h_real_or with h | h <;> rw [h] <;> ring,
    by linear_combination h_iswimm_s,
    by rcases h_cb0_or with h | h <;> rw [h] <;> ring,
    by rcases h_cb1_or with h | h <;> rw [h] <;> ring,
    by rcases h_cb2_or with h | h <;> rw [h] <;> ring,
    by rcases h_cb3_or with h | h <;> rw [h] <;> ring,
    by rcases h_cb4_or with h | h <;> rw [h] <;> ring,
    by rcases h_cb5_or with h | h <;> rw [h] <;> ring,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_within_s hm)⟩,
    by rcases h_s0sel_s with h | h <;> rw [h] <;> ring,
    by rcases h_s0_or with h | h <;> rw [h] <;> ring,
    by rcases h_s1sel_s with h | h <;> rw [h] <;> ring,
    by rcases h_s1_or with h | h <;> rw [h] <;> ring,
    by rcases h_s2sel_s with h | h <;> rw [h] <;> ring,
    by rcases h_s2_or with h | h <;> rw [h] <;> ring,
    by rcases h_s3sel_s with h | h <;> rw [h] <;> ring,
    by rcases h_s3_or with h | h <;> rw [h] <;> ring,
    by rcases h_ssum_s with h | h <;> rw [h] <;> ring,
    by linear_combination h_v01_s,
    by linear_combination h_v012_s,
    by linear_combination h_v0123_s,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_ll0_s hm)⟩,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_hl0_s hm)⟩,
    by linear_combination h_ob0_s,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_ll1_s hm)⟩,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_hl1_s hm)⟩,
    by linear_combination h_ob1_s,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_ll2_s hm)⟩,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_hl2_s hm)⟩,
    by linear_combination h_ob2_s,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_ll3_s hm)⟩,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_hl3_s hm)⟩,
    by linear_combination h_ob3_s,
    by linear_combination h_lr0_s,
    by linear_combination h_lr1_s,
    by linear_combination h_lr2_s,
    by linear_combination h_lr3_s,
    by rcases h_bmsbgate_s with h | h <;> rw [h] <;> ring,
    by linear_combination h_sramsb_s,
    by rcases h_srwgate_s with h | h <;> rw [h] <;> ring,
    by rcases h_o0_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o1_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o2_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o3_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o4_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o5_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o6_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o7_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o8_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o9_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o10_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o11_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o12_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o13_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o14_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_o15_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_w0_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_w1_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_w2_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_w3_s with h | h | h <;> rw [h] <;> ring,
    by rcases h_w4_s with h | h <;> rw [h] <;> ring,
    by rcases h_w5_s with h | h <;> rw [h] <;> ring,
    h_opa0_s⟩

end Assertion

def assertion : FormalAssertion (ZMod p) ShiftRightCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftRight
