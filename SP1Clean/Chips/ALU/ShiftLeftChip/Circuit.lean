import SP1Clean.Chips.ALU.ShiftLeftChip.Lemmas
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

/-! # `ShiftLeftChip` Clean circuit + `FormalAssertion`

Path-2 main lifted from `Aggregate.lean`. Soundness/completeness
sorry'd pending an operation-level bridge (Shift operation is
inline-only — no separate module). -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.ShiftLeft

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Extract a `Range` bound from a (real-row) gated byte-opcode lookup:
`ByteOpcodeGated.Spec ⟨#v[6, x, bnd, 0], mult⟩` with `mult ≠ 0` forces the
witnessed opcode to be `Range`, giving `x.val < 2 ^ bnd.val`. Mirrors
`SP1Clean.OperandAccess.byteOpcodeSpec_range16` but keeps `bnd` symbolic. -/
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
/-- Reverse of `range_gated_bound`: build the gated byte-opcode `Spec`
(`mult = 0 ∨ ByteOpcodeSpec …`) from the `Range` bound. Used for completeness. -/
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
def main (cols : Var ShiftLeftCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, adapter, result,
       c_bits, v_01, v_012, v_0123, shift_u16,
       lower_limb, higher_limb, limb_result, sllw_msb,
       is_sll, is_sllw, is_sllw_imm, adapter_cols⟩ := cols
  -- Bind vector elements to named locals (lets the binop elaborator coerce
  -- numeral literals to `Expression (ZMod p)` — it does not anchor through `getElem`).
  let cb0 := c_bits[0]; let cb1 := c_bits[1]; let cb2 := c_bits[2]
  let cb3 := c_bits[3]; let cb4 := c_bits[4]; let cb5 := c_bits[5]
  let r0 := result[0]; let r1 := result[1]; let r2 := result[2]; let r3 := result[3]
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
  let msb := sllw_msb.msb
  let sum : Expression (ZMod p) := is_sll + is_sllw
  let opcode_e : Expression (ZMod p) := is_sll * 6 + is_sllw * 21
  let clk_low : Expression (ZMod p) := clk_0_16 + clk_16_24 * 65536
  let c6 : Expression (ZMod p) := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8 + cb4 * 16 + cb5 * 32
  let c4 : Expression (ZMod p) := cb0 + cb1 * 2 + cb2 * 4 + cb3 * 8
  let sel : Expression (ZMod p) := cb4 + cb5 * 2 * is_sll
  -- U16MSB (inline faithful): unconditional msb-binary + gated Range-16.
  msb * (msb - 1) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), 2 * r1 - msb * 65536, 16, 0], is_sllw⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  -- CPUState + ALUTypeReader (gated readers).
  SP1Clean.CPUState.Gated.assertion
    (⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩, #v[pc[0] + 4, pc[1], pc[2]], 8, sum⟩ :
      Var SP1Clean.CPUState.Gated.Inputs (ZMod p))
  SP1Clean.ALUTypeReader.Gated.assertion
    (⟨clk_high, clk_low, opcode_e, pc, result, adapter, sum, adapter_cols.is_trusted⟩ :
      Var SP1Clean.ALUTypeReader.Gated.Inputs (ZMod p))
  -- Selector binaries.
  sum * (sum - 1) === 0
  is_sll * (is_sll - 1) === 0
  is_sllw * (is_sllw - 1) === 0
  -- 6-bit shift decomposition binaries.
  cb0 * (cb0 - 1) === 0
  cb1 * (cb1 - 1) === 0
  cb2 * (cb2 - 1) === 0
  cb3 * (cb3 - 1) === 0
  cb4 * (cb4 - 1) === 0
  cb5 * (cb5 - 1) === 0
  -- Within-shift bound: (c - low6)·64⁻¹ < 2^10 (gated Range).
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), (oc0 - c6) * Expression.const (64 : ZMod p)⁻¹, 10, 0], sum⟩ :
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
  sum * (s0 + s1 + s2 + s3 - 1) === 0
  -- Shift-power chain.
  (v_01 - (cb0 + 1) * (cb1 * 3 + 1)) === 0
  (v_012 - v_01 * (cb2 * 15 + 1)) === 0
  (v_0123 - v_012 * (cb3 * 255 + 1)) === 0
  -- Per-limb shift decompositions + bounds (gated Range).
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), ll0, 16 - c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), hl0, c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  (ob0 * v_0123 - (hl0 * 65536 + ll0 * v_0123)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), ll1, 16 - c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), hl1, c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  (ob1 * v_0123 - (hl1 * 65536 + ll1 * v_0123)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), ll2, 16 - c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), hl2, c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  (ob2 * v_0123 - (hl2 * 65536 + ll2 * v_0123)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), ll3, 16 - c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), hl3, c4, 0], sum⟩ : Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  (ob3 * v_0123 - (hl3 * 65536 + ll3 * v_0123)) === 0
  -- limb_result wiring.
  (lr0 - ll0 * v_0123) === 0
  (lr1 - (ll1 * v_0123 + hl0)) === 0
  (lr2 - (ll2 * v_0123 + hl1)) === 0
  (lr3 - (ll3 * v_0123 + hl2)) === 0
  -- SLL output equations (16, gated by is_sll · shift_u16[k]).
  is_sll * (s0 * (r0 - lr0)) === 0
  is_sll * (s0 * (r1 - lr1)) === 0
  is_sll * (s0 * (r2 - lr2)) === 0
  is_sll * (s0 * (r3 - lr3)) === 0
  is_sll * (s1 * r0) === 0
  is_sll * (s1 * (r1 - lr0)) === 0
  is_sll * (s1 * (r2 - lr1)) === 0
  is_sll * (s1 * (r3 - lr2)) === 0
  is_sll * (s2 * r0) === 0
  is_sll * (s2 * r1) === 0
  is_sll * (s2 * (r2 - lr0)) === 0
  is_sll * (s2 * (r3 - lr1)) === 0
  is_sll * (s3 * r0) === 0
  is_sll * (s3 * r1) === 0
  is_sll * (s3 * r2) === 0
  is_sll * (s3 * (r3 - lr0)) === 0
  -- SLLW output equations (6, gated by is_sllw · shift_u16[k]; sign-extend high limbs).
  is_sllw * (s0 * (r0 - lr0)) === 0
  is_sllw * (s0 * (r1 - lr1)) === 0
  is_sllw * (s1 * r0) === 0
  is_sllw * (s1 * (r1 - lr0)) === 0
  is_sllw * (msb * 65535 - r2) === 0
  is_sllw * (msb * 65535 - r3) === 0
  -- is_sllw_imm bridge + op_a_0.
  (is_sllw_imm - is_sllw * adapter.imm_c) === 0
  adapter.op_a_0 === 0

set_option maxHeartbeats 1600000 in
-- ~60 inline gates + 2 readers + 11 gated lookups; consistency synthesis
-- exceeds default cap (precedent: LtChip / MulChip / Multiplicity scaffold).
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) ShiftLeftCols unit where
  name := "SP1Clean.ShiftLeft"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

def Assumptions (cols : ShiftLeftCols (ZMod p)) : Prop :=
  cols.adapter_cols.is_trusted = cols.is_sll + cols.is_sllw ∧
  cols.is_sll + cols.is_sllw = 1

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e_ckh, e_c1624, e_c016, e_pc⟩,
      ⟨e_opa, ⟨e_opapv, e_opapl, e_opadll⟩, e_opa0, e_opb,
        ⟨e_opbpv, e_opbpl, e_opbdll⟩, e_opc, ⟨e_opcpv, e_opcpl, e_opcdll⟩, e_immc⟩,
      e_result, e_cbits, e_v01, e_v012, e_v0123, e_shiftu16, e_lower, e_higher,
      e_limbresult, e_sllwmsb, e_issll, e_issllw, e_issllwimm, e_istrusted⟩ := h_input
  subst_eqs
  obtain ⟨h_trusted, h_sum⟩ := h_assumptions
  simp only [FormalSpec, Vector.getElem_map]
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  haveI : Fact (p > 65536) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_msbbin, h_u16rng, h_cpu, h_alu, h_sumbin, h_sllbin, h_sllwbin,
    h_cb0, h_cb1, h_cb2, h_cb3, h_cb4, h_cb5, h_within, h_s0sel, h_s0bin,
    h_s1sel, h_s1bin, h_s2sel, h_s2bin, h_s3sel, h_s3bin, h_ssum,
    h_v01, h_v012, h_v0123, h_ll0, h_hl0, h_ob0, h_ll1, h_hl1, h_ob1,
    h_ll2, h_hl2, h_ob2, h_ll3, h_hl3, h_ob3, h_lr0, h_lr1, h_lr2, h_lr3,
    h_o0, h_o1, h_o2, h_o3, h_o4, h_o5, h_o6, h_o7, h_o8, h_o9, h_o10, h_o11,
    h_o12, h_o13, h_o14, h_o15, h_w0, h_w1, h_w2, h_w3, h_w4, h_w5,
    h_immeq, h_opa0⟩ := h_holds
  unfold id at *
  refine ⟨⟨by linear_combination h_sllwbin, by linear_combination h_msbbin,
      fun h_ne => ?_⟩,
    h_cpu trivial, h_alu trivial,
    (mul_add_neg_one_eq_zero_iff _).mp h_sumbin,
    (mul_add_neg_one_eq_zero_iff _).mp h_sllbin,
    (mul_add_neg_one_eq_zero_iff _).mp h_sllwbin,
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
    (mul_eq_zero.mp h_o0).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o1).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o2).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o3).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o4).imp id (fun h => mul_eq_zero.mp h),
    (mul_eq_zero.mp h_o5).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o6).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o7).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o8).imp id (fun h => mul_eq_zero.mp h),
    (mul_eq_zero.mp h_o9).imp id (fun h => mul_eq_zero.mp h),
    (mul_eq_zero.mp h_o10).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o11).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_o12).imp id (fun h => mul_eq_zero.mp h),
    (mul_eq_zero.mp h_o13).imp id (fun h => mul_eq_zero.mp h),
    (mul_eq_zero.mp h_o14).imp id (fun h => mul_eq_zero.mp h),
    (mul_eq_zero.mp h_o15).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_w0).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_w1).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_w2).imp id (fun h => mul_eq_zero.mp h),
    (mul_eq_zero.mp h_w3).imp id (fun h => (mul_eq_zero.mp h).imp id (fun h' => by linear_combination h')),
    (mul_eq_zero.mp h_w4).imp id (fun h => by linear_combination h),
    (mul_eq_zero.mp h_w5).imp id (fun h => by linear_combination h),
    by linear_combination h_immeq,
    h_opa0⟩
  · -- g1c: U16MSB sign-witness range (bound 16 → < 65536)
    have hb := range_gated_bound (h_u16rng trivial) h_ne
    have h16 : (16 : ZMod p).val = 16 := by
      have hp : 2 ^ 17 < p := Fact.out
      rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [h16] at hb
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using hb
  · -- g13: within-shift bound
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_within trivial) h_ne
  · -- g26: lower_limb[0]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_ll0 trivial) h_ne
  · -- g27: higher_limb[0]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_hl0 trivial) h_ne
  · -- g29: lower_limb[1]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_ll1 trivial) h_ne
  · -- g30: higher_limb[1]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_hl1 trivial) h_ne
  · -- g32: lower_limb[2]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_ll2 trivial) h_ne
  · -- g33: higher_limb[2]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_hl2 trivial) h_ne
  · -- g35: lower_limb[3]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_ll3 trivial) h_ne
  · -- g36: higher_limb[3]
    simpa only [sub_eq_add_neg, Nat.cast_ofNat] using range_gated_bound (h_hl3 trivial) h_ne

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e_ckh, e_c1624, e_c016, e_pc⟩,
      ⟨e_opa, ⟨e_opapv, e_opapl, e_opadll⟩, e_opa0, e_opb,
        ⟨e_opbpv, e_opbpl, e_opbdll⟩, e_opc, ⟨e_opcpv, e_opcpl, e_opcdll⟩, e_immc⟩,
      e_result, e_cbits, e_v01, e_v012, e_v0123, e_shiftu16, e_lower, e_higher,
      e_limbresult, e_sllwmsb, e_issll, e_issllw, e_issllwimm, e_istrusted⟩ := h_input
  subst_eqs
  obtain ⟨h_trusted, h_sum⟩ := h_assumptions
  unfold id at *
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  haveI : Fact (p > 65536) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [FormalSpec, Vector.getElem_map] at h_spec
  obtain ⟨⟨_h_sllw_bin, h_msb_bin, h_u16range⟩, h_cpu, h_alu, h_sum_or, h_sll_or, h_sllw_or,
    h_cb0_or, h_cb1_or, h_cb2_or, h_cb3_or, h_cb4_or, h_cb5_or, h_within,
    h_s0sel, h_s0_or, h_s1sel, h_s1_or, h_s2sel, h_s2_or, h_s3sel, h_s3_or,
    h_ssum, h_v01, h_v012, h_v0123, h_ll0, h_hl0, h_ob0, h_ll1, h_hl1, h_ob1,
    h_ll2, h_hl2, h_ob2, h_ll3, h_hl3, h_ob3, h_lr0, h_lr1, h_lr2, h_lr3,
    h_o0, h_o1, h_o2, h_o3, h_o4, h_o5, h_o6, h_o7, h_o8, h_o9, h_o10, h_o11,
    h_o12, h_o13, h_o14, h_o15, h_w0, h_w1, h_w2, h_w3, h_w4, h_w5,
    h_immeq, h_opa0⟩ := h_spec
  refine ⟨by linear_combination h_msb_bin,
    ⟨trivial, range_gated_spec (fun hm => by
      have hh := h_u16range hm
      have h16 : (16 : ZMod p).val = 16 := by
        rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
      rw [h16]
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using hh)⟩,
    ⟨trivial, h_cpu⟩, ⟨trivial, h_alu⟩,
    by rcases h_sum_or with h | h <;> rw [h] <;> ring,
    by rcases h_sll_or with h | h <;> rw [h] <;> ring,
    by rcases h_sllw_or with h | h <;> rw [h] <;> ring,
    by rcases h_cb0_or with h | h <;> rw [h] <;> ring,
    by rcases h_cb1_or with h | h <;> rw [h] <;> ring,
    by rcases h_cb2_or with h | h <;> rw [h] <;> ring,
    by rcases h_cb3_or with h | h <;> rw [h] <;> ring,
    by rcases h_cb4_or with h | h <;> rw [h] <;> ring,
    by rcases h_cb5_or with h | h <;> rw [h] <;> ring,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_within hm)⟩,
    by rcases h_s0sel with h | h <;> rw [h] <;> ring,
    by rcases h_s0_or with h | h <;> rw [h] <;> ring,
    by rcases h_s1sel with h | h <;> rw [h] <;> ring,
    by rcases h_s1_or with h | h <;> rw [h] <;> ring,
    by rcases h_s2sel with h | h <;> rw [h] <;> ring,
    by rcases h_s2_or with h | h <;> rw [h] <;> ring,
    by rcases h_s3sel with h | h <;> rw [h] <;> ring,
    by rcases h_s3_or with h | h <;> rw [h] <;> ring,
    by rcases h_ssum with h | h <;> rw [h] <;> ring,
    by rw [h_v01]; push_cast; ring,
    by linear_combination h_v012,
    by linear_combination h_v0123,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_ll0 hm)⟩,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_hl0 hm)⟩,
    by rw [h_ob0]; push_cast; ring,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_ll1 hm)⟩,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_hl1 hm)⟩,
    by rw [h_ob1]; push_cast; ring,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_ll2 hm)⟩,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_hl2 hm)⟩,
    by rw [h_ob2]; push_cast; ring,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_ll3 hm)⟩,
    ⟨trivial, range_gated_spec (fun hm => by
      simpa only [sub_eq_add_neg, Nat.cast_ofNat] using h_hl3 hm)⟩,
    by rw [h_ob3]; push_cast; ring,
    by linear_combination h_lr0,
    by linear_combination h_lr1,
    by linear_combination h_lr2,
    by linear_combination h_lr3,
    by rcases h_o0 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o1 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o2 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o3 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o4 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o5 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o6 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o7 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o8 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o9 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o10 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o11 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o12 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o13 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o14 with h | h | h <;> rw [h] <;> ring,
    by rcases h_o15 with h | h | h <;> rw [h] <;> ring,
    by rcases h_w0 with h | h | h <;> rw [h] <;> ring,
    by rcases h_w1 with h | h | h <;> rw [h] <;> ring,
    by rcases h_w2 with h | h | h <;> rw [h] <;> ring,
    by rcases h_w3 with h | h | h <;> rw [h] <;> ring,
    by rcases h_w4 with h | h <;> first | (rw [h]; ring) | (push_cast at h; rw [h]; ring),
    by rcases h_w5 with h | h <;> first | (rw [h]; ring) | (push_cast at h; rw [h]; ring),
    by linear_combination h_immeq,
    h_opa0⟩

end Assertion

def assertion : FormalAssertion (ZMod p) ShiftLeftCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ShiftLeft
