import SP1Clean.Specs.Operation
import SP1Clean.Foundations.Bitwise
import SP1Clean.Extracted.BitwiseOperation
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Lookup
import Clean.Gadgets.Xor.ByteXorTable
import Clean.Gadgets.And.And8
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.LinearCombination

/-! # `BitwiseU16Operation` as a Clean-native `FormalCircuit`

AND/OR/XOR over two operand words (four 16-bit limbs each) and an `opcode` (AND=0, OR=1,
XOR=2). Witnesses the eight low bytes of `b`/`c` and the eight result bytes; emits one
`ByteXorTable` lookup per byte whose third argument is the opcode-selected combination
unified across all three ops by Lagrange selectors. The `Spec` is semantic — the
reassembled result's `toBitVec64` is the AND/OR/XOR of the operands' — proved via
`reassemble_byteOp`. Faithful to SP1's `operations/bitwise_u16.rs`. -/

namespace SP1Clean.BitwiseU16Operation

open Circuit Gadgets.Xor

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 512) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- Witness the eight low bytes of `b`/`c` and the eight result bytes; emit one
`ByteXorTable` lookup per byte. The lookup's third argument is the opcode-selected
expression that equals the byte XOR for whichever op `opcode` picks (AND: `b+c-2r`,
OR: `2r-b-c`, XOR: `r`), so a single op-uniform table proves all three. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Extracted.BitwiseOperation (ZMod p)) := do
  let b_low ← witnessVector 4 (fun env =>
    #v[(((env input.b[0]).val % 256 : ℕ) : ZMod p), (((env input.b[1]).val % 256 : ℕ) : ZMod p),
       (((env input.b[2]).val % 256 : ℕ) : ZMod p), (((env input.b[3]).val % 256 : ℕ) : ZMod p)])
  let c_low ← witnessVector 4 (fun env =>
    #v[(((env input.c[0]).val % 256 : ℕ) : ZMod p), (((env input.c[1]).val % 256 : ℕ) : ZMod p),
       (((env input.c[2]).val % 256 : ℕ) : ZMod p), (((env input.c[3]).val % 256 : ℕ) : ZMod p)])
  let result ← witnessVector 8 (fun env =>
    let op := (env input.opcode).val
    let b0 := (env input.b[0]).val; let b1 := (env input.b[1]).val
    let b2 := (env input.b[2]).val; let b3 := (env input.b[3]).val
    let c0 := (env input.c[0]).val; let c1 := (env input.c[1]).val
    let c2 := (env input.c[2]).val; let c3 := (env input.c[3]).val
    #v[((byteOp op (b0 % 256) (c0 % 256) : ℕ) : ZMod p),
       ((byteOp op (b0 / 256) (c0 / 256) : ℕ) : ZMod p),
       ((byteOp op (b1 % 256) (c1 % 256) : ℕ) : ZMod p),
       ((byteOp op (b1 / 256) (c1 / 256) : ℕ) : ZMod p),
       ((byteOp op (b2 % 256) (c2 % 256) : ℕ) : ZMod p),
       ((byteOp op (b2 / 256) (c2 / 256) : ℕ) : ZMod p),
       ((byteOp op (b3 % 256) (c3 % 256) : ℕ) : ZMod p),
       ((byteOp op (b3 / 256) (c3 / 256) : ℕ) : ZMod p)])
  let o := input.opcode
  let s_and := (o - 1) * (o - 2) * (2 : ZMod p)⁻¹
  let s_or := -(o * (o - 2))
  let s_xor := o * (o - 1) * (2 : ZMod p)⁻¹
  let xe := fun (bb c res : Expression (ZMod p)) =>
    s_and * (bb + c - 2 * res) + s_or * (2 * res - bb - c) + s_xor * res
  let bh0 := (input.b[0] - b_low[0]) * (256 : ZMod p)⁻¹
  let bh1 := (input.b[1] - b_low[1]) * (256 : ZMod p)⁻¹
  let bh2 := (input.b[2] - b_low[2]) * (256 : ZMod p)⁻¹
  let bh3 := (input.b[3] - b_low[3]) * (256 : ZMod p)⁻¹
  let ch0 := (input.c[0] - c_low[0]) * (256 : ZMod p)⁻¹
  let ch1 := (input.c[1] - c_low[1]) * (256 : ZMod p)⁻¹
  let ch2 := (input.c[2] - c_low[2]) * (256 : ZMod p)⁻¹
  let ch3 := (input.c[3] - c_low[3]) * (256 : ZMod p)⁻¹
  lookup ByteXorTable (b_low[0], c_low[0], xe b_low[0] c_low[0] result[0])
  lookup ByteXorTable (bh0, ch0, xe bh0 ch0 result[1])
  lookup ByteXorTable (b_low[1], c_low[1], xe b_low[1] c_low[1] result[2])
  lookup ByteXorTable (bh1, ch1, xe bh1 ch1 result[3])
  lookup ByteXorTable (b_low[2], c_low[2], xe b_low[2] c_low[2] result[4])
  lookup ByteXorTable (bh2, ch2, xe bh2 ch2 result[5])
  lookup ByteXorTable (b_low[3], c_low[3], xe b_low[3] c_low[3] result[6])
  lookup ByteXorTable (bh3, ch3, xe bh3 ch3 result[7])
  return ⟨result⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Extracted.BitwiseOperation main where
  localLength _ := 16
  output _ i0 := varFromOffset Extracted.BitwiseOperation (i0 + 8)

/-- Operands are 64-bit values; opcode is one of AND/OR/XOR. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.b ∧ Word.isU64 input.c ∧ input.opcode.val < 3

/-! ## Per-byte algebra: from the opcode-selected `ByteXorTable` relation to `byteOp` -/

private lemma two_ne_zero' : (2 : ZMod p) ≠ 0 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : (2 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  intro h
  have hv : ((2 : ℕ) : ZMod p).val = 2 := ZMod.val_natCast_of_lt hp
  rw [Nat.cast_ofNat, h, ZMod.val_zero] at hv
  omega

/-- AND byte: the `ByteXorTable` relation `(x + y - 2z).val = x.val ^^^ y.val` forces
`z = x &&& y` (Clean's `And8` identity, lifted to `ZMod p`). -/
lemma and_of_rel {x y z : ZMod p} (hx : x.val < 256) (hy : y.val < 256)
    (hrel : (x + y - 2 * z).val = x.val ^^^ y.val) : z.val = x.val &&& y.val := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  have hand_lt : x.val &&& y.val < 256 := Nat.and_lt_two_pow (n := 8) x.val (by omega)
  have hxor_lt : x.val ^^^ y.val < 256 := Nat.xor_lt_two_pow (n := 8) (by omega) (by omega)
  have hsum : 2 * (x.val &&& y.val) + (x.val ^^^ y.val) = x.val + y.val :=
    Gadgets.And.And8.and_times_two_add_xor hx hy
  have hle : x.val ^^^ y.val ≤ x.val + y.val := by omega
  have hcast : x + y - 2 * z = ((x.val ^^^ y.val : ℕ) : ZMod p) := by
    conv_lhs => rw [← ZMod.natCast_zmod_val (x + y - 2 * z)]
    rw [hrel]
  have h2z : 2 * z = 2 * ((x.val &&& y.val : ℕ) : ZMod p) := by
    have rhs_eq : 2 * ((x.val &&& y.val : ℕ) : ZMod p) = x + y - ((x.val ^^^ y.val : ℕ) : ZMod p) := by
      rw [← Nat.cast_two, ← Nat.cast_mul,
        show 2 * (x.val &&& y.val) = x.val + y.val - (x.val ^^^ y.val) from by omega,
        Nat.cast_sub hle, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
    rw [rhs_eq]; linear_combination -hcast
  have hz : z = ((x.val &&& y.val : ℕ) : ZMod p) := mul_left_cancel₀ two_ne_zero' h2z
  rw [hz, ZMod.val_natCast_of_lt (by omega : x.val &&& y.val < p)]

/-- OR identity (Clean's `Or8`, `2*(x|||y) = x+y+(x^^^y)` for bytes), ported as a
standalone `Nat` lemma. -/
private lemma or_two_mul {x y : ℕ} (hx : x < 256) (hy : y < 256) :
    2 * (x ||| y) = x + y + (x ^^^ y) := by
  let x16 := x.toUInt16
  let y16 := y.toUInt16
  have h_u16 : (2 * (x16 ||| y16)).toNat = (x16 + y16 + (x16 ^^^ y16)).toNat := by
    apply congrArg UInt16.toNat
    bv_decide
  have hx16 : x.toUInt16.toNat = x := UInt16.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le hx (by decide))
  have hy16 : y.toUInt16.toNat = y := UInt16.toNat_ofNat_of_lt (Nat.lt_of_lt_of_le hy (by decide))
  have h_or_byte : x ||| y < 256 := Nat.or_lt_two_pow (n := 8) hx hy
  have h_xor_byte : x ^^^ y < 256 := Nat.xor_lt_two_pow (n := 8) hx hy
  have h_mod_2_to_16 : (2 * (x ||| y)) % 2 ^ 16 = (x + y + (x ^^^ y)) % 2 ^ 16 := by
    conv_lhs => rw [← hx16, ← hy16]
    conv_rhs => rw [← hx16, ← hy16]
    simp only [x16, y16] at h_u16
    simp only [← UInt16.toNat_or]
    norm_num at h_u16 ⊢
    repeat rw [Nat.mod_eq_of_lt] <;> try omega
    · repeat rw [Nat.mod_eq_of_lt] at h_u16 <;> try omega
      · simpa
      · repeat rw [Nat.mod_eq_of_lt] <;> try omega
        simp only [UInt16.toNat, UInt16.toBitVec_ofNat, BitVec.toNat_ofNat, Nat.reducePow,
          Nat.reduceMod]
        omega
    · repeat rw [Nat.mod_eq_of_lt] <;> try omega
  have h_lhs : 2 * (x ||| y) < 2 ^ 16 := by omega
  have h_rhs : x + y + (x ^^^ y) < 2 ^ 16 := by omega
  rw [Nat.mod_eq_of_lt h_lhs, Nat.mod_eq_of_lt h_rhs] at h_mod_2_to_16
  exact h_mod_2_to_16

/-- OR byte: the relation `(2z - x - y).val = x.val ^^^ y.val` forces `z = x ||| y`
(ported from Clean's `Or8` soundness). -/
lemma or_of_rel {x y z : ZMod p} (hx : x.val < 256) (hy : y.val < 256)
    (hrel : (2 * z - x - y).val = x.val ^^^ y.val) : z.val = x.val ||| y.val := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  set xr := 2 * z - x - y with hxr_def
  have h_xor : xr.val = x.val ^^^ y.val := hrel
  have hor_byte : x.val ||| y.val < 256 := Nat.or_lt_two_pow (n := 8) (by omega) (by omega)
  have two_or_field : 2 * z = x + y + xr := by rw [hxr_def]; ring
  have x_y_val : (x + y).val = x.val + y.val := ZMod.val_add_of_lt (by omega)
  have x_y_xor_val : (x + y + xr).val = x.val + y.val + (x.val ^^^ y.val) := by
    have sum_bound : (x + y).val + xr.val < p := by
      rw [x_y_val, h_xor]
      have hbound := or_two_mul (show x.val < 256 by omega) (show y.val < 256 by omega)
      omega
    rw [ZMod.val_add_of_lt sum_bound, x_y_val, h_xor]
  have two_or : (2 * z).val = 2 * (x.val ||| y.val) := by
    rw [two_or_field, x_y_xor_val, or_two_mul (show x.val < 256 by omega) (show y.val < 256 by omega)]
  have two_mul_val : (2 * z).val = 2 * z.val :=
    FieldUtils.mul_nat_val_of_dvd 2 (by omega) two_or
  rw [two_mul_val] at two_or
  omega

set_option maxHeartbeats 2000000 in
theorem soundness : Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hb, hc, hop⟩ := h_assumptions
  simp only [circuit_norm, ByteXorTable] at h_holds
  have hand_sel : ∀ b c r : ZMod p,
      (0 - 1) * (0 - 2) * 2⁻¹ * (b + c - 2 * r) - 0 * (0 - 2) * (2 * r - b - c)
          + 0 * (0 - 1) * 2⁻¹ * r = b + c - 2 * r := by
    intro b c r
    have h2 : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ two_ne_zero'
    linear_combination (b + c - 2 * r) * h2
  have hor_sel : ∀ b c r : ZMod p,
      (1 - 1) * (1 - 2) * 2⁻¹ * (b + c - 2 * r) - 1 * (1 - 2) * (2 * r - b - c)
          + 1 * (1 - 1) * 2⁻¹ * r = 2 * r - b - c := by
    intro b c r; ring
  have hxor_sel : ∀ b c r : ZMod p,
      (2 - 1) * (2 - 2) * 2⁻¹ * (b + c - 2 * r) - 2 * (2 - 2) * (2 * r - b - c)
          + 2 * (2 - 1) * 2⁻¹ * r = r := by
    intro b c r
    have h2 : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ two_ne_zero'
    linear_combination r * h2
  refine ⟨fun h0 => ?_, fun h1 => ?_, fun h2 => ?_⟩
  · subst h0
    simp only [← sub_eq_add_neg, hand_sel] at h_holds
    obtain ⟨⟨hxb0, hxc0, he0⟩, ⟨hxb1, hxc1, he1⟩, ⟨hxb2, hxc2, he2⟩, ⟨hxb3, hxc3, he3⟩,
           ⟨hxb4, hxc4, he4⟩, ⟨hxb5, hxc5, he5⟩, ⟨hxb6, hxc6, he6⟩, hxb7, hxc7, he7⟩ := h_holds
    have hr0 := and_of_rel hxb0 hxc0 he0
    have hr1 := and_of_rel hxb1 hxc1 he1
    have hr2 := and_of_rel hxb2 hxc2 he2
    have hr3 := and_of_rel hxb3 hxc3 he3
    have hr4 := and_of_rel hxb4 hxc4 he4
    have hr5 := and_of_rel hxb5 hxc5 he5
    have hr6 := and_of_rel hxb6 hxc6 he6
    have hr7 := and_of_rel hxb7 hxc7 he7
    simp only [resultWord, circuit_norm]
    simp only [show i₀ + 4 + 4 = i₀ + 8 from by omega] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
    obtain ⟨hib, hic, -⟩ := h_input
    have eb0 : Expression.eval env input_var_b[0] = input_b[0] := by rw [← hib]; simp only [Vector.getElem_map]
    have eb1 : Expression.eval env input_var_b[1] = input_b[1] := by rw [← hib]; simp only [Vector.getElem_map]
    have eb2 : Expression.eval env input_var_b[2] = input_b[2] := by rw [← hib]; simp only [Vector.getElem_map]
    have eb3 : Expression.eval env input_var_b[3] = input_b[3] := by rw [← hib]; simp only [Vector.getElem_map]
    have ec0 : Expression.eval env input_var_c[0] = input_c[0] := by rw [← hic]; simp only [Vector.getElem_map]
    have ec1 : Expression.eval env input_var_c[1] = input_c[1] := by rw [← hic]; simp only [Vector.getElem_map]
    have ec2 : Expression.eval env input_var_c[2] = input_c[2] := by rw [← hic]; simp only [Vector.getElem_map]
    have ec3 : Expression.eval env input_var_c[3] = input_c[3] := by rw [← hic]; simp only [Vector.getElem_map]
    have hbv0 : input_b[0].val = (env.get i₀).val
        + ((Expression.eval env input_var_b[0] - env.get i₀) * 256⁻¹).val * 256 := by
      rw [show input_b[0] = env.get i₀ + (Expression.eval env input_var_b[0] - env.get i₀) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, eb0]; ring]
      exact val_lo_add_hi hxb0 hxb1
    have hbv1 : input_b[1].val = (env.get (i₀ + 1)).val
        + ((Expression.eval env input_var_b[1] - env.get (i₀ + 1)) * 256⁻¹).val * 256 := by
      rw [show input_b[1] = env.get (i₀ + 1) + (Expression.eval env input_var_b[1] - env.get (i₀ + 1)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, eb1]; ring]
      exact val_lo_add_hi hxb2 hxb3
    have hbv2 : input_b[2].val = (env.get (i₀ + 2)).val
        + ((Expression.eval env input_var_b[2] - env.get (i₀ + 2)) * 256⁻¹).val * 256 := by
      rw [show input_b[2] = env.get (i₀ + 2) + (Expression.eval env input_var_b[2] - env.get (i₀ + 2)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, eb2]; ring]
      exact val_lo_add_hi hxb4 hxb5
    have hbv3 : input_b[3].val = (env.get (i₀ + 3)).val
        + ((Expression.eval env input_var_b[3] - env.get (i₀ + 3)) * 256⁻¹).val * 256 := by
      rw [show input_b[3] = env.get (i₀ + 3) + (Expression.eval env input_var_b[3] - env.get (i₀ + 3)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, eb3]; ring]
      exact val_lo_add_hi hxb6 hxb7
    have hcv0 : input_c[0].val = (env.get (i₀ + 4)).val
        + ((Expression.eval env input_var_c[0] - env.get (i₀ + 4)) * 256⁻¹).val * 256 := by
      rw [show input_c[0] = env.get (i₀ + 4) + (Expression.eval env input_var_c[0] - env.get (i₀ + 4)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, ec0]; ring]
      exact val_lo_add_hi hxc0 hxc1
    have hcv1 : input_c[1].val = (env.get (i₀ + 4 + 1)).val
        + ((Expression.eval env input_var_c[1] - env.get (i₀ + 4 + 1)) * 256⁻¹).val * 256 := by
      rw [show input_c[1] = env.get (i₀ + 4 + 1) + (Expression.eval env input_var_c[1] - env.get (i₀ + 4 + 1)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, ec1]; ring]
      exact val_lo_add_hi hxc2 hxc3
    have hcv2 : input_c[2].val = (env.get (i₀ + 4 + 2)).val
        + ((Expression.eval env input_var_c[2] - env.get (i₀ + 4 + 2)) * 256⁻¹).val * 256 := by
      rw [show input_c[2] = env.get (i₀ + 4 + 2) + (Expression.eval env input_var_c[2] - env.get (i₀ + 4 + 2)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, ec2]; ring]
      exact val_lo_add_hi hxc4 hxc5
    have hcv3 : input_c[3].val = (env.get (i₀ + 4 + 3)).val
        + ((Expression.eval env input_var_c[3] - env.get (i₀ + 4 + 3)) * 256⁻¹).val * 256 := by
      rw [show input_c[3] = env.get (i₀ + 4 + 3) + (Expression.eval env input_var_c[3] - env.get (i₀ + 4 + 3)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, ec3]; ring]
      exact val_lo_add_hi hxc6 hxc7
    have hrb0 : (env.get (i₀ + 8)).val < 256 := by rw [hr0]; exact byteOp_lt256 0 _ _ hxb0 hxc0
    have hrb1 : (env.get (i₀ + 8 + 1)).val < 256 := by rw [hr1]; exact byteOp_lt256 0 _ _ hxb1 hxc1
    have hrb2 : (env.get (i₀ + 8 + 2)).val < 256 := by rw [hr2]; exact byteOp_lt256 0 _ _ hxb2 hxc2
    have hrb3 : (env.get (i₀ + 8 + 3)).val < 256 := by rw [hr3]; exact byteOp_lt256 0 _ _ hxb3 hxc3
    have hrb4 : (env.get (i₀ + 8 + 4)).val < 256 := by rw [hr4]; exact byteOp_lt256 0 _ _ hxb4 hxc4
    have hrb5 : (env.get (i₀ + 8 + 5)).val < 256 := by rw [hr5]; exact byteOp_lt256 0 _ _ hxb5 hxc5
    have hrb6 : (env.get (i₀ + 8 + 6)).val < 256 := by rw [hr6]; exact byteOp_lt256 0 _ _ hxb6 hxc6
    have hrb7 : (env.get (i₀ + 8 + 7)).val < 256 := by rw [hr7]; exact byteOp_lt256 0 _ _ hxb7 hxc7
    rw [toBitVec64_asm8 _ (env.get (i₀ + 8)).val (env.get (i₀ + 8 + 1)).val (env.get (i₀ + 8 + 2)).val
        (env.get (i₀ + 8 + 3)).val (env.get (i₀ + 8 + 4)).val (env.get (i₀ + 8 + 5)).val
        (env.get (i₀ + 8 + 6)).val (env.get (i₀ + 8 + 7)).val
        (val_lo_add_hi hrb0 hrb1) (val_lo_add_hi hrb2 hrb3) (val_lo_add_hi hrb4 hrb5)
        (val_lo_add_hi hrb6 hrb7),
      toBitVec64_asm8 input_b _ _ _ _ _ _ _ _ hbv0 hbv1 hbv2 hbv3,
      toBitVec64_asm8 input_c _ _ _ _ _ _ _ _ hcv0 hcv1 hcv2 hcv3,
      ← bitOp64_zero]
    exact reassemble_byteOp 0 (by omega)
      (env.get i₀).val ((Expression.eval env input_var_b[0] - env.get i₀) * 256⁻¹).val
      (env.get (i₀ + 1)).val ((Expression.eval env input_var_b[1] - env.get (i₀ + 1)) * 256⁻¹).val
      (env.get (i₀ + 2)).val ((Expression.eval env input_var_b[2] - env.get (i₀ + 2)) * 256⁻¹).val
      (env.get (i₀ + 3)).val ((Expression.eval env input_var_b[3] - env.get (i₀ + 3)) * 256⁻¹).val
      (env.get (i₀ + 4)).val ((Expression.eval env input_var_c[0] - env.get (i₀ + 4)) * 256⁻¹).val
      (env.get (i₀ + 4 + 1)).val ((Expression.eval env input_var_c[1] - env.get (i₀ + 4 + 1)) * 256⁻¹).val
      (env.get (i₀ + 4 + 2)).val ((Expression.eval env input_var_c[2] - env.get (i₀ + 4 + 2)) * 256⁻¹).val
      (env.get (i₀ + 4 + 3)).val ((Expression.eval env input_var_c[3] - env.get (i₀ + 4 + 3)) * 256⁻¹).val
      (env.get (i₀ + 8)).val (env.get (i₀ + 8 + 1)).val (env.get (i₀ + 8 + 2)).val (env.get (i₀ + 8 + 3)).val
      (env.get (i₀ + 8 + 4)).val (env.get (i₀ + 8 + 5)).val (env.get (i₀ + 8 + 6)).val (env.get (i₀ + 8 + 7)).val
      hxb0 hxb1 hxb2 hxb3 hxb4 hxb5 hxb6 hxc0 hxc1 hxc2 hxc3 hxc4 hxc5 hxc6
      hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  · subst h1
    simp only [← sub_eq_add_neg, hor_sel] at h_holds
    obtain ⟨⟨hxb0, hxc0, he0⟩, ⟨hxb1, hxc1, he1⟩, ⟨hxb2, hxc2, he2⟩, ⟨hxb3, hxc3, he3⟩,
           ⟨hxb4, hxc4, he4⟩, ⟨hxb5, hxc5, he5⟩, ⟨hxb6, hxc6, he6⟩, hxb7, hxc7, he7⟩ := h_holds
    have hr0 := or_of_rel hxb0 hxc0 he0
    have hr1 := or_of_rel hxb1 hxc1 he1
    have hr2 := or_of_rel hxb2 hxc2 he2
    have hr3 := or_of_rel hxb3 hxc3 he3
    have hr4 := or_of_rel hxb4 hxc4 he4
    have hr5 := or_of_rel hxb5 hxc5 he5
    have hr6 := or_of_rel hxb6 hxc6 he6
    have hr7 := or_of_rel hxb7 hxc7 he7
    simp only [resultWord, circuit_norm]
    simp only [show i₀ + 4 + 4 = i₀ + 8 from by omega] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
    obtain ⟨hib, hic, -⟩ := h_input
    have eb0 : Expression.eval env input_var_b[0] = input_b[0] := by rw [← hib]; simp only [Vector.getElem_map]
    have eb1 : Expression.eval env input_var_b[1] = input_b[1] := by rw [← hib]; simp only [Vector.getElem_map]
    have eb2 : Expression.eval env input_var_b[2] = input_b[2] := by rw [← hib]; simp only [Vector.getElem_map]
    have eb3 : Expression.eval env input_var_b[3] = input_b[3] := by rw [← hib]; simp only [Vector.getElem_map]
    have ec0 : Expression.eval env input_var_c[0] = input_c[0] := by rw [← hic]; simp only [Vector.getElem_map]
    have ec1 : Expression.eval env input_var_c[1] = input_c[1] := by rw [← hic]; simp only [Vector.getElem_map]
    have ec2 : Expression.eval env input_var_c[2] = input_c[2] := by rw [← hic]; simp only [Vector.getElem_map]
    have ec3 : Expression.eval env input_var_c[3] = input_c[3] := by rw [← hic]; simp only [Vector.getElem_map]
    have hbv0 : input_b[0].val = (env.get i₀).val
        + ((Expression.eval env input_var_b[0] - env.get i₀) * 256⁻¹).val * 256 := by
      rw [show input_b[0] = env.get i₀ + (Expression.eval env input_var_b[0] - env.get i₀) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, eb0]; ring]
      exact val_lo_add_hi hxb0 hxb1
    have hbv1 : input_b[1].val = (env.get (i₀ + 1)).val
        + ((Expression.eval env input_var_b[1] - env.get (i₀ + 1)) * 256⁻¹).val * 256 := by
      rw [show input_b[1] = env.get (i₀ + 1) + (Expression.eval env input_var_b[1] - env.get (i₀ + 1)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, eb1]; ring]
      exact val_lo_add_hi hxb2 hxb3
    have hbv2 : input_b[2].val = (env.get (i₀ + 2)).val
        + ((Expression.eval env input_var_b[2] - env.get (i₀ + 2)) * 256⁻¹).val * 256 := by
      rw [show input_b[2] = env.get (i₀ + 2) + (Expression.eval env input_var_b[2] - env.get (i₀ + 2)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, eb2]; ring]
      exact val_lo_add_hi hxb4 hxb5
    have hbv3 : input_b[3].val = (env.get (i₀ + 3)).val
        + ((Expression.eval env input_var_b[3] - env.get (i₀ + 3)) * 256⁻¹).val * 256 := by
      rw [show input_b[3] = env.get (i₀ + 3) + (Expression.eval env input_var_b[3] - env.get (i₀ + 3)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, eb3]; ring]
      exact val_lo_add_hi hxb6 hxb7
    have hcv0 : input_c[0].val = (env.get (i₀ + 4)).val
        + ((Expression.eval env input_var_c[0] - env.get (i₀ + 4)) * 256⁻¹).val * 256 := by
      rw [show input_c[0] = env.get (i₀ + 4) + (Expression.eval env input_var_c[0] - env.get (i₀ + 4)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, ec0]; ring]
      exact val_lo_add_hi hxc0 hxc1
    have hcv1 : input_c[1].val = (env.get (i₀ + 4 + 1)).val
        + ((Expression.eval env input_var_c[1] - env.get (i₀ + 4 + 1)) * 256⁻¹).val * 256 := by
      rw [show input_c[1] = env.get (i₀ + 4 + 1) + (Expression.eval env input_var_c[1] - env.get (i₀ + 4 + 1)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, ec1]; ring]
      exact val_lo_add_hi hxc2 hxc3
    have hcv2 : input_c[2].val = (env.get (i₀ + 4 + 2)).val
        + ((Expression.eval env input_var_c[2] - env.get (i₀ + 4 + 2)) * 256⁻¹).val * 256 := by
      rw [show input_c[2] = env.get (i₀ + 4 + 2) + (Expression.eval env input_var_c[2] - env.get (i₀ + 4 + 2)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, ec2]; ring]
      exact val_lo_add_hi hxc4 hxc5
    have hcv3 : input_c[3].val = (env.get (i₀ + 4 + 3)).val
        + ((Expression.eval env input_var_c[3] - env.get (i₀ + 4 + 3)) * 256⁻¹).val * 256 := by
      rw [show input_c[3] = env.get (i₀ + 4 + 3) + (Expression.eval env input_var_c[3] - env.get (i₀ + 4 + 3)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, ec3]; ring]
      exact val_lo_add_hi hxc6 hxc7
    have hrb0 : (env.get (i₀ + 8)).val < 256 := by rw [hr0]; exact byteOp_lt256 1 _ _ hxb0 hxc0
    have hrb1 : (env.get (i₀ + 8 + 1)).val < 256 := by rw [hr1]; exact byteOp_lt256 1 _ _ hxb1 hxc1
    have hrb2 : (env.get (i₀ + 8 + 2)).val < 256 := by rw [hr2]; exact byteOp_lt256 1 _ _ hxb2 hxc2
    have hrb3 : (env.get (i₀ + 8 + 3)).val < 256 := by rw [hr3]; exact byteOp_lt256 1 _ _ hxb3 hxc3
    have hrb4 : (env.get (i₀ + 8 + 4)).val < 256 := by rw [hr4]; exact byteOp_lt256 1 _ _ hxb4 hxc4
    have hrb5 : (env.get (i₀ + 8 + 5)).val < 256 := by rw [hr5]; exact byteOp_lt256 1 _ _ hxb5 hxc5
    have hrb6 : (env.get (i₀ + 8 + 6)).val < 256 := by rw [hr6]; exact byteOp_lt256 1 _ _ hxb6 hxc6
    have hrb7 : (env.get (i₀ + 8 + 7)).val < 256 := by rw [hr7]; exact byteOp_lt256 1 _ _ hxb7 hxc7
    rw [toBitVec64_asm8 _ (env.get (i₀ + 8)).val (env.get (i₀ + 8 + 1)).val (env.get (i₀ + 8 + 2)).val
        (env.get (i₀ + 8 + 3)).val (env.get (i₀ + 8 + 4)).val (env.get (i₀ + 8 + 5)).val
        (env.get (i₀ + 8 + 6)).val (env.get (i₀ + 8 + 7)).val
        (val_lo_add_hi hrb0 hrb1) (val_lo_add_hi hrb2 hrb3) (val_lo_add_hi hrb4 hrb5)
        (val_lo_add_hi hrb6 hrb7),
      toBitVec64_asm8 input_b _ _ _ _ _ _ _ _ hbv0 hbv1 hbv2 hbv3,
      toBitVec64_asm8 input_c _ _ _ _ _ _ _ _ hcv0 hcv1 hcv2 hcv3,
      ← bitOp64_one]
    exact reassemble_byteOp 1 (by omega)
      (env.get i₀).val ((Expression.eval env input_var_b[0] - env.get i₀) * 256⁻¹).val
      (env.get (i₀ + 1)).val ((Expression.eval env input_var_b[1] - env.get (i₀ + 1)) * 256⁻¹).val
      (env.get (i₀ + 2)).val ((Expression.eval env input_var_b[2] - env.get (i₀ + 2)) * 256⁻¹).val
      (env.get (i₀ + 3)).val ((Expression.eval env input_var_b[3] - env.get (i₀ + 3)) * 256⁻¹).val
      (env.get (i₀ + 4)).val ((Expression.eval env input_var_c[0] - env.get (i₀ + 4)) * 256⁻¹).val
      (env.get (i₀ + 4 + 1)).val ((Expression.eval env input_var_c[1] - env.get (i₀ + 4 + 1)) * 256⁻¹).val
      (env.get (i₀ + 4 + 2)).val ((Expression.eval env input_var_c[2] - env.get (i₀ + 4 + 2)) * 256⁻¹).val
      (env.get (i₀ + 4 + 3)).val ((Expression.eval env input_var_c[3] - env.get (i₀ + 4 + 3)) * 256⁻¹).val
      (env.get (i₀ + 8)).val (env.get (i₀ + 8 + 1)).val (env.get (i₀ + 8 + 2)).val (env.get (i₀ + 8 + 3)).val
      (env.get (i₀ + 8 + 4)).val (env.get (i₀ + 8 + 5)).val (env.get (i₀ + 8 + 6)).val (env.get (i₀ + 8 + 7)).val
      hxb0 hxb1 hxb2 hxb3 hxb4 hxb5 hxb6 hxc0 hxc1 hxc2 hxc3 hxc4 hxc5 hxc6
      hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
  · subst h2
    simp only [← sub_eq_add_neg, hxor_sel] at h_holds
    obtain ⟨⟨hxb0, hxc0, hr0⟩, ⟨hxb1, hxc1, hr1⟩, ⟨hxb2, hxc2, hr2⟩, ⟨hxb3, hxc3, hr3⟩,
           ⟨hxb4, hxc4, hr4⟩, ⟨hxb5, hxc5, hr5⟩, ⟨hxb6, hxc6, hr6⟩, hxb7, hxc7, hr7⟩ := h_holds
    simp only [resultWord, circuit_norm]
    simp only [show i₀ + 4 + 4 = i₀ + 8 from by omega] at hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7
    obtain ⟨hib, hic, -⟩ := h_input
    have eb0 : Expression.eval env input_var_b[0] = input_b[0] := by rw [← hib]; simp only [Vector.getElem_map]
    have eb1 : Expression.eval env input_var_b[1] = input_b[1] := by rw [← hib]; simp only [Vector.getElem_map]
    have eb2 : Expression.eval env input_var_b[2] = input_b[2] := by rw [← hib]; simp only [Vector.getElem_map]
    have eb3 : Expression.eval env input_var_b[3] = input_b[3] := by rw [← hib]; simp only [Vector.getElem_map]
    have ec0 : Expression.eval env input_var_c[0] = input_c[0] := by rw [← hic]; simp only [Vector.getElem_map]
    have ec1 : Expression.eval env input_var_c[1] = input_c[1] := by rw [← hic]; simp only [Vector.getElem_map]
    have ec2 : Expression.eval env input_var_c[2] = input_c[2] := by rw [← hic]; simp only [Vector.getElem_map]
    have ec3 : Expression.eval env input_var_c[3] = input_c[3] := by rw [← hic]; simp only [Vector.getElem_map]
    have hbv0 : input_b[0].val = (env.get i₀).val
        + ((Expression.eval env input_var_b[0] - env.get i₀) * 256⁻¹).val * 256 := by
      rw [show input_b[0] = env.get i₀ + (Expression.eval env input_var_b[0] - env.get i₀) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, eb0]; ring]
      exact val_lo_add_hi hxb0 hxb1
    have hbv1 : input_b[1].val = (env.get (i₀ + 1)).val
        + ((Expression.eval env input_var_b[1] - env.get (i₀ + 1)) * 256⁻¹).val * 256 := by
      rw [show input_b[1] = env.get (i₀ + 1) + (Expression.eval env input_var_b[1] - env.get (i₀ + 1)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, eb1]; ring]
      exact val_lo_add_hi hxb2 hxb3
    have hbv2 : input_b[2].val = (env.get (i₀ + 2)).val
        + ((Expression.eval env input_var_b[2] - env.get (i₀ + 2)) * 256⁻¹).val * 256 := by
      rw [show input_b[2] = env.get (i₀ + 2) + (Expression.eval env input_var_b[2] - env.get (i₀ + 2)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, eb2]; ring]
      exact val_lo_add_hi hxb4 hxb5
    have hbv3 : input_b[3].val = (env.get (i₀ + 3)).val
        + ((Expression.eval env input_var_b[3] - env.get (i₀ + 3)) * 256⁻¹).val * 256 := by
      rw [show input_b[3] = env.get (i₀ + 3) + (Expression.eval env input_var_b[3] - env.get (i₀ + 3)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, eb3]; ring]
      exact val_lo_add_hi hxb6 hxb7
    have hcv0 : input_c[0].val = (env.get (i₀ + 4)).val
        + ((Expression.eval env input_var_c[0] - env.get (i₀ + 4)) * 256⁻¹).val * 256 := by
      rw [show input_c[0] = env.get (i₀ + 4) + (Expression.eval env input_var_c[0] - env.get (i₀ + 4)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, ec0]; ring]
      exact val_lo_add_hi hxc0 hxc1
    have hcv1 : input_c[1].val = (env.get (i₀ + 4 + 1)).val
        + ((Expression.eval env input_var_c[1] - env.get (i₀ + 4 + 1)) * 256⁻¹).val * 256 := by
      rw [show input_c[1] = env.get (i₀ + 4 + 1) + (Expression.eval env input_var_c[1] - env.get (i₀ + 4 + 1)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, ec1]; ring]
      exact val_lo_add_hi hxc2 hxc3
    have hcv2 : input_c[2].val = (env.get (i₀ + 4 + 2)).val
        + ((Expression.eval env input_var_c[2] - env.get (i₀ + 4 + 2)) * 256⁻¹).val * 256 := by
      rw [show input_c[2] = env.get (i₀ + 4 + 2) + (Expression.eval env input_var_c[2] - env.get (i₀ + 4 + 2)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, ec2]; ring]
      exact val_lo_add_hi hxc4 hxc5
    have hcv3 : input_c[3].val = (env.get (i₀ + 4 + 3)).val
        + ((Expression.eval env input_var_c[3] - env.get (i₀ + 4 + 3)) * 256⁻¹).val * 256 := by
      rw [show input_c[3] = env.get (i₀ + 4 + 3) + (Expression.eval env input_var_c[3] - env.get (i₀ + 4 + 3)) * 256⁻¹ * 256 from by
        rw [mul_assoc, inv_mul_cancel₀ val_256_ne_zero, mul_one, ec3]; ring]
      exact val_lo_add_hi hxc6 hxc7
    have hrb0 : (env.get (i₀ + 8)).val < 256 := by rw [hr0]; exact byteOp_lt256 2 _ _ hxb0 hxc0
    have hrb1 : (env.get (i₀ + 8 + 1)).val < 256 := by rw [hr1]; exact byteOp_lt256 2 _ _ hxb1 hxc1
    have hrb2 : (env.get (i₀ + 8 + 2)).val < 256 := by rw [hr2]; exact byteOp_lt256 2 _ _ hxb2 hxc2
    have hrb3 : (env.get (i₀ + 8 + 3)).val < 256 := by rw [hr3]; exact byteOp_lt256 2 _ _ hxb3 hxc3
    have hrb4 : (env.get (i₀ + 8 + 4)).val < 256 := by rw [hr4]; exact byteOp_lt256 2 _ _ hxb4 hxc4
    have hrb5 : (env.get (i₀ + 8 + 5)).val < 256 := by rw [hr5]; exact byteOp_lt256 2 _ _ hxb5 hxc5
    have hrb6 : (env.get (i₀ + 8 + 6)).val < 256 := by rw [hr6]; exact byteOp_lt256 2 _ _ hxb6 hxc6
    have hrb7 : (env.get (i₀ + 8 + 7)).val < 256 := by rw [hr7]; exact byteOp_lt256 2 _ _ hxb7 hxc7
    rw [toBitVec64_asm8 _ (env.get (i₀ + 8)).val (env.get (i₀ + 8 + 1)).val (env.get (i₀ + 8 + 2)).val
        (env.get (i₀ + 8 + 3)).val (env.get (i₀ + 8 + 4)).val (env.get (i₀ + 8 + 5)).val
        (env.get (i₀ + 8 + 6)).val (env.get (i₀ + 8 + 7)).val
        (val_lo_add_hi hrb0 hrb1) (val_lo_add_hi hrb2 hrb3) (val_lo_add_hi hrb4 hrb5)
        (val_lo_add_hi hrb6 hrb7),
      toBitVec64_asm8 input_b _ _ _ _ _ _ _ _ hbv0 hbv1 hbv2 hbv3,
      toBitVec64_asm8 input_c _ _ _ _ _ _ _ _ hcv0 hcv1 hcv2 hcv3,
      ← bitOp64_two]
    exact reassemble_byteOp 2 (by omega)
      (env.get i₀).val ((Expression.eval env input_var_b[0] - env.get i₀) * 256⁻¹).val
      (env.get (i₀ + 1)).val ((Expression.eval env input_var_b[1] - env.get (i₀ + 1)) * 256⁻¹).val
      (env.get (i₀ + 2)).val ((Expression.eval env input_var_b[2] - env.get (i₀ + 2)) * 256⁻¹).val
      (env.get (i₀ + 3)).val ((Expression.eval env input_var_b[3] - env.get (i₀ + 3)) * 256⁻¹).val
      (env.get (i₀ + 4)).val ((Expression.eval env input_var_c[0] - env.get (i₀ + 4)) * 256⁻¹).val
      (env.get (i₀ + 4 + 1)).val ((Expression.eval env input_var_c[1] - env.get (i₀ + 4 + 1)) * 256⁻¹).val
      (env.get (i₀ + 4 + 2)).val ((Expression.eval env input_var_c[2] - env.get (i₀ + 4 + 2)) * 256⁻¹).val
      (env.get (i₀ + 4 + 3)).val ((Expression.eval env input_var_c[3] - env.get (i₀ + 4 + 3)) * 256⁻¹).val
      (env.get (i₀ + 8)).val (env.get (i₀ + 8 + 1)).val (env.get (i₀ + 8 + 2)).val (env.get (i₀ + 8 + 3)).val
      (env.get (i₀ + 8 + 4)).val (env.get (i₀ + 8 + 5)).val (env.get (i₀ + 8 + 6)).val (env.get (i₀ + 8 + 7)).val
      hxb0 hxb1 hxb2 hxb3 hxb4 hxb5 hxb6 hxc0 hxc1 hxc2 hxc3 hxc4 hxc5 hxc6
      hr0 hr1 hr2 hr3 hr4 hr5 hr6 hr7

/-- The witnessed high byte `(b − b_low)·256⁻¹` evaluates to `b.val / 256`. -/
lemma high_byte_eval (b : ZMod p) :
    (b - ((b.val % 256 : ℕ) : ZMod p)) * 256⁻¹ = ((b.val / 256 : ℕ) : ZMod p) := by
  have key : b = ((b.val % 256 : ℕ) : ZMod p) + ((b.val / 256 : ℕ) : ZMod p) * 256 := by
    calc b = ((b.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val b).symm
      _ = ((b.val % 256 + b.val / 256 * 256 : ℕ) : ZMod p) := by congr 1; omega
      _ = ((b.val % 256 : ℕ) : ZMod p) + ((b.val / 256 : ℕ) : ZMod p) * 256 := by push_cast; ring
  rw [show b - ((b.val % 256 : ℕ) : ZMod p) = ((b.val / 256 : ℕ) : ZMod p) * 256 from by
      linear_combination key,
    mul_assoc, mul_inv_cancel₀ val_256_ne_zero, mul_one]

/-- Forward AND: `(↑bn + ↑cn − 2·↑(bn&&&cn)).val = bn ^^^ cn` for bytes. -/
lemma and_fwd {bn cn : ℕ} (hbn : bn < 256) (hcn : cn < 256) :
    ((bn : ZMod p) + (cn : ZMod p) - 2 * ((bn &&& cn : ℕ) : ZMod p)).val = bn ^^^ cn := by
  have hp : 2 ^ 17 < p := Fact.out
  have hsum : 2 * (bn &&& cn) + (bn ^^^ cn) = bn + cn := Gadgets.And.And8.and_times_two_add_xor hbn hcn
  have hxor_lt : bn ^^^ cn < 256 := Nat.xor_lt_two_pow (n := 8) (by omega) (by omega)
  have heq : (bn : ZMod p) + (cn : ZMod p) - 2 * ((bn &&& cn : ℕ) : ZMod p) = ((bn ^^^ cn : ℕ) : ZMod p) := by
    have e1 : (2 * ((bn &&& cn : ℕ) : ZMod p)) = (((2 * (bn &&& cn)) : ℕ) : ZMod p) := by push_cast; ring
    rw [e1, ← Nat.cast_add, ← Nat.cast_sub (by omega),
      show bn + cn - 2 * (bn &&& cn) = bn ^^^ cn from by omega]
  rw [heq, ZMod.val_natCast_of_lt (by omega)]

/-- Forward OR: `(2·↑(bn|||cn) − ↑bn − ↑cn).val = bn ^^^ cn` for bytes. -/
lemma or_fwd {bn cn : ℕ} (hbn : bn < 256) (hcn : cn < 256) :
    (2 * ((bn ||| cn : ℕ) : ZMod p) - (bn : ZMod p) - (cn : ZMod p)).val = bn ^^^ cn := by
  have hp : 2 ^ 17 < p := Fact.out
  have hsum : 2 * (bn ||| cn) = bn + cn + (bn ^^^ cn) := or_two_mul hbn hcn
  have hxor_lt : bn ^^^ cn < 256 := Nat.xor_lt_two_pow (n := 8) (by omega) (by omega)
  have heq : 2 * ((bn ||| cn : ℕ) : ZMod p) - (bn : ZMod p) - (cn : ZMod p) = ((bn ^^^ cn : ℕ) : ZMod p) := by
    have e1 : (2 * ((bn ||| cn : ℕ) : ZMod p)) = (((2 * (bn ||| cn)) : ℕ) : ZMod p) := by push_cast; ring
    rw [e1, show 2 * (bn ||| cn) = bn + cn + (bn ^^^ cn) from hsum]
    push_cast; ring
  rw [heq, ZMod.val_natCast_of_lt (by omega)]

/-- Forward XOR: `(↑(bn^^^cn)).val = bn ^^^ cn` for bytes. -/
lemma xor_fwd {bn cn : ℕ} (hbn : bn < 256) (hcn : cn < 256) :
    (((bn ^^^ cn : ℕ)) : ZMod p).val = bn ^^^ cn := by
  have hp : 2 ^ 17 < p := Fact.out
  have : bn ^^^ cn < 256 := Nat.xor_lt_two_pow (n := 8) (by omega) (by omega)
  exact ZMod.val_natCast_of_lt (by omega)

set_option maxHeartbeats 2000000 in
theorem completeness : Completeness (ZMod p) main Assumptions := by
  circuit_proof_start
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨hb, hc, hop⟩ := h_assumptions
  obtain ⟨hib, hic, hiop⟩ := h_input
  obtain ⟨gb, gc, gr⟩ := h_env
  obtain ⟨hbU0, hbU1, hbU2, hbU3⟩ := Word.lt_cases_of_isU64 hb
  obtain ⟨hcU0, hcU1, hcU2, hcU3⟩ := Word.lt_cases_of_isU64 hc
  have eb0 : Expression.eval env.toEnvironment input_var_b[0] = input_b[0] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb1 : Expression.eval env.toEnvironment input_var_b[1] = input_b[1] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb2 : Expression.eval env.toEnvironment input_var_b[2] = input_b[2] := by rw [← hib]; simp only [Vector.getElem_map]
  have eb3 : Expression.eval env.toEnvironment input_var_b[3] = input_b[3] := by rw [← hib]; simp only [Vector.getElem_map]
  have ec0 : Expression.eval env.toEnvironment input_var_c[0] = input_c[0] := by rw [← hic]; simp only [Vector.getElem_map]
  have ec1 : Expression.eval env.toEnvironment input_var_c[1] = input_c[1] := by rw [← hic]; simp only [Vector.getElem_map]
  have ec2 : Expression.eval env.toEnvironment input_var_c[2] = input_c[2] := by rw [← hic]; simp only [Vector.getElem_map]
  have ec3 : Expression.eval env.toEnvironment input_var_c[3] = input_c[3] := by rw [← hic]; simp only [Vector.getElem_map]
  have g_b0 : env.get i₀ = ((input_b[0].val % 256 : ℕ) : ZMod p) := by simpa [eb0] using gb 0
  have g_b1 : env.get (i₀ + 1) = ((input_b[1].val % 256 : ℕ) : ZMod p) := by simpa [eb1] using gb 1
  have g_b2 : env.get (i₀ + 2) = ((input_b[2].val % 256 : ℕ) : ZMod p) := by simpa [eb2] using gb 2
  have g_b3 : env.get (i₀ + 3) = ((input_b[3].val % 256 : ℕ) : ZMod p) := by simpa [eb3] using gb 3
  have g_c0 : env.get (i₀ + 4) = ((input_c[0].val % 256 : ℕ) : ZMod p) := by simpa [ec0] using gc 0
  have g_c1 : env.get (i₀ + 4 + 1) = ((input_c[1].val % 256 : ℕ) : ZMod p) := by simpa [ec1] using gc 1
  have g_c2 : env.get (i₀ + 4 + 2) = ((input_c[2].val % 256 : ℕ) : ZMod p) := by simpa [ec2] using gc 2
  have g_c3 : env.get (i₀ + 4 + 3) = ((input_c[3].val % 256 : ℕ) : ZMod p) := by simpa [ec3] using gc 3
  have g_r0 : env.get (i₀ + 4 + 4) = ((byteOp input_opcode.val (input_b[0].val % 256) (input_c[0].val % 256) : ℕ) : ZMod p) := by simpa [eb0, ec0] using gr 0
  have g_r1 : env.get (i₀ + 4 + 4 + 1) = ((byteOp input_opcode.val (input_b[0].val / 256) (input_c[0].val / 256) : ℕ) : ZMod p) := by simpa [eb0, ec0] using gr 1
  have g_r2 : env.get (i₀ + 4 + 4 + 2) = ((byteOp input_opcode.val (input_b[1].val % 256) (input_c[1].val % 256) : ℕ) : ZMod p) := by simpa [eb1, ec1] using gr 2
  have g_r3 : env.get (i₀ + 4 + 4 + 3) = ((byteOp input_opcode.val (input_b[1].val / 256) (input_c[1].val / 256) : ℕ) : ZMod p) := by simpa [eb1, ec1] using gr 3
  have g_r4 : env.get (i₀ + 4 + 4 + 4) = ((byteOp input_opcode.val (input_b[2].val % 256) (input_c[2].val % 256) : ℕ) : ZMod p) := by simpa [eb2, ec2] using gr 4
  have g_r5 : env.get (i₀ + 4 + 4 + 5) = ((byteOp input_opcode.val (input_b[2].val / 256) (input_c[2].val / 256) : ℕ) : ZMod p) := by simpa [eb2, ec2] using gr 5
  have g_r6 : env.get (i₀ + 4 + 4 + 6) = ((byteOp input_opcode.val (input_b[3].val % 256) (input_c[3].val % 256) : ℕ) : ZMod p) := by simpa [eb3, ec3] using gr 6
  have g_r7 : env.get (i₀ + 4 + 4 + 7) = ((byteOp input_opcode.val (input_b[3].val / 256) (input_c[3].val / 256) : ℕ) : ZMod p) := by simpa [eb3, ec3] using gr 7
  have hand_sel : ∀ b c r : ZMod p,
      (0 - 1) * (0 - 2) * 2⁻¹ * (b + c - 2 * r) - 0 * (0 - 2) * (2 * r - b - c)
          + 0 * (0 - 1) * 2⁻¹ * r = b + c - 2 * r := by
    intro b c r
    have h2 : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ two_ne_zero'
    linear_combination (b + c - 2 * r) * h2
  have hor_sel : ∀ b c r : ZMod p,
      (1 - 1) * (1 - 2) * 2⁻¹ * (b + c - 2 * r) - 1 * (1 - 2) * (2 * r - b - c)
          + 1 * (1 - 1) * 2⁻¹ * r = 2 * r - b - c := by
    intro b c r; ring
  have hxor_sel : ∀ b c r : ZMod p,
      (2 - 1) * (2 - 2) * 2⁻¹ * (b + c - 2 * r) - 2 * (2 - 2) * (2 * r - b - c)
          + 2 * (2 - 1) * 2⁻¹ * r = r := by
    intro b c r
    have h2 : (2 : ZMod p) * 2⁻¹ = 1 := mul_inv_cancel₀ two_ne_zero'
    linear_combination r * h2
  have hv2 : (2 : ZMod p).val = 2 := by
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by norm_num]
    exact ZMod.val_natCast_of_lt (by omega)
  have hopcase : input_opcode = 0 ∨ input_opcode = 1 ∨ input_opcode = 2 := by
    have key : input_opcode = ((input_opcode.val : ℕ) : ZMod p) := (ZMod.natCast_zmod_val input_opcode).symm
    rcases (show input_opcode.val = 0 ∨ input_opcode.val = 1 ∨ input_opcode.val = 2 from by omega) with h | h | h
    · exact Or.inl (by calc input_opcode = ((input_opcode.val : ℕ) : ZMod p) := key
        _ = ((0 : ℕ) : ZMod p) := by rw [h]
        _ = 0 := by norm_num)
    · exact Or.inr (Or.inl (by calc input_opcode = ((input_opcode.val : ℕ) : ZMod p) := key
        _ = ((1 : ℕ) : ZMod p) := by rw [h]
        _ = 1 := by norm_num))
    · exact Or.inr (Or.inr (by calc input_opcode = ((input_opcode.val : ℕ) : ZMod p) := key
        _ = ((2 : ℕ) : ZMod p) := by rw [h]
        _ = 2 := by norm_num))
  simp only [circuit_norm, ByteXorTable, g_b0, g_b1, g_b2, g_b3, g_c0, g_c1, g_c2, g_c3,
    g_r0, g_r1, g_r2, g_r3, g_r4, g_r5, g_r6, g_r7, eb0, eb1, eb2, eb3, ec0, ec1, ec2, ec3,
    high_byte_eval, ← sub_eq_add_neg]
  have vb0 : ((input_b[0].val % 256 : ℕ) : ZMod p).val = input_b[0].val % 256 := ZMod.val_natCast_of_lt (by omega)
  have vb1 : ((input_b[1].val % 256 : ℕ) : ZMod p).val = input_b[1].val % 256 := ZMod.val_natCast_of_lt (by omega)
  have vb2 : ((input_b[2].val % 256 : ℕ) : ZMod p).val = input_b[2].val % 256 := ZMod.val_natCast_of_lt (by omega)
  have vb3 : ((input_b[3].val % 256 : ℕ) : ZMod p).val = input_b[3].val % 256 := ZMod.val_natCast_of_lt (by omega)
  have vB0 : ((input_b[0].val / 256 : ℕ) : ZMod p).val = input_b[0].val / 256 := ZMod.val_natCast_of_lt (by omega)
  have vB1 : ((input_b[1].val / 256 : ℕ) : ZMod p).val = input_b[1].val / 256 := ZMod.val_natCast_of_lt (by omega)
  have vB2 : ((input_b[2].val / 256 : ℕ) : ZMod p).val = input_b[2].val / 256 := ZMod.val_natCast_of_lt (by omega)
  have vB3 : ((input_b[3].val / 256 : ℕ) : ZMod p).val = input_b[3].val / 256 := ZMod.val_natCast_of_lt (by omega)
  have vc0 : ((input_c[0].val % 256 : ℕ) : ZMod p).val = input_c[0].val % 256 := ZMod.val_natCast_of_lt (by omega)
  have vc1 : ((input_c[1].val % 256 : ℕ) : ZMod p).val = input_c[1].val % 256 := ZMod.val_natCast_of_lt (by omega)
  have vc2 : ((input_c[2].val % 256 : ℕ) : ZMod p).val = input_c[2].val % 256 := ZMod.val_natCast_of_lt (by omega)
  have vc3 : ((input_c[3].val % 256 : ℕ) : ZMod p).val = input_c[3].val % 256 := ZMod.val_natCast_of_lt (by omega)
  have vC0 : ((input_c[0].val / 256 : ℕ) : ZMod p).val = input_c[0].val / 256 := ZMod.val_natCast_of_lt (by omega)
  have vC1 : ((input_c[1].val / 256 : ℕ) : ZMod p).val = input_c[1].val / 256 := ZMod.val_natCast_of_lt (by omega)
  have vC2 : ((input_c[2].val / 256 : ℕ) : ZMod p).val = input_c[2].val / 256 := ZMod.val_natCast_of_lt (by omega)
  have vC3 : ((input_c[3].val / 256 : ℕ) : ZMod p).val = input_c[3].val / 256 := ZMod.val_natCast_of_lt (by omega)
  rcases hopcase with hop0 | hop1 | hop2
  · subst hop0
    simp only [ZMod.val_zero, byteOp_zero, hand_sel,
      vb0, vb1, vb2, vb3, vB0, vB1, vB2, vB3, vc0, vc1, vc2, vc3, vC0, vC1, vC2, vC3]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> first | omega | exact and_fwd (by omega) (by omega)
  · subst hop1
    simp only [ZMod.val_one, byteOp_one, hor_sel,
      vb0, vb1, vb2, vb3, vB0, vB1, vB2, vB3, vc0, vc1, vc2, vc3, vC0, vC1, vC2, vC3]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> first | omega | exact or_fwd (by omega) (by omega)
  · subst hop2
    simp only [hv2, byteOp_two, hxor_sel,
      vb0, vb1, vb2, vb3, vB0, vB1, vB2, vB3, vc0, vc1, vc2, vc3, vC0, vC1, vC2, vC3]
    refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
      ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩ <;> first | omega | exact xor_fwd (by omega) (by omega)

/-- The witnessed `FormalCircuit` for byte-decomposed AND/OR/XOR. -/
def circuit : FormalCircuit (ZMod p) Inputs Extracted.BitwiseOperation :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

end SP1Clean.BitwiseU16Operation
