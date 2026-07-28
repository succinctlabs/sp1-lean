import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Math.EvalVec
import SP1Clean.Math.Word
import SP1Clean.Model.ByteTable
import SP1Clean.Model.Channels
import SP1Clean.Proofs.Operations.AddrAddOperation.Formal
import SP1Clean.Extracted.AddressOperation
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Bits
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `AddressOperation` as a Clean-native witnessed `GeneralFormalCircuit`

Computes a memory address `b + cc` (via `AddrAddOperation`) together with its 3-bit byte offset.
The `offset_bit{0,1,2}` are asserted boolean; `top_two_limb_inv` witnesses that the top two address
limbs are non-zero (the `value[1]+value[2]` inverse gate); and the low 3 bits of `value[0]` are
range-checked (`(value[0] - 4·b₂ - 2·b₁ - b₀)/8 < 2^13`) to pin the offset decomposition.

Address limbs are witnessed via `AddrAddOperation.populate`; `AddrAddOperation` (a `FormalAssertion`)
is composed as a Clean `assertion` (`is_real := 1`). `RawSpec` composes `AddrAddOperation.RawSpec`
plus the offset constraints; `Faithful/AddressOperation.lean` anchors it to the generated
`Extracted.AddressOperation.asserts`/`interactions` lists. Soundness and completeness are axiom-clean.

Measured elaboration floors (ladder against a 1-heartbeat control): `metadata_of_constraints`
(5k, 10k], `soundness` (5k, 10k], `completeness` (30k, 40k]. All three formerly carried a
4000000-heartbeat ceiling — 100-800x over — and now run at the plain default with >=5x
headroom. -/

namespace SP1Clean.AddressOperation

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : NeZero p := ⟨(Fact.out : p.Prime).pos.ne'⟩

/-- Literal meaning of SP1's `AddressOperation` constraint list at `is_real = 1`: the composed
`AddrAddOperation.RawSpec`, the three boolean offset bits, the top-two-limb inverse gate, and the
low-3-bits range check. -/
def RawSpec (b cc : Word (ZMod p)) (offset_bit0 offset_bit1 offset_bit2 : ZMod p)
    (cols : Extracted.AddressOperation (ZMod p)) : Prop :=
  AddrAddOperation.RawSpec #v[b[0], b[1], b[2], b[3]] #v[cc[0], cc[1], cc[2], cc[3]]
      cols.addr_operation ∧
  (offset_bit0 = 0 ∨ offset_bit0 = 1) ∧
  (offset_bit1 = 0 ∨ offset_bit1 = 1) ∧
  (offset_bit2 = 0 ∨ offset_bit2 = 1) ∧
  (cols.top_two_limb_inv * (cols.addr_operation.value[1] + cols.addr_operation.value[2]) - 1 = 0) ∧
  ((cols.addr_operation.value[0] - 4 * offset_bit2 - 2 * offset_bit1 - offset_bit0)
      * (8 : ZMod p)⁻¹).val < 2 ^ 13

omit [Fact p.Prime] in
/-- `2 ^ 13 < p`, the side condition for the offset `rangeCheck 13`. -/
lemma hn13 : 2 ^ 13 < p := by
  have := Fact.out (p := 2 ^ 17 < p); omega

/-- Soundness needs only genuine 64-bit operands. The circuit itself proves that their sum is a
valid 48-bit address and constrains the remaining address metadata. -/
def SoundnessAssumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.b ∧ Word.isU64 input.cc ∧
    (input.is_real = 0 ∨ input.is_real = 1)

/-- The honest prover supplies a **valid, non-reserved, offset-decomposed** 48-bit address. Beyond
the address-fit condition, the three
offset bits are boolean; the address is non-reserved (`≥ 2^16`, so the top two limbs `value[1] +
value[2] ≠ 0` and the inverse gate is satisfiable); and the offset bits are the low 3 bits of the
address (`offset0 + 2·offset1 + 4·offset2 = addr mod 8`, so the offset range check holds). These are
completeness-side witness-generation obligations, kept separate from `SoundnessAssumptions` by the
`GeneralFormalCircuit` boundary. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.b ∧ Word.isU64 input.cc ∧
    (input.is_real = 0 ∨ input.is_real = 1) ∧
    (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 64 < 2 ^ 48 ∧
    (input.offset_bit0 = 0 ∨ input.offset_bit0 = 1) ∧
    (input.offset_bit1 = 0 ∨ input.offset_bit1 = 1) ∧
    (input.offset_bit2 = 0 ∨ input.offset_bit2 = 1) ∧
    2 ^ 16 ≤ (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 ∧
    input.offset_bit0.val + 2 * input.offset_bit1.val + 4 * input.offset_bit2.val
      = (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 % 8

/-- The two address-specific AIR checks have their advertised Rust meaning: the inverse gate
excludes the reserved low 64 KiB, while the 13-bit byte-table range check proves that the three
boolean offset columns are precisely the low bits of the raw address. -/
theorem metadata_of_constraints
    {v0 v1 v2 offset0 offset1 offset2 inv : ZMod p}
    (hv0 : v0.val < 2 ^ 16) (hv1 : v1.val < 2 ^ 16) (hv2 : v2.val < 2 ^ 16)
    (hob0 : offset0 = 0 ∨ offset0 = 1)
    (hob1 : offset1 = 0 ∨ offset1 = 1)
    (hob2 : offset2 = 0 ∨ offset2 = 1)
    (hInv : inv * (v1 + v2) - 1 = 0)
    (hRange : ((v0 - 4 * offset2 - 2 * offset1 - offset0) * (8 : ZMod p)⁻¹).val <
      2 ^ 13) :
    2 ^ 16 ≤ v0.val + 65536 * v1.val + 65536 ^ 2 * v2.val ∧
      offset0.val + 2 * offset1.val + 4 * offset2.val =
        (v0.val + 65536 * v1.val + 65536 ^ 2 * v2.val) % 8 := by
  have hp : 2 ^ 17 < p := Fact.out
  have h12ne : v1 + v2 ≠ 0 := by
    intro h
    rw [h, mul_zero, zero_sub] at hInv
    exact one_ne_zero (neg_eq_zero.mp hInv)
  have h12val : (v1 + v2).val = v1.val + v2.val :=
    ZMod.val_add_of_lt (by omega)
  have h12pos : 0 < v1.val + v2.val := by
    by_contra h
    have hz : (v1 + v2).val = 0 := by omega
    exact h12ne ((ZMod.val_eq_zero _).mp hz)
  refine ⟨by omega, ?_⟩
  let offset : ZMod p := 4 * offset2 + 2 * offset1 + offset0
  let q : ZMod p := (v0 - offset) * (8 : ZMod p)⁻¹
  have hRangeQ : q.val < 2 ^ 13 := by
    dsimp only [q, offset]
    convert hRange using 1
    ring_nf
  have h0le : offset0.val ≤ 1 := bool_val_le hob0
  have h1le : offset1.val ≤ 1 := bool_val_le hob1
  have h2le : offset2.val ≤ 1 := bool_val_le hob2
  have h2mul : (2 * offset1).val = 2 * offset1.val := by
    rw [ZMod.val_mul, val_2_zmod_p, Nat.mod_eq_of_lt (by omega)]
  have h4mul : (4 * offset2).val = 4 * offset2.val := by
    rw [ZMod.val_mul, val_4_zmod_p, Nat.mod_eq_of_lt (by omega)]
  have hFirstAdd :
      (4 * offset2 + 2 * offset1).val = 4 * offset2.val + 2 * offset1.val := by
    rw [ZMod.val_add_of_lt (by rw [h4mul, h2mul]; omega), h4mul, h2mul]
  have hOffsetVal :
      offset.val = offset0.val + 2 * offset1.val + 4 * offset2.val := by
    dsimp only [offset]
    rw [ZMod.val_add_of_lt (by rw [hFirstAdd]; omega), hFirstAdd]
    omega
  have hOffsetLt : offset.val < 8 := by omega
  have hField : v0 = offset + q * 8 := by
    dsimp only [q]
    rw [mul_assoc, inv_mul_cancel₀ val_8_ne_zero, mul_one]
    ring
  have hMulVal : (q * 8).val = q.val * 8 := by
    rw [ZMod.val_mul, val_8_zmod_p, Nat.mod_eq_of_lt (by omega)]
  have hAddVal : (offset + q * 8).val = offset.val + q.val * 8 := by
    rw [ZMod.val_add_of_lt (by rw [hMulVal]; omega), hMulVal]
  have hv0eq : v0.val = offset.val + q.val * 8 := by rw [hField, hAddVal]
  rw [← hOffsetVal, hv0eq]
  omega

/-- Raw → semantic core (for the `Faithful` anchor): the literal `AddressOperation` constraint list
at `is_real = 1` implies the semantic `Spec` — the address sum from the composed
`AddrAddOperation.RawSpec` (via `addrAddSemantics_of_carries`), the offset booleans verbatim, and
the valid-address facts from `metadata_of_constraints`. -/
theorem addressSemantics_of_raw {input : Inputs (ZMod p)}
    {cols : Extracted.AddressOperation (ZMod p)}
    (hb : Word.isU64 input.b) (hcc : Word.isU64 input.cc)
    (h_raw : RawSpec input.b input.cc input.offset_bit0 input.offset_bit1 input.offset_bit2 cols) :
    Spec input cols := by
  obtain ⟨h_aa_raw, hob0, hob1, hob2, h_inv, h_range⟩ := h_raw
  have hbW : Word.isU64 #v[input.b[0], input.b[1], input.b[2], input.b[3]] :=
    Word.isU64_of_cases (hb 0) (hb 1) (hb 2) (hb 3)
  have hccW : Word.isU64 #v[input.cc[0], input.cc[1], input.cc[2], input.cc[3]] :=
    Word.isU64_of_cases (hcc 0) (hcc 1) (hcc 2) (hcc 3)
  have h_sum := AddrAddOperation.addrAddSemantics_of_carries hbW hccW h_aa_raw
  have h_fit := AddrAddOperation.addrAddFits_of_carries hbW hccW h_aa_raw
  have hbNat : Word.toNat #v[input.b[0], input.b[1], input.b[2], input.b[3]] =
      Word.toNat input.b := rfl
  have hccNat : Word.toNat #v[input.cc[0], input.cc[1], input.cc[2], input.cc[3]] =
      Word.toNat input.cc := rfl
  rw [hbNat, hccNat] at h_sum h_fit
  have hSumInput :
      cols.addr_operation.value[0].val + 65536 * cols.addr_operation.value[1].val +
          65536 ^ 2 * cols.addr_operation.value[2].val =
        (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 := h_sum
  have hFitInput :
      (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 64 < 2 ^ 48 := h_fit
  obtain ⟨_, _, _, _, hv0, hv1, hv2⟩ := h_aa_raw
  have hMetadata := metadata_of_constraints hv0 hv1 hv2 hob0 hob1 hob2 h_inv h_range
  refine ⟨hSumInput, hob0, hob1, hob2, hFitInput, ?_, ?_, hv0, hv1, hv2⟩
  · rw [← hSumInput]
    exact hMetadata.1
  · rw [← hSumInput]
    exact hMetadata.2

/-! ## The witnessed `GeneralFormalCircuit`

Witnesses the address limbs via `AddrAddOperation.populate` and composes the gadget as a Clean
`assertion` (`is_real := 1`). Byte-bus limb range checks come from the gadget's `assertion`;
the offset booleans, the top-two-limb inverse gate, and the low-3-bits offset range check stay here. -/

def main (input : Var Inputs (ZMod p)) :
    Circuit (ZMod p) (Var Extracted.AddressOperation (ZMod p)) := do
  let value ← witnessVectorNative 3 (fun env =>
    AddrAddOperation.populate
      #v[env input.b[0], env input.b[1], env input.b[2], env input.b[3]]
      #v[env input.cc[0], env input.cc[1], env input.cc[2], env input.cc[3]])
  assertion AddrAddOperation.circuit ⟨input.b, input.cc, ⟨value⟩, input.is_real⟩
  let inv ← witnessVectorNative 1 (fun env =>
    #v[env input.is_real * (env value[1] + env value[2])⁻¹])
  assertZero (input.is_real * (input.is_real - 1))
  input.offset_bit0 * (input.offset_bit0 - 1) === 0
  input.offset_bit1 * (input.offset_bit1 - 1) === 0
  input.offset_bit2 * (input.offset_bit2 - 1) === 0
  inv[0] * (value[1] + value[2]) - input.is_real === 0
  -- offset low-3-bits range check via the **byte bus** (SP1's `Range(13)` send,
  -- `Extracted/AddressOperation.lean`), not a `ToBits` bit-decomposition: the offset decomposition
  -- `(value[0] - 4·b₂ - 2·b₁ - b₀)/8 < 2^13` as a `byteChannel` `Range` receive (mult `1` — the gadget
  -- runs at `is_real = 1`, like the composed `AddrAddOperation` assertion's sends).
  byteChannel.pullIf input.is_real
    (⟨6, (value[0] - 4 * input.offset_bit2 - 2 * input.offset_bit1 - input.offset_bit0) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  return ⟨⟨value⟩, inv[0]⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Extracted.AddressOperation main where
  -- 3 address limbs + 1 inverse witness; the offset range check is now a byte-bus `Range` receive
  -- (witnesses nothing), and AddrAddOperation (FormalAssertion) adds no cells.
  localLength _ := 3 + 1
  output _ i0 := ⟨varFromOffset Extracted.AddrAddOperation i0, var ⟨i0 + 3⟩⟩
  -- byte-bus channels propagated from the AddrAddOperation assertion.
  channelsWithGuarantees := [byteChannel.toRaw]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 3 + 1 := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma output_eq (x : Var Inputs (ZMod p)) (i0 : ℕ) :
    (elaborated (p := p)).output x i0
      = ⟨varFromOffset Extracted.AddrAddOperation i0, var ⟨i0 + 3⟩⟩ := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees
      : List (RawChannel (ZMod p))) = [byteChannel.toRaw] := rfl

theorem soundness :
    GeneralFormalCircuit.Soundness (ZMod p) main
      (fun input _ => SoundnessAssumptions input) (fun input cols _ => RowSpec input cols) := by
  circuit_proof_start
  obtain ⟨hb, hcc, hbin⟩ := h_assumptions
  obtain ⟨h_addrAdd, _, hob0, hob1, hob2, h_inv, h_range⟩ := h_holds
  have b0 := bool_of_mul_pred hob0
  have b1 := bool_of_mul_pred hob1
  have b2 := bool_of_mul_pred hob2
  refine ⟨⟨b0, b1, b2, fun hr => ?_⟩, Or.inr ⟨hb, hcc, hbin⟩, ?_⟩
  have hr' : input_is_real = 1 := by simpa only using hr
  -- The address-sum equation is the composed `AddrAdd` `assertion`'s `Spec` (its `Assumptions →
  -- Spec`, fed the operand `isU64`s + the shared row selector, then the gated content); the
  -- offset booleans are the three boolean gates. The inverse and range gates establish the
  -- non-reserved-address and exact low-three-bit facts.
  have h_aa := (h_addrAdd ⟨hb, hcc, hbin⟩) hr'
  simp only [circuit_norm] at h_aa
  have c13 : ((13 : ℕ) : ZMod p) = (13 : ZMod p) := by norm_cast
  have h13p : (13 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  have hneg : - input_is_real = -1 := congrArg Neg.neg hr'
  have h_range := h_range hneg
  simp only [byteChannel] at h_range
  rw [← c13] at h_range
  have h_range_nat := (byteRowSpec_range _ h13p).mp h_range
  have h_inv_real : env.get (i₀ + 3) *
      (env.get (i₀ + 1) + env.get (i₀ + 2)) - 1 = 0 := by
    simpa only [hr'] using h_inv
  have hMetadata := metadata_of_constraints h_aa.2.1 h_aa.2.2.1 h_aa.2.2.2.1 b0 b1 b2
    h_inv_real h_range_nat
  simp only [Spec, Vector.getElem_map, Vector.getElem_mapRange, Expression.eval]
  exact ⟨h_aa.1, b0, b1, b2, h_aa.2.2.2.2, by rw [← h_aa.1]; exact hMetadata.1,
    by rw [← h_aa.1]; exact hMetadata.2,
    h_aa.2.1, h_aa.2.2.1, h_aa.2.2.2.1⟩
  · intro h1 h0
    exact off_gate_vacuous hbin h1 h0

theorem completeness :
  GeneralFormalCircuit.Completeness (ZMod p) main
      (fun input _ _ => Assumptions input) (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨hb, hcc, hbin, hfit, hob0, hob1, hob2, haddr_ge, hoff⟩ := h_assumptions
  obtain ⟨hbi, hci, -, -, -, -⟩ := h_input
  obtain ⟨h_value, h_inv_def⟩ := h_env
  have hp : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  -- the witnessed `value` = `populate b cc`: discharges the AddrAdd assertion via `spec_populate`.
  have hbeq : (#v[Expression.eval env.toEnvironment input_var_b[0],
      Expression.eval env.toEnvironment input_var_b[1],
      Expression.eval env.toEnvironment input_var_b[2],
      Expression.eval env.toEnvironment input_var_b[3]] : Word (ZMod p)) = input_b := by
    rw [← hbi]; exact vec4_eval _ _
  have hceq : (#v[Expression.eval env.toEnvironment input_var_cc[0],
      Expression.eval env.toEnvironment input_var_cc[1],
      Expression.eval env.toEnvironment input_var_cc[2],
      Expression.eval env.toEnvironment input_var_cc[3]] : Word (ZMod p)) = input_cc := by
    rw [← hci]; exact vec4_eval _ _
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 3 fun i => var {index := i₀ + i}) : Vector (ZMod p) 3)
      = AddrAddOperation.populate input_b input_cc := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    have h := h_value ⟨i, hi⟩; simp only [hbeq, hceq] at h; exact h
  -- the witnessed limbs equal `populate`'s, so the gadget `Spec` (sum + limb ranges) talks about them.
  have he0 : env.get i₀ = (AddrAddOperation.populate input_b input_cc)[0] := by
    have h := h_value ⟨0, by omega⟩; simp only [hbeq, hceq] at h; simpa using h
  have he1 : env.get (i₀ + 1) = (AddrAddOperation.populate input_b input_cc)[1] := by
    have h := h_value ⟨1, by omega⟩; simp only [hbeq, hceq] at h; simpa using h
  have he2 : env.get (i₀ + 2) = (AddrAddOperation.populate input_b input_cc)[2] := by
    have h := h_value ⟨2, by omega⟩; simp only [hbeq, hceq] at h; simpa using h
  -- the gadget `Spec` (sum + limb ranges) for the witnessed value, on the `is_real = 1` row.
  have h_aa := (AddrAddOperation.spec_populate hb hcc hfit (1 : ZMod p)) rfl
  simp only [circuit_norm] at h_aa
  rw [← he0, ← he1, ← he2] at h_aa
  obtain ⟨h_sum, hv0lt, hv1lt, hv2lt, _⟩ := h_aa
  set v0 := env.get i₀ with hv0d
  set v1 := env.get (i₀ + 1) with hv1d
  set v2 := env.get (i₀ + 2) with hv2d
  set A := (Word.toNat input_b + Word.toNat input_cc) % 2 ^ 48 with hAd
  -- `v0` is the low 16 bits of the address; `A ≥ 2^16` ⟹ `v1 + v2 ≠ 0` (non-reserved).
  have hv0_eq : v0.val = A % 2 ^ 16 := by omega
  have hv12pos : 0 < v1.val + v2.val := by omega
  have hsum_ne : v1 + v2 ≠ 0 := by
    intro h
    have hval2 : (v1 + v2).val = v1.val + v2.val := ZMod.val_add_of_lt (by omega)
    rw [h, ZMod.val_zero] at hval2; omega
  have hcast0 : ((input_offset_bit0.val : ℕ) : ZMod p) = input_offset_bit0 := ZMod.natCast_zmod_val _
  have hcast1 : ((input_offset_bit1.val : ℕ) : ZMod p) = input_offset_bit1 := ZMod.natCast_zmod_val _
  have hcast2 : ((input_offset_bit2.val : ℕ) : ZMod p) = input_offset_bit2 := ZMod.natCast_zmod_val _
  -- range-check argument decomposes as `8 · (v0 / 8)` (offset bits = low 3 bits of `v0`).
  have hmod8 : A % 8 = A % 2 ^ 16 % 8 := (Nat.mod_mod_of_dvd A (by norm_num)).symm
  have hdecomp : v0 + -(4 * input_offset_bit2) + -(2 * input_offset_bit1) + - input_offset_bit0
      = ((8 * (A % 2 ^ 16 / 8) : ℕ) : ZMod p) := by
    have h1 : v0 = ((A % 2 ^ 16 : ℕ) : ZMod p) := by rw [← hv0_eq, ZMod.natCast_zmod_val]
    have h2 : 4 * input_offset_bit2 + 2 * input_offset_bit1 + input_offset_bit0
        = ((A % 2 ^ 16 % 8 : ℕ) : ZMod p) := by
      rw [← hmod8, ← hoff]; push_cast [hcast0, hcast1, hcast2]; ring
    have h3 : A % 2 ^ 16 - A % 2 ^ 16 % 8 = 8 * (A % 2 ^ 16 / 8) := by omega
    rw [h1, show ((A % 2 ^ 16 : ℕ) : ZMod p) + -(4 * input_offset_bit2) + -(2 * input_offset_bit1)
        + - input_offset_bit0 = ((A % 2 ^ 16 : ℕ) : ZMod p) - ((A % 2 ^ 16 % 8 : ℕ) : ZMod p) from by
      linear_combination -h2, ← Nat.cast_sub (Nat.mod_le _ _), h3]
  refine ⟨⟨⟨hb, hcc, hbin⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hval]
    exact AddrAddOperation.spec_populate hb hcc hfit input_is_real
  · rcases hbin with h | h <;> rw [h] <;> simp
  · rcases hob0 with h | h <;> rw [h] <;> simp
  · rcases hob1 with h | h <;> rw [h] <;> simp
  · rcases hob2 with h | h <;> rw [h] <;> simp
  · rcases hbin with h0 | h1
    · rw [h_inv_def, h0]
      simp
    · rw [h_inv_def, h1, one_mul, inv_mul_cancel₀ hsum_ne]
      simp
  · -- the byte-bus `Range(13)` guarantee: `ByteRowSpec ⟨6, arg, 13, 0⟩ ↔ arg.val < 2^13`.
    intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have h13p : (13 : ℕ) < p := by omega
    have c13 : ((13 : ℕ) : ZMod p) = (13 : ZMod p) := by norm_cast
    simp only [circuit_norm, byteChannel]
    rw [← c13]
    refine (byteRowSpec_range _ h13p).mpr ?_
    simp only [sub_eq_add_neg]
    show ((v0 + -(4 * input_offset_bit2) + -(2 * input_offset_bit1) + - input_offset_bit0)
        * (8 : ZMod p)⁻¹).val < 2 ^ 13
    rw [hdecomp, show ((8 * (A % 2 ^ 16 / 8) : ℕ) : ZMod p)
        = (8 : ZMod p) * ((A % 2 ^ 16 / 8 : ℕ) : ZMod p) from by push_cast; ring,
      mul_comm (8 : ZMod p), mul_assoc, mul_inv_cancel₀ val_8_ne_zero, mul_one,
      ZMod.val_natCast_of_lt (by omega : A % 2 ^ 16 / 8 < p)]
    omega

/-- The witnessed `GeneralFormalCircuit` for the address operation. Soundness assumes only 64-bit
operands; completeness retains the stronger valid-address witness contract. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs Extracted.AddressOperation :=
  { main, elaborated,
    Assumptions := fun input _ => SoundnessAssumptions input,
    Spec := fun input cols _ => RowSpec input cols,
    ProverAssumptions := fun input _ _ => Assumptions input,
    ProverSpec := fun _ _ _ => True,
    soundness := soundness,
    completeness := completeness,
    channelsWithRequirements := [],
    requirementsChannelsLawful := fun input_var i₀ => by
      simp only [circuit_norm, main, byteChannel]
      refine ⟨List.nil_subset _, ?_⟩
      intro env hgate hnotone hnotzero
      rcases bool_of_mul_pred hgate with hzero | hone
      · exact absurd hzero hnotzero
      · exact absurd (congrArg Neg.neg hone) hnotone }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 3 + 1 := rfl

end SP1Clean.AddressOperation
