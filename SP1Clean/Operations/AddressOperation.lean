import SP1Clean.Specs.Operation
import SP1Clean.Foundations.Word
import SP1Clean.Foundations.ByteTable
import SP1Clean.Foundations.Channels
import SP1Clean.Operations.AddrAddOperation.Formal
import SP1Clean.Extracted.AddressOperation
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Gadgets.Bits
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `AddressOperation` as a Clean-native witnessed `FormalCircuit`

Computes a memory address `b + cc` (via `AddrAddOperation`) together with its 3-bit byte offset.
The `offset_bit{0,1,2}` are asserted boolean; `top_two_limb_inv` witnesses that the top two address
limbs are non-zero (the `value[1]+value[2]` inverse gate); and the low 3 bits of `value[0]` are
range-checked (`(value[0] - 4·b₂ - 2·b₁ - b₀)/8 < 2^13`) to pin the offset decomposition.

Address limbs are witnessed via `AddrAddOperation.populate`; `AddrAddOperation` (a `FormalAssertion`)
is composed as a Clean `assertion` (`is_real := 1`). `RawSpec` composes `AddrAddOperation.RawSpec`
plus the offset constraints; `Faithful/AddressOperation.lean` anchors it to the generated
`Extracted.AddressOperation.asserts`/`interactions` lists. Soundness and completeness are axiom-clean. -/

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
  have h := Fact.out (p := 2 ^ 17 < p)
  have : (2 : ℕ) ^ 13 < 2 ^ 17 := by norm_num
  omega

/-- The operands are genuine 64-bit values whose sum is a **valid, non-reserved, offset-decomposed**
48-bit address. Beyond the `AddrAddOperation` precondition (`(b + cc) mod 2^64 < 2^48`): the three
offset bits are boolean; the address is non-reserved (`≥ 2^16`, so the top two limbs `value[1] +
value[2] ≠ 0` and the inverse gate is satisfiable); and the offset bits are the low 3 bits of the
address (`offset0 + 2·offset1 + 4·offset2 = addr mod 8`, so the offset range check holds). Soundness
ignores the last four conjuncts (it derives them from the in-circuit inverse gate / range check);
they are the completeness-side "the prover commits a valid aligned address" obligations. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  Word.isU64 input.b ∧ Word.isU64 input.cc ∧
    (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 64 < 2 ^ 48 ∧
    (input.offset_bit0 = 0 ∨ input.offset_bit0 = 1) ∧
    (input.offset_bit1 = 0 ∨ input.offset_bit1 = 1) ∧
    (input.offset_bit2 = 0 ∨ input.offset_bit2 = 1) ∧
    2 ^ 16 ≤ (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 ∧
    input.offset_bit0.val + 2 * input.offset_bit1.val + 4 * input.offset_bit2.val
      = (Word.toNat input.b + Word.toNat input.cc) % 2 ^ 48 % 8

/-- Raw → semantic core (for the `Faithful` anchor): the literal `AddressOperation` constraint list
at `is_real = 1` implies the semantic `Spec` — the address sum from the composed
`AddrAddOperation.RawSpec` (via `addrAddSemantics_of_carries`), the offset booleans verbatim. The
inverse gate and offset range check do not contribute to `Spec`. -/
theorem addressSemantics_of_raw {input : Inputs (ZMod p)}
    {cols : Extracted.AddressOperation (ZMod p)}
    (hb : Word.isU64 input.b) (hcc : Word.isU64 input.cc)
    (h_raw : RawSpec input.b input.cc input.offset_bit0 input.offset_bit1 input.offset_bit2 cols) :
    Spec input cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_aa_raw, hob0, hob1, hob2, _h_inv, _h_range⟩ := h_raw
  have hbW : Word.isU64 #v[input.b[0], input.b[1], input.b[2], input.b[3]] :=
    Word.isU64_of_cases (hb 0) (hb 1) (hb 2) (hb 3)
  have hccW : Word.isU64 #v[input.cc[0], input.cc[1], input.cc[2], input.cc[3]] :=
    Word.isU64_of_cases (hcc 0) (hcc 1) (hcc 2) (hcc 3)
  have h_sum := AddrAddOperation.addrAddSemantics_of_carries hbW hccW h_aa_raw
  refine ⟨?_, hob0, hob1, hob2⟩
  rw [show Word.toNat #v[input.b[0], input.b[1], input.b[2], input.b[3]] = Word.toNat input.b from rfl,
      show Word.toNat #v[input.cc[0], input.cc[1], input.cc[2], input.cc[3]] = Word.toNat input.cc from rfl]
    at h_sum
  exact h_sum

/-! ## The witnessed `FormalCircuit`

Witnesses the address limbs via `AddrAddOperation.populate` and composes the gadget as a Clean
`assertion` (`is_real := 1`). Byte-bus limb range checks come from the gadget's `assertion`;
the offset booleans, the top-two-limb inverse gate, and the low-3-bits offset range check stay here. -/

def main (input : Var Inputs (ZMod p)) :
    Circuit (ZMod p) (Var Extracted.AddressOperation (ZMod p)) := do
  let value ← witnessVector 3 (fun env =>
    AddrAddOperation.populate
      #v[env input.b[0], env input.b[1], env input.b[2], env input.b[3]]
      #v[env input.cc[0], env input.cc[1], env input.cc[2], env input.cc[3]])
  assertion AddrAddOperation.circuit ⟨input.b, input.cc, ⟨value⟩, 1⟩
  let inv ← witnessVector 1 (fun env =>
    #v[(env value[1] + env value[2])⁻¹])
  input.offset_bit0 * (input.offset_bit0 - 1) === 0
  input.offset_bit1 * (input.offset_bit1 - 1) === 0
  input.offset_bit2 * (input.offset_bit2 - 1) === 0
  inv[0] * (value[1] + value[2]) - 1 === 0
  -- offset low-3-bits range check via the **byte bus** (SP1's `Range(13)` send,
  -- `Extracted/AddressOperation.lean`), not a `ToBits` bit-decomposition: the offset decomposition
  -- `(value[0] - 4·b₂ - 2·b₁ - b₀)/8 < 2^13` as a `byteChannel` `Range` receive (mult `1` — the gadget
  -- runs at `is_real = 1`, like the composed `AddrAddOperation` assertion's sends).
  byteChannel.gatedReceive 1
    (⟨6, (value[0] - 4 * input.offset_bit2 - 2 * input.offset_bit1 - input.offset_bit0) * (8 : ZMod p)⁻¹,
       Expression.const ((13 : ℕ) : ZMod p), 0⟩ : ByteRow (Expression (ZMod p)))
  return ⟨⟨value⟩, inv[0]⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Extracted.AddressOperation main where
  -- 3 address limbs + 1 inverse witness; the offset range check is now a byte-bus `Range` receive
  -- (witnesses nothing), and AddrAddOperation (FormalAssertion) adds no cells.
  localLength _ := 3 + 1
  output _ i0 := ⟨varFromOffset Extracted.AddrAddOperation i0, var ⟨i0 + 3⟩⟩
  -- byte-bus channels propagated from the AddrAddOperation assertion.
  channelsWithGuarantees := [byteChannel.toRawGated]
  channelsWithRequirements := [byteChannel.toRawGated]

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
      : List (RawChannel (ZMod p))) = [byteChannel.toRawGated] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    ((elaborated (p := p)).channelsWithRequirements
      : List (RawChannel (ZMod p))) = [byteChannel.toRawGated] := rfl

set_option maxHeartbeats 4000000 in
theorem soundness : Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨hb, hcc, hfit, _, _, _, _, _⟩ := h_assumptions
  obtain ⟨h_addrAdd, hob0, hob1, hob2, _h_inv⟩ := h_holds
  -- The address-sum equation is the composed `AddrAdd` `assertion`'s `Spec` (its `Assumptions →
  -- Spec`, fed the operand `isU64`s + address-fits + `is_real = 1`, then the gated content); the
  -- offset booleans are the three boolean gates. The inverse gate + range check don't enter `Spec`.
  have h_aa := (h_addrAdd ⟨hb, hcc, hfit, Or.inr rfl⟩) rfl
  simp only [circuit_norm] at h_aa
  -- channel-requirement tail: AddrAdd assertion owes its Assumptions (byte-bus pull).
  exact ⟨⟨h_aa.1, bool_of_mul_pred hob0, bool_of_mul_pred hob1, bool_of_mul_pred hob2⟩,
    Or.inr ⟨hb, hcc, hfit, Or.inr rfl⟩⟩

set_option maxHeartbeats 4000000 in
theorem completeness : Completeness (ZMod p) main Assumptions := by
  circuit_proof_start
  obtain ⟨hb, hcc, hfit, hob0, hob1, hob2, haddr_ge, hoff⟩ := h_assumptions
  obtain ⟨hbi, hci, -, -, -⟩ := h_input
  obtain ⟨h_value, h_inv_def⟩ := h_env
  have hp : 131072 < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  -- the witnessed `value` = `populate b cc`: discharges the AddrAdd assertion via `spec_populate`.
  have hbeq : (#v[Expression.eval env.toEnvironment input_var_b[0],
      Expression.eval env.toEnvironment input_var_b[1],
      Expression.eval env.toEnvironment input_var_b[2],
      Expression.eval env.toEnvironment input_var_b[3]] : Word (ZMod p)) = input_b := by
    rw [← hbi]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hceq : (#v[Expression.eval env.toEnvironment input_var_cc[0],
      Expression.eval env.toEnvironment input_var_cc[1],
      Expression.eval env.toEnvironment input_var_cc[2],
      Expression.eval env.toEnvironment input_var_cc[3]] : Word (ZMod p)) = input_cc := by
    rw [← hci]; apply Vector.ext; intro i hi; simp only [Vector.getElem_map]; interval_cases i <;> rfl
  have hval : (Vector.map (Expression.eval env.toEnvironment)
        (Vector.mapRange 3 fun i => var {index := i₀ + i}) : Vector (ZMod p) 3)
      = AddrAddOperation.populate input_b input_cc := by
    apply Vector.ext; intro i hi
    simp only [Vector.getElem_map, Vector.getElem_mapRange, circuit_norm]
    rw [h_value ⟨i, hi⟩, hbeq, hceq]
  -- the witnessed limbs equal `populate`'s, so the gadget `Spec` (sum + limb ranges) talks about them.
  have he0 : env.get i₀ = (AddrAddOperation.populate input_b input_cc)[0] := by
    have h := h_value ⟨0, by omega⟩; rw [hbeq, hceq] at h; simpa using h
  have he1 : env.get (i₀ + 1) = (AddrAddOperation.populate input_b input_cc)[1] := by
    have h := h_value ⟨1, by omega⟩; rw [hbeq, hceq] at h; simpa using h
  have he2 : env.get (i₀ + 2) = (AddrAddOperation.populate input_b input_cc)[2] := by
    have h := h_value ⟨2, by omega⟩; rw [hbeq, hceq] at h; simpa using h
  -- the gadget `Spec` (sum + limb ranges) for the witnessed value, on the `is_real = 1` row.
  have h_aa := (AddrAddOperation.spec_populate hb hcc (1 : ZMod p)) rfl
  simp only [circuit_norm] at h_aa
  rw [← he0, ← he1, ← he2] at h_aa
  obtain ⟨h_sum, hv0lt, hv1lt, hv2lt⟩ := h_aa
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
  have h8ne : (8 : ZMod p) ≠ 0 := by
    have h8v : ((8 : ℕ) : ZMod p).val = 8 := ZMod.val_natCast_of_lt (lt_trans (by norm_num) hp)
    rw [show (8 : ZMod p) = ((8 : ℕ) : ZMod p) from by norm_cast]
    intro hz; rw [hz, ZMod.val_zero] at h8v; exact absurd h8v (by norm_num)
  have hcast0 : ((input_offset_bit0.val : ℕ) : ZMod p) = input_offset_bit0 := ZMod.natCast_zmod_val _
  have hcast1 : ((input_offset_bit1.val : ℕ) : ZMod p) = input_offset_bit1 := ZMod.natCast_zmod_val _
  have hcast2 : ((input_offset_bit2.val : ℕ) : ZMod p) = input_offset_bit2 := ZMod.natCast_zmod_val _
  -- range-check argument decomposes as `8 · (v0 / 8)` (offset bits = low 3 bits of `v0`).
  have hmod8 : A % 8 = A % 2 ^ 16 % 8 := (Nat.mod_mod_of_dvd A (by norm_num)).symm
  have hdecomp : v0 + -(4 * input_offset_bit2) + -(2 * input_offset_bit1) + -input_offset_bit0
      = ((8 * (A % 2 ^ 16 / 8) : ℕ) : ZMod p) := by
    have h1 : v0 = ((A % 2 ^ 16 : ℕ) : ZMod p) := by rw [← hv0_eq, ZMod.natCast_zmod_val]
    have h2 : 4 * input_offset_bit2 + 2 * input_offset_bit1 + input_offset_bit0
        = ((A % 2 ^ 16 % 8 : ℕ) : ZMod p) := by
      rw [← hmod8, ← hoff]; push_cast [hcast0, hcast1, hcast2]; ring
    have h3 : A % 2 ^ 16 - A % 2 ^ 16 % 8 = 8 * (A % 2 ^ 16 / 8) := by omega
    rw [h1, show ((A % 2 ^ 16 : ℕ) : ZMod p) + -(4 * input_offset_bit2) + -(2 * input_offset_bit1)
        + -input_offset_bit0 = ((A % 2 ^ 16 : ℕ) : ZMod p) - ((A % 2 ^ 16 % 8 : ℕ) : ZMod p) from by
      linear_combination -h2, ← Nat.cast_sub (Nat.mod_le _ _), h3]
  refine ⟨⟨⟨hb, hcc, hfit, Or.inr rfl⟩, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hval]; exact AddrAddOperation.spec_populate hb hcc (1 : ZMod p)
  · rcases hob0 with h | h <;> rw [h] <;> simp
  · rcases hob1 with h | h <;> rw [h] <;> simp
  · rcases hob2 with h | h <;> rw [h] <;> simp
  · rw [h_inv_def, inv_mul_cancel₀ hsum_ne]; simp
  · -- the byte-bus `Range(13)` guarantee: `ByteRowSpec ⟨6, arg, 13, 0⟩ ↔ arg.val < 2^13`.
    have h13p : (13 : ℕ) < p := by omega
    have c13 : ((13 : ℕ) : ZMod p) = (13 : ZMod p) := by norm_cast
    simp only [circuit_norm, byteChannel]
    rw [← c13]
    refine (byteRowSpec_range _ h13p).mpr ?_
    show ((v0 + -(4 * input_offset_bit2) + -(2 * input_offset_bit1) + -input_offset_bit0)
        * (8 : ZMod p)⁻¹).val < 2 ^ 13
    rw [hdecomp, show ((8 * (A % 2 ^ 16 / 8) : ℕ) : ZMod p)
        = (8 : ZMod p) * ((A % 2 ^ 16 / 8 : ℕ) : ZMod p) from by push_cast; ring,
      mul_comm (8 : ZMod p), mul_assoc, mul_inv_cancel₀ h8ne, mul_one,
      ZMod.val_natCast_of_lt (by omega : A % 2 ^ 16 / 8 < p)]
    omega

/-- The witnessed `FormalCircuit` for the address operation; output is SP1's `AddressOperation`
column struct. -/
def circuit : FormalCircuit (ZMod p) Inputs Extracted.AddressOperation :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma circuit_localLength (x : Var Inputs (ZMod p)) :
    circuit.localLength x = 3 + 1 := rfl

end SP1Clean.AddressOperation
