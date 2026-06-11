import SP1Clean.Specs.Operation
import SP1Clean.Foundations.Word
import SP1Clean.Foundations.Bitwise
import SP1Clean.Foundations.Channels
import SP1Clean.Foundations.ByteTable
import SP1Clean.Extracted.U16toU8OperationSafe
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Bits
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `U16toU8OperationSafe` as a Clean-native gadget

The **safe** u16→u8 byte split: witness the four low bytes `low_bytes[i]`, read off the high bytes
`high_i = (u16_values[i] - low_bytes[i]) * 256⁻¹`, and range-check every low and high byte to
`< 256`. So the eight output bytes `[low₀, high₀, …, low₃, high₃]` are the genuine little-endian
decomposition of the four limbs. `Faithful/U16toU8OperationSafe.lean` anchors `RawSpec`. -/

namespace SP1Clean.U16toU8OperationSafe

open Circuit
open SP1Clean.Channels (byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

omit [Fact p.Prime] in
/-- `2 ^ 8 < p`, the side condition `Gadgets.ToBits.rangeCheck 8` needs. -/
lemma hn8 : 2 ^ 8 < p := by
  have h := Fact.out (p := 2 ^ 17 < p)
  have : (2 : ℕ) ^ 8 < 2 ^ 17 := by norm_num
  omega

/-- The literal meaning of SP1's `U16toU8OperationSafe` constraint list at `is_real = 1`: each
low byte and each derived high byte `(u16_values[i] - low_bytes[i]) * 256⁻¹` is a genuine byte. -/
def RawSpec (u16_values : Vector (ZMod p) 4) (cols : Extracted.U16toU8Operation (ZMod p)) : Prop :=
  (cols.low_bytes[0].val < 256 ∧ ((u16_values[0] - cols.low_bytes[0]) * 256⁻¹).val < 256) ∧
  (cols.low_bytes[1].val < 256 ∧ ((u16_values[1] - cols.low_bytes[1]) * 256⁻¹).val < 256) ∧
  (cols.low_bytes[2].val < 256 ∧ ((u16_values[2] - cols.low_bytes[2]) * 256⁻¹).val < 256) ∧
  (cols.low_bytes[3].val < 256 ∧ ((u16_values[3] - cols.low_bytes[3]) * 256⁻¹).val < 256)

/-- On a real row (`is_real = 1`) the four limbs are genuine 16-bit values, and `is_real` is binary. The
`< 2^16` precondition is **gated on `is_real`**: a padding row owes nothing, so the composing
`MulOperation` can feed witnessed operand limbs whose range checks are themselves `is_real`-gated. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 1 → input.u16_values[0].val < 2 ^ 16 ∧ input.u16_values[1].val < 2 ^ 16 ∧
    input.u16_values[2].val < 2 ^ 16 ∧ input.u16_values[3].val < 2 ^ 16) ∧
  (input.is_real = 0 ∨ input.is_real = 1)

/-- The reassembly identity `low + (u - low) * 256⁻¹ * 256 = u`. -/
lemma reassemble (u low : ZMod p) :
    u = low + (u - low) * (256 : ZMod p)⁻¹ * 256 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h256 : (256 : ZMod p)⁻¹ * 256 = 1 := inv_mul_cancel₀ val_256_ne_zero
  rw [mul_assoc, h256, mul_one]; ring

/-- The high byte `(u - (u.val % 256)) * 256⁻¹` of a 16-bit value is itself a byte. -/
lemma high_byte_lt (u : ZMod p) (hu : u.val < 2 ^ 16) :
    ((u - ((u.val % 256 : ℕ) : ZMod p)) * (256 : ZMod p)⁻¹).val < 2 ^ 8 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  have e16 : (2 : ℕ) ^ 16 = 65536 := by norm_num
  have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have e17 : (2 : ℕ) ^ 17 = 131072 := by norm_num
  rw [e16] at hu
  rw [e17] at hp
  have key : ((u.val % 256 : ℕ) : ZMod p) + ((256 * (u.val / 256) : ℕ) : ZMod p) = u := by
    rw [← Nat.cast_add, show u.val % 256 + 256 * (u.val / 256) = u.val from by omega,
      ZMod.natCast_zmod_val]
  have hdiff : u - ((u.val % 256 : ℕ) : ZMod p) = ((256 * (u.val / 256) : ℕ) : ZMod p) := by
    linear_combination -key
  rw [hdiff]
  have hcollapse : ((256 * (u.val / 256) : ℕ) : ZMod p) * (256 : ZMod p)⁻¹
      = ((u.val / 256 : ℕ) : ZMod p) := by
    push_cast
    rw [mul_comm (256 : ZMod p) ((u.val / 256 : ℕ) : ZMod p), mul_assoc,
      mul_inv_cancel₀ val_256_ne_zero, mul_one]
  rw [hcollapse, ZMod.val_natCast_of_lt (by omega : u.val / 256 < p), e8]
  omega

/-! ## The witnessed `FormalCircuit` -/

/-- The witness assignment (trace generation): each low byte is `u16_values[i] % 256` (the `% 256`
makes it a genuine byte unconditionally). Mirrors SP1's `populate_u16_to_u8_safe`. -/
def populate (u16_values : Word (ZMod p)) : Extracted.U16toU8Operation (ZMod p) :=
  ⟨#v[((u16_values[0].val % 256 : ℕ) : ZMod p), ((u16_values[1].val % 256 : ℕ) : ZMod p),
      ((u16_values[2].val % 256 : ℕ) : ZMod p), ((u16_values[3].val % 256 : ℕ) : ZMod p)]⟩

/-- SP1's `U16toU8OperationSafe::eval`: four `is_real`-gated byte pulls over the given low bytes.
Witnesses nothing (the column struct is an input). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let u16_values := input.u16_values
  let cols := input.cols
  let is_real := input.is_real
  byteChannel.pullIf is_real
    (⟨3, 0, cols.low_bytes[0], (u16_values[0] - cols.low_bytes[0]) * (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real
    (⟨3, 0, cols.low_bytes[1], (u16_values[1] - cols.low_bytes[1]) * (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real
    (⟨3, 0, cols.low_bytes[2], (u16_values[2] - cols.low_bytes[2]) * (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))
  byteChannel.pullIf is_real
    (⟨3, 0, cols.low_bytes[3], (u16_values[3] - cols.low_bytes[3]) * (256 : ZMod p)⁻¹⟩ : ByteRow (Expression (ZMod p)))

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRaw]
  channelsWithRequirements := [byteChannel.toRaw]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    ((elaborated (p := p)).channelsWithRequirements : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

set_option linter.unusedSimpArgs false in
/-- `populate u16_values` satisfies the gadget `Spec` for any `is_real`. The composing op uses this
to discharge its assertion obligation. -/
theorem spec_populate {u16_values : Word (ZMod p)}
    (h0 : u16_values[0].val < 2 ^ 16) (h1 : u16_values[1].val < 2 ^ 16)
    (h2 : u16_values[2].val < 2 ^ 16) (h3 : u16_values[3].val < 2 ^ 16) (is_real : ZMod p) :
    Spec (⟨u16_values, populate u16_values, is_real⟩ : Inputs (ZMod p)) := by
  have hp256 : (256 : ℕ) < p := by
    have h : (2 : ℕ) ^ 17 < p := Fact.out
    have h2' : (2 : ℕ) ^ 17 = 131072 := by norm_num
    omega
  have lowlt : ∀ (u : ZMod p), (((u.val % 256 : ℕ) : ZMod p)).val < 256 := fun u => by
    rw [ZMod.val_natCast_of_lt (by omega : u.val % 256 < p)]; omega
  intro _ i
  fin_cases i <;>
    simp only [populate, Spec, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
  · exact ⟨lowlt _, high_byte_lt _ h0, reassemble _ _⟩
  · exact ⟨lowlt _, high_byte_lt _ h1, reassemble _ _⟩
  · exact ⟨lowlt _, high_byte_lt _ h2, reassemble _ _⟩
  · exact ⟨lowlt _, high_byte_lt _ h3, reassemble _ _⟩

set_option maxHeartbeats 1000000 in
theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨_himp, _hbin⟩ := h_assumptions
  obtain ⟨hiu, hicols, _⟩ := h_input
  have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have ea0 : Expression.eval env input_var_u16_values[0] = input_u16_values[0] := by rw [← hiu]; simp only [Vector.getElem_map]
  have ea1 : Expression.eval env input_var_u16_values[1] = input_u16_values[1] := by rw [← hiu]; simp only [Vector.getElem_map]
  have ea2 : Expression.eval env input_var_u16_values[2] = input_u16_values[2] := by rw [← hiu]; simp only [Vector.getElem_map]
  have ea3 : Expression.eval env input_var_u16_values[3] = input_u16_values[3] := by rw [← hiu]; simp only [Vector.getElem_map]
  have el0 : Expression.eval env input_var_cols_low_bytes[0] = input_cols_low_bytes[0] := by rw [← hicols]; simp only [Vector.getElem_map]
  have el1 : Expression.eval env input_var_cols_low_bytes[1] = input_cols_low_bytes[1] := by rw [← hicols]; simp only [Vector.getElem_map]
  have el2 : Expression.eval env input_var_cols_low_bytes[2] = input_cols_low_bytes[2] := by rw [← hicols]; simp only [Vector.getElem_map]
  have el3 : Expression.eval env input_var_cols_low_bytes[3] = input_cols_low_bytes[3] := by rw [← hicols]; simp only [Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ea0, ea1, ea2, ea3, el0, el1, el2, el3] at h_holds ⊢
  obtain ⟨hr0, hr1, hr2, hr3⟩ := h_holds
  -- post-#398 the byte receives owe no padding requirement, so the goal is exactly `Spec`.
  intro hr1eq
  have hneg : -input_is_real = -1 := by rw [hr1eq]
  have R0 := hr0 hneg; have R1 := hr1 hneg; have R2 := hr2 hneg; have R3 := hr3 hneg
  rw [byteRowSpec_u8range_pair, e8, ← sub_eq_add_neg] at R0 R1 R2 R3
  intro i
  fin_cases i
  · exact ⟨R0.1, R0.2, reassemble _ _⟩
  · exact ⟨R1.1, R1.2, reassemble _ _⟩
  · exact ⟨R2.1, R2.2, reassemble _ _⟩
  · exact ⟨R3.1, R3.2, reassemble _ _⟩

set_option maxHeartbeats 1000000 in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  obtain ⟨_himp, hbin⟩ := h_assumptions
  obtain ⟨hiu, hicols, _⟩ := h_input
  have e8 : (2 : ℕ) ^ 8 = 256 := by norm_num
  have ea0 : Expression.eval env.toEnvironment input_var_u16_values[0] = input_u16_values[0] := by rw [← hiu]; simp only [Vector.getElem_map]
  have ea1 : Expression.eval env.toEnvironment input_var_u16_values[1] = input_u16_values[1] := by rw [← hiu]; simp only [Vector.getElem_map]
  have ea2 : Expression.eval env.toEnvironment input_var_u16_values[2] = input_u16_values[2] := by rw [← hiu]; simp only [Vector.getElem_map]
  have ea3 : Expression.eval env.toEnvironment input_var_u16_values[3] = input_u16_values[3] := by rw [← hiu]; simp only [Vector.getElem_map]
  have el0 : Expression.eval env.toEnvironment input_var_cols_low_bytes[0] = input_cols_low_bytes[0] := by rw [← hicols]; simp only [Vector.getElem_map]
  have el1 : Expression.eval env.toEnvironment input_var_cols_low_bytes[1] = input_cols_low_bytes[1] := by rw [← hicols]; simp only [Vector.getElem_map]
  have el2 : Expression.eval env.toEnvironment input_var_cols_low_bytes[2] = input_cols_low_bytes[2] := by rw [← hicols]; simp only [Vector.getElem_map]
  have el3 : Expression.eval env.toEnvironment input_var_cols_low_bytes[3] = input_cols_low_bytes[3] := by rw [← hicols]; simp only [Vector.getElem_map]
  simp only [circuit_norm, byteChannel, ea0, ea1, ea2, ea3, el0, el1, el2, el3]
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · intro hneg
    have hr1 : input_is_real = 1 := neg_inj.mp hneg
    have hsp := h_spec hr1
    rw [byteRowSpec_u8range_pair, e8, ← sub_eq_add_neg]
    first
      | exact ⟨(hsp 0).1, (hsp 0).2.1⟩
      | exact ⟨(hsp 1).1, (hsp 1).2.1⟩
      | exact ⟨(hsp 2).1, (hsp 2).2.1⟩
      | exact ⟨(hsp 3).1, (hsp 3).2.1⟩

/-- SP1's `U16toU8OperationSafe::eval` as a Clean-native `FormalAssertion`: `is_real`-gated byte-bus
range checks over the `populate`d low bytes, no fresh witnesses (the column struct is an input). -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

end SP1Clean.U16toU8OperationSafe
