import SP1Clean.Specs.Operation
import SP1Clean.Foundations.Word
import SP1Clean.Foundations.Bitwise
import SP1Clean.Extracted.U16toU8OperationUnsafe
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Bits
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `U16toU8OperationUnsafe` as a Clean-native gadget

The **unsafe** u16→u8 byte split: witness the low byte `low_bytes[i]` for each of four 16-bit
limbs and read off the high byte as `(u16_values[i] - low_bytes[i]) * 256⁻¹`. "Unsafe" because
it imposes no range constraints — SP1's extracted constraint list is empty, so the split is
purely the reassembly identity (the `U16toU8OperationSafe` sibling adds byte bounds).

`RawSpec` is `True`; `Faithful/U16toU8OperationUnsafe.lean` anchors it to
`Extracted.U16toU8OperationUnsafe.constraints`. Soundness and completeness are axiom-clean. -/

namespace SP1Clean.U16toU8OperationUnsafe

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The literal meaning of SP1's `U16toU8OperationUnsafe` constraint list: it is **empty**, so the
unsafe split imposes nothing. -/
def RawSpec (_u16_values : Vector (ZMod p) 4) (_cols : Extracted.U16toU8Operation (ZMod p)) : Prop :=
  True

/-- The four limbs are genuine 16-bit values (used by the semantic spec; the gadget itself is unsafe). -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  input.u16_values[0].val < 2 ^ 16 ∧ input.u16_values[1].val < 2 ^ 16 ∧
  input.u16_values[2].val < 2 ^ 16 ∧ input.u16_values[3].val < 2 ^ 16

/-- Soundness core: the reassembly identity holds for any witness, via `256⁻¹ * 256 = 1`. -/
theorem split_of_raw {input : Inputs (ZMod p)} {cols : Extracted.U16toU8Operation (ZMod p)}
    (_hin : Assumptions input) (_h_raw : RawSpec input.u16_values cols) : Spec input cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h256 : (256 : ZMod p)⁻¹ * 256 = 1 := inv_mul_cancel₀ val_256_ne_zero
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [mul_assoc, h256, mul_one]; ring

/-! ## The witnessed `FormalCircuit` -/

/-- Witness the four low bytes (`u16_values[i].val % 256`); no range checks (unsafe).
Returns `⟨low_bytes⟩`. -/
def main (input : Var Inputs (ZMod p)) :
    Circuit (ZMod p) (Var Extracted.U16toU8Operation (ZMod p)) := do
  let low_bytes ← witnessVector 4 (fun env =>
    #v[(((env input.u16_values[0]).val % 256 : ℕ) : ZMod p),
       (((env input.u16_values[1]).val % 256 : ℕ) : ZMod p),
       (((env input.u16_values[2]).val % 256 : ℕ) : ZMod p),
       (((env input.u16_values[3]).val % 256 : ℕ) : ZMod p)])
  return ⟨low_bytes⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Extracted.U16toU8Operation main where
  localLength _ := 4
  output _ i0 := varFromOffset Extracted.U16toU8Operation i0

theorem soundness : Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  exact split_of_raw (cols := ⟨#v[env.get i₀, env.get (i₀ + 1), env.get (i₀ + 2), env.get (i₀ + 3)]⟩)
    h_assumptions trivial

omit [Fact (2 ^ 17 < p)] in
theorem completeness : Completeness (ZMod p) main Assumptions := by
  circuit_proof_start

/-- The witnessed `FormalCircuit` for the unsafe u16→u8 split; output is SP1's `U16toU8Operation`
column struct (the witnessed low bytes). -/
def circuit : FormalCircuit (ZMod p) Inputs Extracted.U16toU8Operation :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

end SP1Clean.U16toU8OperationUnsafe
