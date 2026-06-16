import SP1Clean.FormalModel.Contracts.Operations
import SP1Clean.Math.Word
import SP1Clean.Math.Bitwise
import SP1Clean.Extracted.U16toU8OperationUnsafe
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # `U16toU8OperationUnsafe` as a Clean-native `FormalAssertion`

The **unsafe** u16→u8 byte split: for each of four 16-bit limbs the low byte `cols.low_bytes[i]` is a
chip-owned column and the high byte is read off as `(u16_values[i] - low_bytes[i]) * 256⁻¹`. "Unsafe"
because it imposes no range constraints — SP1's `eval_u16_to_u8_unsafe` takes no `is_real`, witnesses
nothing, and emits **no** `asserts`/`interactions` (a separate `value : Vector F 8` carries the split
bytes; see `Extracted.U16toU8OperationUnsafe.value`). So the gadget is a `FormalAssertion` with an
**empty** `main`, whose `Spec` is purely the reassembly identity `low + (u - low) * 256⁻¹ * 256 = u`
(true unconditionally). `RawSpec` is `True`; `Faithful/U16toU8OperationUnsafe.lean` anchors it to the
empty extracted lists. The `U16toU8OperationSafe` sibling adds the byte bounds. -/

namespace SP1Clean.U16toU8OperationUnsafe

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The literal meaning of SP1's `U16toU8OperationUnsafe` constraint list: it is **empty**, so the
unsafe split imposes nothing. -/
def RawSpec (_u16_values : Vector (ZMod p) 4) (_cols : Extracted.U16toU8Operation (ZMod p)) : Prop :=
  True

/-- No preconditions: SP1's `eval_u16_to_u8_unsafe` takes no `is_real` gate and asserts nothing. -/
def Assumptions (_input : Inputs (ZMod p)) : Prop := True

/-- SP1's `U16toU8OperationUnsafe::eval` as a Clean-native `FormalAssertion`: it emits **no**
constraints and **no** interactions — the byte split is a pure projection of the chip-owned `cols`
(see `Extracted.U16toU8OperationUnsafe.value`). Witnesses nothing. -/
def main (_input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := pure ()

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := []
  channelsWithRequirements := []

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) = [] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithRequirements_eq :
    ((elaborated (p := p)).channelsWithRequirements : List (RawChannel (ZMod p))) = [] := rfl

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

theorem soundness : FormalAssertion.Soundness (ZMod p) main Assumptions Spec := by
  circuit_proof_start
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h256 : (256 : ZMod p)⁻¹ * 256 = 1 := inv_mul_cancel₀ val_256_ne_zero
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    · rw [mul_assoc, h256, mul_one]; ring

omit [Fact (2 ^ 17 < p)] in
theorem completeness : FormalAssertion.Completeness (ZMod p) main Assumptions Spec := by
  circuit_proof_start

/-- SP1's `U16toU8OperationUnsafe::eval` as a Clean-native `FormalAssertion`: empty `main` (no
constraints, no interactions), `Spec` the reassembly identity over the chip-owned `cols`. -/
def circuit : FormalAssertion (ZMod p) Inputs :=
  { main, elaborated,
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

end SP1Clean.U16toU8OperationUnsafe
