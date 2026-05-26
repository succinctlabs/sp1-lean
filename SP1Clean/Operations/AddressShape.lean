import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Gadgets.Equality
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Clean.ByteOpcodeTable
import SP1Clean.Operations.AddOperation

/-! # `AddressShape` sub-circuit — shared by Load and Store chips

Wraps the constraints SP1's `AddressOperation` emits beyond the inner
`AddrAddOp` carry chain:
- `offset_bit_2`, `offset_bit_1`, `offset_bit_0` are each in `{0, 1}`
- `top_two_limb_inv * (addr[1] + addr[2]) = 1`
  (forces the upper two limbs of the 3-limb address to be zero whenever
  the address falls below 2^16, with `top_two_limb_inv` the inverse witness)
- `((addr[0] - 4 * offset_bit_0 - 2 * offset_bit_1 - offset_bit_2) * 8⁻¹).val < 2 ^ 13`
  (low-limb bit decomposition: `addr[0] mod 8` equals the 3-bit offset value)

This is the "address shape" portion that sits alongside `AddrAddOp.assertion`
inside SP1's `AddressOperation.constraints`. Load and Store chips compose
both as sub-circuits.

`main` emits 3 boolean offset-bit gates, 1 top-two-limb inverse gate,
and 1 Range-13 lookup on the low-limb bit-decomposition (mirrors SP1's
`AddressOperation.constraints` minus the `AddrAddOp` sub-call and the
chip-layer `is_real` row gate). The lookup discharge uses the generic
`SP1Clean.AddOp.Assertion.byteOpcodeSpec_range{,_of_lt}` helpers. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.AddressShape

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled input: the 3-limb address, the inverse witness for the
upper-two-limb-zero check, and the 3 offset bits. -/
structure Inputs (F : Type) where
  addr : Vector F 3
  top_two_limb_inv : F
  offset_bit_2 : F
  offset_bit_1 : F
  offset_bit_0 : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Clean-side circuit. Emits the 3 boolean offset-bit gates, the
top-two-limb inverse-witness gate, and the low-limb bit-decomposition
Range-13 lookup. Mirrors SP1's `AddressOperation.constraints` minus the
`AddrAddOp.constraints` sub-call (which Load/Store chips compose in
parallel as a separate sub-circuit) and the chip-layer `is_real` row
gate. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  input.offset_bit_2 * (input.offset_bit_2 - 1) === 0
  input.offset_bit_1 * (input.offset_bit_1 - 1) === 0
  input.offset_bit_0 * (input.offset_bit_0 - 1) === 0
  (input.top_two_limb_inv * (input.addr[1] + input.addr[2]) - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)),
        (input.addr[0] - 4 * input.offset_bit_0 - 2 * input.offset_bit_1
          - input.offset_bit_2) * (8 : ZMod p)⁻¹,
        13, 0] : Vector (Expression (ZMod p)) 4)

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.AddressShape"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Per-row spec: the 4 facts SP1 surfaces alongside the AddrAddOp carry
chain inside `AddressOperation.constraints`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  (input.offset_bit_2 = 0 ∨ input.offset_bit_2 = 1) ∧
  (input.offset_bit_1 = 0 ∨ input.offset_bit_1 = 1) ∧
  (input.offset_bit_0 = 0 ∨ input.offset_bit_0 = 1) ∧
  input.top_two_limb_inv * (input.addr[1] + input.addr[2]) = 1 ∧
  ((input.addr[0] - 4 * input.offset_bit_0 - 2 * input.offset_bit_1
        - input.offset_bit_2) * (8 : ZMod p)⁻¹).val
    < 2 ^ ZMod.val (13 : ZMod p)

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_addr, h_inv, h_b2, h_b1, h_b0⟩ := h_input
  subst_eqs
  simp only [circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_b2_bin, h_b1_bin, h_b0_bin, h_inv_eq, h_send⟩ := h_holds
  simp only [Vector.getElem_map, sub_eq_add_neg]
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases mul_eq_zero.mp h_b2_bin with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · rcases mul_eq_zero.mp h_b1_bin with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · rcases mul_eq_zero.mp h_b0_bin with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · linear_combination h_inv_eq
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range _ _ _ h_send

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_addr, h_inv, h_b2, h_b1, h_b0⟩ := h_input
  subst_eqs
  simp only [Vector.getElem_map, sub_eq_add_neg] at h_spec
  obtain ⟨h_b2_or, h_b1_or, h_b0_or, h_inv_eq, h_range⟩ := h_spec
  simp only [circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rcases h_b2_or with h | h <;> rw [h] <;> ring
  · rcases h_b1_or with h | h <;> rw [h] <;> ring
  · rcases h_b0_or with h | h <;> rw [h] <;> ring
  · linear_combination h_inv_eq
  · exact SP1Clean.AddOp.Assertion.byteOpcodeSpec_range_of_lt _ _ _ h_range

end Assertion

def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.AddressShape
