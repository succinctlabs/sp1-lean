import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Foundations.Word
import SP1Clean.ByteOpcodeTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState

/-! # `OperandAccess.assertion` — single-operand memory-access byte-bus primitive

The SP1 R-Type / I-Type / Load / Store readers each emit, per memory-operand,
a fixed set of byte lookups that constrain the operand's
`(diff_low_limb, prev_low, prev_value)` triple. This file packages those
lookups into a single Clean `FormalAssertion` so chip-level `Assertion.main`
blocks can compose memory-bus byte content without duplicating lookups.

## Constraint surface (6 byte lookups per operand)

For a memory operand with the given `(clk_low, offset, prev_low,
diff_low_limb, prev_value)` triple:

- `diff_low_limb` is in `Range 16` (lookup opcode 6, bound 16) ⇒
  `diff_low_limb.val < 65536`.
- The scaled timestamp `(clk_low + offset - prev_low - 1 - diff_low_limb) *
  65536⁻¹` is in `U8Range` (lookup opcode 3) ⇒ value `< 256`.
- Each `prev_value[i]` (i = 0..3) is in `Range 16` ⇒ all four limbs `< 65536`,
  which is exactly `Word.isU64 prev_value`.

## Spec

`Spec input ≡ memoryAccessSpec input.clk_low input.offset
  ⟨#v[0,0,0], input.prev_value, input.prev_low, input.diff_low_limb⟩`

The address (`addr`) is `#v[0,0,0]` here because it isn't byte-bus content
— the chip's program-table and state-bus interactions establish the
register or RAM address. `OperandAccess.assertion` only covers the
byte-bus side; downstream memory-bus aggregation handles the address.

The chip-level caller threads the real address into the trace-level
`MemoryAccess` record via `MemoryAccess.toAccessTuple`; the per-row
`memoryAccessSpec` here just provides the bounds the aggregator needs.
-/

namespace SP1Clean.OperandAccess

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

/-- Inputs to the per-operand byte-bus assertion. `clk_low` is the chip's
composed low clock `clk_0_16 + clk_16_24 * 65536`; `offset` is the
per-operand sub-clock offset (canonically 2 / 3 / 4 for R-type op_c / op_b /
op_a). -/
structure Inputs (F : Type) where
  clk_low : F
  offset : F
  prev_low : F
  diff_low_limb : F
  prev_value : Vector F 4
deriving ProvableStruct

/-- Emit the 6 byte lookups for a single memory-operand's byte-bus side. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- diff_low_limb in Range 16
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.diff_low_limb, 16, 0]
      : Vector (Expression (ZMod p)) 4)
  -- (clk_low + offset - prev_low - 1 - diff_low_limb) * 65536⁻¹ in U8Range
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0,
        (input.clk_low + input.offset - input.prev_low - 1 -
          input.diff_low_limb) * (65536 : ZMod p)⁻¹,
        0]
      : Vector (Expression (ZMod p)) 4)
  -- prev_value[0..3] each in Range 16 (Word.isU64)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.prev_value[0], 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.prev_value[1], 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.prev_value[2], 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.prev_value[3], 16, 0]
      : Vector (Expression (ZMod p)) 4)

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.OperandAccess"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Per-operand byte-bus spec — the byte-bus consequences of the 6
lookups, equivalent to `memoryAccessSpec` on an operand record. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.diff_low_limb.val < 65536 ∧
  (input.clk_low + input.offset - input.prev_low - 1 - input.diff_low_limb)
      * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
  Word.isU64 input.prev_value

/-- Helper: `byteOpcodeSpec` row `#v[6, x, 16, 0]` ⇒ `x.val < 65536`. -/
lemma byteOpcodeSpec_range16
    (x : ZMod p)
    (h : SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, 16, 0])) :
    x.val < 65536 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨bop, hbop, hconstr⟩ := h
  have h_eq : bop = .Range := by
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
  have h16 : (16 : ZMod p).val = 16 := by
    rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [h16] at hconstr
  exact hconstr

/-- Helper for completeness: `x.val < 65536` ⇒ `byteOpcodeSpec #v[6, x, 16, 0]`. -/
lemma byteOpcodeSpec_range16_of_lt
    (x : ZMod p) (hx : x.val < 65536) :
    SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, 16, 0]) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  refine ⟨.Range, ?_, ?_⟩
  · simp only [ByteOpcode.toNat, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, Nat.cast_ofNat]
  · simp only [ByteOpcode.constrain_Range, Vector.getElem_mk,
               List.getElem_toArray, List.getElem_cons_zero,
               List.getElem_cons_succ]
    have h16 : (16 : ZMod p).val = 16 := by
      rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [h16]
    exact hx

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_clk_low_eq, h_offset_eq, h_prev_low_eq, h_diff_low_eq,
          h_prev_value_eq⟩ := h_input
  subst_eqs
  simp only [main, circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_diff, h_ts, h_pv0, h_pv1, h_pv2, h_pv3⟩ := h_holds
  refine ⟨?_, ?_, ?_⟩
  · exact byteOpcodeSpec_range16 _ h_diff
  · have h := SP1Clean.CPUState.Assertion.byteOpcodeSpec_u8range _ h_ts
    convert h using 1
    ring
  · apply Word.isU64_of_cases
    · rw [Vector.getElem_map]; exact byteOpcodeSpec_range16 _ h_pv0
    · rw [Vector.getElem_map]; exact byteOpcodeSpec_range16 _ h_pv1
    · rw [Vector.getElem_map]; exact byteOpcodeSpec_range16 _ h_pv2
    · rw [Vector.getElem_map]; exact byteOpcodeSpec_range16 _ h_pv3

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_clk_low_eq, h_offset_eq, h_prev_low_eq, h_diff_low_eq,
          h_prev_value_eq⟩ := h_input
  subst_eqs
  obtain ⟨h_diff, h_ts, h_isU64⟩ := h_spec
  obtain ⟨h_pv0, h_pv1, h_pv2, h_pv3⟩ := Word.lt_cases_of_isU64 h_isU64
  simp only [main, circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  refine ⟨byteOpcodeSpec_range16_of_lt _ h_diff, ?_, ?_, ?_, ?_, ?_⟩
  · have := SP1Clean.CPUState.Assertion.byteOpcodeSpec_u8range_of_lt _ h_ts
    convert this using 3
    ring
  · rw [Vector.getElem_map] at h_pv0
    exact byteOpcodeSpec_range16_of_lt _ h_pv0
  · rw [Vector.getElem_map] at h_pv1
    exact byteOpcodeSpec_range16_of_lt _ h_pv1
  · rw [Vector.getElem_map] at h_pv2
    exact byteOpcodeSpec_range16_of_lt _ h_pv2
  · rw [Vector.getElem_map] at h_pv3
    exact byteOpcodeSpec_range16_of_lt _ h_pv3

end Assertion

/-- The full Clean `FormalAssertion` for a single memory-operand's
byte-bus side: 6 byte lookups ⇒ `memoryAccessSpec` consequences. -/
def assertion : FormalAssertion (ZMod p) Assertion.Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.OperandAccess
