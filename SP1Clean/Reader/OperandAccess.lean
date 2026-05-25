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
import SP1Clean.Reader.RegisterAccessTimestamp
import SP1Clean.Reader.WordRange
import SP1Clean.SP1Lookup

/-! # `OperandAccess.assertion` — per-operand memory-access byte-bus primitive

The constraint surface is 6 byte lookups, conceptually splitting into:

- **Timestamp byte lookups** — `diff_low_limb < 65536` and the scaled
  timestamp `< 256`. This mirrors Rust's `eval_register_access_timestamp`
  (`crates/core/machine/src/air/memory.rs:332`).
- **Word range checks** — each `prev_value[i] < 65536`, i.e. `Word.isU64`.

Two FormalAssertions are exposed:

- `OperandAccess.assertion` (ungated) — emits 6 inline `lookup ByteOpcodeTable`
  calls; `localLength = 0`. Used directly by ~21 chip files (Branch, DivRem,
  Load*, Store*, Bitwise, Mul, Shift*, Lt, Sub*, UType, Jal, Jalr…). Spec:
  `diff < 65536 ∧ ts < 256 ∧ Word.isU64 prev_value`.

- `OperandAccess.assertionGated` (multiplicity-aware) — composes the two
  Rust-aligned leaves `RegisterAccessTimestamp.assertion` and
  `WordRange.assertion` with a shared `mult`; the leaves use
  `byteOpcodeGated` and therefore witness cells, so `localLength = 24`.
  Used by `RegisterAccess.assertion` (and indirectly by all RType/IType/
  ALU-Type reader composition). Spec: `mult = 0 ∨ <byte facts>`.

The two forms expose the same byte-bus Spec contract (modulo the gated
`Or`), so they're interchangeable from a chip-level reasoning standpoint.
The split exists because the gated form needs witness cells to encode the
disjunction, while the ungated form doesn't. -/

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
    ring_nf
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
byte-bus side: 6 byte lookups ⇒ `memoryAccessSpec` consequences.
`localLength = 0` (inline lookups, no witness cells). -/
def assertion : FormalAssertion (ZMod p) Assertion.Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-! ## Gated variant — multiplicity-aware byte-bus assertion via sub-circuit composition

A drop-in replacement for `OperandAccess.assertion` that takes an extra
`mult : F` field. When `mult = 0`, the assertion contributes nothing; when
`mult ≠ 0`, it forces the same 6 byte facts as the unconditional variant.

Composes the two Rust-aligned leaves `RegisterAccessTimestamp.assertion`
(mirrors Rust's `eval_register_access_timestamp`) and `WordRange.assertion`
(`Word.isU64` range checks), threading `mult` through both. -/

namespace AssertionGated

open Circuit

/-- Inputs to the gated per-operand byte-bus assertion. Same as
`Assertion.Inputs` plus a shared multiplicity `mult`. -/
structure Inputs (F : Type) where
  clk_low : F
  offset : F
  prev_low : F
  diff_low_limb : F
  prev_value : Vector F 4
  mult : F
deriving ProvableStruct

/-- Compose the two leaf sub-circuits with a shared `mult`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  SP1Clean.RegisterAccessTimestamp.assertion
    (⟨input.clk_low, input.offset, input.prev_low,
       input.diff_low_limb, input.mult⟩ :
      Var SP1Clean.RegisterAccessTimestamp.Assertion.Inputs (ZMod p))
  SP1Clean.WordRange.assertion
    (⟨input.prev_value, input.mult⟩ :
      Var SP1Clean.WordRange.Assertion.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.OperandAccessGated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Per-operand gated byte-bus spec. The disjunction makes the assertion
vacuous when `mult = 0`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.mult = 0 ∨
    (input.diff_low_limb.val < 65536 ∧
     (input.clk_low + input.offset - input.prev_low - 1 - input.diff_low_limb)
        * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
     Word.isU64 input.prev_value)

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_clk_low_eq, h_offset_eq, h_prev_low_eq, h_diff_low_eq,
          h_prev_value_eq, h_mult_eq⟩ := h_input
  subst_eqs
  obtain ⟨h_ts_sub, h_wr_sub⟩ := h_holds
  have h_ts := h_ts_sub trivial
  have h_wr := h_wr_sub trivial
  by_cases h_mult : Expression.eval env input_var_mult = 0
  · exact Or.inl h_mult
  right
  have h_ts' := h_ts.resolve_left h_mult
  have h_wr' := h_wr.resolve_left h_mult
  exact ⟨h_ts'.1, h_ts'.2, h_wr'⟩

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_clk_low_eq, h_offset_eq, h_prev_low_eq, h_diff_low_eq,
          h_prev_value_eq, h_mult_eq⟩ := h_input
  subst_eqs
  rcases h_spec with h_mult_zero | ⟨h_diff, h_ts, h_isU64⟩
  · refine ⟨⟨trivial, Or.inl h_mult_zero⟩, ⟨trivial, Or.inl h_mult_zero⟩⟩
  · refine ⟨⟨trivial, ?_⟩, ⟨trivial, ?_⟩⟩
    · right; exact ⟨h_diff, h_ts⟩
    · right; exact h_isU64

end AssertionGated

/-- Gated variant: same Spec contract as `assertion`, but threads a
shared `mult` through `RegisterAccessTimestamp.assertion` and
`WordRange.assertion`. Spec is `mult = 0 ∨ <byte facts>`. -/
def assertionGated : FormalAssertion (ZMod p) AssertionGated.Inputs :=
  { AssertionGated.elaborated with
    Assumptions := AssertionGated.Assumptions,
    Spec := AssertionGated.Spec,
    soundness := AssertionGated.soundness,
    completeness := AssertionGated.completeness }

end SP1Clean.OperandAccess
