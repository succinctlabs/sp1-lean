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
import SP1Operations.Operation.AddwOperation.AddwOperation
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.SP1Lookup
import SP1Clean.Operations.AddOperation
import SP1Clean.Operations.U16MSBOperation

/-! # `AddwOperation` Clean mirror — faithful sub-circuit composition

SP1's `AddwOperation.constraints` is a 2-limb carry-chain 32-bit add plus
a sub-call to `U16MSBOperation.constraints` on the high result limb
(see `SP1Operations/Operation/AddwOperation/Constraints.lean`). This
Clean mirror faithfully reproduces that composition: `main` calls
`SP1Clean.U16MSBOp.assertion` as a true subcircuit, and `Spec` composes
`U16MSBOp.Assertion.Spec` by direct field reference.

There is exactly one `main`, one `Spec`, one `assertion`, and one
`iff_sp1` bridge to SP1's `allHold`. No standalone top-level Circuit
form, no `InlinedSpec`, no `assertion_spec_to_spec` bridging helpers —
the file's structure mirrors the SP1 composition graph directly.

See `CLAUDE.md` § "Faithful sub-circuit composition" for the principle. -/

namespace SP1Clean.AddwOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled inputs for the AddwOperation FormalAssertion: the two operand
words, the 2-limb result, and the externally-supplied msb bit. -/
structure Inputs (F : Type) where
  a : fields 4 F
  b : fields 4 F
  result : fields 2 F
  msb : F
deriving ProvableStruct

/-- Clean-side circuit: 2-limb carry chain + byte-bounds on result limbs +
`U16MSBOp.assertion` as a true sub-circuit on the high result limb
(mirrors SP1's `AddwOperation.constraints` composition of
`U16MSBOperation.constraints`). -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let c0 := (input.a[0] + input.b[0] - input.result[0]) * (65536 : ZMod p)⁻¹
  let c1 := (input.a[1] + input.b[1] - input.result[1] + c0) * (65536 : ZMod p)⁻¹
  c0 * (c0 - 1) === 0
  c1 * (c1 - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.result[0], 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), input.result[1], 16, 0]
      : Vector (Expression (ZMod p)) 4)
  -- U16MSB as a true sub-circuit (not inlined).
  SP1Clean.U16MSBOp.assertion
    (⟨input.result[1], input.msb⟩ : Var SP1Clean.U16MSBOp.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.AddwOp"
  main := main
  localLength _ := 0

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Single canonical Spec. Composes `U16MSBOp.Assertion.Spec` for the high
result limb's MSB sub-fragment by direct field reference — no
`List.Forall toProp` SP1-native envelope. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let carry0 : ZMod p := (input.a[0] + input.b[0] - input.result[0]) * 65536⁻¹
  let carry1 : ZMod p :=
    (input.a[1] + input.b[1] - input.result[1] + carry0) * 65536⁻¹
  (carry0 = 0 ∨ carry0 = 1) ∧
  (carry1 = 0 ∨ carry1 = 1) ∧
  input.result[0].val < 65536 ∧
  input.result[1].val < 65536 ∧
  SP1Clean.U16MSBOp.Assertion.Spec ⟨input.result[1], input.msb⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq, h_m_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  subst h_m_eq
  haveI : NeZero p := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩
  simp only [main, circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_c0, h_c1, h_l0, h_l1, h_u16_sub⟩ := h_holds
  have h_u16 := h_u16_sub trivial
  simp only [Spec, Vector.getElem_map, sub_eq_add_neg]
  unfold id at *
  refine ⟨?_, ?_,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l0,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l1,
          ?_⟩
  · obtain h | h := mul_eq_zero.mp h_c0
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · obtain h | h := mul_eq_zero.mp h_c1
    · exact Or.inl (by linear_combination h)
    · exact Or.inr (by linear_combination h)
  · -- U16MSBOp sub-circuit's Spec is exactly what we need for the last
    -- conjunct (modulo the `+ -` vs `-` normalization in the inputs).
    convert h_u16 using 2

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq, h_m_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  subst h_m_eq
  haveI : NeZero p := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩
  simp only [Spec, Vector.getElem_map, sub_eq_add_neg] at h_spec
  obtain ⟨hb0, hb1, hr0, hr1, h_u16⟩ := h_spec
  simp only [main, circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  unfold id at *
  refine ⟨?_, ?_,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr0,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr1,
          ?_⟩
  · rcases hb0 with h | h <;> rw [h] <;> ring
  · rcases hb1 with h | h <;> rw [h] <;> ring
  · refine ⟨trivial, ?_⟩
    convert h_u16 using 2

/-- The full Clean `FormalAssertion` for `AddwOperation`. The single
canonical spec composes `U16MSBOp.Assertion.Spec` directly. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

/-- Bridge to SP1: the `Inputs`-shaped `Spec` is equivalent to SP1's
`AddwOperation.constraints` `allHold` form. Chains `AddwOperation`'s
top-level iff with `U16MSBOperation`'s iff to bridge the sub-component. -/
theorem iff_sp1 (input : Inputs (ZMod p)) :
    Spec input ↔
      (_root_.AddwOperation.constraints input.a input.b
        { value := input.result, msb := { msb := input.msb } } 1).allHold := by
  haveI : NeZero p := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩
  rw [_root_.AddwOperation.allHold_constraints_iff]
  -- The SP1-native RHS now has the form:
  -- `List.Forall toProp (U16MSBOperation.constraints …)` ∧ carries ∧ ranges
  -- Our `Spec` has:
  -- carries ∧ ranges ∧ `U16MSBOp.Assertion.Spec`
  -- Bridge the U16MSB conjunct via `U16MSBOperation.allHold_constraints_iff`,
  -- plus the `msb * (msb-1) = 0 ↔ msb ∈ {0,1}` field-arithmetic step.
  unfold Spec SP1Clean.U16MSBOp.Assertion.Spec
  rw [U16MSBOperation.allHold_constraints_iff]
  constructor
  · rintro ⟨h_c0, h_c1, h_r0, h_r1, h_msb_bin, h_msb_range⟩
    refine ⟨⟨Or.inr rfl, ?_, fun _ => h_msb_range⟩, h_c0, h_c1, h_r0, h_r1⟩
    rcases mul_eq_zero.mp h_msb_bin with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  · rintro ⟨⟨_, h_msb_bin, h_msb_range⟩, h_c0, h_c1, h_r0, h_r1⟩
    refine ⟨h_c0, h_c1, h_r0, h_r1, ?_, h_msb_range one_ne_zero⟩
    change input.msb = 0 ∨ input.msb = 1 at h_msb_bin
    rcases h_msb_bin with h | h <;> rw [h] <;> ring

/-! ## Multiplicity-gated `AssertionGated` form

Parallel to the unconditional `Assertion` namespace above. Adds an
`is_real` multiplicity gate that vanishes every emitted constraint on
padding rows, matching SP1's `AddwOperation.constraints` gating pattern.

The contract is **semantic-only**: `Spec` carries the BV32 + MSB
equation directly (matching `AddwOperation.iff_sp1_full`'s RHS verbatim)
under `is_real = 1`. The carry-form decomposition is an implementation
detail of `main`. -/

/-- Multiplicity-aware input: two operand words, the 2-limb result, the
externally-supplied msb bit, and the gating multiplicity `is_real`. -/
structure InputsGated (F : Type) where
  a : fields 4 F
  b : fields 4 F
  result : fields 2 F
  msb : F
  is_real : F
deriving ProvableStruct

namespace AssertionGated

open Circuit

/-- Multiplicity-gated `main`: gates the 2-limb carry chain, both
byte-range lookups, and the U16MSB sub-circuit by `is_real`. -/
@[reducible]
def main (input : Var InputsGated (ZMod p)) : Circuit (ZMod p) Unit := do
  input.is_real * (input.is_real - 1) === 0
  let c0 := (input.a[0] + input.b[0] - input.result[0]) * (65536 : ZMod p)⁻¹
  let c1 := (input.a[1] + input.b[1] - input.result[1] + c0) * (65536 : ZMod p)⁻¹
  input.is_real * (c0 * (c0 - 1)) === 0
  input.is_real * (c1 * (c1 - 1)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), input.result[0], 16, 0], input.is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), input.result[1], 16, 0], input.is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Clean.U16MSBOp.assertionGated
    (⟨input.result[1], input.msb, input.is_real⟩ :
     Var SP1Clean.U16MSBOp.InputsGated (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) InputsGated unit where
  name := "SP1Clean.AddwOpGated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

/-- Binarity of `is_real` (asserted by chip side) plus the operand
`isU64` bounds needed to bridge the carry-form Spec to the semantic
`AddwOperation.iff_sp1_full` RHS. -/
def Assumptions (input : InputsGated (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 → Word.isU64 input.a ∧ Word.isU64 input.b)

/-- Semantic contract mirroring `AddwOperation.iff_sp1_full`'s RHS:
on real rows, the 2-limb result is a u32, its 32-bit BitVec equals the
32-bit ADDW of the operands, and `msb` is the BitVec-msb-of-result bit. -/
def Spec (input : InputsGated (ZMod p)) : Prop :=
  input.is_real = 1 →
    HWord.isU32 input.result ∧
    HWord.toBitVec32 input.result =
      execute_RTYPEW_pure_32_w input.a input.b .ADDW ∧
    input.msb = (if (HWord.toBitVec32 input.result).msb then 1 else 0)

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [AssertionGated.main]
  obtain ⟨h_a_eq, h_b_eq, h_r_eq, h_m_eq, h_ir_eq⟩ := h_input
  subst h_a_eq; subst h_b_eq; subst h_r_eq; subst h_m_eq; subst h_ir_eq
  obtain ⟨h_ir_bin, h_gc0, h_gc1, h_l0_sub, h_l1_sub, h_u16_sub⟩ := h_holds
  obtain ⟨_h_ir_binary, h_bounds⟩ := h_assumptions
  intro h_is_real
  unfold id at *
  obtain ⟨h_isU64_a, h_isU64_b⟩ := h_bounds h_is_real
  have h_ir_ne_zero : Expression.eval env input_var_is_real ≠ 0 := by
    rw [h_is_real]; exact one_ne_zero
  -- Extract ungated carry/range facts from gated emissions.
  have h_c0 := (mul_eq_zero.mp h_gc0).resolve_left h_ir_ne_zero
  have h_c1 := (mul_eq_zero.mp h_gc1).resolve_left h_ir_ne_zero
  have hr0 :=
    SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _
      ((h_l0_sub trivial).resolve_left h_ir_ne_zero)
  have hr1 :=
    SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _
      ((h_l1_sub trivial).resolve_left h_ir_ne_zero)
  -- U16MSBOp.assertionGated's Spec under is_real = 1: `(msb_bool ∧ msb_range)`.
  have h_u16_assumps :
      Expression.eval env input_var_is_real = 0 ∨
      Expression.eval env input_var_is_real = 1 := Or.inr h_is_real
  have ⟨h_msb_bin, h_msb_check⟩ := (h_u16_sub h_u16_assumps) h_is_real
  -- Assemble AddwOp.Spec (carry-form) from the carry + range + U16MSB facts.
  have h_addwop : SP1Clean.AddwOp.Spec
      ⟨Vector.map (Expression.eval env) input_var_a,
        Vector.map (Expression.eval env) input_var_b,
        Vector.map (Expression.eval env) input_var_result,
        Expression.eval env input_var_msb⟩ := by
    simp only [SP1Clean.AddwOp.Spec, Vector.getElem_map, sub_eq_add_neg]
    refine ⟨?_, ?_, hr0, hr1, ?_⟩
    · rcases mul_eq_zero.mp h_c0 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    · rcases mul_eq_zero.mp h_c1 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    · -- U16MSBOp.Assertion.Spec ⟨result[1], msb⟩: 2-conjunct.
      refine ⟨?_, ?_⟩
      · linear_combination h_msb_bin
      · exact h_msb_check
  -- Bridge to SP1's allHold and consume iff_sp1_full's RHS.
  have h_allHold :
      (_root_.AddwOperation.constraints
        (Vector.map (Expression.eval env) input_var_a)
        (Vector.map (Expression.eval env) input_var_b)
        { value := Vector.map (Expression.eval env) input_var_result,
          msb := { msb := Expression.eval env input_var_msb } } 1).allHold :=
    (SP1Clean.AddwOp.iff_sp1 _).mp h_addwop
  exact (_root_.AddwOperation.iff_sp1_full h_isU64_a h_isU64_b).mp h_allHold

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [AssertionGated.main]
  obtain ⟨h_a_eq, h_b_eq, h_r_eq, h_m_eq, h_ir_eq⟩ := h_input
  subst h_a_eq; subst h_b_eq; subst h_r_eq; subst h_m_eq; subst h_ir_eq
  obtain ⟨h_ir_binary, h_bounds⟩ := h_assumptions
  haveI : NeZero p := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩
  unfold id at *
  rcases h_ir_binary with h_ir0 | h_ir1
  · -- Padding row: is_real = 0; all gated emissions trivialize.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ir0]; ring
    · rw [h_ir0]; ring
    · rw [h_ir0]; ring
    · exact ⟨trivial, Or.inl h_ir0⟩
    · exact ⟨trivial, Or.inl h_ir0⟩
    · -- U16MSBOp.assertionGated: ⟨SubAssumptions, SubSpec⟩.
      -- SubAssumptions = `is_real = 0 ∨ is_real = 1` → Or.inl h_ir0.
      -- SubSpec = `is_real = 1 → ...` → vacuous on padding.
      refine ⟨Or.inl h_ir0, fun h_contra => ?_⟩
      exact absurd (h_ir0.symm.trans h_contra) zero_ne_one
  · -- Real row: recover AddwOp.Spec via iff_sp1_full.mpr, then disassemble.
    obtain ⟨h_isU64_a, h_isU64_b⟩ := h_bounds h_ir1
    obtain ⟨h_isU32_v, h_bv, h_msb_eq⟩ := h_spec h_ir1
    -- Use AddwOperation.spec_inv directly (avoids the slow cols-unification
    -- that iff_sp1_full's .mpr would trigger).
    have h_allHold :=
      _root_.AddwOperation.spec_inv
        (cols := { value := Vector.map (Expression.eval env) input_var_result,
                   msb := { msb := Expression.eval env input_var_msb } })
        h_isU64_a h_isU64_b h_isU32_v h_bv h_msb_eq
    have h_addwop := (SP1Clean.AddwOp.iff_sp1 ⟨
        Vector.map (Expression.eval env) input_var_a,
        Vector.map (Expression.eval env) input_var_b,
        Vector.map (Expression.eval env) input_var_result,
        Expression.eval env input_var_msb⟩).mpr h_allHold
    -- AddwOp.Spec carries the carry-bool / range / U16MSB facts.
    simp only [SP1Clean.AddwOp.Spec, Vector.getElem_map, sub_eq_add_neg] at h_addwop
    obtain ⟨hc0, hc1, hr0, hr1, h_u16⟩ := h_addwop
    simp only [SP1Clean.U16MSBOp.Assertion.Spec] at h_u16
    obtain ⟨h_msb_bin, h_msb_check⟩ := h_u16
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ir1]; ring
    · rw [h_ir1]; rcases hc0 with h | h <;> rw [h] <;> ring
    · rw [h_ir1]; rcases hc1 with h | h <;> rw [h] <;> ring
    · exact ⟨trivial,
             Or.inr (SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr0)⟩
    · exact ⟨trivial,
             Or.inr (SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr1)⟩
    · -- U16MSBOp.assertionGated: ⟨SubAssumptions, SubSpec⟩.
      refine ⟨Or.inr h_ir1, fun _ => ⟨?_, ?_⟩⟩
      · linear_combination h_msb_bin
      · exact h_msb_check

end AssertionGated

/-- Multiplicity-gated FormalAssertion for `AddwOperation`. Spec is the
semantic `AddwOperation.iff_sp1_full` RHS (gated on `is_real = 1`),
identical in shape to `AddOp.assertion`'s contract one level down. -/
def assertionGated : FormalAssertion (ZMod p) InputsGated :=
  { AssertionGated.elaborated with
    Assumptions := AssertionGated.Assumptions,
    Spec := AssertionGated.Spec,
    soundness := AssertionGated.soundness,
    completeness := AssertionGated.completeness }

end SP1Clean.AddwOp
