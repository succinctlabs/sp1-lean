import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Clean.Operations.LtOperationSigned
import SP1Clean.Operations.GatedLtUnsignedOp
import SP1Clean.Operations.Gated

/-! # `GatedLtSignedOp` — gated form of `LtSignedOp.assertion`

Second gated combinator. Composes `GatedLtUnsignedOp.assertion` on
sign-flipped operands as a sub-circuit (re-using the same `gate`) and
inlines the 2 U16MSB bit-gates + 3 surviving scalar gates of
`LtSignedOp`, each multiplied by `gate`. The byte-range lookups that
`U16MSBOp` and `U16CompareOp` emit are **dropped here** — they live
on the chip-level multiplicity bus.

The `FormalSpec` is `gate = 0 ∨ <carry-only Spec>`. The inner Spec
captures:
- 2× U16MSB bit-gates (`b_msb`, `c_msb` each boolean)
- the embedded `GatedLtUnsignedOp.FormalSpec` on sign-flipped operands
- 1× `is_signed` boolean
- 2× sign-vacuity gates (`(is_signed - 1) * {b,c}_msb = 0`)

Mirrors `LtOperationSigned.constraints` under `is_real := gate`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.GatedLtSignedOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled input. Mirrors `LtSignedOp.Inputs` + a `gate : F` field. -/
structure Inputs (F : Type) where
  b : fields 4 F
  c : fields 4 F
  is_signed : F
  -- Embedded `LtUnsignedOp` cols:
  compare_bit : F
  u16_flags : fields 4 F
  not_eq_inv : F
  comparison_limbs : fields 2 F
  -- The two U16MSBOp witnesses:
  b_msb : F
  c_msb : F
  gate : F
deriving ProvableStruct

/-- Carry-only Spec for the gated signed-less-than operation. The
embedded GatedLtUnsignedOp's FormalSpec stays disjunctive (already
`gate = 0 ∨ ...`); the surrounding 5 gates are inlined as equalities. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let one : ZMod p := 1
  let b3' := input.b[3] + input.is_signed * 32768 - 65536 * input.b_msb
  let c3' := input.c[3] + input.is_signed * 32768 - 65536 * input.c_msb
  -- 2× U16MSB bit-gates.
  input.b_msb * (input.b_msb - one) = 0 ∧
  input.c_msb * (input.c_msb - one) = 0 ∧
  -- Embedded GatedLtUnsignedOp on sign-flipped operands.
  SP1Clean.GatedLtUnsignedOp.Assertion.FormalSpec
    ⟨#v[input.b[0], input.b[1], input.b[2], b3'],
     #v[input.c[0], input.c[1], input.c[2], c3'],
     input.compare_bit, input.u16_flags, input.not_eq_inv,
     input.comparison_limbs, input.gate⟩ ∧
  -- 3 surviving scalar gates.
  input.is_signed * (input.is_signed - one) = 0 ∧
  (input.is_signed - one) * input.b_msb = 0 ∧
  (input.is_signed - one) * input.c_msb = 0

namespace Assertion

open Circuit

/-- Gated `main`. 2× gated U16MSB bit-gates + 1× sub-circuit
`GatedLtUnsignedOp.assertion` (carries its own gating) + 3× gated
scalar gates. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let gate := input.gate
  let one_expr : Expression (ZMod p) := 1
  -- U16MSB bit-gates (gated; lookups dropped).
  gate * (input.b_msb * (input.b_msb - one_expr)) === 0
  gate * (input.c_msb * (input.c_msb - one_expr)) === 0
  -- Sub-circuit: GatedLtUnsignedOp on sign-flipped operands.
  let b3' := input.b[3] + input.is_signed * 32768 - 65536 * input.b_msb
  let c3' := input.c[3] + input.is_signed * 32768 - 65536 * input.c_msb
  SP1Clean.GatedLtUnsignedOp.assertion
    (⟨#v[input.b[0], input.b[1], input.b[2], b3'],
       #v[input.c[0], input.c[1], input.c[2], c3'],
       input.compare_bit, input.u16_flags, input.not_eq_inv,
       input.comparison_limbs, gate⟩ :
      Var SP1Clean.GatedLtUnsignedOp.Inputs (ZMod p))
  -- 3 surviving scalar gates (gated).
  gate * (input.is_signed * (input.is_signed - one_expr)) === 0
  gate * ((input.is_signed - one_expr) * input.b_msb) === 0
  gate * ((input.is_signed - one_expr) * input.c_msb) === 0

set_option maxHeartbeats 800000 in
-- Sub-circuit GatedLtUnsignedOp + 5 scalar gates exceeds default
-- `subcircuitsConsistent` synth budget.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.GatedLtSignedOp"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The FormalAssertion's spec: either the gate is zero (vacuous), or
the underlying carry-only `Spec` holds. -/
def FormalSpec (input : Inputs (ZMod p)) : Prop :=
  input.gate = 0 ∨ SP1Clean.GatedLtSignedOp.Spec input

omit [Fact (2 ^ 17 < p)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_b_eq, h_c_eq, h_is_signed_eq, h_bit_eq, h_f_eq, h_nei_eq,
          h_cl_eq, h_bmsb_eq, h_cmsb_eq, h_g_eq⟩ := h_input
  subst h_b_eq
  subst h_c_eq
  subst h_is_signed_eq
  subst h_bit_eq
  subst h_f_eq
  subst h_nei_eq
  subst h_cl_eq
  subst h_bmsb_eq
  subst h_cmsb_eq
  subst h_g_eq
  obtain ⟨h_bmsb, h_cmsb, h_sub_call, h_isigned, h_bmsb_v, h_cmsb_v⟩ := h_holds
  -- Sub-circuit hypothesis fires under trivial assumption.
  have h_sub := h_sub_call trivial
  simp only [FormalSpec, SP1Clean.GatedLtSignedOp.Spec, Vector.getElem_map,
             sub_eq_add_neg]
  unfold id at *
  -- Case-split: either gate is 0 (Or.inl) or all 5 inline gates hold + sub.
  obtain h_g | h_bmsb' := mul_eq_zero.mp h_bmsb
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_cmsb' := mul_eq_zero.mp h_cmsb
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_isigned' := mul_eq_zero.mp h_isigned
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_bmsb_v' := mul_eq_zero.mp h_bmsb_v
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_cmsb_v' := mul_eq_zero.mp h_cmsb_v
  · exact Or.inl (by linear_combination h_g)
  -- All 5 gates' factors nonzero, plus sub-circuit Spec holds.
  refine Or.inr ⟨h_bmsb', h_cmsb', ?_, h_isigned', h_bmsb_v', h_cmsb_v'⟩
  -- The sub-FormalSpec is exactly `h_sub` modulo the `Vector.map` shape
  -- of `b`/`c` after `subst` (`Vector.getElem_map` already in scope).
  convert h_sub using 2

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_b_eq, h_c_eq, h_is_signed_eq, h_bit_eq, h_f_eq, h_nei_eq,
          h_cl_eq, h_bmsb_eq, h_cmsb_eq, h_g_eq⟩ := h_input
  subst h_b_eq
  subst h_c_eq
  subst h_is_signed_eq
  subst h_bit_eq
  subst h_f_eq
  subst h_nei_eq
  subst h_cl_eq
  subst h_bmsb_eq
  subst h_cmsb_eq
  subst h_g_eq
  unfold id at *
  rcases h_spec with h_gate | h_spec'
  · -- gate = 0: every `gate * _` is trivially 0, and the sub-FormalSpec
    -- is satisfied via its own `Or.inl` (gate = 0).
    dsimp only at h_gate
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · -- Sub-circuit completeness premise: tuple `⟨assumption, spec⟩`.
      -- Discharge the spec via the sub's `gate = 0` disjunct.
      exact ⟨trivial, Or.inl h_gate⟩
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · rw [h_gate]; ring
  · -- Inner Spec holds: each inline gate by multiplication; sub-FormalSpec
    -- comes from the inner Spec directly.
    simp only [SP1Clean.GatedLtSignedOp.Spec, Vector.getElem_map] at h_spec'
    obtain ⟨h_bmsb', h_cmsb', h_sub_spec, h_isigned', h_bmsb_v', h_cmsb_v'⟩ :=
      h_spec'
    set g := Expression.eval env.toEnvironment input_var_gate
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination g * h_bmsb'
    · linear_combination g * h_cmsb'
    · refine ⟨trivial, ?_⟩
      convert h_sub_spec using 2 <;> simp only [sub_eq_add_neg]
    · linear_combination g * h_isigned'
    · linear_combination g * h_bmsb_v'
    · linear_combination g * h_cmsb_v'

end Assertion

/-- The gated `FormalAssertion`. Compose into a chip's `Assertion.main`
via `SP1Clean.GatedLtSignedOp.assertion ⟨b, c, is_signed, …, gate⟩`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.GatedLtSignedOp
