import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Clean.Operations.LtOperationUnsigned
import SP1Clean.Operations.Gated
import SP1Clean.SP1Lookup
import SP1Clean.ByteOpcodeTable

/-! # `GatedLtUnsignedOp` — gated form of `LtUnsignedOp.assertion`

Gated combinator for `SP1Clean.LtUnsignedOp` (Phase 1.3). Takes the same
inputs as `LtUnsignedOp` plus a `gate : F` field, emits each of the 13
`assertZero` constraints multiplied by `gate`, AND emits the U16Compare
byte-range lookup via `SP1Lookup.byteOpcodeGated` with multiplicity
`gate` — vacuous on padding rows, real on `gate ≠ 0` rows.

The `FormalSpec` is `gate = 0 ∨ <carry Spec ∧ byte-range fact>`. On
padding / inactive opcode rows where the chip's gate evaluates to 0,
the disjunction's left branch fires vacuously; on real rows, the inner
carry spec + the disjunctive byte-range conjunct hold.

Mirrors `LtOperationUnsigned.constraints` under `is_real := gate`. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.GatedLtUnsignedOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)] [Fact (p > 512)]

/-- Bundled input to the gated FormalAssertion: the two operand words,
the cols-struct fields, and the gate scalar. -/
structure Inputs (F : Type) where
  b : fields 4 F
  c : fields 4 F
  compare_bit : F
  u16_flags : fields 4 F
  not_eq_inv : F
  comparison_limbs : fields 2 F
  gate : F
deriving ProvableStruct

/-- Carry-and-lookup Spec for the gated unsigned-less-than operation.
13 carry conjuncts + 1 disjunctive byte-range conjunct (the U16Compare
range-16 lookup, emitted via `SP1Lookup.byteOpcodeGated` with
multiplicity `gate` — vacuous on `gate = 0`). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let one : ZMod p := 1
  -- U16Compare bit boolean.
  input.compare_bit * (input.compare_bit - one) = 0 ∧
  -- 4 one-hot flag booleans (MSB→LSB).
  input.u16_flags[0] * (input.u16_flags[0] - one) = 0 ∧
  input.u16_flags[1] * (input.u16_flags[1] - one) = 0 ∧
  input.u16_flags[2] * (input.u16_flags[2] - one) = 0 ∧
  input.u16_flags[3] * (input.u16_flags[3] - one) = 0 ∧
  -- Sum-of-flags is boolean.
  (let s := input.u16_flags[0] + input.u16_flags[1] +
            input.u16_flags[2] + input.u16_flags[3]
   s * (s - one) = 0) ∧
  -- Cross-limb selection: `(1 - cum) * (b[i] - c[i]) = 0` for each i.
  (one - input.u16_flags[3]) * (input.b[3] - input.c[3]) = 0 ∧
  (one - (input.u16_flags[3] + input.u16_flags[2])) *
    (input.b[2] - input.c[2]) = 0 ∧
  (one - (input.u16_flags[3] + input.u16_flags[2] + input.u16_flags[1])) *
    (input.b[1] - input.c[1]) = 0 ∧
  (one - (input.u16_flags[3] + input.u16_flags[2] +
        input.u16_flags[1] + input.u16_flags[0])) *
    (input.b[0] - input.c[0]) = 0 ∧
  -- comparison_limbs derivation: Σ flag[i] * b[i] = cl[0], Σ flag[i] * c[i] = cl[1].
  (input.b[3] * input.u16_flags[3] + input.b[2] * input.u16_flags[2] +
    input.b[1] * input.u16_flags[1] + input.b[0] * input.u16_flags[0]) -
      input.comparison_limbs[0] = 0 ∧
  (input.c[3] * input.u16_flags[3] + input.c[2] * input.u16_flags[2] +
    input.c[1] * input.u16_flags[1] + input.c[0] * input.u16_flags[0]) -
      input.comparison_limbs[1] = 0 ∧
  -- not_eq_inv discipline.
  (let s := input.u16_flags[0] + input.u16_flags[1] +
            input.u16_flags[2] + input.u16_flags[3]
   (-s) * (input.not_eq_inv *
     (input.comparison_limbs[0] - input.comparison_limbs[1]) - one) = 0) ∧
  -- U16Compare byte-range (disjunctive — vacuous on `gate = 0`).
  (input.gate = 0 ∨ SP1Clean.ByteOpcodeSpec
    (#v[6, input.comparison_limbs[0] - input.comparison_limbs[1] +
         input.compare_bit * 65536, 16, 0] : Vector (ZMod p) 4))

namespace Assertion

open Circuit

/-- Gated `main`: emits `gate * <each inner assertZero> === 0` for the 13
inner constraints, plus 1 `byteOpcodeGated` call with multiplicity `gate`
for the U16Compare byte-range lookup. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let gate := input.gate
  let one_expr : Expression (ZMod p) := 1
  -- U16Compare bit boolean (gated).
  gate * (input.compare_bit * (input.compare_bit - one_expr)) === 0
  -- 4 one-hot flag booleans (gated).
  gate * (input.u16_flags[0] * (input.u16_flags[0] - one_expr)) === 0
  gate * (input.u16_flags[1] * (input.u16_flags[1] - one_expr)) === 0
  gate * (input.u16_flags[2] * (input.u16_flags[2] - one_expr)) === 0
  gate * (input.u16_flags[3] * (input.u16_flags[3] - one_expr)) === 0
  -- Sum-of-flags is boolean (gated).
  let s := input.u16_flags[0] + input.u16_flags[1] +
           input.u16_flags[2] + input.u16_flags[3]
  gate * (s * (s - one_expr)) === 0
  -- Cross-limb selection (4 gated gates).
  let cum3 := input.u16_flags[3]
  let cum2 := cum3 + input.u16_flags[2]
  let cum1 := cum2 + input.u16_flags[1]
  let cum0 := cum1 + input.u16_flags[0]
  gate * ((one_expr - cum3) * (input.b[3] - input.c[3])) === 0
  gate * ((one_expr - cum2) * (input.b[2] - input.c[2])) === 0
  gate * ((one_expr - cum1) * (input.b[1] - input.c[1])) === 0
  gate * ((one_expr - cum0) * (input.b[0] - input.c[0])) === 0
  -- comparison_limbs derivation (2 gated gates).
  let cl0_expected := input.b[3] * input.u16_flags[3] +
    input.b[2] * input.u16_flags[2] + input.b[1] * input.u16_flags[1] +
    input.b[0] * input.u16_flags[0]
  let cl1_expected := input.c[3] * input.u16_flags[3] +
    input.c[2] * input.u16_flags[2] + input.c[1] * input.u16_flags[1] +
    input.c[0] * input.u16_flags[0]
  gate * (cl0_expected - input.comparison_limbs[0]) === 0
  gate * (cl1_expected - input.comparison_limbs[1]) === 0
  -- not_eq_inv discipline (1 gated gate).
  gate * ((-s) * (input.not_eq_inv *
    (input.comparison_limbs[0] - input.comparison_limbs[1]) - one_expr)) === 0
  -- U16Compare byte-range lookup, gated by `gate`.
  SP1Lookup.byteOpcodeGated
    (⟨#v[6, input.comparison_limbs[0] - input.comparison_limbs[1] +
         input.compare_bit * 65536, 16, 0], gate⟩ :
      Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))

set_option maxHeartbeats 800000 in
-- Sub-circuit `byteOpcodeGated` + 13 scalar gates exceeds default
-- `subcircuitsConsistent` synth budget.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.GatedLtUnsignedOp"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The FormalAssertion's spec: either the gate is zero (vacuous), or
the underlying carry-only `Spec` holds. -/
def FormalSpec (input : Inputs (ZMod p)) : Prop :=
  input.gate = 0 ∨ SP1Clean.GatedLtUnsignedOp.Spec input

omit [Fact (2 ^ 17 < p)] in
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_b_eq, h_c_eq, h_bit_eq, h_f_eq, h_nei_eq, h_cl_eq, h_g_eq⟩ := h_input
  subst h_b_eq
  subst h_c_eq
  subst h_bit_eq
  subst h_f_eq
  subst h_nei_eq
  subst h_cl_eq
  subst h_g_eq
  obtain ⟨h_bit, h_f0, h_f1, h_f2, h_f3, h_s, h_x3, h_x2, h_x1, h_x0, h_cl0, h_cl1,
          h_nei, h_byte_sub⟩ := h_holds
  simp only [FormalSpec, SP1Clean.GatedLtUnsignedOp.Spec, Vector.getElem_map,
             sub_eq_add_neg]
  unfold id at *
  -- The `byteOpcodeGated` subcircuit hands back the disjunctive spec
  -- `gate = 0 ∨ ByteOpcodeSpec entry` directly.
  have h_byte := h_byte_sub trivial
  -- For each gated assertZero, either gate = 0 or the inner gate holds.
  obtain h_g | h_bit' := mul_eq_zero.mp h_bit
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_f0' := mul_eq_zero.mp h_f0
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_f1' := mul_eq_zero.mp h_f1
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_f2' := mul_eq_zero.mp h_f2
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_f3' := mul_eq_zero.mp h_f3
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_s' := mul_eq_zero.mp h_s
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_x3' := mul_eq_zero.mp h_x3
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_x2' := mul_eq_zero.mp h_x2
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_x1' := mul_eq_zero.mp h_x1
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_x0' := mul_eq_zero.mp h_x0
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_cl0' := mul_eq_zero.mp h_cl0
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_cl1' := mul_eq_zero.mp h_cl1
  · exact Or.inl (by linear_combination h_g)
  obtain h_g | h_nei' := mul_eq_zero.mp h_nei
  · exact Or.inl (by linear_combination h_g)
  -- All 13 gate factors were nonzero, so every inner gate holds.
  refine Or.inr ⟨h_bit', h_f0', h_f1', h_f2', h_f3', h_s', h_x3', h_x2', h_x1',
                h_x0', h_cl0', h_cl1', ?_, ?_⟩
  -- `h_nei'` has `-(s * Y) = 0`; goal needs `(-s) * Y = 0` (equivalent via `neg_mul`).
  · linear_combination h_nei'
  -- Disjunctive byte-range conjunct comes from `byteOpcodeGated.soundness`.
  · simpa using h_byte

omit [Fact (2 ^ 17 < p)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_b_eq, h_c_eq, h_bit_eq, h_f_eq, h_nei_eq, h_cl_eq, h_g_eq⟩ := h_input
  subst h_b_eq
  subst h_c_eq
  subst h_bit_eq
  subst h_f_eq
  subst h_nei_eq
  subst h_cl_eq
  subst h_g_eq
  unfold id at *
  rcases h_spec with h_gate | h_spec'
  · -- gate = 0: every `gate * _` is trivially 0; the byteOpcodeGated
    -- subcircuit takes `gate = 0 ∨ ByteOpcodeSpec _` and `gate = 0` works.
    dsimp only at h_gate
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · rw [h_gate]; ring
    · exact ⟨trivial, Or.inl h_gate⟩
  · -- inner Spec holds: multiply each inner gate by gate.
    simp only [SP1Clean.GatedLtUnsignedOp.Spec, Vector.getElem_map] at h_spec'
    obtain ⟨h_bit', h_f0', h_f1', h_f2', h_f3', h_s', h_x3', h_x2', h_x1', h_x0',
            h_cl0', h_cl1', h_nei', h_byte'⟩ := h_spec'
    -- Each goal is `gate * <X> = 0` and we have `h_<X> : <X> = 0`. After
    -- `subst h_g_eq`, the gate name is `input_var_gate` (under `Expression.eval`).
    set g := Expression.eval env.toEnvironment input_var_gate
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · linear_combination g * h_bit'
    · linear_combination g * h_f0'
    · linear_combination g * h_f1'
    · linear_combination g * h_f2'
    · linear_combination g * h_f3'
    · linear_combination g * h_s'
    · linear_combination g * h_x3'
    · linear_combination g * h_x2'
    · linear_combination g * h_x1'
    · linear_combination g * h_x0'
    · linear_combination g * h_cl0'
    · linear_combination g * h_cl1'
    · linear_combination g * h_nei'
    · -- byteOpcodeGated subcircuit completeness: ⟨Assumptions, Spec⟩.
      -- The Spec branch `mult = 0 ∨ ByteOpcodeSpec entry` is exactly
      -- `h_byte'` (the 14th inner-Spec conjunct), modulo the `a - b ↔
      -- a + -b` shape that simp introduces on the goal side.
      refine ⟨trivial, ?_⟩
      change g = 0 ∨ ByteOpcodeSpec _
      simpa [sub_eq_add_neg] using h_byte'

end Assertion

/-- The gated `FormalAssertion`. Compose into a chip's `Assertion.main`
via `SP1Clean.GatedLtUnsignedOp.assertion ⟨b, c, bit, u16_flags, nei, cl, gate⟩`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.GatedLtUnsignedOp
