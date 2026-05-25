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
import SP1Operations.Operation.SubOperation.SubOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.Operations.AddOperation

/-! # `SubOperation` gadget mirror — Assertion style

The borrow-chain twin of `SP1Clean.AddOperation`. SP1's `SubOperation` is a
4-limb borrow-chain 64-bit subtract; its auto-gen carries `d_i` are in
inverse/borrow form, while the natural-form iff lemma
`SubOperation.allHold_constraints_iff` re-phrases them as the
natural-form carries `c_i`.

The Clean-side `main` matches SP1's auto-gen RHS (borrow form) verbatim,
keeping the `iff_sp1` bridge a one-line re-export. The `Spec` uses the
natural-form carries so it reads symmetrically with `AddOp.Spec`, and the
`Assertion.Spec` (mirroring `AddOp.Assertion.Spec`) re-packages the top-level
`SP1Clean.SubOp.Spec` on the struct fields — one `main`, one `Spec` per
file. Soundness and completeness bridge the borrow-form `main` to the
natural-form `Spec` internally via `d_i = 1 - c_i` (same recipe as
`SubOperation.allHold_constraints_iff`).
-/

namespace SP1Clean.SubOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Asserts the borrow chain holds between the operand
limbs `a`, `b` and the result limbs `result`, and that each result limb
fits in `< 2^16`. The borrow expression matches SP1's auto-gen
`SubOperation.constraints` verbatim. -/
def main (a b result : Vector (Expression (ZMod p)) 4) : Circuit (ZMod p) Unit := do
  let k65536 : Expression (ZMod p) := 65536
  let k1 : Expression (ZMod p) := 1
  let d0 := (a[0] + k65536 - k1 - b[0] - result[0] + k1) * (65536 : ZMod p)⁻¹
  let d1 := (a[1] + k65536 - k1 - b[1] - result[1] + d0) * (65536 : ZMod p)⁻¹
  let d2 := (a[2] + k65536 - k1 - b[2] - result[2] + d1) * (65536 : ZMod p)⁻¹
  let d3 := (a[3] + k65536 - k1 - b[3] - result[3] + d2) * (65536 : ZMod p)⁻¹
  d0 * (d0 - 1) === 0
  d1 * (d1 - 1) === 0
  d2 * (d2 - 1) === 0
  d3 * (d3 - 1) === 0
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[0], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[1], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[2], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), result[3], 16, 0] : Vector (Expression (ZMod p)) 4)

/-- Pilot Spec, mirroring `SubOperation.allHold_constraints_iff` RHS
verbatim: each of the 4 natural-form carries is boolean and each result
limb fits in `< 65536`. -/
def Spec (a b result : Word (ZMod p)) : Prop :=
  let carry0 : ZMod p := (b[0] + result[0] - a[0]) * 65536⁻¹
  let carry1 : ZMod p := (b[1] + result[1] - a[1] + carry0) * 65536⁻¹
  let carry2 : ZMod p := (b[2] + result[2] - a[2] + carry1) * 65536⁻¹
  let carry3 : ZMod p := (b[3] + result[3] - a[3] + carry2) * 65536⁻¹
  (carry0 = 0 ∨ carry0 = 1) ∧
  (carry1 = 0 ∨ carry1 = 1) ∧
  (carry2 = 0 ∨ carry2 = 1) ∧
  (carry3 = 0 ∨ carry3 = 1) ∧
  result[0].val < 65536 ∧
  result[1].val < 65536 ∧
  result[2].val < 65536 ∧
  result[3].val < 65536

/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. Direct re-export of
`SubOperation.allHold_constraints_iff`. -/
theorem iff_sp1 (a b : Word (ZMod p)) (cols : SubOperation (ZMod p)) :
    (SubOperation.constraints a b cols 1).allHold ↔
      Spec a b cols.value :=
  SubOperation.allHold_constraints_iff a b cols

/-! ## Full `FormalAssertion` promotion — natural-carry form

Wraps the assertion-style `main` above into a Clean `FormalAssertion` whose
`Assertion.Spec` is the natural-carry form `SP1Clean.SubOp.Spec`
(matching the AddOp parallel — one Spec per file, identical shape across
operations). `main` continues to emit the borrow-form constraints verbatim
(matching SP1's auto-gen); the bridge between the two forms is handled
internally via the algebraic identity `d_i = 1 - c_i` (same recipe as
`SubOperation.allHold_constraints_iff`). -/

/-- Bundled FormalAssertion input: the two operand words and the result
word. -/
structure Inputs (F : Type) where
  a : fields 4 F
  b : fields 4 F
  result : fields 4 F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Wrapper around `SP1Clean.SubOp.main` that destructures a `Var Inputs`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Clean.SubOp.main input.a input.b input.result

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.SubOp"
  main := main
  localLength _ := 0

/-- No external assumptions. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The FormalAssertion's spec, in **natural-carry form**: mirrors
`AddOp.Assertion.Spec` (which re-packages `SP1Clean.AddOp.Spec` on the
struct fields). Stated this way so chip-level `circuit_proof_start`
produces the same `SP1Clean.SubOp.Spec a b result` form that
`SubOp.iff_sp1` bridges to SP1's `SubOperation.constraints.allHold`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  SP1Clean.SubOp.Spec input.a input.b input.result

/-! ### Bridge helpers

Two parametric helpers that abstract the algebraic content of the
borrow ↔ natural form swap. Each takes a `bridge : x + y = 1` identity
relating the borrow value `x` to the natural carry `y`, plus the
corresponding boolean fact, and produces the other form. The bridge
identity itself is established per-limb via `linear_combination hbridge`
(possibly chained through the previous limb's bridge for `i > 0`). -/

private lemma c_bool_of_d_quad_bridge {p : ℕ} [Fact (Nat.Prime p)]
    (x y : ZMod p) (hxy : x + y = 1) (h : x * (x - 1) = 0) :
    y = 0 ∨ y = 1 := by
  rcases mul_eq_zero.mp h with h | h
  · exact Or.inr (by linear_combination hxy - h)
  · exact Or.inl (by linear_combination hxy - h)

private lemma d_quad_of_c_bool_bridge {p : ℕ} [Fact (Nat.Prime p)]
    (x y : ZMod p) (hxy : x + y = 1) (h : y = 0 ∨ y = 1) :
    x * (x + -1) = 0 := by
  rcases h with h | h
  · have hx : x = 1 := by linear_combination hxy - h
    rw [hx]; ring
  · have hx : x = 0 := by linear_combination hxy - h
    rw [hx]; ring

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  simp only [SP1Clean.SubOp.main, circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_d0, h_d1, h_d2, h_d3, h_l0, h_l1, h_l2, h_l3⟩ := h_holds
  simp only [SP1Clean.SubOp.Spec, Vector.getElem_map]
  unfold id at *
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hbridge : (65536 : ZMod p)⁻¹ * (65536 : ZMod p) = 1 :=
    inv_mul_cancel₀ val_65536_ne_zero
  refine ⟨?_, ?_, ?_, ?_,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l0,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l1,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l2,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _ h_l3⟩
  · -- c_0 ∈ {0, 1}: close directly via linear_combination on h_d0 and hbridge.
    obtain h | h := mul_eq_zero.mp h_d0
    · exact Or.inr (by linear_combination -h + hbridge)
    · exact Or.inl (by linear_combination -h + hbridge)
  · obtain h | h := mul_eq_zero.mp h_d1
    · exact Or.inr (by
        linear_combination -h + (1 + (65536 : ZMod p)⁻¹) * hbridge)
    · exact Or.inl (by
        linear_combination -h + (1 + (65536 : ZMod p)⁻¹) * hbridge)
  · obtain h | h := mul_eq_zero.mp h_d2
    · exact Or.inr (by
        linear_combination -h +
          (1 + (65536 : ZMod p)⁻¹ + (65536 : ZMod p)⁻¹ ^ 2) * hbridge)
    · exact Or.inl (by
        linear_combination -h +
          (1 + (65536 : ZMod p)⁻¹ + (65536 : ZMod p)⁻¹ ^ 2) * hbridge)
  · obtain h | h := mul_eq_zero.mp h_d3
    · exact Or.inr (by
        linear_combination -h + (1 + (65536 : ZMod p)⁻¹ +
          (65536 : ZMod p)⁻¹ ^ 2 + (65536 : ZMod p)⁻¹ ^ 3) * hbridge)
    · exact Or.inl (by
        linear_combination -h + (1 + (65536 : ZMod p)⁻¹ +
          (65536 : ZMod p)⁻¹ ^ 2 + (65536 : ZMod p)⁻¹ ^ 3) * hbridge)

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  dsimp only [Spec, SP1Clean.SubOp.Spec] at h_spec
  simp only [Vector.getElem_map] at h_spec
  obtain ⟨hc0_bool, hc1_bool, hc2_bool, hc3_bool, hr0, hr1, hr2, hr3⟩ := h_spec
  simp only [SP1Clean.SubOp.main, circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  unfold id at *
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hbridge : (65536 : ZMod p)⁻¹ * (65536 : ZMod p) = 1 :=
    inv_mul_cancel₀ val_65536_ne_zero
  -- Establish per-limb bridge identities `d_i + c_i = 1`. The d_i side
  -- is in post-`circuit_norm` form (`+ -1 + -<eval>`); the c_i side is
  -- in natural-spec form (`+ <eval> - <eval>`). Each literal is annotated
  -- with `(... : ZMod p)` to avoid `Nat → ZMod p` coercions that would
  -- mis-align the bridge type with the (un-coerced) goal.
  have hdc0 :
      (Expression.eval env.toEnvironment input_var_a[0] + (65536 : ZMod p) +
       (-1 : ZMod p) +
       -Expression.eval env.toEnvironment input_var_b[0] +
       -Expression.eval env.toEnvironment input_var_result[0] +
       (1 : ZMod p)) * (65536 : ZMod p)⁻¹ +
      (Expression.eval env.toEnvironment input_var_b[0] +
       Expression.eval env.toEnvironment input_var_result[0] -
       Expression.eval env.toEnvironment input_var_a[0]) *
        (65536 : ZMod p)⁻¹ = (1 : ZMod p) := by
    linear_combination hbridge
  have hdc1 :
      (Expression.eval env.toEnvironment input_var_a[1] + (65536 : ZMod p) +
       (-1 : ZMod p) +
       -Expression.eval env.toEnvironment input_var_b[1] +
       -Expression.eval env.toEnvironment input_var_result[1] +
       (Expression.eval env.toEnvironment input_var_a[0] + (65536 : ZMod p) +
        (-1 : ZMod p) +
        -Expression.eval env.toEnvironment input_var_b[0] +
        -Expression.eval env.toEnvironment input_var_result[0] +
        (1 : ZMod p)) * (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹ +
      (Expression.eval env.toEnvironment input_var_b[1] +
       Expression.eval env.toEnvironment input_var_result[1] -
       Expression.eval env.toEnvironment input_var_a[1] +
       (Expression.eval env.toEnvironment input_var_b[0] +
        Expression.eval env.toEnvironment input_var_result[0] -
        Expression.eval env.toEnvironment input_var_a[0]) *
         (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹ = (1 : ZMod p) := by
    linear_combination (1 + (65536 : ZMod p)⁻¹) * hbridge
  have hdc2 :
      (Expression.eval env.toEnvironment input_var_a[2] + (65536 : ZMod p) +
       (-1 : ZMod p) +
       -Expression.eval env.toEnvironment input_var_b[2] +
       -Expression.eval env.toEnvironment input_var_result[2] +
       (Expression.eval env.toEnvironment input_var_a[1] + (65536 : ZMod p) +
        (-1 : ZMod p) +
        -Expression.eval env.toEnvironment input_var_b[1] +
        -Expression.eval env.toEnvironment input_var_result[1] +
        (Expression.eval env.toEnvironment input_var_a[0] + (65536 : ZMod p) +
         (-1 : ZMod p) +
         -Expression.eval env.toEnvironment input_var_b[0] +
         -Expression.eval env.toEnvironment input_var_result[0] +
         (1 : ZMod p)) * (65536 : ZMod p)⁻¹) *
        (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹ +
      (Expression.eval env.toEnvironment input_var_b[2] +
       Expression.eval env.toEnvironment input_var_result[2] -
       Expression.eval env.toEnvironment input_var_a[2] +
       (Expression.eval env.toEnvironment input_var_b[1] +
        Expression.eval env.toEnvironment input_var_result[1] -
        Expression.eval env.toEnvironment input_var_a[1] +
        (Expression.eval env.toEnvironment input_var_b[0] +
         Expression.eval env.toEnvironment input_var_result[0] -
         Expression.eval env.toEnvironment input_var_a[0]) *
          (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹) *
        (65536 : ZMod p)⁻¹ = (1 : ZMod p) := by
    linear_combination
      (1 + (65536 : ZMod p)⁻¹ + (65536 : ZMod p)⁻¹ ^ 2) * hbridge
  have hdc3 :
      (Expression.eval env.toEnvironment input_var_a[3] + (65536 : ZMod p) +
       (-1 : ZMod p) +
       -Expression.eval env.toEnvironment input_var_b[3] +
       -Expression.eval env.toEnvironment input_var_result[3] +
       (Expression.eval env.toEnvironment input_var_a[2] + (65536 : ZMod p) +
        (-1 : ZMod p) +
        -Expression.eval env.toEnvironment input_var_b[2] +
        -Expression.eval env.toEnvironment input_var_result[2] +
        (Expression.eval env.toEnvironment input_var_a[1] + (65536 : ZMod p) +
         (-1 : ZMod p) +
         -Expression.eval env.toEnvironment input_var_b[1] +
         -Expression.eval env.toEnvironment input_var_result[1] +
         (Expression.eval env.toEnvironment input_var_a[0] + (65536 : ZMod p) +
          (-1 : ZMod p) +
          -Expression.eval env.toEnvironment input_var_b[0] +
          -Expression.eval env.toEnvironment input_var_result[0] +
          (1 : ZMod p)) * (65536 : ZMod p)⁻¹) *
         (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹) *
       (65536 : ZMod p)⁻¹ +
      (Expression.eval env.toEnvironment input_var_b[3] +
       Expression.eval env.toEnvironment input_var_result[3] -
       Expression.eval env.toEnvironment input_var_a[3] +
       (Expression.eval env.toEnvironment input_var_b[2] +
        Expression.eval env.toEnvironment input_var_result[2] -
        Expression.eval env.toEnvironment input_var_a[2] +
        (Expression.eval env.toEnvironment input_var_b[1] +
         Expression.eval env.toEnvironment input_var_result[1] -
         Expression.eval env.toEnvironment input_var_a[1] +
         (Expression.eval env.toEnvironment input_var_b[0] +
          Expression.eval env.toEnvironment input_var_result[0] -
          Expression.eval env.toEnvironment input_var_a[0]) *
           (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹) *
         (65536 : ZMod p)⁻¹) * (65536 : ZMod p)⁻¹ = (1 : ZMod p) := by
    linear_combination
      (1 + (65536 : ZMod p)⁻¹ + (65536 : ZMod p)⁻¹ ^ 2 +
       (65536 : ZMod p)⁻¹ ^ 3) * hbridge
  refine ⟨?_, ?_, ?_, ?_,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr0,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr1,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr2,
          SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr3⟩
  · exact d_quad_of_c_bool_bridge _ _ hdc0 hc0_bool
  · exact d_quad_of_c_bool_bridge _ _ hdc1 hc1_bool
  · exact d_quad_of_c_bool_bridge _ _ hdc2 hc2_bool
  · exact d_quad_of_c_bool_bridge _ _ hdc3 hc3_bool

end Assertion

/-- The full Clean `FormalAssertion` for `SubOperation`: soundness +
completeness against the natural-form `Spec` (mirroring AddOp). The
borrow-form auto-gen carries in `main` are bridged internally via
`d_i = 1 - c_i` (cf. `SubOperation.allHold_constraints_iff`). -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.SubOp
