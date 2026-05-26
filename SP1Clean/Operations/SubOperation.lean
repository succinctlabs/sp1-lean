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
import SP1Clean.SP1Lookup
import SP1Clean.Operations.AddOperation

/-! # `SubOperation` gadget mirror — Assertion style (multiplicity-gated)

The borrow-chain twin of `SP1Clean.AddOperation`. SP1's `SubOperation` is a
4-limb borrow-chain 64-bit subtract; its auto-gen carries `d_i` are in
inverse/borrow form, while the natural-form iff lemma
`SubOperation.allHold_constraints_iff` re-phrases them as the
natural-form carries `c_i`.

This Clean mirror adopts the same gated shape as `SP1Clean.AddOp`: `main`
takes `(a, b, result, is_real)` and emits a binarity gate, 4 `is_real`-gated
borrow-bool asserts, and 4 `byteOpcodeGated` lookups (multiplicity = `is_real`)
matching SP1's `InteractionKind::Byte` per-row contribution.

## Contract design — semantic-only `FormalAssertion.Spec`

`RawSpec` keeps SP1's `allHold_constraints_iff` RHS verbatim (natural
carry-bool + range form) as a top-level helper; `iff_sp1` is a one-line
re-export. The FormalAssertion's `Spec` carries only the semantic content
(BitVec subtraction identity + `isU64` on the result), gated by `is_real = 1`:

```
Assumptions input := (is_real ∈ {0,1}) ∧ (is_real = 1 → isU64 a ∧ isU64 b)
Spec        input := is_real = 1 → (isU64 result ∧ BV equation)
```

Both vacuous on padding rows. Mirrors `SP1Clean.AddOp` one-for-one; the
borrow/carry bridge is an implementation detail of `main`'s emission form. -/

namespace SP1Clean.SubOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 512) := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩

/-- Clean-side circuit. Asserts (gated by `is_real`) the borrow chain
between operand limbs `a`, `b` and result limbs `result`, and that each
result limb fits in `< 2^16` via `byteOpcodeGated` with `mult = is_real`.
The borrow expression matches SP1's auto-gen `SubOperation.constraints`
verbatim; gating + binarity match SP1's `InteractionKind::Byte` shape. -/
def main (a b result : Vector (Expression (ZMod p)) 4)
    (is_real : Expression (ZMod p)) : Circuit (ZMod p) Unit := do
  is_real * (is_real - 1) === 0
  let k65536 : Expression (ZMod p) := 65536
  let k1 : Expression (ZMod p) := 1
  let d0 := (a[0] + k65536 - k1 - b[0] - result[0] + k1) * (65536 : ZMod p)⁻¹
  let d1 := (a[1] + k65536 - k1 - b[1] - result[1] + d0) * (65536 : ZMod p)⁻¹
  let d2 := (a[2] + k65536 - k1 - b[2] - result[2] + d1) * (65536 : ZMod p)⁻¹
  let d3 := (a[3] + k65536 - k1 - b[3] - result[3] + d2) * (65536 : ZMod p)⁻¹
  is_real * (d0 * (d0 - 1)) === 0
  is_real * (d1 * (d1 - 1)) === 0
  is_real * (d2 * (d2 - 1)) === 0
  is_real * (d3 * (d3 - 1)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), result[0], 16, 0], is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), result[1], 16, 0], is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), result[2], 16, 0], is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), result[3], 16, 0], is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))

/-- Pilot Spec, mirroring `SubOperation.allHold_constraints_iff` RHS
verbatim: each of the 4 natural-form carries is boolean and each result
limb fits in `< 65536`. Kept as a top-level helper for callers that want
the carry-form bridge (e.g. for direct `iff_sp1` consumption). -/
def RawSpec (a b result : Word (ZMod p)) : Prop :=
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
the pilot `RawSpec`. Direct re-export of
`SubOperation.allHold_constraints_iff`. -/
theorem iff_sp1 (a b : Word (ZMod p)) (cols : SubOperation (ZMod p)) :
    (SubOperation.constraints a b cols 1).allHold ↔
      RawSpec a b cols.value :=
  SubOperation.allHold_constraints_iff a b cols

/-! ## Full `FormalAssertion` promotion

Wraps the assertion-style `main` above into a Clean `FormalAssertion`.
Mirrors `SP1Clean.AddOp.assertion` one-for-one — `Spec` is semantic-only
(BitVec subtraction identity), `RawSpec` stays around as a helper for the
internal borrow-form bridging. -/

/-- Bundled FormalAssertion input: the two operand words, the result word,
and the `is_real` flag (binarity + gate for the byte bus). -/
structure Inputs (F : Type) where
  a : fields 4 F
  b : fields 4 F
  result : fields 4 F
  is_real : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Wrapper around `SP1Clean.SubOp.main` that destructures a `Var Inputs`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Clean.SubOp.main input.a input.b input.result input.is_real

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.SubOp"
  main := main
  -- 4 × `byteOpcodeGated.localLength` (= 4 hint rows each) = 16.
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, SP1Clean.SubOp.main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, SP1Clean.SubOp.main, circuit_norm]

/-- Assumptions mirror `SP1Clean.AddOp.Assertion.Assumptions`: chip callers
witness the binarity of `is_real` externally (the in-circuit
`is_real * (is_real - 1) = 0` gate doesn't surface to `Spec`); the
conditional operand bounds carry the `Word.isU64` facts under `is_real = 1`,
typically pulled from the reader sub-circuit's `RegisterAccess.Spec`. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 → (Word.isU64 input.a ∧ Word.isU64 input.b))

/-- The FormalAssertion's semantic contract. Mirrors `AddOp.Assertion.Spec`:
vacuous on padding rows; on real rows asserts `isU64 result` and the
BitVec subtraction identity. The borrow/carry decomposition that `main`
threads internally is *not* exposed here — it's the implementation detail
of the byte-level encoding and can be recovered on demand via
`SubOperation.iff_sp1_full`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    Word.isU64 input.result ∧
    Word.toBitVec64 input.result =
      Word.toBitVec64 input.a - Word.toBitVec64 input.b

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

/-- Soundness of `SP1Clean.SubOp.assertion`. Under `is_real = 1`, the
circuit's gated emissions reduce (via `mul_eq_zero` + `resolve_left`) to
the borrow-form quadratics plus result-limb ranges. The borrow ↔ natural
carry form bridge gives `RawSpec`; `iff_sp1.mpr` then SP1's `allHold`;
`SubOperation.spec` lifts to `(isU64 result ∧ BV eq)`. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [SP1Clean.SubOp.main]
  obtain ⟨h_a, h_b, h_r, h_ir⟩ := h_input
  subst h_a; subst h_b; subst h_r; subst h_ir
  obtain ⟨h_ir_bin, h_gd0, h_gd1, h_gd2, h_gd3,
          h_l0_sub, h_l1_sub, h_l2_sub, h_l3_sub⟩ := h_holds
  obtain ⟨_h_ir_binary, h_bounds⟩ := h_assumptions
  intro h_is_real
  unfold id at *
  obtain ⟨h_isU64_a, h_isU64_b⟩ := h_bounds h_is_real
  have h_ir_ne_zero : Expression.eval env input_var_is_real ≠ 0 := by
    rw [h_is_real]; exact one_ne_zero
  have h_d0 := (mul_eq_zero.mp h_gd0).resolve_left h_ir_ne_zero
  have h_d1 := (mul_eq_zero.mp h_gd1).resolve_left h_ir_ne_zero
  have h_d2 := (mul_eq_zero.mp h_gd2).resolve_left h_ir_ne_zero
  have h_d3 := (mul_eq_zero.mp h_gd3).resolve_left h_ir_ne_zero
  have hr0 := SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _
                ((h_l0_sub trivial).resolve_left h_ir_ne_zero)
  have hr1 := SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _
                ((h_l1_sub trivial).resolve_left h_ir_ne_zero)
  have hr2 := SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _
                ((h_l2_sub trivial).resolve_left h_ir_ne_zero)
  have hr3 := SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16 _
                ((h_l3_sub trivial).resolve_left h_ir_ne_zero)
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hbridge : (65536 : ZMod p)⁻¹ * (65536 : ZMod p) = 1 :=
    inv_mul_cancel₀ val_65536_ne_zero
  -- Build RawSpec by bridging each borrow-form quadratic to a natural-form
  -- carry-bool fact via the d ↔ c identity `d_i + c_i = 1`.
  have h_raw : SP1Clean.SubOp.RawSpec
      (Vector.map (Expression.eval env) input_var_a)
      (Vector.map (Expression.eval env) input_var_b)
      (Vector.map (Expression.eval env) input_var_result) := by
    simp only [SP1Clean.SubOp.RawSpec, Vector.getElem_map]
    refine ⟨?_, ?_, ?_, ?_, hr0, hr1, hr2, hr3⟩
    · obtain h | h := mul_eq_zero.mp h_d0
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
  have h_allHold : (SubOperation.constraints
        (Vector.map (Expression.eval env) input_var_a)
        (Vector.map (Expression.eval env) input_var_b)
        ⟨Vector.map (Expression.eval env) input_var_result⟩
        1).allHold :=
    (iff_sp1 _ _ _).mpr h_raw
  have ⟨h_isU64_v, h_bv⟩ := SubOperation.spec h_isU64_a h_isU64_b h_allHold
  refine ⟨h_isU64_v, ?_⟩
  exact h_bv

/-- Completeness of `SP1Clean.SubOp.assertion`. Case-splits on `is_real
∈ {0, 1}` (from `Assumptions`): padding rows trivialize every gated
emission; real rows recover `RawSpec` via `SubOperation.iff_sp1_full`
from the chip's semantic `Spec` plus operand bounds, and each gate
discharges via the natural ↔ borrow bridge. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [SP1Clean.SubOp.main]
  obtain ⟨h_a, h_b, h_r, h_ir⟩ := h_input
  subst h_a; subst h_b; subst h_r; subst h_ir
  obtain ⟨h_ir_binary, h_bounds⟩ := h_assumptions
  unfold id at *
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hbridge : (65536 : ZMod p)⁻¹ * (65536 : ZMod p) = 1 :=
    inv_mul_cancel₀ val_65536_ne_zero
  rcases h_ir_binary with h_ir0 | h_ir1
  · -- Padding row: is_real = 0; every gated emission trivializes.
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ir0]; ring
    · rw [h_ir0]; ring
    · rw [h_ir0]; ring
    · rw [h_ir0]; ring
    · rw [h_ir0]; ring
    · exact ⟨trivial, Or.inl h_ir0⟩
    · exact ⟨trivial, Or.inl h_ir0⟩
    · exact ⟨trivial, Or.inl h_ir0⟩
    · exact ⟨trivial, Or.inl h_ir0⟩
  · -- Real row: is_real = 1. Recover RawSpec via iff_sp1_full + iff_sp1 from
    -- the chip's semantic Spec + operand bounds; then bridge natural ↔ borrow.
    obtain ⟨h_isU64_a, h_isU64_b⟩ := h_bounds h_ir1
    obtain ⟨h_isU64_v, h_bv⟩ := h_spec h_ir1
    have h_bv' : Word.toBitVec64
        (Vector.map (Expression.eval env.toEnvironment) input_var_result) =
        execute_RTYPE_pure_w
          (Vector.map (Expression.eval env.toEnvironment) input_var_a)
          (Vector.map (Expression.eval env.toEnvironment) input_var_b) .SUB := h_bv
    have h_allHold := (SubOperation.iff_sp1_full h_isU64_a h_isU64_b
      (cols := ⟨Vector.map (Expression.eval env.toEnvironment) input_var_result⟩)).mpr
        ⟨h_isU64_v, h_bv'⟩
    have h_raw := (iff_sp1 _ _ _).mp h_allHold
    obtain ⟨hc0, hc1, hc2, hc3, hr0, hr1, hr2, hr3⟩ := h_raw
    simp only [Vector.getElem_map] at hc0 hc1 hc2 hc3 hr0 hr1 hr2 hr3
    -- Establish per-limb bridge identities `d_i + c_i = 1`. The d_i side
    -- is in post-`circuit_norm` form (`+ -1 + -<eval>`); the c_i side is
    -- in natural-spec form (`+ <eval> - <eval>`).
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
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ir1]; ring
    · rw [h_ir1]; rw [d_quad_of_c_bool_bridge _ _ hdc0 hc0]; ring
    · rw [h_ir1]; rw [d_quad_of_c_bool_bridge _ _ hdc1 hc1]; ring
    · rw [h_ir1]; rw [d_quad_of_c_bool_bridge _ _ hdc2 hc2]; ring
    · rw [h_ir1]; rw [d_quad_of_c_bool_bridge _ _ hdc3 hc3]; ring
    · exact ⟨trivial,
        Or.inr (SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr0)⟩
    · exact ⟨trivial,
        Or.inr (SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr1)⟩
    · exact ⟨trivial,
        Or.inr (SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr2)⟩
    · exact ⟨trivial,
        Or.inr (SP1Clean.AddOp.Assertion.byteOpcodeSpec_range16_of_lt _ hr3)⟩

end Assertion

/-- The full Clean `FormalAssertion` for `SubOperation`: soundness +
completeness against the semantic `Spec` (mirroring AddOp). The
borrow-form auto-gen carries in `main` are bridged internally via
`d_i = 1 - c_i` (cf. `SubOperation.allHold_constraints_iff`). -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.SubOp
