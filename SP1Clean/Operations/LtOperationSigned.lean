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
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Clean.Operations.LtOperationUnsigned
import SP1Clean.Operations.U16MSBOperation

/-! # `LtOperationSigned` Clean mirror (scaffold)

SP1's `LtOperationSigned` extends `LtOperationUnsigned` with sign
handling via two `U16MSBOperation` sub-calls on the high limbs and a
limb-3 sign-XOR transform (`b[3] + is_signed*32768 - 65536*b_msb`).
Rust nesting: 3 subcircuit calls + 5 surrounding gates.

Composes:
- `SP1Clean.U16MSBOp.assertion` on `b[3]` (gated by `is_signed`)
- `SP1Clean.U16MSBOp.assertion` on `c[3]` (gated by `is_signed`)
- `SP1Clean.LtUnsignedOp.assertion` on sign-flipped operands (gated by `is_real`)

The `is_signed : F` toggle lets the SAME wrapper handle signed (SLT/SLTI)
and unsigned (SLTU/SLTIU) comparisons — when `is_signed = 0`, the U16MSB
sub-calls become vacuous and the limb-3 transform reduces to identity. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LtSignedOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled FormalAssertion input. Mirrors Rust `LtOperationSigned<T>`'s
cols struct: an embedded `LtOperationUnsigned`-cols + two `U16MSBOp`-cols
(`b_msb`, `c_msb`), plus the two compared words and the `is_signed`
toggle (taken as part of the input rather than a separate parameter so
the chip-level destructure is uniform). -/
structure Inputs (F : Type) where
  b : fields 4 F
  c : fields 4 F
  is_signed : F
  -- Embedded `LtOperationUnsigned` cols:
  compare_bit : F
  u16_flags : fields 4 F
  not_eq_inv : F
  comparison_limbs : fields 2 F
  -- The two U16MSBOp witnesses:
  b_msb : F
  c_msb : F
deriving ProvableStruct

/-- Clean-side circuit. Composes 3 subcircuits per Rust nesting + 5
trailing scalar gates wiring the sign-handling discipline. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- Sub-circuit 1: U16MSB on b[3] (sign bit of high limb).
  SP1Clean.U16MSBOp.assertion
    (⟨input.b[3], input.b_msb⟩ : Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  -- Sub-circuit 2: U16MSB on c[3].
  SP1Clean.U16MSBOp.assertion
    (⟨input.c[3], input.c_msb⟩ : Var SP1Clean.U16MSBOp.Inputs (ZMod p))
  -- Sub-circuit 3: unsigned `<` on sign-flipped operands.
  -- Limb-3 transform: `b'[3] = b[3] + is_signed*32768 - 65536*b_msb`.
  let b3' := input.b[3] + input.is_signed * 32768 - 65536 * input.b_msb
  let c3' := input.c[3] + input.is_signed * 32768 - 65536 * input.c_msb
  SP1Clean.LtUnsignedOp.assertion
    (⟨#v[input.b[0], input.b[1], input.b[2], b3'],
       #v[input.c[0], input.c[1], input.c[2], c3'],
       input.compare_bit,
       input.u16_flags,
       input.not_eq_inv,
       input.comparison_limbs⟩ :
      Var SP1Clean.LtUnsignedOp.Inputs (ZMod p))
  -- 5 trailing scalar gates (`E1, E3, E5, E7, E9` from SP1):
  -- `is_signed` is boolean.
  input.is_signed * (input.is_signed - 1) === 0
  -- `is_real` discipline is delegated to the caller (chip level supplies
  -- `is_real = 1`, so the `is_real * (is_real - 1) = 0` gate is vacuous
  -- inside this wrapper).
  -- `(is_real - 1) * is_signed === 0`: when is_real = 0, is_signed must
  -- be 0 too. Again delegated to caller.
  -- `(is_signed - 1) * b_msb === 0`: when not signed, b_msb = 0.
  (input.is_signed - 1) * input.b_msb === 0
  -- `(is_signed - 1) * c_msb === 0`: when not signed, c_msb = 0.
  (input.is_signed - 1) * input.c_msb === 0

set_option maxHeartbeats 800000 in
-- 3 subcircuits + 3 scalar gates exceeds default `subcircuitsConsistent`.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.LtSignedOp"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Spec composes the three sub-Specs by direct field reference + the 3
surviving trailing gates (is_signed binary + 2 sign-vacuity gates). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let one : ZMod p := 1
  SP1Clean.U16MSBOp.Assertion.Spec ⟨input.b[3], input.b_msb⟩ ∧
  SP1Clean.U16MSBOp.Assertion.Spec ⟨input.c[3], input.c_msb⟩ ∧
  (let b3' := input.b[3] + input.is_signed * 32768 - 65536 * input.b_msb
   let c3' := input.c[3] + input.is_signed * 32768 - 65536 * input.c_msb
   SP1Clean.LtUnsignedOp.Spec
    ⟨#v[input.b[0], input.b[1], input.b[2], b3'],
     #v[input.c[0], input.c[1], input.c[2], c3'],
     input.compare_bit,
     input.u16_flags,
     input.not_eq_inv,
     input.comparison_limbs⟩) ∧
  input.is_signed * (input.is_signed - one) = 0 ∧
  (input.is_signed - one) * input.b_msb = 0 ∧
  (input.is_signed - one) * input.c_msb = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_b_eq, h_c_eq, h_is_signed_eq, h_bit_eq, h_f_eq, h_nei_eq,
          h_cl_eq, h_bmsb_eq, h_cmsb_eq⟩ := h_input
  subst h_b_eq
  subst h_c_eq
  subst h_is_signed_eq
  subst h_bit_eq
  subst h_f_eq
  subst h_nei_eq
  subst h_cl_eq
  subst h_bmsb_eq
  subst h_cmsb_eq
  obtain ⟨h_u16_b_sub, h_u16_c_sub, h_lt_sub, h_is_signed, h_b_vac, h_c_vac⟩ := h_holds
  have h_u16_b := h_u16_b_sub trivial
  have h_u16_c := h_u16_c_sub trivial
  have h_lt := h_lt_sub trivial
  unfold id at *
  simp only [Spec, Vector.getElem_map]
  refine ⟨h_u16_b, h_u16_c, ?_, ?_, ?_, ?_⟩
  · -- LtUnsignedOp.Spec on sign-flipped operands: matches modulo
    -- `a - b = a + (-b)` (`circuit_proof_start` simps `sub_eq_add_neg`
    -- on h_lt's sign-flipped limb expressions).
    convert h_lt using 2 <;> ring
  · linear_combination h_is_signed
  · linear_combination h_b_vac
  · linear_combination h_c_vac

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_b_eq, h_c_eq, h_is_signed_eq, h_bit_eq, h_f_eq, h_nei_eq,
          h_cl_eq, h_bmsb_eq, h_cmsb_eq⟩ := h_input
  subst h_b_eq
  subst h_c_eq
  subst h_is_signed_eq
  subst h_bit_eq
  subst h_f_eq
  subst h_nei_eq
  subst h_cl_eq
  subst h_bmsb_eq
  subst h_cmsb_eq
  simp only [Spec, Vector.getElem_map] at h_spec
  obtain ⟨h_u16_b, h_u16_c, h_lt, h_is_signed, h_b_vac, h_c_vac⟩ := h_spec
  unfold id at *
  refine ⟨⟨trivial, h_u16_b⟩, ⟨trivial, h_u16_c⟩, ⟨trivial, ?_⟩, ?_, ?_, ?_⟩
  · convert h_lt using 2 <;> ring
  · linear_combination h_is_signed
  · linear_combination h_b_vac
  · linear_combination h_c_vac

/-- The full Clean `FormalAssertion` for `LtOperationSigned`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

/-- Bridge `Spec input` to SP1's `allHold` form under `is_signed = 1`.
Composes `U16MSBOp.iff_sp1` ×2 + `LtUnsignedOp.iff_sp1` on the
sign-shifted operand vectors, plus Vector-4/2 eta to align the
`u16_flags` / `comparison_limbs` reshape that SP1's `Constraints.lean`
emits as explicit `#v[v[0], …, v[k]]` literals. Under `is_signed = 1`
the three trailing scalar gates from SP1's RHS (`is_signed` binary +
two sign-vacuity disjunctions) collapse to `True`, and our `Spec`'s
matching three trailing gates collapse to trivial `0 = 0`.

The `is_signed = 1` hypothesis is necessary because: when `is_signed = 0`,
SP1's `CS0`/`CS1` (`U16MSBOperation.constraints`, gated by `is_signed`)
become vacuous; but `main` here unconditionally invokes
`U16MSBOp.assertion`, making `Spec` strictly stronger than SP1's allHold
for the unsigned-mode case. Chip-level callers that need the unsigned
mode go through `GatedLtSignedOp` (the disjunctive form), not this
non-gated `LtSignedOp` mirror. -/
theorem iff_sp1 (input : Inputs (ZMod p)) (h_is_signed : input.is_signed = 1) :
    Spec input ↔
      (LtOperationSigned.constraints input.b input.c
        { result := { u16_compare_operation := { bit := input.compare_bit },
                      u16_flags := input.u16_flags,
                      not_eq_inv := input.not_eq_inv,
                      comparison_limbs := input.comparison_limbs },
          b_msb := { msb := input.b_msb },
          c_msb := { msb := input.c_msb } }
        input.is_signed 1).allHold := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  haveI : Fact (p > 65536) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  haveI : Fact (p > 512) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show ((LtOperationSigned.constraints input.b input.c _ input.is_signed 1).allHold)
        = List.Forall SP1Constraint.toProp
            (LtOperationSigned.constraints input.b input.c _ input.is_signed 1) from rfl,
      LtOperationSigned.allHold_constraints_iff, h_is_signed]
  simp only [show (1 : ZMod p) = 0 ↔ False from by simp,
             show (1 : ZMod p) = 1 ↔ True from by simp,
             or_true, true_or, true_and, and_true]
  -- Bridge both U16MSB sub-CS to their Clean `Spec` form.
  rw [show ∀ (a m : ZMod p),
        List.Forall SP1Constraint.toProp
          (U16MSBOperation.constraints (F := ZMod p) a {msb := m} 1) ↔
        U16MSBOp.Spec a m
      from fun a m => U16MSBOp.iff_sp1 a {msb := m},
      show ∀ (a m : ZMod p),
        List.Forall SP1Constraint.toProp
          (U16MSBOperation.constraints (F := ZMod p) a {msb := m} 1) ↔
        U16MSBOp.Spec a m
      from fun a m => U16MSBOp.iff_sp1 a {msb := m}]
  -- Align the `#v[u16_flags[0..3]]` / `#v[comparison_limbs[0..1]]` reshape
  -- that SP1 emits with our `input.u16_flags` / `input.comparison_limbs`.
  have h_vec4 : #v[input.u16_flags[0], input.u16_flags[1], input.u16_flags[2],
                   input.u16_flags[3]] = input.u16_flags := by
    ext i; fin_cases i <;> rfl
  have h_vec2 : #v[input.comparison_limbs[0], input.comparison_limbs[1]]
                  = input.comparison_limbs := by
    ext i; fin_cases i <;> rfl
  rw [h_vec4, h_vec2]
  -- Unfold Spec, collapse 3 trailing trivial gates, bridge the LtUnsigned sub-CS.
  unfold Spec
  rw [h_is_signed]
  refine ⟨?_, ?_⟩
  · rintro ⟨h_u16_b, h_u16_c, h_lt_spec, _, _, _⟩
    refine ⟨h_u16_b, h_u16_c, ?_⟩
    exact (LtUnsignedOp.iff_sp1
      (⟨#v[input.b[0], input.b[1], input.b[2],
            input.b[3] + 1 * 32768 - 65536 * input.b_msb],
        #v[input.c[0], input.c[1], input.c[2],
            input.c[3] + 1 * 32768 - 65536 * input.c_msb],
        input.compare_bit, input.u16_flags,
        input.not_eq_inv, input.comparison_limbs⟩
       : LtUnsignedOp.Inputs (ZMod p))).mp h_lt_spec
  · rintro ⟨h_u16_b, h_u16_c, h_lt⟩
    refine ⟨h_u16_b, h_u16_c, ?_, ?_, ?_, ?_⟩
    · exact (LtUnsignedOp.iff_sp1
        (⟨#v[input.b[0], input.b[1], input.b[2],
              input.b[3] + 1 * 32768 - 65536 * input.b_msb],
          #v[input.c[0], input.c[1], input.c[2],
              input.c[3] + 1 * 32768 - 65536 * input.c_msb],
          input.compare_bit, input.u16_flags,
          input.not_eq_inv, input.comparison_limbs⟩
         : LtUnsignedOp.Inputs (ZMod p))).mpr h_lt
    · ring
    · ring
    · ring

/-! ## Multiplicity-gated `AssertionGated` form

Parallel to the unconditional `Assertion` namespace above. The
`AssertionGated` form threads a multiplicity expression `is_real` and
gates the three sub-circuits + the four trailing scalar gates (strict
gating; matches the U16CompareOp/AddwOp/LtUnsignedOp.AssertionGated
convention).

The two U16MSB sub-calls use multiplicity = `is_signed` (matching SP1's
`U16MSBOperation.constraints b[3] {...} is_signed`); the LtUnsignedOp
sub-call uses multiplicity = `is_real`. On real rows the chip's gate
`is_signed * (is_signed - 1) = 0` (carried inside the Spec) establishes
`is_signed`'s binarity, satisfying the U16MSB sub-assumption.

Spec is **literal-conjunction under `is_real = 1 →`** — the BV-collapsed
semantic form is unavailable because `LtOperationSigned.iff_sp1_full.mpr`
contains a `sorry` (no `spec_inv` exists for signed-`<`). -/

/-- Multiplicity-aware input: same fields as `Inputs` plus the gating
multiplicity `is_real`. -/
structure InputsGated (F : Type) where
  b : fields 4 F
  c : fields 4 F
  is_signed : F
  compare_bit : F
  u16_flags : fields 4 F
  not_eq_inv : F
  comparison_limbs : fields 2 F
  b_msb : F
  c_msb : F
  is_real : F
deriving ProvableStruct

namespace AssertionGated

open Circuit

/-- Multiplicity-gated `main`: composes three gated sub-assertions
(`U16MSBOp.assertionGated` ×2 with multiplicity = `is_signed`,
`LtUnsignedOp.assertionGated` with multiplicity = `is_real`) plus the
four trailing scalar gates each multiplied by `is_real`. -/
@[reducible]
def main (input : Var InputsGated (ZMod p)) : Circuit (ZMod p) Unit := do
  -- Binarity of `is_real`.
  input.is_real * (input.is_real - 1) === 0
  -- Sub-circuit 1: U16MSB on b[3] (sign bit of high limb), gated by is_signed.
  SP1Clean.U16MSBOp.assertionGated
    (⟨input.b[3], input.b_msb, input.is_signed⟩ :
      Var SP1Clean.U16MSBOp.InputsGated (ZMod p))
  -- Sub-circuit 2: U16MSB on c[3], gated by is_signed.
  SP1Clean.U16MSBOp.assertionGated
    (⟨input.c[3], input.c_msb, input.is_signed⟩ :
      Var SP1Clean.U16MSBOp.InputsGated (ZMod p))
  -- Sub-circuit 3: unsigned `<` on sign-flipped operands, gated by is_real.
  let b3' := input.b[3] + input.is_signed * 32768 - 65536 * input.b_msb
  let c3' := input.c[3] + input.is_signed * 32768 - 65536 * input.c_msb
  SP1Clean.LtUnsignedOp.assertionGated
    (⟨#v[input.b[0], input.b[1], input.b[2], b3'],
       #v[input.c[0], input.c[1], input.c[2], c3'],
       input.compare_bit,
       input.u16_flags,
       input.not_eq_inv,
       input.comparison_limbs,
       input.is_real⟩ :
      Var SP1Clean.LtUnsignedOp.InputsGated (ZMod p))
  -- 3 trailing scalar gates, each gated by is_real.
  input.is_real * (input.is_signed * (input.is_signed - 1)) === 0
  input.is_real * ((input.is_signed - 1) * input.b_msb) === 0
  input.is_real * ((input.is_signed - 1) * input.c_msb) === 0

set_option maxHeartbeats 800000 in
-- 3 subcircuits + 4 scalar gates exceeds default `subcircuitsConsistent`.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) InputsGated unit where
  name := "SP1Clean.LtSignedOpGated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

/-- Three chip-side invariants the caller must establish:
1. `is_real` binarity (chip-side `is_real * (is_real - 1) = 0` gate).
2. `is_signed` binarity (chip-side selector sum, e.g. `is_blt + is_bge`).
3. Padding implies unsigned mode (`is_real = 0 → is_signed = 0`) — true
   by chip-level selector arithmetic since `is_signed ≤ sum_of_selectors
   = is_real`. Used to discharge the U16MSB sub-circuit's Spec
   (`is_signed = 1 → ...`) on padding rows. -/
def Assumptions (input : InputsGated (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_signed = 0 ∨ input.is_signed = 1) ∧
  (input.is_real = 0 → input.is_signed = 0)

/-- Semantic contract: vacuous on padding rows, references the three gated
sub-Specs opaquely (matching what each sub's FormalAssertion returns) +
the three trailing scalar facts on real rows. -/
def Spec (input : InputsGated (ZMod p)) : Prop :=
  input.is_real = 1 →
    let one : ZMod p := 1
    SP1Clean.U16MSBOp.AssertionGated.Spec
      ⟨input.b[3], input.b_msb, input.is_signed⟩ ∧
    SP1Clean.U16MSBOp.AssertionGated.Spec
      ⟨input.c[3], input.c_msb, input.is_signed⟩ ∧
    (let b3' := input.b[3] + input.is_signed * 32768 - 65536 * input.b_msb
     let c3' := input.c[3] + input.is_signed * 32768 - 65536 * input.c_msb
     SP1Clean.LtUnsignedOp.AssertionGated.Spec
      ⟨#v[input.b[0], input.b[1], input.b[2], b3'],
       #v[input.c[0], input.c[1], input.c[2], c3'],
       input.compare_bit,
       input.u16_flags,
       input.not_eq_inv,
       input.comparison_limbs,
       input.is_real⟩) ∧
    input.is_signed * (input.is_signed - one) = 0 ∧
    (input.is_signed - one) * input.b_msb = 0 ∧
    (input.is_signed - one) * input.c_msb = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [AssertionGated.main]
  obtain ⟨h_b_eq, h_c_eq, h_is_signed_eq, h_bit_eq, h_f_eq, h_nei_eq,
          h_cl_eq, h_bmsb_eq, h_cmsb_eq, h_ir_eq⟩ := h_input
  subst h_b_eq; subst h_c_eq; subst h_is_signed_eq; subst h_bit_eq
  subst h_f_eq; subst h_nei_eq; subst h_cl_eq; subst h_bmsb_eq
  subst h_cmsb_eq; subst h_ir_eq
  obtain ⟨h_ir_bin, h_u16_b_sub, h_u16_c_sub, h_lt_sub, h_sb, h_bvac, h_cvac⟩ :=
    h_holds
  obtain ⟨h_ir_binary, h_is_signed_or, _h_padding_unsigned⟩ := h_assumptions
  intro h_is_real
  unfold id at *
  have h_ir_ne_zero : Expression.eval env input_var_is_real ≠ 0 := by
    rw [h_is_real]; exact one_ne_zero
  -- Trailing scalar facts on real rows (after factoring out is_real).
  have h_is_signed_bin :=
    (mul_eq_zero.mp h_sb).resolve_left h_ir_ne_zero
  have h_b_vacuity :=
    (mul_eq_zero.mp h_bvac).resolve_left h_ir_ne_zero
  have h_c_vacuity :=
    (mul_eq_zero.mp h_cvac).resolve_left h_ir_ne_zero
  -- LtUnsignedOp sub-assumption is is_real binarity (Or.inr branch).
  have h_lt_assumps :
      Expression.eval env input_var_is_real = 0 ∨
      Expression.eval env input_var_is_real = 1 := Or.inr h_is_real
  -- U16MSB / LtUnsigned subs hand back their gated Specs.
  have h_u16_b_spec := h_u16_b_sub h_is_signed_or
  have h_u16_c_spec := h_u16_c_sub h_is_signed_or
  have h_lt_spec := h_lt_sub h_lt_assumps
  simp only [Spec, Vector.getElem_map]
  refine ⟨h_u16_b_spec, h_u16_c_spec, ?_, ?_, ?_, ?_⟩
  · -- LtUnsignedOp.AssertionGated.Spec on sign-flipped operands. Both
    -- h_lt_spec and the goal have the same Spec form; the only diff is
    -- `a - b` (goal, from our `let b3'`) vs `a + -b` (h_lt_spec, from
    -- circuit_norm's sub_eq_add_neg normalization).
    convert h_lt_spec using 4 <;> ring
  · linear_combination h_is_signed_bin
  · linear_combination h_b_vacuity
  · linear_combination h_c_vacuity

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [AssertionGated.main]
  obtain ⟨h_b_eq, h_c_eq, h_is_signed_eq, h_bit_eq, h_f_eq, h_nei_eq,
          h_cl_eq, h_bmsb_eq, h_cmsb_eq, h_ir_eq⟩ := h_input
  subst h_b_eq; subst h_c_eq; subst h_is_signed_eq; subst h_bit_eq
  subst h_f_eq; subst h_nei_eq; subst h_cl_eq; subst h_bmsb_eq
  subst h_cmsb_eq; subst h_ir_eq
  unfold id at *
  obtain ⟨h_ir_binary, h_is_signed_or, h_padding_unsigned⟩ := h_assumptions
  rcases h_ir_binary with h_ir0 | h_ir1
  · -- Padding row: is_real = 0; gates trivialize.
    have h_is_signed_zero : Expression.eval env input_var_is_signed = 0 :=
      h_padding_unsigned h_ir0
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ir0]; ring
    · -- U16MSB.assertionGated on b[3]: ⟨SubAssumptions, SubSpec⟩.
      -- SubSpec `is_signed = 1 → ...` is vacuous since is_signed = 0.
      refine ⟨h_is_signed_or, fun h_contra => ?_⟩
      exact absurd (h_is_signed_zero.symm.trans h_contra) zero_ne_one
    · refine ⟨h_is_signed_or, fun h_contra => ?_⟩
      exact absurd (h_is_signed_zero.symm.trans h_contra) zero_ne_one
    · -- LtUnsignedOp.assertionGated: ⟨SubAssumptions, SubSpec⟩.
      refine ⟨Or.inl h_ir0, fun h_contra => ?_⟩
      exact absurd (h_ir0.symm.trans h_contra) zero_ne_one
    · rw [h_ir0]; ring
    · rw [h_ir0]; ring
    · rw [h_ir0]; ring
  · -- Real row: recover all facts from Spec.
    simp only [Spec, Vector.getElem_map] at h_spec
    obtain ⟨h_u16_b, h_u16_c, h_lt, h_sb, h_bvac, h_cvac⟩ := h_spec h_ir1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ir1]; ring
    · -- U16MSB.assertionGated: ⟨SubAssumptions, h_u16_b⟩.
      exact ⟨h_is_signed_or, h_u16_b⟩
    · exact ⟨h_is_signed_or, h_u16_c⟩
    · -- LtUnsignedOp.assertionGated: ⟨Or.inr h_ir1, h_lt⟩ modulo sub_eq_add_neg.
      refine ⟨Or.inr h_ir1, ?_⟩
      convert h_lt using 4 <;> ring
    · rw [h_ir1]; linear_combination h_sb
    · rw [h_ir1]; linear_combination h_bvac
    · rw [h_ir1]; linear_combination h_cvac

/-- Bridge the multiplicity-gated `AssertionGated.Spec` (on real rows,
`is_real = 1`) to SP1's `LtOperationSigned.constraints … is_signed 1`
`allHold`. Both `is_signed` branches are handled:

- `is_signed = 1`: the gated sub-Specs collapse to the non-gated
  `U16MSBOp.Assertion.Spec` / `LtUnsignedOp.Spec` bodies (identical
  bodies, applied to `1 = 1`), reassembling `LtSignedOp.Spec`, which
  `LtSignedOp.iff_sp1` bridges to the raw `allHold`.
- `is_signed = 0`: the two `U16MSBOp` sub-CS are mult-0 vacuous (only the
  `msb` binarity survives, discharged by the sign-vacuity gates forcing
  `b_msb = c_msb = 0`); the `LtUnsignedOp` sub-CS matches the gated
  Spec's `is_real = 1` body modulo the zero-shifted limb-3 collapse.

Consumed by the chip-level `Lemmas.allHold_iff_structural`. -/
theorem iff_sp1 (input : InputsGated (ZMod p))
    (h_is_signed_bin : input.is_signed = 0 ∨ input.is_signed = 1)
    (h_is_real : input.is_real = 1) :
    AssertionGated.Spec input ↔
      (LtOperationSigned.constraints input.b input.c
        { result := { u16_compare_operation := { bit := input.compare_bit },
                      u16_flags := input.u16_flags,
                      not_eq_inv := input.not_eq_inv,
                      comparison_limbs := input.comparison_limbs },
          b_msb := { msb := input.b_msb },
          c_msb := { msb := input.c_msb } }
        input.is_signed 1).allHold := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Unfold the gated Spec at `is_real = 1` to drop the leading implication.
  have hSpec_iff : AssertionGated.Spec input ↔
      (SP1Clean.U16MSBOp.AssertionGated.Spec ⟨input.b[3], input.b_msb, input.is_signed⟩ ∧
       SP1Clean.U16MSBOp.AssertionGated.Spec ⟨input.c[3], input.c_msb, input.is_signed⟩ ∧
       (let b3' := input.b[3] + input.is_signed * 32768 - 65536 * input.b_msb
        let c3' := input.c[3] + input.is_signed * 32768 - 65536 * input.c_msb
        SP1Clean.LtUnsignedOp.AssertionGated.Spec
          ⟨#v[input.b[0], input.b[1], input.b[2], b3'],
           #v[input.c[0], input.c[1], input.c[2], c3'],
           input.compare_bit, input.u16_flags, input.not_eq_inv,
           input.comparison_limbs, input.is_real⟩) ∧
       input.is_signed * (input.is_signed - 1) = 0 ∧
       (input.is_signed - 1) * input.b_msb = 0 ∧
       (input.is_signed - 1) * input.c_msb = 0) := by
    simp only [AssertionGated.Spec, h_is_real, forall_const]
  -- Two helper iffs collapsing the gated sub-Specs to their non-gated forms
  -- on real rows (`is_real = 1`).
  have hU : ∀ (a msb : ZMod p),
      SP1Clean.U16MSBOp.AssertionGated.Spec ⟨a, msb, 1⟩ ↔
      SP1Clean.U16MSBOp.Assertion.Spec ⟨a, msb⟩ := by
    intro a msb
    simp only [SP1Clean.U16MSBOp.AssertionGated.Spec, SP1Clean.U16MSBOp.Assertion.Spec,
      one_ne_zero, forall_const]
  -- Gated LtUnsigned Spec at `is_real = 1` ↔ non-gated `LtUnsignedOp.Spec`.
  have hLt : ∀ (b c : Vector (ZMod p) 4) (cb : ZMod p) (uf : Vector (ZMod p) 4)
      (nei : ZMod p) (cl : Vector (ZMod p) 2),
      SP1Clean.LtUnsignedOp.AssertionGated.Spec ⟨b, c, cb, uf, nei, cl, 1⟩ ↔
      SP1Clean.LtUnsignedOp.Spec ⟨b, c, cb, uf, nei, cl⟩ := by
    intro b c cb uf nei cl
    simp only [SP1Clean.LtUnsignedOp.AssertionGated.Spec, SP1Clean.LtUnsignedOp.Spec,
      one_ne_zero, forall_const]
  -- Gated LtUnsigned Spec at `is_real = 1` ↔ raw `LtOperationUnsigned.constraints` allHold.
  have hLtB : ∀ (b c : Vector (ZMod p) 4) (cb : ZMod p) (uf : Vector (ZMod p) 4)
      (nei : ZMod p) (cl : Vector (ZMod p) 2),
      SP1Clean.LtUnsignedOp.AssertionGated.Spec ⟨b, c, cb, uf, nei, cl, 1⟩ ↔
      List.Forall SP1Constraint.toProp (LtOperationUnsigned.constraints b c
        { u16_compare_operation := { bit := cb }, u16_flags := uf,
          not_eq_inv := nei, comparison_limbs := cl } 1) := by
    intro b c cb uf nei cl
    rw [hLt]
    exact SP1Clean.LtUnsignedOp.iff_sp1 ⟨b, c, cb, uf, nei, cl⟩
  -- Raw U16MSB block at mult 0 ↔ msb binarity (the byte send is vacuous).
  have hU0 : ∀ (a m : ZMod p),
      List.Forall SP1Constraint.toProp
        (U16MSBOperation.constraints (F := ZMod p) a { msb := m } 0) ↔ m * (m - 1) = 0 := by
    intro a m
    simp only [U16MSBOperation.constraints, List.Forall, SP1Constraint.toProp]
    constructor
    · rintro ⟨_, h, _⟩
      linear_combination h
    · intro h
      exact ⟨by ring, by linear_combination h, fun hcon => absurd rfl hcon⟩
  rw [hSpec_iff]
  simp only [h_is_real]
  rcases h_is_signed_bin with h_sgn | h_sgn
  · -- Unsigned mode (`is_signed = 0`): U16MSB subs vacuous, LtUnsigned active.
    rw [h_sgn]
    rw [show ((LtOperationSigned.constraints input.b input.c
          { result := { u16_compare_operation := { bit := input.compare_bit },
                        u16_flags := input.u16_flags, not_eq_inv := input.not_eq_inv,
                        comparison_limbs := input.comparison_limbs },
            b_msb := { msb := input.b_msb }, c_msb := { msb := input.c_msb } }
          (0 : ZMod p) 1).allHold) =
        List.Forall SP1Constraint.toProp (LtOperationSigned.constraints input.b input.c
          { result := { u16_compare_operation := { bit := input.compare_bit },
                        u16_flags := input.u16_flags, not_eq_inv := input.not_eq_inv,
                        comparison_limbs := input.comparison_limbs },
            b_msb := { msb := input.b_msb }, c_msb := { msb := input.c_msb } }
          (0 : ZMod p) 1) from rfl, LtOperationSigned.allHold_constraints_iff]
    dsimp only
    have hv4 : #v[input.u16_flags[0], input.u16_flags[1], input.u16_flags[2],
                  input.u16_flags[3]] = input.u16_flags := by ext i; fin_cases i <;> rfl
    have hv2 : #v[input.comparison_limbs[0], input.comparison_limbs[1]] =
                  input.comparison_limbs := by ext i; fin_cases i <;> rfl
    rw [hv4, hv2]
    simp only [SP1Clean.U16MSBOp.AssertionGated.Spec, zero_ne_one, forall_const,
      false_implies, true_and, hLtB, hU0]
    constructor
    · rintro ⟨hlt, _, hb, hc⟩
      have hb0 : input.b_msb = 0 := by linear_combination -hb
      have hc0 : input.c_msb = 0 := by linear_combination -hc
      refine ⟨?_, ?_, hlt, Or.inl trivial, Or.inr hb0, Or.inr hc0⟩
      · rw [hb0]; ring
      · rw [hc0]; ring
    · rintro ⟨_, _, hlt, _, hb, hc⟩
      have hb0 : input.b_msb = 0 := hb.resolve_left (by simp)
      have hc0 : input.c_msb = 0 := hc.resolve_left (by simp)
      exact ⟨hlt, by ring, by rw [hb0]; ring, by rw [hc0]; ring⟩
  · -- Signed mode (`is_signed = 1`): all sub-Specs become the non-gated bodies,
    -- reassembling `LtSignedOp.Spec`, which `LtSignedOp.iff_sp1` bridges.
    rw [h_sgn]
    refine Iff.trans ?_ (SP1Clean.LtSignedOp.iff_sp1
      ⟨input.b, input.c, 1, input.compare_bit, input.u16_flags, input.not_eq_inv,
       input.comparison_limbs, input.b_msb, input.c_msb⟩ rfl)
    unfold SP1Clean.LtSignedOp.Spec
    simp only [hU, hLt]

end AssertionGated

/-- Multiplicity-gated FormalAssertion for `LtOperationSigned`. Compose
via `LtSignedOp.assertionGated input` in `Chips/.../Multiplicity/`
mirrors. -/
def assertionGated : FormalAssertion (ZMod p) InputsGated :=
  { AssertionGated.elaborated with
    Assumptions := AssertionGated.Assumptions,
    Spec := AssertionGated.Spec,
    soundness := AssertionGated.soundness,
    completeness := AssertionGated.completeness }

end SP1Clean.LtSignedOp
