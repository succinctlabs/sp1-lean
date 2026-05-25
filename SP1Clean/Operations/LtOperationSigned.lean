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

/-- Bridge to SP1: `Spec input` is equivalent to SP1's
`LtOperationSigned.constraints` `allHold` form under `is_real = 1` AND
`is_signed = 1`. The proof is structural — SP1's `allHold_constraints_iff`
exposes 3 sub-CS + 3 disjunctive scalar gates; each sub-CS bridges via
the matching op's `iff_sp1`; the 3 scalar gates trivialize under
`is_signed = 1`.

The `is_signed = 1` hypothesis is necessary because: when `is_signed = 0`,
SP1's `CS0`/`CS1` (`U16MSBOperation.constraints`, gated by `is_signed`)
become vacuous; but `main` here unconditionally invokes
`U16MSBOp.assertion`, making `Spec` strictly stronger than SP1's allHold
for the unsigned-mode case. Chip-level callers that need the unsigned
mode go through `GatedLtSignedOp` (the disjunctive form), not this
non-gated `LtSignedOp` mirror.

**Note.** The bridge body is `sorry` pending resolution of the Vector
unification between SP1's `allHold_constraints_iff` RHS (which projects
through `cols.b_msb.msb`, `cols.result.u16_flags[0]`, etc.) and our
`Inputs`-shaped Spec (which uses `input.b_msb`, `input.u16_flags`
directly). The structural correspondence is straightforward in principle
(soundness + completeness already close axiom-clean) but the Lean
elaboration friction is high enough that we don't burn time on it for
a theorem with zero downstream consumers. See
`docs/CLEAN_PILOT_ROADMAP.md` for the broader sorries punch-list. -/
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
  sorry

end SP1Clean.LtSignedOp
