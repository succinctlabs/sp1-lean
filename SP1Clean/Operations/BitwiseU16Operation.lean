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
import SP1Operations.Operation.BitwiseU16Operation.BitwiseU16Operation
import SP1Clean.ByteOpcodeTable
import SP1Clean.SP1Lookup
import SP1Clean.Operations.BitwiseOperation
import SP1Clean.Operations.U16toU8OperationUnsafe

/-! # `BitwiseU16Operation` Clean mirror — faithful sub-circuit composition

SP1's `BitwiseU16Operation.constraints` (see
`SP1Operations/Operation/BitwiseU16Operation/Constraints.lean:12-34`)
composes three sub-operations:
- `U16toU8OperationUnsafe.constraints` on `b`  (algebraic byte decomposition; empty constraint list)
- `U16toU8OperationUnsafe.constraints` on `cc` (algebraic byte decomposition; empty constraint list)
- `BitwiseOperation.constraints` on the decomposed bytes (8 byte-table lookups, gated by `is_real`)

plus a binarity gate `is_real * (is_real - 1) = 0`.

This Clean mirror composes the corresponding three `FormalAssertion`s as
true sub-circuits — `SP1Clean.U16toU8OpUnsafe.assertion` (×2, trivial)
and `SP1Clean.BitwiseOpGated.assertion` (with `mult = input.is_real`) —
plus the binarity gate emission.

Following the structural-fidelity principle from the user feedback: the
`Spec` directly mirrors what each sub-assertion hands back — a 2-tuple
of (binarity equation, gated per-byte disjunction). The bridge to the
SP1-native `BitwiseU16Operation.allHold_constraints_iff` form lives as a
separate `iff_sp1` theorem at the end.

See `CLAUDE.md` § "Faithful sub-circuit composition" for the principle.
-/

namespace SP1Clean.BitwiseU16Op

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 512) := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩

/-- Bundled FormalAssertion input. Mirrors SP1's `BitwiseU16Operation`
column-struct (`b_low_bytes`, `c_low_bytes`, `bitwise_operation.result`)
flattened with the two operands, opcode, and is_real gate. -/
structure Inputs (F : Type) where
  b : fields 4 F
  cc : fields 4 F
  b_low_bytes : fields 4 F
  c_low_bytes : fields 4 F
  result : fields 8 F
  opcode : F
  is_real : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Clean-side circuit. Emits the binarity gate, two (trivial)
`U16toU8OpUnsafe` sub-assertions matching SP1's composition graph, and
the `BitwiseOpGated` sub-assertion on the algebraic 8-byte
decompositions of `b` and `cc`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  input.is_real * (input.is_real - 1) === 0
  SP1Clean.U16toU8OpUnsafe.assertion
    (⟨input.b, input.b_low_bytes⟩ : Var SP1Clean.U16toU8OpUnsafe.Inputs (ZMod p))
  SP1Clean.U16toU8OpUnsafe.assertion
    (⟨input.cc, input.c_low_bytes⟩ : Var SP1Clean.U16toU8OpUnsafe.Inputs (ZMod p))
  SP1Clean.BitwiseOpGated.assertion
    (⟨#v[input.b_low_bytes[0],
         (input.b[0] - input.b_low_bytes[0]) * (256 : ZMod p)⁻¹,
         input.b_low_bytes[1],
         (input.b[1] - input.b_low_bytes[1]) * (256 : ZMod p)⁻¹,
         input.b_low_bytes[2],
         (input.b[2] - input.b_low_bytes[2]) * (256 : ZMod p)⁻¹,
         input.b_low_bytes[3],
         (input.b[3] - input.b_low_bytes[3]) * (256 : ZMod p)⁻¹],
       #v[input.c_low_bytes[0],
         (input.cc[0] - input.c_low_bytes[0]) * (256 : ZMod p)⁻¹,
         input.c_low_bytes[1],
         (input.cc[1] - input.c_low_bytes[1]) * (256 : ZMod p)⁻¹,
         input.c_low_bytes[2],
         (input.cc[2] - input.c_low_bytes[2]) * (256 : ZMod p)⁻¹,
         input.c_low_bytes[3],
         (input.cc[3] - input.c_low_bytes[3]) * (256 : ZMod p)⁻¹],
       input.result, input.opcode, input.is_real⟩ :
     Var SP1Clean.BitwiseOpGated.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.BitwiseU16Op"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

/-- The chip is responsible for enforcing `opcode.val < 7`. Forwarded
verbatim to the inner `BitwiseOpGated` Assumptions discipline at the
`iff_sp1` bridge. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Direct Spec: exactly what the three sub-assertions hand back —
the binarity equation and the per-byte gated disjunction from
`BitwiseOpGated.Assertion.Spec` (the `U16toU8OpUnsafe` sub-Specs are
`True` and contribute nothing). No bridging to the SP1-native form yet;
that's `iff_sp1` below. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real * (input.is_real - 1) = 0 ∧
  SP1Clean.BitwiseOpGated.Assertion.Spec
    ⟨#v[input.b_low_bytes[0],
        (input.b[0] - input.b_low_bytes[0]) * (256 : ZMod p)⁻¹,
        input.b_low_bytes[1],
        (input.b[1] - input.b_low_bytes[1]) * (256 : ZMod p)⁻¹,
        input.b_low_bytes[2],
        (input.b[2] - input.b_low_bytes[2]) * (256 : ZMod p)⁻¹,
        input.b_low_bytes[3],
        (input.b[3] - input.b_low_bytes[3]) * (256 : ZMod p)⁻¹],
     #v[input.c_low_bytes[0],
        (input.cc[0] - input.c_low_bytes[0]) * (256 : ZMod p)⁻¹,
        input.c_low_bytes[1],
        (input.cc[1] - input.c_low_bytes[1]) * (256 : ZMod p)⁻¹,
        input.c_low_bytes[2],
        (input.cc[2] - input.c_low_bytes[2]) * (256 : ZMod p)⁻¹,
        input.c_low_bytes[3],
        (input.cc[3] - input.c_low_bytes[3]) * (256 : ZMod p)⁻¹],
     input.result, input.opcode, input.is_real⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_b_eq, h_cc_eq, h_blb_eq, h_clb_eq, h_r_eq, h_op_eq, h_ir_eq⟩ := h_input
  subst h_b_eq; subst h_cc_eq; subst h_blb_eq; subst h_clb_eq
  subst h_r_eq; subst h_op_eq; subst h_ir_eq
  obtain ⟨h_bin, _h_u16b, _h_u16c, h_bwg⟩ := h_holds
  have h_bwg' := h_bwg trivial
  unfold id at *
  -- Normalize the goal: `-` (ZMod-level) → `+ -` (matching eval'd Expression
  -- subtraction in hypotheses), and `Vector.getElem_map` to bridge the
  -- `(Vector.map eval _)[i]` ↔ `eval _[i]` normalization at indices.
  simp only [sub_eq_add_neg, Vector.getElem_map]
  exact ⟨h_bin, h_bwg'⟩

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_b_eq, h_cc_eq, h_blb_eq, h_clb_eq, h_r_eq, h_op_eq, h_ir_eq⟩ := h_input
  subst h_b_eq; subst h_cc_eq; subst h_blb_eq; subst h_clb_eq
  subst h_r_eq; subst h_op_eq; subst h_ir_eq
  -- Normalize Spec's `-` to `+ -` and Vector.getElem_map to match goal shape.
  simp only [sub_eq_add_neg, Vector.getElem_map] at h_spec
  obtain ⟨h_bin, h_bwg⟩ := h_spec
  unfold id at *
  refine ⟨h_bin, ⟨trivial, trivial⟩, ⟨trivial, trivial⟩, ⟨trivial, h_bwg⟩⟩

end Assertion

/-- The full Clean `FormalAssertion` for `BitwiseU16Operation`. Composes
two trivial `U16toU8OpUnsafe.assertion` sub-calls and one
`BitwiseOpGated.assertion` sub-call. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-- Bridge: under `is_real = 1` and `opcode.val < 7`, the assertion-style
`Spec` is equivalent to the SP1-native `BitwiseU16Operation.constraints
… 1`'s `allHold`. Chains `BitwiseU16Operation.allHold_constraints_iff`
(upstream) with `BitwiseOpGated.spec_iff_bitwiseOp` (Clean) and the
ungated `BitwiseOp.Spec` definition. -/
theorem iff_sp1 (input : Inputs (ZMod p))
    (h_op : input.opcode.val < 7)
    (h_is_real : input.is_real = 1) :
    Assertion.Spec input ↔
      let cols : BitwiseU16Operation (ZMod p) :=
        { b_low_bytes := { low_bytes := input.b_low_bytes },
          c_low_bytes := { low_bytes := input.c_low_bytes },
          bitwise_operation := { result := input.result } }
      (BitwiseU16Operation.constraints input.b input.cc cols input.opcode 1).2.allHold := by
  haveI : NeZero p := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩
  simp only
  rw [BitwiseU16Operation.allHold_constraints_iff]
  unfold Assertion.Spec
  rw [SP1Clean.BitwiseOpGated.spec_iff_bitwiseOp _ _ _ _ _ h_op]
  unfold SP1Clean.BitwiseOp.Spec
  constructor
  · rintro ⟨_h_bin, h⟩
    -- h : is_real = 0 ∨ ∀ i, (op.ofNat opcode.val).constrain result[i] bytes_b[i] bytes_c[i]
    -- Since is_real = 1, the first disjunct is impossible.
    rcases h with h_z | h_spec
    · rw [h_is_real] at h_z; exact absurd h_z one_ne_zero
    · exact h_spec
  · intro h_spec
    refine ⟨?_, ?_⟩
    · rw [h_is_real]; ring
    · exact Or.inr h_spec

end SP1Clean.BitwiseU16Op
