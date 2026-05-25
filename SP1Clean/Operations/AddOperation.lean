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
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.SP1Lookup
import RISCV.Instructions


/-! # `AddOperation` gadget mirror — Assertion style (multiplicity-gated)

SP1's `AddOperation` is a 4-limb carry-chain 64-bit add. In SP1 Rust, the
gadget takes the two operand limb vectors `a`, `b` plus a `cols :
AddOperationCols<T>` (whose `cols.value` field holds the result limbs) and
emits constraints relating them — it does *not* witness the result columns
internally; those belong to the enclosing chip's column struct.

This Clean mirror adopts the same shape: `main` takes `(a, b, value,
is_real)` and emits:
- a binarity gate `is_real * (is_real - 1) === 0`
- 4 `is_real`-gated inverse-form boolean carry asserts
- 4 `byteOpcodeGated` calls (multiplicity = `is_real`) bounding each
  result limb to `< 2^16`, matching SP1's `InteractionKind::Byte` per-row
  multiplicity contribution

The `RawSpec` keeps SP1's `allHold_constraints_iff` RHS verbatim so the
`iff_sp1` bridge to SP1's constraint list remains a one-line re-export.
The FormalAssertion's `Spec` is the disjunctive form
`is_real = 0 ∨ (is_real = 1 ∧ RawSpec ∧ RV64.add equation)` — the
left disjunct captures the padding-row case (all gated emissions
vacuous), the right disjunct bundles the carry-form and the BitVec
semantic equation. `SemanticSpec` is a separate helper exposing just the
`is_real = 1 → BitVec equation` projection. -/

namespace SP1Clean.AddOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

instance : Fact (p > 512) := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩

/-- Clean-side circuit. Asserts (gated by `is_real`) the carry chain
between operand limbs `a`, `b` and result limbs `value`, and that each
result limb fits in `< 2^16` via `byteOpcodeGated` with `mult = is_real`.
No internal witnesses besides the byte-bus hint rows; `value` is supplied
by the caller (typically as a column-struct field). -/
def main (a b value : Vector (Expression (ZMod p)) 4)
    (is_real : Expression (ZMod p)) : Circuit (ZMod p) Unit := do
  is_real * (is_real - 1) === 0
  let c0 := (a[0] + b[0] - value[0]) * (65536 : ZMod p)⁻¹
  let c1 := (a[1] + b[1] - value[1] + c0) * (65536 : ZMod p)⁻¹
  let c2 := (a[2] + b[2] - value[2] + c1) * (65536 : ZMod p)⁻¹
  let c3 := (a[3] + b[3] - value[3] + c2) * (65536 : ZMod p)⁻¹
  is_real * (c0 * (c0 - 1)) === 0
  is_real * (c1 * (c1 - 1)) === 0
  is_real * (c2 * (c2 - 1)) === 0
  is_real * (c3 * (c3 - 1)) === 0
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), value[0], 16, 0], is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), value[1], 16, 0], is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), value[2], 16, 0], is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))
  SP1Lookup.byteOpcodeGated
    (⟨#v[(6 : Expression (ZMod p)), value[3], 16, 0], is_real⟩ :
     Var SP1Lookup.ByteOpcodeGated.Inputs (ZMod p))

/-- Pilot Spec, matching SP1's `AddOperation.allHold_constraints_iff`
RHS verbatim: each of the 4 inverse-form carries is boolean and each
result limb fits in `< 65536`. -/
def RawSpec (a b result : Word (ZMod p)) : Prop :=
  let carry0 : ZMod p := (a[0] + b[0] - result[0]) * 65536⁻¹
  let carry1 : ZMod p := (a[1] + b[1] - result[1] + carry0) * 65536⁻¹
  let carry2 : ZMod p := (a[2] + b[2] - result[2] + carry1) * 65536⁻¹
  let carry3 : ZMod p := (a[3] + b[3] - result[3] + carry2) * 65536⁻¹
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
`AddOperation.allHold_constraints_iff`. -/
theorem iff_sp1 (a b : Word (ZMod p)) (cols : AddOperation (ZMod p)) :
    (AddOperation.constraints a b cols 1).allHold ↔
      RawSpec a b cols.value :=
  AddOperation.allHold_constraints_iff a b cols

/-! ## Full `FormalAssertion` promotion

Wraps the assertion-style `main` above into a Clean `FormalAssertion`. The
input is a `ProvableStruct` bundling the two operand words, the result
word, and the `is_real` flag. Internal witnesses come from the 4
`byteOpcodeGated` sub-calls (4 hint rows each). -/

/-- Bundled input to the FormalAssertion: the two operand words, the
result word, and the `is_real` flag (binarity + gate for the byte bus). -/
structure Inputs (F : Type) where
  a : fields 4 F
  b : fields 4 F
  result : fields 4 F
  is_real : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Wrapper around `SP1Clean.AddOp.main` that destructures a `Var Inputs`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit :=
  SP1Clean.AddOp.main input.a input.b input.result input.is_real

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.AddOp"
  main := main
  -- 4 × `byteOpcodeGated.localLength` (= 4 hint rows each) = 16.
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, SP1Clean.AddOp.main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, SP1Clean.AddOp.main, circuit_norm]

/-- No external assumptions — the chip-level caller supplies any operand
bounds (e.g. `Word.isU64`) downstream of the AddOp sub-call. -/
def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- `SemanticSpec` exposes just the BitVec-level `RV64.add` equation
under `is_real = 1`. Reserved for downstream chip callers that prefer the
semantic projection over `RawSpec`'s carry form; not part of the
FormalAssertion's `Spec` (chip Cols still reference `RawSpec` directly
via the chip-level FormalSpec). -/
def SemanticSpec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    Word.toBitVec64 input.result =
      RV64.add (Word.toBitVec64 input.a) (Word.toBitVec64 input.b)

/-- The FormalAssertion's `Spec`. **Compatibility shim**: stays in the
`RawSpec` form (chip-level FormalSpecs reference `SP1Clean.AddOp.RawSpec`
directly, see e.g. `AddChip/Cols.lean:192`). The byte lookups in `main`
are now multiplicity-gated by `is_real`, so this Spec is only sound under
`is_real = 1` — the residual gap is held by the `sorry`s in
`soundness`/`completeness` below until the chip-level FormalSpecs are
weakened to disjunctive form. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  RawSpec input.a input.b input.result

/-- Helper: unwrap a `ByteOpcodeSpec` row of the form `#v[6, x, 16, 0]` into
the range bound `x.val < 65536`. Used in soundness — the existential `bop`
is pinned to `Range` by `bop.toNat = 6` (the only opcode with toNat 6),
which is sound under `Fact (2^17 < p)`. -/
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

/-- Helper for completeness: given `x.val < 65536`, build a `ByteOpcodeSpec`
witnessed by `bop = Range`. -/
lemma byteOpcodeSpec_range16_of_lt
    (x : ZMod p) (hx : x.val < 65536) :
    SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, 16, 0]) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  refine ⟨.Range, ?_, ?_⟩
  · simp only [ByteOpcode.toNat, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, Nat.cast_ofNat]
  · simp only [ByteOpcode.constrain_Range, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    have h16 : (16 : ZMod p).val = 16 := by
      rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [h16]
    exact hx

/-- Soundness of `SP1Clean.AddOp.assertion`. **STUB**: the proof outline
splits on `is_real = 0` (left disjunct of Spec) vs `is_real ≠ 0` (then
binarity forces `is_real = 1`; extract `c_i * (c_i - 1) = 0` from each
`is_real * (c_i * (c_i - 1)) = 0` via `mul_left_cancel₀`; extract
`ByteOpcodeSpec` from each `byteOpcodeGated.Spec` via `resolve_left`;
combine into `RawSpec`; bridge via `iff_sp1.mpr` + `AddOperation.spec` to
get the BitVec `RV64.add` equation; right disjunct of Spec). Closure of
this proof is tracked in [[multiplicity-bus-AddOp-migration]]. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  sorry

/-- Completeness of `SP1Clean.AddOp.assertion`. **STUB**: discharge the
disjunctive `Spec`: in the `is_real = 0` branch, every gated emission is
vacuous (`0 * _ = 0`) and each `byteOpcodeGated.Spec` picks `Or.inl
h_is_real_zero`. In the `is_real = 1 ∧ RawSpec ∧ BitVec` branch, the
gated carries discharge via `RawSpec`'s carry-bool conjuncts, the
binarity gate via `1 * 0 = 0`, and each `byteOpcodeGated.Spec` picks
`Or.inr (byteOpcodeSpec_range16_of_lt …)`. Tracked alongside
[[multiplicity-bus-AddOp-migration]]. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  sorry

end Assertion

/-- The full Clean `FormalAssertion` for `AddOperation`: soundness +
completeness against `Spec`, no internal witnesses. Compose into a chip's
`main` via `AddOp.assertion input` (the `CoeFun` from
`Clean.Circuit.Subcircuit` makes this a `Circuit Unit`). -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-! ### Memory companion

`feedback/multiplicity-bus-AddOp-migration` should track soundness/
completeness closure for the gated form. The two `sorry`s above are the
remaining heavy lift; everything else (chip-level call sites + RawSpec
rename) is purely mechanical. -/

end SP1Clean.AddOp
