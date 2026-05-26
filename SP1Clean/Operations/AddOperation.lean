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

## Contract design — semantic-only `FormalAssertion.Spec`

`RawSpec` keeps SP1's `allHold_constraints_iff` RHS verbatim (carry-bool
+ range form) so the `iff_sp1` bridge to SP1's constraint list remains a
one-line re-export. It is a standalone top-level helper, available for
ad-hoc use but *not* exposed inside the FormalAssertion. `SemanticSpec`
likewise exposes the pure BitVec equation.

The FormalAssertion's `Spec` carries only the semantic content (BitVec
`RV64.add` identity + `isU64` on the result), gated by `is_real = 1`:

```
Assumptions input := (is_real ∈ {0,1}) ∧ (is_real = 1 → isU64 a ∧ isU64 b)
Spec        input := is_real = 1 → (isU64 result ∧ BV equation)
```

Both vacuous on padding rows. This mirrors `SP1Clean.AddChip`'s
"contract as semantic" pattern (commit `b82c79e`) one level down: the
carry chain is an implementation detail of the byte-level encoding, not
part of the operation's contract. Chips that need the carry form can
still recover it via `AddOperation.iff_sp1_full` on demand. -/

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

/-- Assumptions: the binarity of `is_real` is asserted by the chip via
the in-circuit `is_real * (is_real - 1) = 0` gate, but completeness can't
extract that from `Spec` alone, so chip callers must witness binarity
externally. The conditional operand bounds carry the U64 facts on the
two operands when `is_real = 1`; chips supply these from their reader
sub-circuit's `RegisterAccess.Spec`. -/
def Assumptions (input : Inputs (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 → (Word.isU64 input.a ∧ Word.isU64 input.b))

/-- The FormalAssertion's semantic contract. Mirrors the AddChip-level
contract (commit `b82c79e`) one level down: vacuous on padding rows;
on real rows asserts `isU64 result` and the BitVec sum identity. The
carry-chain decomposition is an implementation detail of `main` and can
be recovered on demand via `AddOperation.iff_sp1_full`. Chip-level
`FormalSpec`s rephrase this in `RV64.add op_c op_b` form to match
upstream's RISC-V calling convention. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.is_real = 1 →
    Word.isU64 input.result ∧
    Word.toBitVec64 input.result =
      Word.toBitVec64 input.a + Word.toBitVec64 input.b

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

/-- Generic variant of `byteOpcodeSpec_range16` parametric in the bound `b`:
unwrap a `ByteOpcodeSpec` row of the form `#v[6, x, b, c]` into
`x.val < 2 ^ b.val`. The `c` slot is ignored by the `Range` opcode. -/
lemma byteOpcodeSpec_range
    (x b c : ZMod p)
    (h : SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, b, c])) :
    x.val < 2 ^ b.val := by
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
  exact hconstr

omit [Fact (2 ^ 17 < p)] in
/-- Generic completeness helper: given `x.val < 2 ^ b.val`, build a
`ByteOpcodeSpec` witnessed by `bop = Range`. -/
lemma byteOpcodeSpec_range_of_lt
    (x b c : ZMod p) (hx : x.val < 2 ^ b.val) :
    SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, b, c]) := by
  refine ⟨.Range, ?_, ?_⟩
  · simp only [ByteOpcode.toNat, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, Nat.cast_ofNat]
  · simp only [ByteOpcode.constrain_Range, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    exact hx

/-- Soundness of `SP1Clean.AddOp.assertion`. Under `is_real = 1`, the
circuit's gated emissions reduce (via `mul_eq_zero` + `resolve_left`) to
the carry-bool form plus result-limb ranges from each
`byteOpcodeGated.Spec`. Assembled into `RawSpec`, bridged to SP1's
`allHold` via `iff_sp1`, and finally lifted to `(isU64 result ∧ BV eq)`
by `AddOperation.spec`. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [SP1Clean.AddOp.main]
  obtain ⟨h_a, h_b, h_r, h_ir⟩ := h_input
  subst h_a; subst h_b; subst h_r; subst h_ir
  obtain ⟨h_ir_bin, h_gc0, h_gc1, h_gc2, h_gc3,
          h_l0_sub, h_l1_sub, h_l2_sub, h_l3_sub⟩ := h_holds
  obtain ⟨_h_ir_binary, h_bounds⟩ := h_assumptions
  intro h_is_real
  unfold id at *
  obtain ⟨h_isU64_a, h_isU64_b⟩ := h_bounds h_is_real
  have h_ir_ne_zero : Expression.eval env input_var_is_real ≠ 0 := by
    rw [h_is_real]; exact one_ne_zero
  have h_c0 := (mul_eq_zero.mp h_gc0).resolve_left h_ir_ne_zero
  have h_c1 := (mul_eq_zero.mp h_gc1).resolve_left h_ir_ne_zero
  have h_c2 := (mul_eq_zero.mp h_gc2).resolve_left h_ir_ne_zero
  have h_c3 := (mul_eq_zero.mp h_gc3).resolve_left h_ir_ne_zero
  have hr0 := byteOpcodeSpec_range16 _ ((h_l0_sub trivial).resolve_left h_ir_ne_zero)
  have hr1 := byteOpcodeSpec_range16 _ ((h_l1_sub trivial).resolve_left h_ir_ne_zero)
  have hr2 := byteOpcodeSpec_range16 _ ((h_l2_sub trivial).resolve_left h_ir_ne_zero)
  have hr3 := byteOpcodeSpec_range16 _ ((h_l3_sub trivial).resolve_left h_ir_ne_zero)
  have h_raw : SP1Clean.AddOp.RawSpec
      (Vector.map (Expression.eval env) input_var_a)
      (Vector.map (Expression.eval env) input_var_b)
      (Vector.map (Expression.eval env) input_var_result) := by
    simp only [SP1Clean.AddOp.RawSpec, Vector.getElem_map]
    refine ⟨?_, ?_, ?_, ?_, hr0, hr1, hr2, hr3⟩
    · rcases mul_eq_zero.mp h_c0 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    · rcases mul_eq_zero.mp h_c1 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    · rcases mul_eq_zero.mp h_c2 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
    · rcases mul_eq_zero.mp h_c3 with h | h
      · exact Or.inl (by linear_combination h)
      · exact Or.inr (by linear_combination h)
  have h_allHold : (AddOperation.constraints
        (Vector.map (Expression.eval env) input_var_a)
        (Vector.map (Expression.eval env) input_var_b)
        ⟨Vector.map (Expression.eval env) input_var_result⟩
        1).allHold :=
    (iff_sp1 _ _ _).mpr h_raw
  have ⟨h_isU64_v, h_bv⟩ := AddOperation.spec h_isU64_a h_isU64_b h_allHold
  refine ⟨h_isU64_v, ?_⟩
  exact h_bv

/-- Completeness of `SP1Clean.AddOp.assertion`. Case-splits on `is_real
∈ {0, 1}` (from `Assumptions`): on padding rows every gated emission is
vacuous (`0 * _ = 0`); on real rows the chip-supplied semantic `Spec`
plus operand bounds recover `RawSpec` via `AddOperation.iff_sp1_full`,
and each gate discharges from RawSpec's carry-bool / range conjuncts. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start [SP1Clean.AddOp.main]
  obtain ⟨h_a, h_b, h_r, h_ir⟩ := h_input
  subst h_a; subst h_b; subst h_r; subst h_ir
  obtain ⟨h_ir_binary, h_bounds⟩ := h_assumptions
  unfold id at *
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
  · -- Real row: is_real = 1. Recover RawSpec via iff_sp1_full from the
    -- chip's semantic Spec + the operand bounds.
    obtain ⟨h_isU64_a, h_isU64_b⟩ := h_bounds h_ir1
    obtain ⟨h_isU64_v, h_bv⟩ := h_spec h_ir1
    have h_bv' : Word.toBitVec64
        (Vector.map (Expression.eval env.toEnvironment) input_var_result) =
        execute_RTYPE_pure_w
          (Vector.map (Expression.eval env.toEnvironment) input_var_a)
          (Vector.map (Expression.eval env.toEnvironment) input_var_b) .ADD := h_bv
    have h_allHold := (AddOperation.iff_sp1_full h_isU64_a h_isU64_b
      (cols := ⟨Vector.map (Expression.eval env.toEnvironment) input_var_result⟩)).mpr
        ⟨h_isU64_v, h_bv'⟩
    have h_raw := (iff_sp1 _ _ _).mp h_allHold
    obtain ⟨hc0, hc1, hc2, hc3, hr0, hr1, hr2, hr3⟩ := h_raw
    simp only [sub_eq_add_neg, Vector.getElem_map] at hc0 hc1 hc2 hc3 hr0 hr1 hr2 hr3
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h_ir1]; ring
    · rw [h_ir1]; rcases hc0 with h | h <;> rw [h] <;> ring
    · rw [h_ir1]; rcases hc1 with h | h <;> rw [h] <;> ring
    · rw [h_ir1]; rcases hc2 with h | h <;> rw [h] <;> ring
    · rw [h_ir1]; rcases hc3 with h | h <;> rw [h] <;> ring
    · exact ⟨trivial, Or.inr (byteOpcodeSpec_range16_of_lt _ hr0)⟩
    · exact ⟨trivial, Or.inr (byteOpcodeSpec_range16_of_lt _ hr1)⟩
    · exact ⟨trivial, Or.inr (byteOpcodeSpec_range16_of_lt _ hr2)⟩
    · exact ⟨trivial, Or.inr (byteOpcodeSpec_range16_of_lt _ hr3)⟩

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

end SP1Clean.AddOp
