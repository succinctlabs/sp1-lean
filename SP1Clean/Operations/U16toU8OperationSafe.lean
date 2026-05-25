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
import SP1Operations.Operation.U16toU8OperationSafe.U16toU8OperationSafe
import SP1Clean.ByteOpcodeTable
import SP1Clean.Operations.U16toU8OperationUnsafe

/-! # `U16toU8OperationSafe` Clean mirror (scaffold)

SP1's `U16toU8OperationSafe` enforces the byte-range invariant on the
4-limb u16 → 8-byte decomposition that the Unsafe variant only
algebraically describes. The constraint list under `is_real = 1`:
```
[ .send (.byte U8Range 0 low_bytes[0] (u16_values[0]-low_bytes[0])/256) is_real
, .send (.byte U8Range 0 low_bytes[1] (u16_values[1]-low_bytes[1])/256) is_real
, .send (.byte U8Range 0 low_bytes[2] (u16_values[2]-low_bytes[2])/256) is_real
, .send (.byte U8Range 0 low_bytes[3] (u16_values[3]-low_bytes[3])/256) is_real ]
```
(opcode is `ByteOpcode.ofNat 3` = `U8Range`).

Rust nesting: `U16toU8OperationSafe::eval` composes
`U16toU8OperationUnsafe::eval` (for the algebraic decomposition) then
adds the 4 U8-range byte lookups. The Clean mirror does the same:
`Assertion.main` calls `U16toU8OpUnsafe.assertion` as a subcircuit and
then emits the 4 byte lookups. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.U16toU8OpSafe

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled FormalAssertion input: the 4-limb u16 word + 4 low-byte
witnesses. Matches `U16toU8OpUnsafe.Inputs`. -/
structure Inputs (F : Type) where
  u16_values : fields 4 F
  low_bytes : fields 4 F
deriving ProvableStruct

/-- Clean-side circuit. Composes `U16toU8OpUnsafe.assertion` (the
algebraic decomposition, trivially empty) and emits the 4 U8-range byte
lookups for both low and high bytes of each u16 limb. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- Sub-circuit: algebraic byte decomposition (Unsafe variant — no constraints).
  SP1Clean.U16toU8OpUnsafe.assertion
    (⟨input.u16_values, input.low_bytes⟩ : Var SP1Clean.U16toU8OpUnsafe.Inputs (ZMod p))
  -- 4 U8-range byte lookups (opcode 3 = U8Range).
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.low_bytes[0],
        (input.u16_values[0] - input.low_bytes[0]) * (256 : ZMod p)⁻¹]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.low_bytes[1],
        (input.u16_values[1] - input.low_bytes[1]) * (256 : ZMod p)⁻¹]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.low_bytes[2],
        (input.u16_values[2] - input.low_bytes[2]) * (256 : ZMod p)⁻¹]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.low_bytes[3],
        (input.u16_values[3] - input.low_bytes[3]) * (256 : ZMod p)⁻¹]
      : Vector (Expression (ZMod p)) 4)

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.U16toU8OpSafe"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Spec: each `low_bytes[i].val < 256` AND
`((u16_values[i] - low_bytes[i]) * 256⁻¹).val < 256` (i.e., low and high
bytes of each u16 limb are both u8). -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.low_bytes[0].val < 256 ∧
  ((input.u16_values[0] - input.low_bytes[0]) * (256 : ZMod p)⁻¹).val < 256 ∧
  input.low_bytes[1].val < 256 ∧
  ((input.u16_values[1] - input.low_bytes[1]) * (256 : ZMod p)⁻¹).val < 256 ∧
  input.low_bytes[2].val < 256 ∧
  ((input.u16_values[2] - input.low_bytes[2]) * (256 : ZMod p)⁻¹).val < 256 ∧
  input.low_bytes[3].val < 256 ∧
  ((input.u16_values[3] - input.low_bytes[3]) * (256 : ZMod p)⁻¹).val < 256

/-- Helper: unwrap a `ByteOpcodeSpec` row of the form `#v[3, 0, x, y]`
into the byte-range bounds `x.val < 256 ∧ y.val < 256`. The existential
`bop` is pinned to `U8Range` by `bop.toNat = 3`. -/
lemma byteOpcodeSpec_u8range
    (x y : ZMod p)
    (h : SP1Clean.ByteOpcodeSpec (#v[(3 : ZMod p), 0, x, y])) :
    x.val < 256 ∧ y.val < 256 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  obtain ⟨bop, hbop, hconstr⟩ := h
  have h_eq : bop = .U8Range := by
    have h3 : (3 : ZMod p) = ((3 : ℕ) : ZMod p) := by push_cast; rfl
    simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at hbop
    rw [h3] at hbop
    apply_fun ZMod.val at hbop
    have h_lt : bop.toNat < 7 := by cases bop <;> simp [ByteOpcode.toNat]
    rw [ZMod.val_natCast, ZMod.val_natCast,
        Nat.mod_eq_of_lt (by omega : bop.toNat < p),
        Nat.mod_eq_of_lt (by omega : (3 : ℕ) < p)] at hbop
    cases bop <;> simp [ByteOpcode.toNat] at hbop
    rfl
  subst h_eq
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
             List.getElem_cons_zero, ByteOpcode.constrain_U8Range] at hconstr
  have h256_val : (256 : ZMod p).val = 256 := by
    rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  obtain ⟨_, hx, hy⟩ := hconstr
  refine ⟨?_, ?_⟩
  · have : x.val < (256 : ZMod p).val := hx; rwa [h256_val] at this
  · have : y.val < (256 : ZMod p).val := hy; rwa [h256_val] at this

/-- Helper for completeness: given `x.val < 256 ∧ y.val < 256`, build the
`ByteOpcodeSpec` for `#v[3, 0, x, y]` witnessed by `bop = U8Range`. -/
lemma byteOpcodeSpec_u8range_of_lt
    (x y : ZMod p) (hx : x.val < 256) (hy : y.val < 256) :
    SP1Clean.ByteOpcodeSpec (#v[(3 : ZMod p), 0, x, y]) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  refine ⟨.U8Range, ?_, ?_⟩
  · simp only [ByteOpcode.toNat, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, Nat.cast_ofNat]
  · simp only [ByteOpcode.constrain_U8Range, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    have h0_lt_256 : (0 : ZMod p) < (256 : ZMod p) := by
      change (0 : ZMod p).val < (256 : ZMod p).val
      have h256_val : (256 : ZMod p).val = 256 := by
        rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      simp [h256_val]
    refine ⟨h0_lt_256, ?_, ?_⟩
    · have h256_val : (256 : ZMod p).val = 256 := by
        rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      change x.val < (256 : ZMod p).val; rwa [h256_val]
    · have h256_val : (256 : ZMod p).val = 256 := by
        rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      change y.val < (256 : ZMod p).val; rwa [h256_val]

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_uv_eq, h_lb_eq⟩ := h_input
  subst_eqs
  simp only [main, circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨_h_unsafe, h_l0, h_l1, h_l2, h_l3⟩ := h_holds
  simp only [Spec, Vector.getElem_map, sub_eq_add_neg]
  obtain ⟨hb0, hd0⟩ := byteOpcodeSpec_u8range _ _ h_l0
  obtain ⟨hb1, hd1⟩ := byteOpcodeSpec_u8range _ _ h_l1
  obtain ⟨hb2, hd2⟩ := byteOpcodeSpec_u8range _ _ h_l2
  obtain ⟨hb3, hd3⟩ := byteOpcodeSpec_u8range _ _ h_l3
  exact ⟨hb0, hd0, hb1, hd1, hb2, hd2, hb3, hd3⟩

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_uv_eq, h_lb_eq⟩ := h_input
  subst_eqs
  simp only [Spec, Vector.getElem_map, sub_eq_add_neg] at h_spec
  obtain ⟨hb0, hd0, hb1, hd1, hb2, hd2, hb3, hd3⟩ := h_spec
  simp only [main, circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  refine ⟨⟨trivial, trivial⟩, ?_, ?_, ?_, ?_⟩
  · exact byteOpcodeSpec_u8range_of_lt _ _ hb0 hd0
  · exact byteOpcodeSpec_u8range_of_lt _ _ hb1 hd1
  · exact byteOpcodeSpec_u8range_of_lt _ _ hb2 hd2
  · exact byteOpcodeSpec_u8range_of_lt _ _ hb3 hd3

/-- The full Clean `FormalAssertion` for `U16toU8OperationSafe`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { elaborated with
    Assumptions := Assumptions,
    Spec := Spec,
    soundness := soundness,
    completeness := completeness }

/-- Bridge to SP1: under `is_real = 1`, `Spec input` is equivalent to
SP1's `U16toU8OperationSafe.constraints` `allHold` form. Direct re-export
of `U16toU8OperationSafe.allHold_constraints_iff` (pinned `is_real = 1`),
plus a `.val < ⟷ field <` conversion (`val_256_zmod_p`). -/
theorem iff_sp1 (input : Inputs (ZMod p)) :
    Spec input ↔
      List.Forall SP1Constraint.toProp
        (U16toU8OperationSafe.constraints input.u16_values
          { low_bytes := input.low_bytes } 1).2 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [U16toU8OperationSafe.allHold_constraints_iff]
  simp only [Spec, one_ne_zero, not_false_eq_true, true_imp_iff]
  have h256_val : (256 : ZMod p).val = 256 := by
    rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by have := Fact.out (p := 2 ^ 17 < p); omega)]
  constructor
  · rintro ⟨hb0, hd0, hb1, hd1, hb2, hd2, hb3, hd3⟩
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      (change _ < (256 : ZMod p).val; rwa [h256_val])
  · rintro ⟨⟨hb0, hd0⟩, ⟨hb1, hd1⟩, ⟨hb2, hd2⟩, ⟨hb3, hd3⟩⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      first
        | (have : _ < (256 : ZMod p).val := hb0; rwa [h256_val] at this)
        | (have : _ < (256 : ZMod p).val := hd0; rwa [h256_val] at this)
        | (have : _ < (256 : ZMod p).val := hb1; rwa [h256_val] at this)
        | (have : _ < (256 : ZMod p).val := hd1; rwa [h256_val] at this)
        | (have : _ < (256 : ZMod p).val := hb2; rwa [h256_val] at this)
        | (have : _ < (256 : ZMod p).val := hd2; rwa [h256_val] at this)
        | (have : _ < (256 : ZMod p).val := hb3; rwa [h256_val] at this)
        | (have : _ < (256 : ZMod p).val := hd3; rwa [h256_val] at this)

end SP1Clean.U16toU8OpSafe
