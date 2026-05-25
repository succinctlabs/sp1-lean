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
import SP1Operations.Operation.BitwiseOperation.Operation
import SP1Operations.Operation.BitwiseOperation.Constraints
import SP1Clean.ByteOpcodeTable

/-! # Tier 2c pilot: `BitwiseOperation` mirror

SP1's `BitwiseOperation` mirrors a per-byte bitwise op (AND/OR/XOR) for an
8-limb word. Its constraint list is **8 `send (.byte (ByteOpcode.ofNat
opcode) result[i] a[i] b[i]) is_real`** — and nothing else. This makes it the
single best Tier-2 test for the opcode-parametric, multi-payload byte
interaction encoding from `SP1Clean/ByteOpcodeTable.lean`.

The pilot deliverable is the **equivalence iff** between SP1's `allHold`
and the Clean spec — `FormalCircuit` integration is deferred per the
import-collision note in `IsZeroOperation.lean`.
-/

namespace SP1Clean.BitwiseOp

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/-- Clean-side circuit. Witnesses the 8-byte `result`, then performs 8
byte-opcode lookups, one per limb. The opcode flows through as a single
parameter; whichever `ByteOpcode` it resolves to (AND/OR/XOR for a typical
chip use) is checked by the `ByteOpcodeSpec` existential. -/
def main (a b : Vector (Expression (ZMod p)) 8) (opcode : Expression (ZMod p)) :
    Circuit (ZMod p) (Vector (Expression (ZMod p)) 8) := do
  let r0 ← witnessField (fun _ => 0)
  let r1 ← witnessField (fun _ => 0)
  let r2 ← witnessField (fun _ => 0)
  let r3 ← witnessField (fun _ => 0)
  let r4 ← witnessField (fun _ => 0)
  let r5 ← witnessField (fun _ => 0)
  let r6 ← witnessField (fun _ => 0)
  let r7 ← witnessField (fun _ => 0)
  -- 8 byte-opcode lookups. Row layout #v[opcode, result_i, a_i, b_i].
  lookup ByteOpcodeTable (#v[opcode, r0, a[0], b[0]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r1, a[1], b[1]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r2, a[2], b[2]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r3, a[3], b[3]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r4, a[4], b[4]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r5, a[5], b[5]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r6, a[6], b[6]] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable (#v[opcode, r7, a[7], b[7]] : Vector (Expression (ZMod p)) 4)
  return #v[r0, r1, r2, r3, r4, r5, r6, r7]

/-- Pilot Spec: under SP1's `is_real = 1`, each of the 8 byte-sends asserts
that `(ByteOpcode.ofNat opcode.val).constrain` holds on the per-byte
triple `(result[i], a[i], b[i])`.

This phrasing matches SP1's `toProp` exactly, which makes the iff a
case-split on `i`. The connection to `ByteOpcodeTable.ByteOpcodeSpec` (via
the existential over `ByteOpcode`) goes through `ByteOpcode.ofNat opcode.val`
as the witness — provable only when `opcode.val < 7`, a hypothesis that is
the **chip's** responsibility to supply (typically via an extra constraint
like `opcode * (opcode - 1) * (opcode - 2) = 0`). -/
def Spec (a b : Vector (ZMod p) 8) (opcode : ZMod p) (result : Vector (ZMod p) 8) : Prop :=
  ∀ i : Fin 8, (ByteOpcode.ofNat opcode.val).constrain
    (result[i.val]'i.is_lt) (a[i.val]'i.is_lt) (b[i.val]'i.is_lt)

omit [Fact (p > 512)] in
/-- The bridge to SP1: SP1's `allHold` under `is_real = 1` is exactly
the pilot `Spec`. Pure case-split on the `Fin 8` index — no opcode
round-trip needed. -/
theorem iff_sp1
    (a b : Vector (ZMod p) 8) (opcode : ZMod p)
    (cols : BitwiseOperation (ZMod p)) :
    (BitwiseOperation.constraints (F := ZMod p) a b cols opcode 1).allHold ↔
    Spec a b opcode cols.result := by
  have h1ne : ((1 : ZMod p) ≠ 0) := one_ne_zero
  simp only [BitwiseOperation.constraints, SP1ConstraintList.allHold, List.Forall,
    SP1Constraint.toProp, Spec]
  constructor
  · rintro ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ i
    match i with
    | ⟨0, _⟩ => exact h0 h1ne
    | ⟨1, _⟩ => exact h1 h1ne
    | ⟨2, _⟩ => exact h2 h1ne
    | ⟨3, _⟩ => exact h3 h1ne
    | ⟨4, _⟩ => exact h4 h1ne
    | ⟨5, _⟩ => exact h5 h1ne
    | ⟨6, _⟩ => exact h6 h1ne
    | ⟨7, _⟩ => exact h7 h1ne
  · intro hSpec
    refine ⟨fun _ => hSpec ⟨0, by omega⟩, fun _ => hSpec ⟨1, by omega⟩,
            fun _ => hSpec ⟨2, by omega⟩, fun _ => hSpec ⟨3, by omega⟩,
            fun _ => hSpec ⟨4, by omega⟩, fun _ => hSpec ⟨5, by omega⟩,
            fun _ => hSpec ⟨6, by omega⟩, fun _ => hSpec ⟨7, by omega⟩⟩

omit [Fact (p > 512)] in
/-- Connection to `ByteOpcodeTable.ByteOpcodeSpec`. When `opcode.val < 7`
(a discipline the chip enforces — see e.g. `SP1Chips/BitwiseChip.lean`'s
`is_and ∨ is_or ∨ is_xor` decomposition), the existential over `ByteOpcode`
inside the table's `Spec` is witnessed by `ByteOpcode.ofNat opcode.val`. -/
lemma ByteOpcodeSpec_of_Spec_when_lt7
    (a b : Vector (ZMod p) 8) (opcode : ZMod p) (result : Vector (ZMod p) 8)
    (h_opcode : opcode.val < 7) (hSpec : Spec a b opcode result) :
    ∀ i : Fin 8,
      SP1Clean.ByteOpcodeSpec (#v[opcode, result[i.val]'i.is_lt,
        a[i.val]'i.is_lt, b[i.val]'i.is_lt] : Vector (ZMod p) 4) := by
  intro i
  refine ⟨ByteOpcode.ofNat opcode.val, ?_, hSpec i⟩
  -- `((ByteOpcode.ofNat opcode.val).toNat : ZMod p) = opcode.val = opcode`
  -- when `opcode.val < 7`: case-split on `opcode.val ∈ {0,…,6}`.
  have hround : ((opcode.val : ℕ) : ZMod p) = opcode := by
    exact_mod_cast ZMod.natCast_zmod_val opcode
  interval_cases opcode.val <;> push_cast at hround <;> simp [hround]

/-- The reverse of `ByteOpcodeSpec_of_Spec_when_lt7`. Given a per-byte
`ByteOpcodeSpec` and `opcode.val < 7`, the existential `bop` is pinned to
`ByteOpcode.ofNat opcode.val` and the `Spec` falls out. -/
lemma Spec_of_ByteOpcodeSpec_when_lt7
    (a b : Vector (ZMod p) 8) (opcode : ZMod p) (result : Vector (ZMod p) 8)
    (_h_opcode : opcode.val < 7)
    (h_each : ∀ i : Fin 8,
      SP1Clean.ByteOpcodeSpec (#v[opcode, result[i.val]'i.is_lt,
        a[i.val]'i.is_lt, b[i.val]'i.is_lt] : Vector (ZMod p) 4)) :
    Spec a b opcode result := by
  haveI : NeZero p := ⟨by have := Fact.out (p := p > 512); omega⟩
  have hp : 512 < p := Fact.out
  intro i
  obtain ⟨bop, hbop, hconstr⟩ := h_each i
  simp only [Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_succ, List.getElem_cons_zero] at hbop hconstr
  have hbop_lt : bop.toNat < 7 := by cases bop <;> simp [ByteOpcode.toNat]
  -- From `(bop.toNat : ZMod p) = opcode`, derive `bop.toNat = opcode.val`.
  have hbop_val : bop.toNat = opcode.val := by
    apply_fun ZMod.val at hbop
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (by omega : bop.toNat < p)] at hbop
    exact hbop
  -- ByteOpcode.ofNat round-trip closes the case.
  have hbop_eq : bop = ByteOpcode.ofNat opcode.val := by
    rw [← hbop_val]
    cases bop <;> simp [ByteOpcode.toNat]
  rw [hbop_eq] at hconstr
  exact hconstr

/-! ## Full `FormalAssertion` promotion

Wraps an assertion-style `main` (taking `result` as a parameter, not
witnessing it) into a Clean `FormalAssertion`. The chip must supply
`opcode.val < 7` as an `Assumptions` discharger — this gates the
`ByteOpcode.ofNat opcode.val` round-trip in both directions. -/

/-- Bundled FormalAssertion input: the two 8-byte operands, the externally
supplied 8-byte result, and the opcode field. -/
structure Inputs (F : Type) where
  a : fields 8 F
  b : fields 8 F
  result : fields 8 F
  opcode : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Assertion-style `main`. Takes the 8-byte `result` as a parameter
rather than witnessing each limb internally. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  lookup ByteOpcodeTable
    (#v[input.opcode, input.result[0], input.a[0], input.b[0]]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[input.opcode, input.result[1], input.a[1], input.b[1]]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[input.opcode, input.result[2], input.a[2], input.b[2]]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[input.opcode, input.result[3], input.a[3], input.b[3]]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[input.opcode, input.result[4], input.a[4], input.b[4]]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[input.opcode, input.result[5], input.a[5], input.b[5]]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[input.opcode, input.result[6], input.a[6], input.b[6]]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[input.opcode, input.result[7], input.a[7], input.b[7]]
      : Vector (Expression (ZMod p)) 4)

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.BitwiseOp"
  main := main
  localLength _ := 0

/-- The chip is responsible for enforcing `opcode.val < 7` (typically via
its `is_and + is_or + is_xor = 1` one-hot decomposition). -/
def Assumptions (input : Inputs (ZMod p)) : Prop := input.opcode.val < 7

/-- The FormalAssertion's spec, identical to the top-level
`SP1Clean.BitwiseOp.Spec`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  SP1Clean.BitwiseOp.Spec input.a input.b input.opcode input.result

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq, h_op_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  subst h_op_eq
  simp only [circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7⟩ := h_holds
  refine Spec_of_ByteOpcodeSpec_when_lt7 _ _ _ _ h_assumptions ?_
  intro i
  simp only [Vector.getElem_map]
  match i with
  | ⟨0, _⟩ => exact h0
  | ⟨1, _⟩ => exact h1
  | ⟨2, _⟩ => exact h2
  | ⟨3, _⟩ => exact h3
  | ⟨4, _⟩ => exact h4
  | ⟨5, _⟩ => exact h5
  | ⟨6, _⟩ => exact h6
  | ⟨7, _⟩ => exact h7

omit [Fact (p > 512)] in
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_a_eq, h_b_eq, h_r_eq, h_op_eq⟩ := h_input
  subst h_a_eq
  subst h_b_eq
  subst h_r_eq
  subst h_op_eq
  simp only [circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  have h_specs := ByteOpcodeSpec_of_Spec_when_lt7 _ _ _ _ h_assumptions h_spec
  simp only [Vector.getElem_map] at h_specs
  exact ⟨h_specs ⟨0, by omega⟩, h_specs ⟨1, by omega⟩,
         h_specs ⟨2, by omega⟩, h_specs ⟨3, by omega⟩,
         h_specs ⟨4, by omega⟩, h_specs ⟨5, by omega⟩,
         h_specs ⟨6, by omega⟩, h_specs ⟨7, by omega⟩⟩

end Assertion

/-- The full Clean `FormalAssertion` for `BitwiseOperation`: soundness +
completeness against the opcode-parametric per-byte `Spec`, gated by
`opcode.val < 7` in `Assumptions`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.BitwiseOp
