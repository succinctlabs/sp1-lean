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
import SP1Foundations.MemoryConsistency
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Operations.Reader.ITypeReader.ITypeReader
import SP1Operations.Reader.JTypeReader.JTypeReader
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Operations.Operation.U16toU8OperationUnsafe.U16toU8OperationUnsafe
import SP1Operations.Operation.BitwiseOperation.BitwiseOperation
import SP1Operations.Operation.BitwiseU16Operation.BitwiseU16Operation
import SP1Operations.Operation.MulOperation.MulOperation
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Compare.IsZeroOperation.IsZeroOperation
import SP1Operations.Compare.IsZeroWordOperation.IsZeroWordOperation
import SP1Operations.Compare.IsEqualWordOperation.IsEqualWordOperation
import SP1Clean.Compare.LtOperationSigned
import SP1Clean.ByteOpcodeTable
import SP1Clean.StateBusTable

/-! # Reusable `CPUState` Spec helper

Factors out the inline `clk_0_16`/`clk_16_24` range clauses that every
chip-level `Spec` would otherwise expand by hand. The `iff_sp1` re-export
turns `CPUState.allHold_constraints_iff_is_real` into a one-line
rewrite at the chip level.

This file also carries the sidecar `deriving instance ProvableStruct
for CPUState` so chip Cols structs can nest `CPUState T` as a single
field (matching upstream's composition) rather than flattening to four
fields. See `SP1Clean.Compare.LtOperationSigned` for the same pattern
applied to the `LtOperationSigned` chain.
-/

deriving instance ProvableStruct for CPUState
deriving instance ProvableStruct for MemoryAccessInShardTimestamp
deriving instance ProvableStruct for MemoryAccessInSharedCols
deriving instance ProvableStruct for RTypeReader
deriving instance ProvableStruct for ITypeReader
deriving instance ProvableStruct for JTypeReader
deriving instance ProvableStruct for ALUTypeReader
-- ITypeReaderImmutable reuses ITypeReader's struct, so no separate derivation needed.

-- Operation gadget derivations for Phase 3c sub-operation nesting in
-- chip Cols. U16MSBOperation already has a sidecar in
-- `SP1Clean/Compare/LtOperationSigned.lean`.
deriving instance ProvableStruct for U16toU8Operation
deriving instance ProvableStruct for BitwiseOperation
deriving instance ProvableStruct for BitwiseU16Operation
deriving instance ProvableStruct for MulOperation
deriving instance ProvableStruct for AddOperation
deriving instance ProvableStruct for IsZeroOperation
deriving instance ProvableStruct for IsZeroWordOperation
deriving instance ProvableStruct for IsEqualWordOperation

namespace SP1Clean.CPUState

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RHS of `_root_.CPUState.allHold_constraints_iff_is_real`,
packaged as a named predicate. Captures the two range bounds the CPU-state
fragment imposes on the clock fields under `is_real = 1`. The fragment's
other arguments (`pc`, `next_pc`, `clk_increment`) appear in the `send
(.state …)` interactions handled at the state-bridge level, not in this
predicate. -/
def cpuStateSpec (clk_0_16 clk_16_24 : ZMod p) : Prop :=
  ((clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 8192 ∧
  clk_16_24 < (256 : ZMod p)

/-- The bridge to SP1: under `is_real = 1`, the CPUState constraint list's
`allHold` is exactly `cpuStateSpec`. Pure re-export of
`_root_.CPUState.allHold_constraints_iff_is_real`. -/
theorem cpuStateSpec_iff_sp1
    {cols : _root_.CPUState (ZMod p)} {next_pc : Vector (ZMod p) 3}
    {clk_increment : ZMod p} :
    (_root_.CPUState.constraints cols next_pc clk_increment 1).allHold ↔
      cpuStateSpec cols.clk_0_16 cols.clk_16_24 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  exact _root_.CPUState.allHold_constraints_iff_is_real rfl

/-! ## Full `FormalAssertion` promotion

Wraps the propositional layer of `_root_.CPUState.constraints` — the two
byte lookups under `is_real = 1` — into a Clean `FormalAssertion`. The
state `send`/`receive` interactions stay on the SP1 side (they live in
`initialState`, not in `allHold`).
-/

/-- Bundled inputs: just the two clock-field components. -/
structure Inputs (F : Type) where
  clk_0_16 : F
  clk_16_24 : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Clean-side circuit. Mirrors the two byte sends in
`_root_.CPUState.constraints` under `is_real = 1`:
- `(.byte (ofNat 6) ((clk_0_16 - 1)*8⁻¹) 13 0)` → Range bound 13 bits
- `(.byte (ofNat 3) 0 clk_16_24 0)`              → U8Range bound on clk_16_24 -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), (input.clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, input.clk_16_24, 0]
      : Vector (Expression (ZMod p)) 4)

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.CPUState"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

def Spec (input : Inputs (ZMod p)) : Prop :=
  cpuStateSpec input.clk_0_16 input.clk_16_24

/-- Helper: unwrap a `ByteOpcodeSpec` row `#v[6, x, 13, 0]` (Range with
13-bit bound) into `x.val < 8192`. -/
lemma byteOpcodeSpec_range13
    (x : ZMod p)
    (h : SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, 13, 0])) :
    x.val < 8192 := by
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
  have h13 : (13 : ZMod p).val = 13 := by
    rw [show (13 : ZMod p) = ((13 : ℕ) : ZMod p) from by push_cast; rfl,
        ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  rw [h13] at hconstr
  exact hconstr

/-- Helper for completeness (Range 13-bit): given `x.val < 8192`, build a
`ByteOpcodeSpec` witnessed by `bop = Range`. -/
lemma byteOpcodeSpec_range13_of_lt
    (x : ZMod p) (hx : x.val < 8192) :
    SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, 13, 0]) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  refine ⟨.Range, ?_, ?_⟩
  · simp only [ByteOpcode.toNat, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, Nat.cast_ofNat]
  · simp only [ByteOpcode.constrain_Range, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    have h13 : (13 : ZMod p).val = 13 := by
      rw [show (13 : ZMod p) = ((13 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [h13]
    exact hx

/-- Helper: unwrap a `ByteOpcodeSpec` row `#v[3, 0, x, 0]` (U8Range) into
`x < 256`. -/
lemma byteOpcodeSpec_u8range
    (x : ZMod p)
    (h : SP1Clean.ByteOpcodeSpec (#v[(3 : ZMod p), 0, x, 0])) :
    x < (256 : ZMod p) := by
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
  exact hconstr.2.1

/-- Helper for completeness (U8Range): given `x < 256`, build a
`ByteOpcodeSpec` row `#v[3, 0, x, 0]` witnessed by `bop = U8Range`. -/
lemma byteOpcodeSpec_u8range_of_lt
    (x : ZMod p) (hx : x < (256 : ZMod p)) :
    SP1Clean.ByteOpcodeSpec (#v[(3 : ZMod p), 0, x, 0]) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  refine ⟨.U8Range, ?_, ?_⟩
  · simp only [ByteOpcode.toNat, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, Nat.cast_ofNat]
  · simp only [ByteOpcode.constrain_U8Range, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    have h_zero_lt : (0 : ZMod p) < (256 : ZMod p) := by
      change (0 : ZMod p).val < (256 : ZMod p).val
      have h256 : (256 : ZMod p).val = 256 := by
        rw [show (256 : ZMod p) = ((256 : ℕ) : ZMod p) from by push_cast; rfl,
            ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
      simp [h256]
    exact ⟨h_zero_lt, hx, h_zero_lt⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_clk_0_16_eq, h_clk_16_24_eq⟩ := h_input
  subst h_clk_0_16_eq
  subst h_clk_16_24_eq
  simp only [main, circuit_norm, Lookup.Soundness, Table.toRaw,
             SP1Clean.ByteOpcodeTable] at h_holds
  obtain ⟨h_l0, h_l1⟩ := h_holds
  simp only [cpuStateSpec]
  refine ⟨?_, ?_⟩
  · have h := byteOpcodeSpec_range13 _ h_l0
    convert h using 2
    ring
  · exact byteOpcodeSpec_u8range _ h_l1

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_clk_0_16_eq, h_clk_16_24_eq⟩ := h_input
  subst h_clk_0_16_eq
  subst h_clk_16_24_eq
  simp only [cpuStateSpec] at h_spec
  obtain ⟨h_range13, h_u8range⟩ := h_spec
  simp only [main, circuit_norm, Lookup.Completeness, Table.toRaw,
             SP1Clean.ByteOpcodeTable]
  refine ⟨?_, byteOpcodeSpec_u8range_of_lt _ h_u8range⟩
  have h := byteOpcodeSpec_range13_of_lt _ h_range13
  convert h using 3
  ring_nf

end Assertion

/-- The full Clean `FormalAssertion` for the propositional part of
`_root_.CPUState.constraints`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-! ## Flag-threaded variant (`Gated`)

Mirrors Rust's `eval_cpu_state(cols, next_pc, clk_increment, is_real)` (see
`sp1/crates/core/machine/src/adapter/state.rs`). The full 4-field `cols`
struct (clk_high, clk_16_24, clk_0_16, pc[3]) plus the three Rust-side
parameters (`next_pc`, `clk_increment`, `is_real`) live in `Gated.Inputs`,
and `Gated.assertion`'s `main` emits all 5 SP1-native constraints (binary
gate + 2 state-bus + 2 byte lookups, each gated by `is_real`).

The `Spec` is **disjunctive**: `(is_real = 0 ∨ is_real = 1) ∧
(is_real = 0 ∨ <range/U8 facts>)`. On rows where `is_real = 0`, every
gated lookup is vacuous (matches SP1's bus semantics); on real rows, the
right disjunct's facts hold unconditionally. The state-bus emissions
contribute nothing to the row-level `Spec` (their per-row `Spec` is
trivially `True`); per-key balance is enforced at the trace level by
`pcChainProp` over `aggregateStateAccesses`.

This is a **parallel** API to the legacy 2-field `assertion` above — the
22 existing consumers (Branch, Load*, Store*, Div*, Shift*, Sub*, Mul,
Jal*, Lt) continue to use the legacy form pinned at `is_real = 1`. Phase
4 chips (Add, Addi, Addw) opt into the gated form. -/

namespace Gated

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

-- Derive `Fact (p > 512)` from `Fact (2 ^ 17 < p)` for byteOpcodeGated.
instance : Fact (p > 512) := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩

/-- Bundled inputs mirroring Rust `eval_cpu_state(cols, next_pc,
clk_increment, is_real)`. -/
structure Inputs (F : Type) where
  cols : _root_.CPUState F
  next_pc : Vector F 3
  clk_increment : F
  is_real : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Clean-side gated CPUState circuit. Mirrors the 5 SP1-native constraints
in `_root_.CPUState.constraints`:
1. `is_real * (is_real - 1) === 0` — binary gate.
2. `stateBusGated` (receive at current pc) with `mult = is_real`.
3. `stateBusGated` (send at next_pc, clock + clk_increment) with `mult = is_real`.
4. `byteOpcodeGated` Range-13 on `(clk_0_16 - 1) * 8⁻¹` with `mult = is_real`.
5. `byteOpcodeGated` U8Range on `clk_16_24` with `mult = is_real`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨cols, next_pc, clk_increment, is_real⟩ := input
  let clk_combined := cols.clk_0_16 + cols.clk_16_24 * 65536
  is_real * (is_real - 1) === 0
  SP1Lookup.stateBusGated
    ⟨#v[cols.clk_high, clk_combined, cols.pc[0], cols.pc[1], cols.pc[2]], is_real⟩
  SP1Lookup.stateBusGated
    ⟨#v[cols.clk_high, clk_combined + clk_increment, next_pc[0], next_pc[1], next_pc[2]], is_real⟩
  SP1Lookup.byteOpcodeGated
    ⟨#v[(6 : Expression (ZMod p)), (cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0], is_real⟩
  SP1Lookup.byteOpcodeGated
    ⟨#v[(3 : Expression (ZMod p)), 0, cols.clk_16_24, 0], is_real⟩

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.CPUState.Gated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The `Spec` is the literal conjunction of sub-circuit `Spec`s — one
per emission in `main`. Chip consumers destructure this 5-tuple and
access each sub-Spec by direct field. Aligns with CLAUDE.md's "Faithful
sub-circuit composition" principle. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let cols := input.cols
  let clk_combined := cols.clk_0_16 + cols.clk_16_24 * 65536
  input.is_real * (input.is_real - 1) = 0 ∧
  SP1Lookup.StateBusGated.Spec
    ⟨#v[cols.clk_high, clk_combined, cols.pc[0], cols.pc[1], cols.pc[2]],
     input.is_real⟩ ∧
  SP1Lookup.StateBusGated.Spec
    ⟨#v[cols.clk_high, clk_combined + input.clk_increment,
        input.next_pc[0], input.next_pc[1], input.next_pc[2]],
     input.is_real⟩ ∧
  SP1Lookup.ByteOpcodeGated.Spec
    ⟨#v[(6 : ZMod p), (cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0],
     input.is_real⟩ ∧
  SP1Lookup.ByteOpcodeGated.Spec
    ⟨#v[(3 : ZMod p), 0, cols.clk_16_24, 0],
     input.is_real⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨⟨e_ch, e_c16, e_c0, e_pc⟩, e_npc, e_ci, e_ir⟩ := h_input
  subst_eqs
  obtain ⟨h_gate, h_sr_sub, h_ss_sub, h_b13_sub, h_b8r_sub⟩ := h_holds
  -- `Expression.eval` reduces `(a - b)` to `(a + -b)`; normalize Spec target
  -- to match the form the sub-circuit hyps carry.
  simp only [Spec, sub_eq_add_neg]
  exact ⟨h_gate, h_sr_sub trivial, h_ss_sub trivial,
         h_b13_sub trivial, h_b8r_sub trivial⟩

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨⟨e_ch, e_c16, e_c0, e_pc⟩, e_npc, e_ci, e_ir⟩ := h_input
  subst_eqs
  simp only [Spec, sub_eq_add_neg] at h_spec
  obtain ⟨h_gate, h_sr, h_ss, h_b13, h_b8r⟩ := h_spec
  exact ⟨h_gate, ⟨trivial, h_sr⟩, ⟨trivial, h_ss⟩,
         ⟨trivial, h_b13⟩, ⟨trivial, h_b8r⟩⟩

end Assertion

/-- The flag-threaded Clean `FormalAssertion` for CPUState. Mirrors Rust
`eval_cpu_state` shape; emits all 5 SP1-native constraints gated by
`is_real`. `Spec` is the literal conjunction of sub-circuit `Spec`s. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-! ### Semantic view + SP1 bridge

`cpuStateSpec` is the row-level semantic predicate (binary gate + the
disjunctive `is_real = 0 ∨ <range/U8 facts>`). `cpuStateSpec_iff_sp1`
bridges to the SP1-native `allHold` form. Chip consumers can either
destructure `Assertion.Spec` directly (sub-circuit composition) or
apply `cpuStateSpec_of_assertionSpec` to get the semantic form. -/

/-- The flag-threaded semantic RHS — disjunctive form. -/
def cpuStateSpec
    (cols : _root_.CPUState (ZMod p)) (is_real : ZMod p) : Prop :=
  (is_real = 0 ∨ is_real = 1) ∧
  (is_real = 0 ∨
    (((cols.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 8192 ∧
      cols.clk_16_24 < (256 : ZMod p)))

/-- The flag-aware bridge: `(SP1-native constraints).allHold ↔ cpuStateSpec`,
no `is_real = 1` pinning. Converts the SP1-native lemma's implication form
into the disjunctive form classically. -/
theorem cpuStateSpec_iff_sp1
    {cols : _root_.CPUState (ZMod p)} {next_pc : Vector (ZMod p) 3}
    {clk_increment is_real : ZMod p} :
    (_root_.CPUState.constraints cols next_pc clk_increment is_real).allHold ↔
      cpuStateSpec cols is_real := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.CPUState.constraints cols next_pc clk_increment is_real).allHold
        = List.Forall SP1Constraint.toProp
            (_root_.CPUState.constraints cols next_pc clk_increment is_real) from rfl]
  rw [_root_.CPUState.allHold_constraints_iff]
  simp only [cpuStateSpec]
  constructor
  · rintro ⟨h_bin, h_imp⟩
    refine ⟨h_bin, ?_⟩
    by_cases h : is_real = 0
    · exact Or.inl h
    · exact Or.inr (h_imp h)
  · rintro ⟨h_bin, h_disj⟩
    refine ⟨h_bin, fun h_ne => ?_⟩
    exact h_disj.resolve_left h_ne

/-- Bridge from SP1-native `CPUState.constraints.allHold` to the literal
sub-circuit conjunction `Assertion.Spec`. Composes `cpuStateSpec_iff_sp1`
(SP1-native → disjunctive `cpuStateSpec`) with the Clean-side reformulation
of `cpuStateSpec` as the sub-circuit conjunction (binary gate + 2 trivial
state-bus disjuncts + 2 byte-opcode disjuncts). The byte-opcode pieces
reuse `byteOpcodeSpec_range13{,_of_lt}` / `byteOpcodeSpec_u8range{,_of_lt}`
from the legacy `Assertion` namespace. -/
theorem Assertion.Spec_iff_sp1
    {cols : _root_.CPUState (ZMod p)} {next_pc : Vector (ZMod p) 3}
    {clk_increment is_real : ZMod p} :
    (_root_.CPUState.constraints cols next_pc clk_increment is_real).allHold ↔
      Assertion.Spec ⟨cols, next_pc, clk_increment, is_real⟩ := by
  rw [cpuStateSpec_iff_sp1]
  simp only [cpuStateSpec, Assertion.Spec,
    SP1Lookup.StateBusGated.Spec, SP1Lookup.ByteOpcodeGated.Spec]
  refine ⟨?_, ?_⟩
  · rintro ⟨h_bin, h_disj⟩
    refine ⟨?_, Or.inr trivial, Or.inr trivial, ?_, ?_⟩
    · rcases h_bin with h0 | h1
      · subst h0; ring
      · have h_sub : is_real - 1 = 0 := sub_eq_zero.mpr h1
        rw [h_sub]; ring
    · rcases h_disj with h0 | ⟨h_r, _⟩
      · exact Or.inl h0
      · exact Or.inr
          (SP1Clean.CPUState.Assertion.byteOpcodeSpec_range13_of_lt _ h_r)
    · rcases h_disj with h0 | ⟨_, h_u⟩
      · exact Or.inl h0
      · exact Or.inr
          (SP1Clean.CPUState.Assertion.byteOpcodeSpec_u8range_of_lt _ h_u)
  · rintro ⟨h_mul, _, _, h_r_disj, h_u_disj⟩
    refine ⟨?_, ?_⟩
    · rcases mul_eq_zero.mp h_mul with h0 | h_sub
      · exact Or.inl h0
      · exact Or.inr (sub_eq_zero.mp h_sub)
    · rcases h_r_disj with h0 | h_r
      · exact Or.inl h0
      · rcases h_u_disj with h0' | h_u
        · exact Or.inl h0'
        · exact Or.inr
            ⟨SP1Clean.CPUState.Assertion.byteOpcodeSpec_range13 _ h_r,
             SP1Clean.CPUState.Assertion.byteOpcodeSpec_u8range _ h_u⟩

end Gated

end SP1Clean.CPUState
