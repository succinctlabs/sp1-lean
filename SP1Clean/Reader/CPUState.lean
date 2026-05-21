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
import SP1Operations.Reader.CPUState
import SP1Clean.ByteOpcodeTable

/-! # Reusable `CPUState` Spec helper

Factors out the inline `clk_0_16`/`clk_16_24` range clauses that every
chip-level `Spec` would otherwise expand by hand. The `iff_sp1` re-export
turns `CPUState.allHold_constraints_iff_is_real` into a one-line
rewrite at the chip level.
-/

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
  ring

end Assertion

/-- The full Clean `FormalAssertion` for the propositional part of
`_root_.CPUState.constraints`. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.CPUState
