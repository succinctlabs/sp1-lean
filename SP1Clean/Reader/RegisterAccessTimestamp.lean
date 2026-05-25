import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Field
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.ByteOpcode
import SP1Foundations.Field
import SP1Clean.ByteOpcodeTable
import SP1Clean.Reader.CPUState
import SP1Clean.SP1Lookup

/-! # `RegisterAccessTimestamp.assertion` — Rust `eval_register_access_timestamp`

Mirrors SP1's `eval_register_access_timestamp` from
`crates/core/machine/src/air/memory.rs:332`. Emits exactly the two byte
lookups that the Rust helper sends:

- `diff_low_limb` in `Range 16` (opcode 6).
- The scaled timestamp `(clk_low + offset - prev_low - 1 - diff_low_limb) *
  65536⁻¹` in `U8Range` (opcode 3).

Both lookups are emitted via `SP1Lookup.byteOpcodeGated`, so a `mult` field
controls whether they fire — `mult = 1` for unconditional emission (matching
the `is_real` flag passed by R/I-type readers) or `mult = 1 - imm_c` (ALU-Type
op_c, vacuous on ADDIW rows).

The 4 prev_value `Word.isU64` range checks that the Rust `assert_word`
contributes alongside `eval_register_access_timestamp` are split into the
companion `WordRange.assertion`; the two together rebuild the original
`OperandAccess` byte-bus surface. -/

namespace SP1Clean.RegisterAccessTimestamp

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

namespace Assertion

open Circuit

instance : Fact (p > 512) := ⟨by have : 2 ^ 17 < p := Fact.out; omega⟩

/-- Inputs for the gated register-access-timestamp assertion. `clk_low +
offset` is the row's access timestamp; `prev_low` and `diff_low_limb` are
the timestamp-difference witnesses from the operand's
`RegisterAccessTimestamp` substruct. -/
structure Inputs (F : Type) where
  clk_low : F
  offset : F
  prev_low : F
  diff_low_limb : F
  mult : F
deriving ProvableStruct

/-- Emit the 2 gated byte lookups that constitute
`eval_register_access_timestamp`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  SP1Lookup.byteOpcodeGated
    ⟨#v[(6 : Expression (ZMod p)), input.diff_low_limb, 16, 0], input.mult⟩
  SP1Lookup.byteOpcodeGated
    ⟨#v[(3 : Expression (ZMod p)), 0,
        (input.clk_low + input.offset - input.prev_low - 1 -
          input.diff_low_limb) * (65536 : ZMod p)⁻¹, 0], input.mult⟩

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.RegisterAccessTimestamp"
  main := main
  -- 2 byteOpcodeGated subcircuit calls × 4 witnesses each = 8.
  localLength _ := 8
  localLength_eq _ _ := by simp only [main, circuit_norm]
  subcircuitsConsistent _ _ := by simp +arith only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- Gated spec: vacuous when `mult = 0`; otherwise constrains
`diff_low_limb < 65536` and `(clk_low + offset - prev_low - 1 -
diff_low_limb) * 65536⁻¹ < 256`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  input.mult = 0 ∨
    (input.diff_low_limb.val < 65536 ∧
     (input.clk_low + input.offset - input.prev_low - 1 - input.diff_low_limb)
        * (65536 : ZMod p)⁻¹ < (256 : ZMod p))

/-- Helper: `byteOpcodeSpec` row `#v[6, x, 16, 0]` ⇒ `x.val < 65536`.
Local copy of the same helper used in `OperandAccess` / `AddOperation` etc. -/
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

lemma byteOpcodeSpec_range16_of_lt
    (x : ZMod p) (hx : x.val < 65536) :
    SP1Clean.ByteOpcodeSpec (#v[(6 : ZMod p), x, 16, 0]) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  refine ⟨.Range, ?_, ?_⟩
  · simp only [ByteOpcode.toNat, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, Nat.cast_ofNat]
  · simp only [ByteOpcode.constrain_Range, Vector.getElem_mk,
               List.getElem_toArray, List.getElem_cons_zero,
               List.getElem_cons_succ]
    have h16 : (16 : ZMod p).val = 16 := by
      rw [show (16 : ZMod p) = ((16 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    rw [h16]
    exact hx

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_clk_low_eq, h_offset_eq, h_prev_low_eq, h_diff_low_eq,
          h_mult_eq⟩ := h_input
  subst_eqs
  obtain ⟨d1, d2⟩ := h_holds
  simp only [SP1Lookup.ByteOpcodeGated.Spec, SP1Lookup.ByteOpcodeGated.Assumptions,
             forall_const] at d1 d2
  by_cases h_mult : Expression.eval env input_var_mult = 0
  · exact Or.inl h_mult
  right
  have r1 := d1.resolve_left h_mult
  have r2 := d2.resolve_left h_mult
  refine ⟨byteOpcodeSpec_range16 _ r1, ?_⟩
  have h := SP1Clean.CPUState.Assertion.byteOpcodeSpec_u8range _ r2
  convert h using 1; ring

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨h_clk_low_eq, h_offset_eq, h_prev_low_eq, h_diff_low_eq,
          h_mult_eq⟩ := h_input
  subst_eqs
  rcases h_spec with h_mult_zero | ⟨h_dll, h_ts⟩
  · simp only [SP1Lookup.ByteOpcodeGated.Spec, SP1Lookup.ByteOpcodeGated.Assumptions,
               true_and]
    exact ⟨Or.inl h_mult_zero, Or.inl h_mult_zero⟩
  · simp only [SP1Lookup.ByteOpcodeGated.Spec, SP1Lookup.ByteOpcodeGated.Assumptions,
               true_and]
    refine ⟨?_, ?_⟩
    · right; exact byteOpcodeSpec_range16_of_lt _ h_dll
    · right
      have := SP1Clean.CPUState.Assertion.byteOpcodeSpec_u8range_of_lt _ h_ts
      convert this using 3; ring_nf

end Assertion

/-- The Clean `FormalAssertion` for the per-operand timestamp byte-bus
content, mirroring Rust's `eval_register_access_timestamp`. Emits 2
`byteOpcodeGated` lookups (diff_low_limb in Range 16, scaled timestamp in
U8Range). Composed by `OperandAccess.assertion` alongside `WordRange`. -/
def assertion : FormalAssertion (ZMod p) Assertion.Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.RegisterAccessTimestamp
