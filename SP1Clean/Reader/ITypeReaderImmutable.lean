import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.ITypeReaderImmutable.ITypeReaderImmutable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.OperandAccess
import SP1Clean.Reader.RegisterAccess

/-! # Reusable `ITypeReaderImmutable` Spec helper + FormalAssertion

Packages the RHS of `_root_.ITypeReaderImmutable.allHold_constraints_iff_is_real`
as a named predicate `itypeReaderImmutableSpec`. Sibling of
`SP1Clean.ITypeReader.itypeReaderSpec`; differs in that there is no
`op_a_write_value` parameter — `ITypeReaderImmutable` is the reader for
Store chips, which read op_a as the source data rather than writing it.
The `cols.op_a_0 ≠ 0 → …` trailer constrains
`cols.op_a_memory.prev_value` to zero rather than constraining a separate
write value.

Provides a full `FormalAssertion` bundle composing one
`ProgramTable.assertion` and two `RegisterAccess.assertion` calls (op_a
and op_b, both as reads — `write_value = prev_value`). Mirrors Rust's
`i_type.rs:117-139` (`eval_op_a_immutable` delegates to `eval` with
`op_a_write_value = cols.op_a_memory.prev_value`). -/

namespace SP1Clean.ITypeReaderImmutable

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RHS of `_root_.ITypeReaderImmutable.allHold_constraints_iff_is_real`,
packaged as a named predicate. -/
def itypeReaderImmutableSpec
    (clk_low opcode : ZMod p)
    (pc : Vector (ZMod p) 3)
    (cols : _root_.ITypeReader (ZMod p)) : Prop :=
  Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0
      cols.op_c_imm[0] cols.op_c_imm[1] cols.op_c_imm[2] cols.op_c_imm[3] 0 1 ∧
  cols.op_a < (32 : ZMod p) ∧
  cols.op_b < (65536 : ZMod p) ∧
  cols.op_c_imm[0] < (65536 : ZMod p) ∧ cols.op_c_imm[1] < (65536 : ZMod p) ∧
  cols.op_c_imm[2] < (65536 : ZMod p) ∧ cols.op_c_imm[3] < (65536 : ZMod p) ∧
  (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
  (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
  pc[0] % 4 = 0 ∧
  pc[0] < (65536 : ZMod p) ∧ pc[1] < (65536 : ZMod p) ∧ pc[2] < (65536 : ZMod p) ∧
  cols.op_a_memory.access_timestamp.diff_low_limb.val < 65536 ∧
  (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 -
      cols.op_a_memory.access_timestamp.diff_low_limb)
    * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
  Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
    cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
  cols.op_b_memory.access_timestamp.diff_low_limb.val < 65536 ∧
  (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 -
      cols.op_b_memory.access_timestamp.diff_low_limb)
    * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
  Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
    cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
  (cols.op_a_0 ≠ 0 →
    cols.op_a_memory.prev_value[0] = 0 ∧ cols.op_a_memory.prev_value[1] = 0 ∧
    cols.op_a_memory.prev_value[2] = 0 ∧ cols.op_a_memory.prev_value[3] = 0)

/-- The bridge to SP1: under `is_real = is_trusted = 1`, the
ITypeReaderImmutable's constraint list `allHold` is exactly
`itypeReaderImmutableSpec`. -/
theorem itypeReaderImmutableSpec_iff_sp1
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {cols : _root_.ITypeReader (ZMod p)} :
    (_root_.ITypeReaderImmutable.constraints clk_high clk_low pc opcode
        cols 1 1).allHold ↔
      itypeReaderImmutableSpec clk_low opcode pc cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.ITypeReaderImmutable.constraints clk_high clk_low pc opcode
        cols 1 1).allHold
        = List.Forall SP1Constraint.toProp
            (_root_.ITypeReaderImmutable.constraints clk_high clk_low pc opcode
              cols 1 1) from rfl]
  rw [_root_.ITypeReaderImmutable.allHold_constraints_iff_is_real rfl rfl]
  rfl

/-! ## Full `FormalAssertion` promotion -/

/-- Bundled inputs for the ITypeReaderImmutable assertion. No
`op_a_write_value` — op_a is read-only (write_value = prev_value). -/
structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  opcode : F
  pc : Vector F 3
  cols : _root_.ITypeReader F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Clean-side circuit. Emits ProgramTable + 2 RegisterAccess.assertion
calls (op_a and op_b, both reads — `write_value = prev_value`) + 4
`op_a_0 * op_a_memory.prev_value[i] = 0` gates. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨clk_high, clk_low, opcode, pc,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩⟩ := input
  -- Program-bus interaction.
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- op_a: register-access read (write_value = prev_value, the immutable case).
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 4, op_a, op_a_memory.prev_value, op_a_memory.prev_value,
       op_a_memory.access_timestamp.prev_low,
       op_a_memory.access_timestamp.diff_low_limb, 1⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  -- op_b: register-access read.
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 3, op_b, op_b_memory.prev_value, op_b_memory.prev_value,
       op_b_memory.access_timestamp.prev_low,
       op_b_memory.access_timestamp.diff_low_limb, 1⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  -- Four assertZero gates: op_a_0 * op_a_memory.prev_value[i] = 0.
  -- Differs from ITypeReader: constrains the prev_value directly (no
  -- separate write_value).
  op_a_0 * op_a_memory.prev_value[0] === 0
  op_a_0 * op_a_memory.prev_value[1] === 0
  op_a_0 * op_a_memory.prev_value[2] === 0
  op_a_0 * op_a_memory.prev_value[3] === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.ITypeReaderImmutable"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

def Spec (input : Inputs (ZMod p)) : Prop :=
  itypeReaderImmutableSpec input.clk_low input.opcode input.pc input.cols

omit [Fact (2 ^ 17 < p)] [Fact (Nat.Prime p)] in
lemma isU64_iff_index_form [NeZero p] (w : Word (ZMod p)) :
    Word.isU64 w ↔ Word.isU64 #v[w[0], w[1], w[2], w[3]] := by
  constructor
  · intro hw
    obtain ⟨b0, b1, b2, b3⟩ := Word.lt_cases_of_isU64 hw
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_
    · simpa using b0
    · simpa using b1
    · simpa using b2
    · simpa using b3
  · intro hw
    obtain ⟨b0, b1, b2, b3⟩ := Word.lt_cases_of_isU64 hw
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_
    · simpa using b0
    · simpa using b1
    · simpa using b2
    · simpa using b3

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨e_ckh, e_clk, e_opc, e_pc, e_oa,
          ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
          ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oci⟩ := h_input
  subst_eqs
  obtain ⟨h_prog_sub, h_ra_a_sub, h_ra_b_sub,
          h_z0, h_z1, h_z2, h_z3⟩ := h_holds
  have h_prog := h_prog_sub trivial
  have h_ra_a := (h_ra_a_sub trivial).resolve_left one_ne_zero
  have h_ra_b := (h_ra_b_sub trivial).resolve_left one_ne_zero
  simp only [SP1Clean.ProgramTable.assertion, SP1Clean.ProgramTable.Spec,
             SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
  obtain ⟨h_ti, h_op_a_lt, ⟨h_op_b_lt, _, _, _⟩,
          ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
          h_op_a_0_bin, h_op_a_0_iff, _, _,
          h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩ := h_prog
  simp only [itypeReaderImmutableSpec]
  refine ⟨h_ti, h_op_a_lt, h_op_b_lt, h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt,
          h_op_a_0_bin, h_op_a_0_iff, h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt,
          h_ra_a.1, h_ra_a.2.1, (isU64_iff_index_form _).mp h_ra_a.2.2,
          h_ra_b.1, h_ra_b.2.1, (isU64_iff_index_form _).mp h_ra_b.2.2, ?_⟩
  intro h_ne
  simp only [Vector.getElem_map]
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (mul_eq_zero.mp h_z0).resolve_left h_ne
  · exact (mul_eq_zero.mp h_z1).resolve_left h_ne
  · exact (mul_eq_zero.mp h_z2).resolve_left h_ne
  · exact (mul_eq_zero.mp h_z3).resolve_left h_ne

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨e_ckh, e_clk, e_opc, e_pc, e_oa,
          ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
          ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oci⟩ := h_input
  subst_eqs
  simp only [itypeReaderImmutableSpec] at h_spec
  obtain ⟨h_ti, h_op_a_lt, h_op_b_lt, h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt,
          h_op_a_0_bin, h_op_a_0_iff, h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt,
          h_diff_a, h_ts_a, h_isU64_a, h_diff_b, h_ts_b, h_isU64_b,
          h_op_a_0_imp⟩ := h_spec
  have h_zero_lt : (0 : ZMod p) < (65536 : ZMod p) := by
    change (0 : ZMod p).val < (65536 : ZMod p).val
    have h65536 : (65536 : ZMod p).val = 65536 := by
      have hp : 2 ^ 17 < p := Fact.out
      rw [show (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp [h65536]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- ProgramTable subcircuit obligation
  · refine ⟨trivial, ?_⟩
    simp only [SP1Clean.ProgramTable.assertion, SP1Clean.ProgramTable.Spec,
               SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    exact ⟨h_ti, h_op_a_lt,
           ⟨h_op_b_lt, h_zero_lt, h_zero_lt, h_zero_lt⟩,
           ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
           h_op_a_0_bin, h_op_a_0_iff, Or.inl trivial, Or.inr trivial,
           h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩
  -- RegisterAccess for op_a (offset 4, read)
  · refine ⟨trivial, ?_⟩
    right
    exact ⟨h_diff_a, h_ts_a, (isU64_iff_index_form _).mpr h_isU64_a⟩
  -- RegisterAccess for op_b (offset 3, read)
  · refine ⟨trivial, ?_⟩
    right
    exact ⟨h_diff_b, h_ts_b, (isU64_iff_index_form _).mpr h_isU64_b⟩
  -- 4 assertZero gates: op_a_0 * op_a_memory.prev_value[i] = 0
  · by_cases h : Expression.eval env.toEnvironment input_var_cols_op_a_0 = 0
    · simp [h]
    · have := (h_op_a_0_imp h).1
      rw [Vector.getElem_map] at this
      rw [this, mul_zero]
  · by_cases h : Expression.eval env.toEnvironment input_var_cols_op_a_0 = 0
    · simp [h]
    · have := (h_op_a_0_imp h).2.1
      rw [Vector.getElem_map] at this
      rw [this, mul_zero]
  · by_cases h : Expression.eval env.toEnvironment input_var_cols_op_a_0 = 0
    · simp [h]
    · have := (h_op_a_0_imp h).2.2.1
      rw [Vector.getElem_map] at this
      rw [this, mul_zero]
  · by_cases h : Expression.eval env.toEnvironment input_var_cols_op_a_0 = 0
    · simp [h]
    · have := (h_op_a_0_imp h).2.2.2
      rw [Vector.getElem_map] at this
      rw [this, mul_zero]

end Assertion

/-- The Clean `FormalAssertion` for the full immutable I-type reader spec
(`itypeReaderImmutableSpec`). Composes `ProgramTable.assertion`, two
`RegisterAccess.assertion` calls (op_a/op_b reads), and four
`op_a_0 * op_a_memory.prev_value[i] = 0` scalar gates. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-! ## Flag-threaded variant (`Gated`)

Mirrors Rust's `eval_op_a_immutable(cols, ..., is_real, is_trusted)`. Same
pattern as `SP1Clean.ITypeReader.Gated`, but with op_a as a READ
(`write_value = prev_value`) and the four op_a_0 gates constraining
`op_a_memory.prev_value[i]` directly (no separate write value). Used by
`BranchChip` (Phase 4) to absorb the chip-level `is_real`/`is_trusted`
binary gates. -/

namespace Gated

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  opcode : F
  pc : Vector F 3
  cols : _root_.ITypeReader F
  is_real : F
  is_trusted : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Clean-side flag-threaded immutable I-type reader circuit. Two
RegisterAccess subcircuits (op_a + op_b, both read shape with
`write_value = prev_value`), gated by `is_real`; one ProgramGated lookup
gated by `is_trusted`; 4 op_a_0 prev_value zero gates. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨clk_high, clk_low, opcode, pc,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩,
       is_real, is_trusted⟩ := input
  is_real * (is_real - 1) === 0
  SP1Clean.programGated
    (⟨#v[pc[0], pc[1], pc[2], opcode, op_a, op_b, 0, 0, 0,
         op_c_imm[0], op_c_imm[1], op_c_imm[2], op_c_imm[3],
         op_a_0, 0, 1],
       is_trusted⟩ : Var SP1Clean.ProgramGated.Inputs (ZMod p))
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 4, op_a, op_a_memory.prev_value, op_a_memory.prev_value,
       op_a_memory.access_timestamp.prev_low,
       op_a_memory.access_timestamp.diff_low_limb, is_real⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 3, op_b, op_b_memory.prev_value, op_b_memory.prev_value,
       op_b_memory.access_timestamp.prev_low,
       op_b_memory.access_timestamp.diff_low_limb, is_real⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  op_a_0 * op_a_memory.prev_value[0] === 0
  op_a_0 * op_a_memory.prev_value[1] === 0
  op_a_0 * op_a_memory.prev_value[2] === 0
  op_a_0 * op_a_memory.prev_value[3] === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.ITypeReaderImmutable.Gated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

def Spec (input : Inputs (ZMod p)) : Prop :=
  let ⟨clk_high, clk_low, opcode, pc, cols, is_real, is_trusted⟩ := input
  is_real * (is_real - 1) = 0 ∧
  SP1Clean.ProgramGated.Spec
    ⟨#v[pc[0], pc[1], pc[2], opcode, cols.op_a, cols.op_b, 0, 0, 0,
        cols.op_c_imm[0], cols.op_c_imm[1], cols.op_c_imm[2], cols.op_c_imm[3],
        cols.op_a_0, 0, 1],
     is_trusted⟩ ∧
  SP1Clean.RegisterAccess.Assertion.Spec
    ⟨clk_high, clk_low, 4, cols.op_a, cols.op_a_memory.prev_value,
     cols.op_a_memory.prev_value, cols.op_a_memory.access_timestamp.prev_low,
     cols.op_a_memory.access_timestamp.diff_low_limb, is_real⟩ ∧
  SP1Clean.RegisterAccess.Assertion.Spec
    ⟨clk_high, clk_low, 3, cols.op_b, cols.op_b_memory.prev_value,
     cols.op_b_memory.prev_value, cols.op_b_memory.access_timestamp.prev_low,
     cols.op_b_memory.access_timestamp.diff_low_limb, is_real⟩ ∧
  cols.op_a_0 * cols.op_a_memory.prev_value[0] = 0 ∧
  cols.op_a_0 * cols.op_a_memory.prev_value[1] = 0 ∧
  cols.op_a_0 * cols.op_a_memory.prev_value[2] = 0 ∧
  cols.op_a_0 * cols.op_a_memory.prev_value[3] = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨e_ckh, e_cl, e_opc, e_pc,
          ⟨e_oa, ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
           ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oci⟩,
          e_ir, e_it⟩ := h_input
  subst_eqs
  obtain ⟨h_gate, h_prog_sub, h_ra_a_sub, h_ra_b_sub,
          h_z0, h_z1, h_z2, h_z3⟩ := h_holds
  simp only [Spec, sub_eq_add_neg, Vector.getElem_map]
  exact ⟨h_gate, h_prog_sub trivial, h_ra_a_sub trivial, h_ra_b_sub trivial,
         h_z0, h_z1, h_z2, h_z3⟩

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨e_ckh, e_cl, e_opc, e_pc,
          ⟨e_oa, ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
           ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oci⟩,
          e_ir, e_it⟩ := h_input
  subst_eqs
  simp only [Spec, sub_eq_add_neg, Vector.getElem_map] at h_spec
  obtain ⟨h_gate, h_prog, h_ra_a, h_ra_b, h_z0, h_z1, h_z2, h_z3⟩ := h_spec
  exact ⟨h_gate, ⟨trivial, h_prog⟩, ⟨trivial, h_ra_a⟩, ⟨trivial, h_ra_b⟩,
         h_z0, h_z1, h_z2, h_z3⟩

end Assertion

def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-- Bridge from SP1-native `ITypeReaderImmutable.constraints.allHold` to
the literal sub-circuit conjunction `Gated.Assertion.Spec`. Used by
chip-level `allHold_iff_structural` proofs (BranchChip) to bridge SP1's
flat `allHold` to the chip `FormalSpec`'s structured sub-circuit
composition. -/
theorem Assertion.Spec_iff_sp1
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {cols : _root_.ITypeReader (ZMod p)}
    {is_real is_trusted : ZMod p} :
    (_root_.ITypeReaderImmutable.constraints clk_high clk_low pc opcode
        cols is_real is_trusted).allHold ↔
      Assertion.Spec ⟨clk_high, clk_low, opcode, pc, cols,
                      is_real, is_trusted⟩ := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.ITypeReaderImmutable.constraints clk_high clk_low pc opcode
            cols is_real is_trusted).allHold =
       List.Forall SP1Constraint.toProp
        (_root_.ITypeReaderImmutable.constraints clk_high clk_low pc opcode
          cols is_real is_trusted) from rfl]
  rw [_root_.ITypeReaderImmutable.allHold_constraints_iff]
  have h_0_lt_65536 : (0 : ZMod p) < (65536 : ZMod p) := by
    change (0 : ZMod p).val < (65536 : ZMod p).val; simp
  simp only [Assertion.Spec, SP1Clean.ProgramGated.Spec, SP1Clean.ProgramSpec,
    SP1Clean.RegisterAccess.Assertion.Spec,
    SP1Clean.OperandAccess.AssertionGated.Spec,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  refine ⟨?_, ?_⟩
  -- → direction.
  · rintro ⟨h_bin, h_prog_imp, h_mem_imp, h_op_a_0_imp⟩
    have h_ir_mul : is_real * (is_real - 1) = 0 := by
      rcases h_bin with h0 | h1
      · subst h0; ring
      · have h_sub : is_real - 1 = 0 := sub_eq_zero.mpr h1
        rw [h_sub]; ring
    have h_z0 : cols.op_a_0 * cols.op_a_memory.prev_value[0] = 0 := by
      by_cases h0 : cols.op_a_0 = 0
      · rw [h0]; ring
      · rw [(h_op_a_0_imp h0).1]; ring
    have h_z1 : cols.op_a_0 * cols.op_a_memory.prev_value[1] = 0 := by
      by_cases h0 : cols.op_a_0 = 0
      · rw [h0]; ring
      · rw [(h_op_a_0_imp h0).2.1]; ring
    have h_z2 : cols.op_a_0 * cols.op_a_memory.prev_value[2] = 0 := by
      by_cases h0 : cols.op_a_0 = 0
      · rw [h0]; ring
      · rw [(h_op_a_0_imp h0).2.2.1]; ring
    have h_z3 : cols.op_a_0 * cols.op_a_memory.prev_value[3] = 0 := by
      by_cases h0 : cols.op_a_0 = 0
      · rw [h0]; ring
      · rw [(h_op_a_0_imp h0).2.2.2]; ring
    refine ⟨h_ir_mul, ?_, ?_, ?_, h_z0, h_z1, h_z2, h_z3⟩
    · by_cases h_t : is_trusted = 0
      · exact Or.inl h_t
      · right
        obtain ⟨h_ti, h_op_a, h_op_b, h_oci0, h_oci1, h_oci2, h_oci3,
                h_op_a_0_bin, h_op_a_0_iff,
                h_pc0_mod, h_pc0_lt, h_pc1_lt, h_pc2_lt⟩ := h_prog_imp h_t
        refine ⟨h_ti, h_op_a,
                ⟨h_op_b, h_0_lt_65536, h_0_lt_65536, h_0_lt_65536⟩,
                ⟨h_oci0, h_oci1, h_oci2, h_oci3⟩,
                h_op_a_0_bin, h_op_a_0_iff, Or.inl trivial, ?_,
                h_pc0_mod, h_pc0_lt, h_pc1_lt, h_pc2_lt⟩
        exact Or.inr trivial
    · by_cases h_r : is_real = 0
      · exact Or.inl h_r
      · right
        obtain ⟨h_diff_a, h_ts_a, h_isU64_a, _, _, _⟩ := h_mem_imp h_r
        exact ⟨h_diff_a, h_ts_a, (Assertion.isU64_iff_index_form _).mpr h_isU64_a⟩
    · by_cases h_r : is_real = 0
      · exact Or.inl h_r
      · right
        obtain ⟨_, _, _, h_diff_b, h_ts_b, h_isU64_b⟩ := h_mem_imp h_r
        exact ⟨h_diff_b, h_ts_b, (Assertion.isU64_iff_index_form _).mpr h_isU64_b⟩
  -- ← direction.
  · rintro ⟨h_ir_mul, h_prog_disj, h_ra_a_disj, h_ra_b_disj, h_z0, h_z1, h_z2, h_z3⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases mul_eq_zero.mp h_ir_mul with h | h_sub
      · exact Or.inl h
      · exact Or.inr (sub_eq_zero.mp h_sub)
    · intro h_t_ne
      rcases h_prog_disj with h0 | h_ps
      · exact absurd h0 h_t_ne
      obtain ⟨h_ti, h_op_a, ⟨h_op_b, _, _, _⟩,
              ⟨h_oci0, h_oci1, h_oci2, h_oci3⟩,
              h_op_a_0_bin, h_op_a_0_iff, _, _,
              h_pc0_mod, h_pc0_lt, h_pc1_lt, h_pc2_lt⟩ := h_ps
      exact ⟨h_ti, h_op_a, h_op_b, h_oci0, h_oci1, h_oci2, h_oci3,
             h_op_a_0_bin, h_op_a_0_iff,
             h_pc0_mod, h_pc0_lt, h_pc1_lt, h_pc2_lt⟩
    · intro h_r_ne
      have h_a := h_ra_a_disj.resolve_left h_r_ne
      have h_b := h_ra_b_disj.resolve_left h_r_ne
      exact ⟨h_a.1, h_a.2.1, (Assertion.isU64_iff_index_form _).mp h_a.2.2,
             h_b.1, h_b.2.1, (Assertion.isU64_iff_index_form _).mp h_b.2.2⟩
    · intro h_op_a_0_ne
      exact ⟨(mul_eq_zero.mp h_z0).resolve_left h_op_a_0_ne,
             (mul_eq_zero.mp h_z1).resolve_left h_op_a_0_ne,
             (mul_eq_zero.mp h_z2).resolve_left h_op_a_0_ne,
             (mul_eq_zero.mp h_z3).resolve_left h_op_a_0_ne⟩

end Gated

end SP1Clean.ITypeReaderImmutable
