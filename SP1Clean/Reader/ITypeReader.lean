import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.ITypeReader.ITypeReader
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.OperandAccess

/-! # Reusable `ITypeReader` Spec helper + FormalAssertion

Packages the RHS of `_root_.ITypeReader.allHold_constraints_iff_is_real`
as a named predicate `itypeReaderSpec`. Differs from `rtypeReaderSpec` by
having `op_c_imm` as a 4-limb immediate (with no memory access) instead of
the register `op_c` with its full memory-access substruct.

Also provides a full `FormalAssertion` bundle (mirroring
`SP1Clean.RTypeReader.assertion`) that chip-level `Assertion.main` blocks
can compose as a single subcircuit. The bundle composes one
`ProgramTable.assertion` (covering `trusted_instr`, register bounds, the
4 immediate-limb bounds, `op_a_0` binary/iff, PC alignment) and two
`OperandAccess.assertion` calls at sub-clock offsets +4/+3 (op_a/op_b —
no op_c memory access because op_c is the immediate), plus four scalar
`op_a_0 * op_a_write_value[i] = 0` gates encoding the
`op_a_0 ≠ 0 → op_a_write_value = 0` last conjunct of `itypeReaderSpec`.
-/

namespace SP1Clean.ITypeReader

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RHS of `_root_.ITypeReader.allHold_constraints_iff_is_real`,
packaged as a named predicate. -/
def itypeReaderSpec
    (clk_low opcode : ZMod p)
    (pc : Vector (ZMod p) 3)
    (op_a_write_value : Word (ZMod p))
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
  cols.op_b_memory.access_timestamp.diff_low_limb.val < 65536 ∧
  (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 -
      cols.op_b_memory.access_timestamp.diff_low_limb)
    * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
  (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 -
      cols.op_a_memory.access_timestamp.diff_low_limb)
    * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
  Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
    cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
  Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
    cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
  (cols.op_a_0 ≠ 0 →
    op_a_write_value[0] = 0 ∧ op_a_write_value[1] = 0 ∧
    op_a_write_value[2] = 0 ∧ op_a_write_value[3] = 0)

/-- The bridge to SP1: under `is_real = is_trusted = 1`, the I-type reader's
constraint list `allHold` is exactly `itypeReaderSpec`. -/
theorem itypeReaderSpec_iff_sp1
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {op_a_write_value : Word (ZMod p)}
    {cols : _root_.ITypeReader (ZMod p)} :
    (_root_.ITypeReader.constraints clk_high clk_low pc opcode op_a_write_value
        cols 1 1).allHold ↔
      itypeReaderSpec clk_low opcode pc op_a_write_value cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.ITypeReader.constraints clk_high clk_low pc opcode
        op_a_write_value cols 1 1).allHold
        = List.Forall SP1Constraint.toProp
            (_root_.ITypeReader.constraints clk_high clk_low pc opcode
              op_a_write_value cols 1 1) from rfl]
  rw [_root_.ITypeReader.allHold_constraints_iff_is_real rfl rfl]
  rfl

/-! ## Full `FormalAssertion` promotion

Wraps the byte/program-lookup-derivable surface of
`_root_.ITypeReader.constraints` (under `is_real = is_trusted = 1`) into a
single Clean `FormalAssertion`. Composes one `SP1Clean.ProgramTable.assertion`
(supplying `trusted_instr`, register bounds, the 4 immediate-limb bounds,
`op_a_0` binary/iff, PC alignment) and two `SP1Clean.OperandAccess.assertion`
calls at sub-clock offsets +4/+3 (op_a/op_b — no op_c memory access), plus
four scalar `op_a_0 * op_a_write_value[i] = 0` gates that encode the
`op_a_0 ≠ 0 → op_a_write_value = 0` last conjunct of `itypeReaderSpec`. -/

/-- Bundled inputs for the ITypeReader assertion. Mirrors the call signature
of `_root_.ITypeReader.constraints clk_high clk_low pc opcode op_a_write_value
cols 1 1` modulo the unused `clk_high` and the pinned `is_real = is_trusted = 1`. -/
structure Inputs (F : Type) where
  clk_low : F
  opcode : F
  pc : Vector F 3
  op_a_write_value : Vector F 4
  cols : _root_.ITypeReader F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Clean-side circuit. Emits exactly the byte/program lookups inside
`_root_.ITypeReader.constraints` under `is_real = is_trusted = 1`.

The 2 per-operand byte-bus assertions use `OperandAccess.assertionGated`
with `mult := 1` (uniform with AddwChip's op_c which uses a real
multiplicity). The `mult = 1` disjunctive Spec collapses back to the
unconditional form via `one_ne_zero` in the soundness/completeness
proofs below — external chips that call `ITypeReader.assertion` see
the same unconditional `itypeReaderSpec`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨clk_low, opcode, pc, op_a_write_value,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩⟩ := input
  -- Program-bus interaction.
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Two per-operand byte-bus assertions via `assertionGated mult=1`.
  SP1Clean.OperandAccess.assertionGated
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low,
       op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value, 1⟩ :
      Var SP1Clean.OperandAccess.AssertionGated.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertionGated
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low,
       op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value, 1⟩ :
      Var SP1Clean.OperandAccess.AssertionGated.Inputs (ZMod p))
  -- Four assertZero gates that, with `op_a_0` field-binary from ProgramSpec,
  -- give `op_a_0 ≠ 0 → op_a_write_value[i] = 0`.
  op_a_0 * op_a_write_value[0] === 0
  op_a_0 * op_a_write_value[1] === 0
  op_a_0 * op_a_write_value[2] === 0
  op_a_0 * op_a_write_value[3] === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.ITypeReader"
  main := main
  -- Computed from main: 2 assertionGated × 24 witnesses = 48.
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The full `itypeReaderSpec` predicate — same as the RHS of
`itypeReaderSpec_iff_sp1`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  itypeReaderSpec input.clk_low input.opcode input.pc
    input.op_a_write_value input.cols

omit [Fact (2 ^ 17 < p)] [Fact (Nat.Prime p)] in
/-- `Word.isU64` on a whole `Vector` is equivalent to `Word.isU64` on its
`#v[w[0], w[1], w[2], w[3]]` re-indexed form (the shape `itypeReaderSpec`
uses for its memory-bus clauses). -/
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
  obtain ⟨e_clk, e_opc, e_pc, e_oawv, e_oa,
          ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
          ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oci⟩ := h_input
  subst_eqs
  obtain ⟨h_prog_sub, h_oa_a_sub, h_oa_b_sub,
          h_z0, h_z1, h_z2, h_z3⟩ := h_holds
  have h_prog := h_prog_sub trivial
  -- assertionGated.Spec ⟨..., 1⟩ = (1 = 0 ∨ <byte facts>); 1 ≠ 0 so right disjunct.
  have h_oa_a := (h_oa_a_sub trivial).resolve_left one_ne_zero
  have h_oa_b := (h_oa_b_sub trivial).resolve_left one_ne_zero
  simp only [SP1Clean.ProgramTable.assertion, SP1Clean.ProgramTable.Spec,
             SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
  obtain ⟨h_ti, h_op_a_lt, ⟨h_op_b_lt, _, _, _⟩,
          ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
          h_op_a_0_bin, h_op_a_0_iff, _, _, h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩ := h_prog
  simp only [Spec, itypeReaderSpec]
  refine ⟨h_ti, h_op_a_lt, h_op_b_lt, h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt,
          h_op_a_0_bin, h_op_a_0_iff, h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt,
          h_oa_a.1, h_oa_b.1, h_oa_b.2.1, h_oa_a.2.1,
          (isU64_iff_index_form _).mp h_oa_a.2.2,
          (isU64_iff_index_form _).mp h_oa_b.2.2,
          ?_⟩
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
  obtain ⟨e_clk, e_opc, e_pc, e_oawv, e_oa,
          ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
          ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oci⟩ := h_input
  subst_eqs
  simp only [Spec, itypeReaderSpec] at h_spec
  obtain ⟨h_ti, h_op_a_lt, h_op_b_lt, h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt,
          h_op_a_0_bin, h_op_a_0_iff, h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt,
          h_diff_a, h_diff_b, h_ts_b, h_ts_a, h_isU64_a, h_isU64_b,
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
  -- OperandAccess for op_a (offset 4) — provide right disjunct of assertionGated.Spec
  · refine ⟨trivial, ?_⟩
    right
    exact ⟨h_diff_a, h_ts_a, (isU64_iff_index_form _).mpr h_isU64_a⟩
  -- OperandAccess for op_b (offset 3)
  · refine ⟨trivial, ?_⟩
    right
    exact ⟨h_diff_b, h_ts_b, (isU64_iff_index_form _).mpr h_isU64_b⟩
  -- 4 assertZero gates: op_a_0 * op_a_write_value[i] = 0
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

/-- The Clean `FormalAssertion` for the full I-type reader spec
(`itypeReaderSpec`). Composes `ProgramTable.assertion`, two
`OperandAccess.assertion` calls, and four `op_a_0 * op_a_write_value[i] = 0`
scalar gates. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ITypeReader
