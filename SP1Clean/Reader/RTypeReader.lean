import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.OperandAccess

/-! # Reusable `RTypeReader` Spec helper

Packages the RHS of `_root_.RTypeReader.allHold_constraints_iff_is_real`
as a named predicate `rtypeReaderSpec`. Differs from `itypeReaderSpec` by
having `op_c` as a register (with full memory-access substruct) instead of
the four immediate limbs `op_c_imm`.

Also exposes `programRow` — the 16-tuple `fields 16` view of an R-type
row that is the natural argument to `lookup SP1Clean.ProgramTable`.
-/

namespace SP1Clean.RTypeReader

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The 16-tuple program-bus row for an R-type instruction with opcode
`opcode`. Matches `AirInteraction.program` from `SP1Foundations/Constraint.lean`:
`#v[pc0, pc1, pc2, opcode, op_a, op_b_0..3, op_c_0..3, op_a_0, imm_b, imm_c]`,
with the R-type discipline that `op_b` and `op_c` are single-limb register
indices (limbs 1–3 are zero) and `imm_b = imm_c = 0`. -/
@[reducible]
def programRow (opcode : ZMod p) (pc : Vector (ZMod p) 3)
    (cols : _root_.RTypeReader (ZMod p)) : fields 16 (ZMod p) :=
  #v[pc[0], pc[1], pc[2], opcode,
     cols.op_a, cols.op_b, 0, 0, 0,
     cols.op_c, 0, 0, 0,
     cols.op_a_0, 0, 0]

/-- The RHS of `_root_.RTypeReader.allHold_constraints_iff_is_real`,
packaged as a named predicate. -/
def rtypeReaderSpec
    (clk_low opcode : ZMod p)
    (pc : Vector (ZMod p) 3)
    (op_a_write_value : Word (ZMod p))
    (cols : _root_.RTypeReader (ZMod p)) : Prop :=
  Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0
      cols.op_c 0 0 0 0 0 ∧
  cols.op_a < (32 : ZMod p) ∧
  cols.op_b < (65536 : ZMod p) ∧
  cols.op_c < (65536 : ZMod p) ∧
  (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
  (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
  (pc[0] % 4 = 0 ∧
   pc[0] < (65536 : ZMod p) ∧ pc[1] < (65536 : ZMod p) ∧ pc[2] < (65536 : ZMod p)) ∧
  ((cols.op_a_memory.access_timestamp.diff_low_limb.val < 65536 ∧
    cols.op_b_memory.access_timestamp.diff_low_limb.val < 65536 ∧
    cols.op_c_memory.access_timestamp.diff_low_limb.val < 65536) ∧
   ((clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1 -
        cols.op_c_memory.access_timestamp.diff_low_limb)
      * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
    (clk_low + 3 - cols.op_b_memory.access_timestamp.prev_low - 1 -
        cols.op_b_memory.access_timestamp.diff_low_limb)
      * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
    (clk_low + 4 - cols.op_a_memory.access_timestamp.prev_low - 1 -
        cols.op_a_memory.access_timestamp.diff_low_limb)
      * (65536 : ZMod p)⁻¹ < (256 : ZMod p)) ∧
   (Word.isU64 #v[cols.op_a_memory.prev_value[0], cols.op_a_memory.prev_value[1],
      cols.op_a_memory.prev_value[2], cols.op_a_memory.prev_value[3]] ∧
    Word.isU64 #v[cols.op_b_memory.prev_value[0], cols.op_b_memory.prev_value[1],
      cols.op_b_memory.prev_value[2], cols.op_b_memory.prev_value[3]] ∧
    Word.isU64 #v[cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1],
      cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]])) ∧
  (cols.op_a_0 ≠ 0 →
    op_a_write_value[0] = 0 ∧ op_a_write_value[1] = 0 ∧
    op_a_write_value[2] = 0 ∧ op_a_write_value[3] = 0)

/-- The bridge to SP1: under `is_real = is_trusted = 1`, the R-type reader's
constraint list `allHold` is exactly `rtypeReaderSpec`. -/
theorem rtypeReaderSpec_iff_sp1
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {op_a_write_value : Word (ZMod p)}
    {cols : _root_.RTypeReader (ZMod p)} :
    (_root_.RTypeReader.constraints clk_high clk_low pc opcode op_a_write_value
        cols 1 1).allHold ↔
      rtypeReaderSpec clk_low opcode pc op_a_write_value cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.RTypeReader.constraints clk_high clk_low pc opcode
        op_a_write_value cols 1 1).allHold
        = List.Forall SP1Constraint.toProp
            (_root_.RTypeReader.constraints clk_high clk_low pc opcode
              op_a_write_value cols 1 1) from rfl]
  rw [_root_.RTypeReader.allHold_constraints_iff_is_real rfl rfl]
  rfl

/-! ## Full `FormalAssertion` promotion

Wraps the byte/program-lookup-derivable surface of
`_root_.RTypeReader.constraints` (under `is_real = is_trusted = 1`) into a
single Clean `FormalAssertion`. Composes one `SP1Clean.ProgramTable.assertion`
(supplying `trusted_instr`, register bounds, op_a_0 binary/iff, PC alignment)
and three `SP1Clean.OperandAccess.assertion` calls at sub-clock offsets +4/+3/+2
(supplying diff_low/timestamp/U64 bounds for each operand), plus four scalar
`op_a_0 * op_a_write_value[i] = 0` gates that encode the
`op_a_0 ≠ 0 → op_a_write_value = 0` last conjunct of `rtypeReaderSpec`. -/

/-- Bundled inputs for the RTypeReader assertion. Mirrors the call signature
of `_root_.RTypeReader.constraints clk_high clk_low pc opcode op_a_write_value
cols 1 1` modulo the unused `clk_high` (only `clk_low` participates in any
lookup) and the pinned `is_real = is_trusted = 1`. -/
structure Inputs (F : Type) where
  clk_low : F
  opcode : F
  pc : Vector F 3
  op_a_write_value : Vector F 4
  cols : _root_.RTypeReader F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Clean-side circuit. Emits exactly the byte/program lookups inside
`_root_.RTypeReader.constraints` under `is_real = is_trusted = 1`. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨clk_low, opcode, pc, op_a_write_value,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory⟩⟩ := input
  -- Program-bus interaction (covers trusted_instr + register bounds +
  -- op_a_0 binary/iff + PC alignment+bounds). R-type discipline: op_b/op_c
  -- single-limb register indices with limbs 1–3 zero; imm_b = imm_c = 0.
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode, op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Three per-operand byte-bus assertions. Sub-clock offsets follow the
  -- R-type convention: op_a at +4, op_b at +3, op_c at +2.
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low,
       op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low,
       op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 2, op_c_memory.access_timestamp.prev_low,
       op_c_memory.access_timestamp.diff_low_limb,
       op_c_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  -- Four assertZero gates that, with `op_a_0` field-binary from ProgramSpec,
  -- give `op_a_0 ≠ 0 → op_a_write_value[i] = 0`.
  op_a_0 * op_a_write_value[0] === 0
  op_a_0 * op_a_write_value[1] === 0
  op_a_0 * op_a_write_value[2] === 0
  op_a_0 * op_a_write_value[3] === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.RTypeReader"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The full `rtypeReaderSpec` predicate — same as the RHS of
`rtypeReaderSpec_iff_sp1`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  rtypeReaderSpec input.clk_low input.opcode input.pc
    input.op_a_write_value input.cols

omit [Fact (2 ^ 17 < p)] [Fact (Nat.Prime p)] in
/-- `Word.isU64` on a whole `Vector` is equivalent to `Word.isU64` on its
`#v[w[0], w[1], w[2], w[3]]` re-indexed form (the shape `rtypeReaderSpec`
uses for its memory-bus clauses). Used by trace-level discharges that need
to bridge `rtypeReaderSpec` extracts back to whole-`Vector` `memoryAccessSpec`. -/
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
          ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oc,
          e_pv_c, e_pl_c, e_dll_c⟩ := h_input
  subst_eqs
  obtain ⟨h_prog_sub, h_oa_a_sub, h_oa_b_sub, h_oa_c_sub,
          h_z0, h_z1, h_z2, h_z3⟩ := h_holds
  have h_prog := h_prog_sub trivial
  have h_oa_a := h_oa_a_sub trivial
  have h_oa_b := h_oa_b_sub trivial
  have h_oa_c := h_oa_c_sub trivial
  simp only [SP1Clean.ProgramTable.assertion, SP1Clean.ProgramTable.Spec,
             SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
  simp only [SP1Clean.OperandAccess.assertion, SP1Clean.OperandAccess.Assertion.Spec]
    at h_oa_a h_oa_b h_oa_c
  obtain ⟨h_ti, h_op_a_lt, ⟨h_op_b_lt, _, _, _⟩, ⟨h_op_c_lt, _, _, _⟩,
          h_op_a_0_bin, h_op_a_0_iff, _, _, h_pc⟩ := h_prog
  simp only [Spec, rtypeReaderSpec]
  refine ⟨h_ti, h_op_a_lt, h_op_b_lt, h_op_c_lt, h_op_a_0_bin, h_op_a_0_iff, h_pc,
          ⟨⟨h_oa_a.1, h_oa_b.1, h_oa_c.1⟩,
           ⟨h_oa_c.2.1, h_oa_b.2.1, h_oa_a.2.1⟩,
           (isU64_iff_index_form _).mp h_oa_a.2.2,
           (isU64_iff_index_form _).mp h_oa_b.2.2,
           (isU64_iff_index_form _).mp h_oa_c.2.2⟩,
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
          ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oc,
          e_pv_c, e_pl_c, e_dll_c⟩ := h_input
  subst_eqs
  simp only [Spec, rtypeReaderSpec] at h_spec
  obtain ⟨h_ti, h_op_a_lt, h_op_b_lt, h_op_c_lt, h_op_a_0_bin, h_op_a_0_iff,
          ⟨h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩,
          ⟨⟨h_diff_a, h_diff_b, h_diff_c⟩,
           ⟨h_ts_c, h_ts_b, h_ts_a⟩,
           ⟨h_isU64_a, h_isU64_b, h_isU64_c⟩⟩,
          h_op_a_0_imp⟩ := h_spec
  have h_zero_lt : (0 : ZMod p) < (65536 : ZMod p) := by
    change (0 : ZMod p).val < (65536 : ZMod p).val
    have h65536 : (65536 : ZMod p).val = 65536 := by
      have hp : 2 ^ 17 < p := Fact.out
      rw [show (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp [h65536]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- ProgramTable subcircuit obligation
  · refine ⟨trivial, ?_⟩
    simp only [SP1Clean.ProgramTable.assertion, SP1Clean.ProgramTable.Spec,
               SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    exact ⟨h_ti, h_op_a_lt,
           ⟨h_op_b_lt, h_zero_lt, h_zero_lt, h_zero_lt⟩,
           ⟨h_op_c_lt, h_zero_lt, h_zero_lt, h_zero_lt⟩,
           h_op_a_0_bin, h_op_a_0_iff, Or.inl trivial, Or.inl trivial,
           h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩
  -- OperandAccess for op_a (offset 4)
  · refine ⟨trivial, ?_⟩
    simp only [SP1Clean.OperandAccess.assertion, SP1Clean.OperandAccess.Assertion.Spec]
    exact ⟨h_diff_a, h_ts_a, (isU64_iff_index_form _).mpr h_isU64_a⟩
  -- OperandAccess for op_b (offset 3)
  · refine ⟨trivial, ?_⟩
    simp only [SP1Clean.OperandAccess.assertion, SP1Clean.OperandAccess.Assertion.Spec]
    exact ⟨h_diff_b, h_ts_b, (isU64_iff_index_form _).mpr h_isU64_b⟩
  -- OperandAccess for op_c (offset 2)
  · refine ⟨trivial, ?_⟩
    simp only [SP1Clean.OperandAccess.assertion, SP1Clean.OperandAccess.Assertion.Spec]
    exact ⟨h_diff_c, h_ts_c, (isU64_iff_index_form _).mpr h_isU64_c⟩
  -- 4 assertZero gates: op_a_0 * op_a_write_value[i] = 0
  -- Convert h_op_a_0_imp's `(Vector.map ...)[i]` form to match the goal's
  -- `eval env input_var_op_a_write_value[i]` form via Vector.getElem_map.
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

/-- The Clean `FormalAssertion` for the full R-type reader spec
(`rtypeReaderSpec`). Composes `ProgramTable.assertion`, three
`OperandAccess.assertion` calls, and four `op_a_0 * op_a_write_value[i] = 0`
scalar gates. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.RTypeReader
