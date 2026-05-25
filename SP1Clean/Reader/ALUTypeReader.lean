import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Circuit.Lookup
import Clean.Circuit.Subcircuit
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.OperandAccess
import SP1Clean.SP1Lookup

/-! # Reusable `ALUTypeReader` Spec helper + FormalAssertion

Packages the RHS of `_root_.ALUTypeReader.allHold_constraints_iff_is_real`
as a named predicate `aluTypeReaderSpec`. Differs from `rtypeReaderSpec` by
having `op_c` as a 4-limb `Word` and carrying an `imm_c` flag that gates the
op_c memory access (`imm_c = 0` ⇒ register read; `imm_c = 1` ⇒ immediate, with
`op_c_memory.prev_value` constrained to equal `op_c`).

Provides a complete `FormalAssertion` bundle that captures the full
`aluTypeReaderSpec`:
- `ProgramTable.assertion` covering `trusted_instr`, register bounds, the
  4 op_c limb bounds, `op_a_0` binary/iff, `imm_c` binary, PC alignment.
- Three `OperandAccess.assertionGated` calls (op_a/+4, op_b/+3 with mult=1;
  op_c/+2 with `mult := 1 - imm_c`). The op_c gating mirrors SP1's
  `alu_type.rs:142` (multiplicity `is_real - imm_c`); since the reader pins
  `is_real = 1`, this is equivalent to `1 - imm_c`.
- Four `op_a_0 * op_a_write_value[i] = 0` gates (enforcing the
  `op_a_0 ≠ 0 → op_a_write_value = 0` clause of the spec).
- Four `imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0` gates
  (enforcing the `imm_c = 1 → prev_value = op_c` clause; mirrors SP1's
  `alu_type.rs:170–177`).

All three add chips (`Add`, `Addi`, `Addw`) now route their byte/program
lookups through a uniform reader subcircuit: `Add` → `RTypeReader.assertion`,
`Addi` → `ITypeReader.assertion`, `Addw` → `ALUTypeReader.assertion`. -/

namespace SP1Clean.ALUTypeReader

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The RHS of `_root_.ALUTypeReader.allHold_constraints_iff_is_real`,
packaged as a named predicate. -/
def aluTypeReaderSpec
    (clk_low opcode : ZMod p)
    (pc : Vector (ZMod p) 3)
    (op_a_write_value : Word (ZMod p))
    (cols : _root_.ALUTypeReader (ZMod p)) : Prop :=
  Opcode.trusted_instr (Opcode.ofNat opcode.val) cols.op_a cols.op_b 0 0 0
      cols.op_c[0] cols.op_c[1] cols.op_c[2] cols.op_c[3] 0 cols.imm_c ∧
  cols.op_a < (32 : ZMod p) ∧
  cols.op_b < (65536 : ZMod p) ∧
  (cols.op_c[0] < (65536 : ZMod p) ∧ cols.op_c[1] < (65536 : ZMod p) ∧
   cols.op_c[2] < (65536 : ZMod p) ∧ cols.op_c[3] < (65536 : ZMod p)) ∧
  (cols.op_a_0 = 0 ∨ cols.op_a_0 = 1) ∧
  (cols.op_a_0 = 1 ↔ cols.op_a = 0) ∧
  (cols.imm_c = 0 ∨ cols.imm_c = 1) ∧
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
  (cols.imm_c = 0 →
    (clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1 -
        cols.op_c_memory.access_timestamp.diff_low_limb)
      * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
    cols.op_c_memory.access_timestamp.diff_low_limb.val < 65536 ∧
    Word.isU64 #v[cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1],
      cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]]) ∧
  (¬cols.op_a_0 = 0 →
    op_a_write_value[0] = 0 ∧ op_a_write_value[1] = 0 ∧
    op_a_write_value[2] = 0 ∧ op_a_write_value[3] = 0) ∧
  (¬cols.imm_c = 0 →
    cols.op_c_memory.prev_value[0] = cols.op_c[0] ∧
    cols.op_c_memory.prev_value[1] = cols.op_c[1] ∧
    cols.op_c_memory.prev_value[2] = cols.op_c[2] ∧
    cols.op_c_memory.prev_value[3] = cols.op_c[3])

/-- The bridge to SP1: under `is_real = is_trusted = 1`, the ALU-type reader's
constraint list `allHold` is exactly `aluTypeReaderSpec`. -/
theorem aluTypeReaderSpec_iff_sp1
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {op_a_write_value : Word (ZMod p)}
    {cols : _root_.ALUTypeReader (ZMod p)} :
    (_root_.ALUTypeReader.constraints clk_high clk_low pc opcode op_a_write_value
        cols 1 1).allHold ↔
      aluTypeReaderSpec clk_low opcode pc op_a_write_value cols := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [show (_root_.ALUTypeReader.constraints clk_high clk_low pc opcode
        op_a_write_value cols 1 1).allHold
        = List.Forall SP1Constraint.toProp
            (_root_.ALUTypeReader.constraints clk_high clk_low pc opcode
              op_a_write_value cols 1 1) from rfl]
  rw [_root_.ALUTypeReader.allHold_constraints_iff_is_real rfl rfl]
  rfl

/-! ## `FormalAssertion` promotion

The bundle covers ProgramTable + 3 OperandAccess.assertionGated calls (op_a
and op_b with mult=1, op_c with mult = `1 - imm_c`) + 4 op_a_0 gates + 4
imm_c-equality gates. The full `aluTypeReaderSpec` is the Spec. -/

/-- Bundled inputs for the ALUTypeReader assertion. -/
structure Inputs (F : Type) where
  clk_low : F
  opcode : F
  pc : Vector F 3
  op_a_write_value : Vector F 4
  cols : _root_.ALUTypeReader F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Clean-side circuit: ProgramTable + 3 OperandAccess.assertionGated +
4 op_a_0 gates + 4 imm_c-equality gates. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨clk_low, opcode, pc, op_a_write_value,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩⟩ := input
  -- Program-bus interaction.
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode, op_a, #v[op_b, 0, 0, 0], op_c, op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Three per-operand byte-bus assertions via `assertionGated`.
  -- op_a/op_b: mult=1 (uniform with R/I-Type readers). op_c: mult=1-imm_c
  -- (vacuous on ADDIW rows where imm_c=1, matching SP1's `alu_type.rs:142`).
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
  SP1Clean.OperandAccess.assertionGated
    (⟨clk_low, 2, op_c_memory.access_timestamp.prev_low,
       op_c_memory.access_timestamp.diff_low_limb,
       op_c_memory.prev_value, 1 - imm_c⟩ :
      Var SP1Clean.OperandAccess.AssertionGated.Inputs (ZMod p))
  -- Four assertZero gates: op_a_0 * op_a_write_value[i] = 0.
  op_a_0 * op_a_write_value[0] === 0
  op_a_0 * op_a_write_value[1] === 0
  op_a_0 * op_a_write_value[2] === 0
  op_a_0 * op_a_write_value[3] === 0
  -- Four assertZero gates: imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0.
  -- When imm_c=1, forces op_c_memory.prev_value = op_c (the immediate value).
  imm_c * (op_c_memory.prev_value[0] - op_c[0]) === 0
  imm_c * (op_c_memory.prev_value[1] - op_c[1]) === 0
  imm_c * (op_c_memory.prev_value[2] - op_c[2]) === 0
  imm_c * (op_c_memory.prev_value[3] - op_c[3]) === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.ALUTypeReader"
  main := main
  -- Computed from main: 3 assertionGated × 24 witnesses = 72.
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The full `aluTypeReaderSpec` — same as the RHS of `aluTypeReaderSpec_iff_sp1`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  aluTypeReaderSpec input.clk_low input.opcode input.pc
    input.op_a_write_value input.cols

omit [Fact (2 ^ 17 < p)] [Fact (Nat.Prime p)] in
/-- `Word.isU64` on a whole `Vector` is equivalent to `Word.isU64` on its
`#v[w[0], w[1], w[2], w[3]]` re-indexed form. -/
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
          ⟨e_pv_c, e_pl_c, e_dll_c⟩, e_immc⟩ := h_input
  subst_eqs
  obtain ⟨h_prog_sub, h_oa_a_sub, h_oa_b_sub, h_oa_c_sub,
          h_z0, h_z1, h_z2, h_z3,
          h_im0, h_im1, h_im2, h_im3⟩ := h_holds
  have h_prog := h_prog_sub trivial
  -- op_a/op_b: mult=1, resolve via one_ne_zero.
  have h_oa_a := (h_oa_a_sub trivial).resolve_left one_ne_zero
  have h_oa_b := (h_oa_b_sub trivial).resolve_left one_ne_zero
  -- op_c: mult = 1 - imm_c; the disjunction stays.
  have h_oa_c_disj := h_oa_c_sub trivial
  simp only [SP1Clean.ProgramTable.assertion, SP1Clean.ProgramTable.Spec,
             SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
  obtain ⟨h_ti, h_op_a_lt, ⟨h_op_b_lt, _, _, _⟩,
          ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
          h_op_a_0_bin, h_op_a_0_iff, _, h_imm_c_bin,
          h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩ := h_prog
  simp only [Spec, aluTypeReaderSpec]
  refine ⟨h_ti, h_op_a_lt, h_op_b_lt,
          ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
          h_op_a_0_bin, h_op_a_0_iff, h_imm_c_bin,
          h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt,
          h_oa_a.1, h_oa_b.1, h_oa_b.2.1, h_oa_a.2.1,
          (isU64_iff_index_form _).mp h_oa_a.2.2,
          (isU64_iff_index_form _).mp h_oa_b.2.2,
          ?_, ?_, ?_⟩
  -- Clause: `imm_c = 0 → op_c memory byte/timestamp/U64 bounds`.
  · intro h_immc_zero
    -- mult = 1 - imm_c = 1 - 0 = 1 ≠ 0; extract right disjunct of h_oa_c_disj.
    have h_mult_ne : (1 + -Expression.eval env input_var_cols_imm_c) ≠ 0 := by
      rw [h_immc_zero]; simp
    have h_oa_c := h_oa_c_disj.resolve_left h_mult_ne
    refine ⟨h_oa_c.2.1, h_oa_c.1, (isU64_iff_index_form _).mp h_oa_c.2.2⟩
  -- Clause: `op_a_0 ≠ 0 → op_a_write_value[i] = 0`.
  · intro h_ne
    simp only [Vector.getElem_map]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact (mul_eq_zero.mp h_z0).resolve_left h_ne
    · exact (mul_eq_zero.mp h_z1).resolve_left h_ne
    · exact (mul_eq_zero.mp h_z2).resolve_left h_ne
    · exact (mul_eq_zero.mp h_z3).resolve_left h_ne
  -- Clause: `imm_c ≠ 0 → op_c_memory.prev_value = op_c`.
  · intro h_ne
    simp only [Vector.getElem_map]
    -- h_im_i : imm_c * (prev_value[i] + -op_c[i]) = 0. Resolve to the diff = 0
    -- side via mul_eq_zero, then convert `+ -` to `-` and use add_neg_eq_zero.
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact add_neg_eq_zero.mp ((mul_eq_zero.mp h_im0).resolve_left h_ne)
    · exact add_neg_eq_zero.mp ((mul_eq_zero.mp h_im1).resolve_left h_ne)
    · exact add_neg_eq_zero.mp ((mul_eq_zero.mp h_im2).resolve_left h_ne)
    · exact add_neg_eq_zero.mp ((mul_eq_zero.mp h_im3).resolve_left h_ne)

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨e_clk, e_opc, e_pc, e_oawv, e_oa,
          ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
          ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oc,
          ⟨e_pv_c, e_pl_c, e_dll_c⟩, e_immc⟩ := h_input
  subst_eqs
  simp only [Spec, aluTypeReaderSpec] at h_spec
  obtain ⟨h_ti, h_op_a_lt, h_op_b_lt,
          ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
          h_op_a_0_bin, h_op_a_0_iff, h_imm_c_bin,
          h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt,
          h_diff_a, h_diff_b, h_ts_b, h_ts_a, h_isU64_a, h_isU64_b,
          h_oc_imp, h_op_a_0_imp, h_imm_c_imp⟩ := h_spec
  have h_zero_lt : (0 : ZMod p) < (65536 : ZMod p) := by
    change (0 : ZMod p).val < (65536 : ZMod p).val
    have h65536 : (65536 : ZMod p).val = 65536 := by
      have hp : 2 ^ 17 < p := Fact.out
      rw [show (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) from by push_cast; rfl,
          ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
    simp [h65536]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  -- ProgramTable subcircuit obligation
  · refine ⟨trivial, ?_⟩
    simp only [SP1Clean.ProgramTable.assertion, SP1Clean.ProgramTable.Spec,
               SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
               List.getElem_cons_zero, List.getElem_cons_succ]
    exact ⟨h_ti, h_op_a_lt,
           ⟨h_op_b_lt, h_zero_lt, h_zero_lt, h_zero_lt⟩,
           ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
           h_op_a_0_bin, h_op_a_0_iff, Or.inl trivial, h_imm_c_bin,
           h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩
  -- OperandAccess for op_a (offset 4, mult=1) — right disjunct of assertionGated.Spec
  · refine ⟨trivial, ?_⟩
    right
    exact ⟨h_diff_a, h_ts_a, (isU64_iff_index_form _).mpr h_isU64_a⟩
  -- OperandAccess for op_b (offset 3, mult=1)
  · refine ⟨trivial, ?_⟩
    right
    exact ⟨h_diff_b, h_ts_b, (isU64_iff_index_form _).mpr h_isU64_b⟩
  -- OperandAccess for op_c (offset 2, mult=1-imm_c) — case-split on imm_c=0
  · refine ⟨trivial, ?_⟩
    by_cases h_immc_zero : Expression.eval env input_var_cols_imm_c = 0
    · -- mult = 1 - 0 = 1 ≠ 0; provide the right disjunct via h_oc_imp.
      right
      obtain ⟨h_ts_c, h_diff_c, h_isU64_c⟩ := h_oc_imp h_immc_zero
      exact ⟨h_diff_c, h_ts_c, (isU64_iff_index_form _).mpr h_isU64_c⟩
    · -- mult = 1 - imm_c ≠ 0? Well actually if imm_c ≠ 0 and imm_c is binary (0 or 1),
      -- then imm_c = 1, so mult = 0 — left disjunct.
      left
      rcases h_imm_c_bin with h0 | h1
      · exact absurd h0 h_immc_zero
      · simp [h1]
  -- 4 op_a_0 gates
  · by_cases h : Expression.eval env input_var_cols_op_a_0 = 0
    · simp [h]
    · have := (h_op_a_0_imp h).1
      rw [Vector.getElem_map] at this
      rw [this, mul_zero]
  · by_cases h : Expression.eval env input_var_cols_op_a_0 = 0
    · simp [h]
    · have := (h_op_a_0_imp h).2.1
      rw [Vector.getElem_map] at this
      rw [this, mul_zero]
  · by_cases h : Expression.eval env input_var_cols_op_a_0 = 0
    · simp [h]
    · have := (h_op_a_0_imp h).2.2.1
      rw [Vector.getElem_map] at this
      rw [this, mul_zero]
  · by_cases h : Expression.eval env input_var_cols_op_a_0 = 0
    · simp [h]
    · have := (h_op_a_0_imp h).2.2.2
      rw [Vector.getElem_map] at this
      rw [this, mul_zero]
  -- 4 imm_c-equality gates: imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0
  · by_cases h : Expression.eval env input_var_cols_imm_c = 0
    · simp [h]
    · have := (h_imm_c_imp h).1
      rw [Vector.getElem_map, Vector.getElem_map] at this
      rw [this]; ring
  · by_cases h : Expression.eval env input_var_cols_imm_c = 0
    · simp [h]
    · have := (h_imm_c_imp h).2.1
      rw [Vector.getElem_map, Vector.getElem_map] at this
      rw [this]; ring
  · by_cases h : Expression.eval env input_var_cols_imm_c = 0
    · simp [h]
    · have := (h_imm_c_imp h).2.2.1
      rw [Vector.getElem_map, Vector.getElem_map] at this
      rw [this]; ring
  · by_cases h : Expression.eval env input_var_cols_imm_c = 0
    · simp [h]
    · have := (h_imm_c_imp h).2.2.2
      rw [Vector.getElem_map, Vector.getElem_map] at this
      rw [this]; ring

end Assertion

/-- The Clean `FormalAssertion` for the full ALU-type reader spec
(`aluTypeReaderSpec`). Composes `ProgramTable.assertion`, three
`OperandAccess.assertionGated` calls (op_a/op_b with mult=1, op_c with
mult=1-imm_c), four `op_a_0 * op_a_write_value[i] = 0` scalar gates, and
four `imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0` scalar gates. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ALUTypeReader
