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
import SP1Clean.Reader.RegisterAccess
import SP1Clean.SP1Lookup

/-! # Reusable `ALUTypeReader` Spec helper + FormalAssertion

Packages the RHS of `_root_.ALUTypeReader.allHold_constraints_iff_is_real`
as a named predicate `aluTypeReaderSpec`. Differs from `rtypeReaderSpec` by
having `op_c` as a 4-limb `Word` and carrying an `imm_c` flag that gates the
op_c memory access (`imm_c = 0` ⇒ register read; `imm_c = 1` ⇒ immediate, with
`op_c_memory.prev_value` constrained to equal `op_c`).

Provides a complete `FormalAssertion` bundle:
- `ProgramTable.assertion` covering `trusted_instr`, register bounds, the
  4 op_c limb bounds, `op_a_0` binary/iff, `imm_c` binary, PC alignment.
- Three `RegisterAccess.assertion` calls (op_a/+4, op_b/+3 with mult=1;
  op_c/+2 with `mult := 1 - imm_c`). The op_c gating mirrors SP1's
  `alu_type.rs:142` (multiplicity `is_real - imm_c`); since the reader pins
  `is_real = 1`, this is equivalent to `1 - imm_c`. Each call bundles the
  byte-bus content (via `OperandAccess.assertionGated`) with two memory-bus
  emissions (send `prev_value`, receive `write_value`). For op_b/op_c
  (read-only) `write_value = prev_value`; for op_a (write)
  `write_value = op_a_write_value`.
- Four `op_a_0 * op_a_write_value[i] = 0` gates (enforcing the
  `op_a_0 ≠ 0 → op_a_write_value = 0` clause of the spec).
- Four `imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0` gates
  (enforcing the `imm_c = 1 → prev_value = op_c` clause; mirrors SP1's
  `alu_type.rs:170–177`).

All three add chips (`Add`, `Addi`, `Addw`) now route their byte/program/
memory lookups through a uniform reader subcircuit: `Add` →
`RTypeReader.assertion`, `Addi` → `ITypeReader.assertion`, `Addw` →
`ALUTypeReader.assertion`. -/

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

The bundle covers ProgramTable + 3 RegisterAccess calls (op_a/op_b with
mult=1, op_c with mult = `1 - imm_c`) + 4 op_a_0 gates + 4 imm_c-equality
gates. The full `aluTypeReaderSpec` is the Spec. -/

/-- Bundled inputs for the ALUTypeReader assertion. `clk_high` is threaded
through to the memory-bus emissions inside `RegisterAccess.assertion`. -/
structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  opcode : F
  pc : Vector F 3
  op_a_write_value : Vector F 4
  cols : _root_.ALUTypeReader F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Clean-side circuit: ProgramTable + 3 RegisterAccess.assertion + 4
op_a_0 gates + 4 imm_c-equality gates. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨clk_high, clk_low, opcode, pc, op_a_write_value,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩⟩ := input
  -- Program-bus interaction.
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode, op_a, #v[op_b, 0, 0, 0], op_c, op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- op_a: register-access write (mirrors Rust eval_register_access_write).
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 4, op_a, op_a_memory.prev_value, op_a_write_value,
       op_a_memory.access_timestamp.prev_low,
       op_a_memory.access_timestamp.diff_low_limb, 1⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  -- op_b: register-access read (mirrors Rust eval_register_access_read).
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 3, op_b, op_b_memory.prev_value, op_b_memory.prev_value,
       op_b_memory.access_timestamp.prev_low,
       op_b_memory.access_timestamp.diff_low_limb, 1⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  -- op_c: register-access read gated by `1 - imm_c` (vacuous on rows
  -- where imm_c=1, matching alu_type.rs:142). The Rust side uses
  -- `op_c[0]` as the register index (alu_type.rs:140).
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 2, op_c[0], op_c_memory.prev_value, op_c_memory.prev_value,
       op_c_memory.access_timestamp.prev_low,
       op_c_memory.access_timestamp.diff_low_limb, 1 - imm_c⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
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
  obtain ⟨e_ckh, e_clk, e_opc, e_pc, e_oawv, e_oa,
          ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
          ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oc,
          ⟨e_pv_c, e_pl_c, e_dll_c⟩, e_immc⟩ := h_input
  subst_eqs
  obtain ⟨h_prog_sub, h_ra_a_sub, h_ra_b_sub, h_ra_c_sub,
          h_z0, h_z1, h_z2, h_z3,
          h_im0, h_im1, h_im2, h_im3⟩ := h_holds
  have h_prog := h_prog_sub trivial
  -- op_a/op_b: mult=1, resolve via one_ne_zero.
  have h_ra_a := (h_ra_a_sub trivial).resolve_left one_ne_zero
  have h_ra_b := (h_ra_b_sub trivial).resolve_left one_ne_zero
  -- op_c: mult = 1 - imm_c; the disjunction stays.
  have h_ra_c_disj := h_ra_c_sub trivial
  simp only [SP1Clean.ProgramTable.assertion, SP1Clean.ProgramTable.Spec,
             SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
  obtain ⟨h_ti, h_op_a_lt, ⟨h_op_b_lt, _, _, _⟩,
          ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
          h_op_a_0_bin, h_op_a_0_iff, _, h_imm_c_bin,
          h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩ := h_prog
  simp only [aluTypeReaderSpec]
  refine ⟨h_ti, h_op_a_lt, h_op_b_lt,
          ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
          h_op_a_0_bin, h_op_a_0_iff, h_imm_c_bin,
          h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt,
          h_ra_a.1, h_ra_b.1, h_ra_b.2.1, h_ra_a.2.1,
          (isU64_iff_index_form _).mp h_ra_a.2.2,
          (isU64_iff_index_form _).mp h_ra_b.2.2,
          ?_, ?_, ?_⟩
  -- Clause: `imm_c = 0 → op_c memory byte/timestamp/U64 bounds`.
  · intro h_immc_zero
    -- mult = 1 - imm_c = 1 - 0 = 1 ≠ 0; extract right disjunct of h_ra_c_disj.
    have h_mult_ne : (1 + -Expression.eval env input_var_cols_imm_c) ≠ 0 := by
      rw [h_immc_zero]; simp
    have h_ra_c := h_ra_c_disj.resolve_left h_mult_ne
    refine ⟨h_ra_c.2.1, h_ra_c.1, (isU64_iff_index_form _).mp h_ra_c.2.2⟩
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
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact add_neg_eq_zero.mp ((mul_eq_zero.mp h_im0).resolve_left h_ne)
    · exact add_neg_eq_zero.mp ((mul_eq_zero.mp h_im1).resolve_left h_ne)
    · exact add_neg_eq_zero.mp ((mul_eq_zero.mp h_im2).resolve_left h_ne)
    · exact add_neg_eq_zero.mp ((mul_eq_zero.mp h_im3).resolve_left h_ne)

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨e_ckh, e_clk, e_opc, e_pc, e_oawv, e_oa,
          ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
          ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oc,
          ⟨e_pv_c, e_pl_c, e_dll_c⟩, e_immc⟩ := h_input
  subst_eqs
  simp only [aluTypeReaderSpec] at h_spec
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
  -- RegisterAccess for op_a (offset 4, mult=1) — right disjunct of
  -- OperandAccess.AssertionGated.Spec.
  · refine ⟨trivial, ?_⟩
    right
    exact ⟨h_diff_a, h_ts_a, (isU64_iff_index_form _).mpr h_isU64_a⟩
  -- RegisterAccess for op_b (offset 3, mult=1)
  · refine ⟨trivial, ?_⟩
    right
    exact ⟨h_diff_b, h_ts_b, (isU64_iff_index_form _).mpr h_isU64_b⟩
  -- RegisterAccess for op_c (offset 2, mult=1-imm_c) — case-split on imm_c=0
  · refine ⟨trivial, ?_⟩
    by_cases h_immc_zero : Expression.eval env input_var_cols_imm_c = 0
    · -- mult = 1 - 0 = 1 ≠ 0; provide the right disjunct via h_oc_imp.
      right
      obtain ⟨h_ts_c, h_diff_c, h_isU64_c⟩ := h_oc_imp h_immc_zero
      exact ⟨h_diff_c, h_ts_c, (isU64_iff_index_form _).mpr h_isU64_c⟩
    · -- mult = 1 - imm_c ≠ 0? If imm_c ≠ 0 and imm_c is binary (0 or 1),
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
      rw [this]; ring_nf
  · by_cases h : Expression.eval env input_var_cols_imm_c = 0
    · simp [h]
    · have := (h_imm_c_imp h).2.1
      rw [Vector.getElem_map, Vector.getElem_map] at this
      rw [this]; ring_nf
  · by_cases h : Expression.eval env input_var_cols_imm_c = 0
    · simp [h]
    · have := (h_imm_c_imp h).2.2.1
      rw [Vector.getElem_map, Vector.getElem_map] at this
      rw [this]; ring_nf
  · by_cases h : Expression.eval env input_var_cols_imm_c = 0
    · simp [h]
    · have := (h_imm_c_imp h).2.2.2
      rw [Vector.getElem_map, Vector.getElem_map] at this
      rw [this]; ring_nf

end Assertion

/-- The Clean `FormalAssertion` for the full ALU-type reader spec
(`aluTypeReaderSpec`). Composes `ProgramTable.assertion`, three
`RegisterAccess.assertion` calls (op_a/op_b with mult=1, op_c with
mult=1-imm_c), four `op_a_0 * op_a_write_value[i] = 0` scalar gates, and
four `imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0` scalar gates. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-! ## Flag-threaded variant (`Gated`)

Mirrors Rust's `eval_alu_type(cols, ..., is_real, is_trusted)`. The op_c
register-access multiplicity is `is_real - imm_c` (mirrors `alu_type.rs:142`).
On rows with `imm_c = 1` the op_c memory access is vacuous; on `imm_c = 0`
and `is_real = 1` it's active. -/

namespace Gated

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  opcode : F
  pc : Vector F 3
  op_a_write_value : Vector F 4
  cols : _root_.ALUTypeReader F
  is_real : F
  is_trusted : F
deriving ProvableStruct

namespace Assertion

open Circuit

@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨clk_high, clk_low, opcode, pc, op_a_write_value,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩,
       is_real, is_trusted⟩ := input
  is_real * (is_real - 1) === 0
  SP1Clean.programGated
    (⟨#v[pc[0], pc[1], pc[2], opcode, op_a, op_b, 0, 0, 0,
         op_c[0], op_c[1], op_c[2], op_c[3], op_a_0, 0, imm_c],
       is_trusted⟩ : Var SP1Clean.ProgramGated.Inputs (ZMod p))
  -- op_a: write, gated by is_real
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 4, op_a, op_a_memory.prev_value, op_a_write_value,
       op_a_memory.access_timestamp.prev_low,
       op_a_memory.access_timestamp.diff_low_limb, is_real⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  -- op_b: read, gated by is_real
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 3, op_b, op_b_memory.prev_value, op_b_memory.prev_value,
       op_b_memory.access_timestamp.prev_low,
       op_b_memory.access_timestamp.diff_low_limb, is_real⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  -- op_c: read, gated by `is_real - imm_c` (mirrors Rust alu_type.rs:142)
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 2, op_c[0], op_c_memory.prev_value, op_c_memory.prev_value,
       op_c_memory.access_timestamp.prev_low,
       op_c_memory.access_timestamp.diff_low_limb, is_real - imm_c⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  op_a_0 * op_a_write_value[0] === 0
  op_a_0 * op_a_write_value[1] === 0
  op_a_0 * op_a_write_value[2] === 0
  op_a_0 * op_a_write_value[3] === 0
  imm_c * (op_c_memory.prev_value[0] - op_c[0]) === 0
  imm_c * (op_c_memory.prev_value[1] - op_c[1]) === 0
  imm_c * (op_c_memory.prev_value[2] - op_c[2]) === 0
  imm_c * (op_c_memory.prev_value[3] - op_c[3]) === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.ALUTypeReader.Gated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

def Spec (input : Inputs (ZMod p)) : Prop :=
  let ⟨clk_high, clk_low, opcode, pc, op_a_write_value,
       cols, is_real, is_trusted⟩ := input
  is_real * (is_real - 1) = 0 ∧
  SP1Clean.ProgramGated.Spec
    ⟨#v[pc[0], pc[1], pc[2], opcode, cols.op_a, cols.op_b, 0, 0, 0,
        cols.op_c[0], cols.op_c[1], cols.op_c[2], cols.op_c[3],
        cols.op_a_0, 0, cols.imm_c],
     is_trusted⟩ ∧
  SP1Clean.RegisterAccess.Assertion.Spec
    ⟨clk_high, clk_low, 4, cols.op_a, cols.op_a_memory.prev_value,
     op_a_write_value, cols.op_a_memory.access_timestamp.prev_low,
     cols.op_a_memory.access_timestamp.diff_low_limb, is_real⟩ ∧
  SP1Clean.RegisterAccess.Assertion.Spec
    ⟨clk_high, clk_low, 3, cols.op_b, cols.op_b_memory.prev_value,
     cols.op_b_memory.prev_value, cols.op_b_memory.access_timestamp.prev_low,
     cols.op_b_memory.access_timestamp.diff_low_limb, is_real⟩ ∧
  SP1Clean.RegisterAccess.Assertion.Spec
    ⟨clk_high, clk_low, 2, cols.op_c[0], cols.op_c_memory.prev_value,
     cols.op_c_memory.prev_value, cols.op_c_memory.access_timestamp.prev_low,
     cols.op_c_memory.access_timestamp.diff_low_limb, is_real - cols.imm_c⟩ ∧
  cols.op_a_0 * op_a_write_value[0] = 0 ∧
  cols.op_a_0 * op_a_write_value[1] = 0 ∧
  cols.op_a_0 * op_a_write_value[2] = 0 ∧
  cols.op_a_0 * op_a_write_value[3] = 0 ∧
  cols.imm_c * (cols.op_c_memory.prev_value[0] - cols.op_c[0]) = 0 ∧
  cols.imm_c * (cols.op_c_memory.prev_value[1] - cols.op_c[1]) = 0 ∧
  cols.imm_c * (cols.op_c_memory.prev_value[2] - cols.op_c[2]) = 0 ∧
  cols.imm_c * (cols.op_c_memory.prev_value[3] - cols.op_c[3]) = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨e_ckh, e_cl, e_opc, e_pc, e_oawv,
          ⟨e_oa, ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
           ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oc,
           ⟨e_pv_c, e_pl_c, e_dll_c⟩, e_immc⟩,
          e_ir, e_it⟩ := h_input
  subst_eqs
  obtain ⟨h_gate, h_prog_sub, h_ra_a_sub, h_ra_b_sub, h_ra_c_sub,
          h_z0, h_z1, h_z2, h_z3, h_im0, h_im1, h_im2, h_im3⟩ := h_holds
  simp only [Spec, sub_eq_add_neg, Vector.getElem_map]
  exact ⟨h_gate, h_prog_sub trivial, h_ra_a_sub trivial, h_ra_b_sub trivial,
         h_ra_c_sub trivial, h_z0, h_z1, h_z2, h_z3,
         h_im0, h_im1, h_im2, h_im3⟩

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨e_ckh, e_cl, e_opc, e_pc, e_oawv,
          ⟨e_oa, ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
           ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oc,
           ⟨e_pv_c, e_pl_c, e_dll_c⟩, e_immc⟩,
          e_ir, e_it⟩ := h_input
  subst_eqs
  simp only [Spec, sub_eq_add_neg, Vector.getElem_map] at h_spec
  obtain ⟨h_gate, h_prog, h_ra_a, h_ra_b, h_ra_c,
          h_z0, h_z1, h_z2, h_z3, h_im0, h_im1, h_im2, h_im3⟩ := h_spec
  exact ⟨h_gate, ⟨trivial, h_prog⟩, ⟨trivial, h_ra_a⟩, ⟨trivial, h_ra_b⟩,
         ⟨trivial, h_ra_c⟩, h_z0, h_z1, h_z2, h_z3,
         h_im0, h_im1, h_im2, h_im3⟩

end Assertion

def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-- Bridge from SP1-native `ALUTypeReader.constraints.allHold` (under
`is_real = is_trusted = 1` pinning) to the literal sub-circuit conjunction
`Gated.Assertion.Spec ⟨..., 1, 1⟩`. The pinned form is sufficient for
chip-level `allHold_iff_structural` proofs (which always specialize via
`h_is_real : Main[N-1] = 1`).

Unlike R/I-type, the ALU bridge is necessarily pinned: SP1's
`_root_.ALUTypeReader.allHold_constraints_iff` carries two extra conjuncts
(`is_real = 0 → imm_c = 0` and `(is_real - imm_c) * (is_real - imm_c - 1)
= 0`) that the flag-threaded `Gated.Spec` does NOT carry — they become
trivial / derivable from `ProgramSpec`'s `imm_c` binary clause under
`is_real = 1`. -/
theorem Assertion.Spec_iff_sp1
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {op_a_write_value : Word (ZMod p)}
    {cols : _root_.ALUTypeReader (ZMod p)} :
    (_root_.ALUTypeReader.constraints clk_high clk_low pc opcode op_a_write_value
        cols 1 1).allHold ↔
      Assertion.Spec ⟨clk_high, clk_low, opcode, pc, op_a_write_value, cols,
                      1, 1⟩ := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  rw [aluTypeReaderSpec_iff_sp1]
  have h_0_lt_65536 : (0 : ZMod p) < (65536 : ZMod p) := by
    change (0 : ZMod p).val < (65536 : ZMod p).val; simp
  simp only [Assertion.Spec, aluTypeReaderSpec,
    SP1Clean.ProgramGated.Spec, SP1Clean.ProgramSpec,
    SP1Clean.RegisterAccess.Assertion.Spec,
    SP1Clean.OperandAccess.AssertionGated.Spec,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  refine ⟨?_, ?_⟩
  -- → direction.
  · rintro ⟨h_ti, h_op_a, h_op_b, ⟨h_oc0, h_oc1, h_oc2, h_oc3⟩,
            h_op_a_0_bin, h_op_a_0_iff, h_immc_bin,
            h_pc0_mod, h_pc0_lt, h_pc1_lt, h_pc2_lt,
            h_diff_a, h_diff_b, h_ts_b, h_ts_a, h_isU64_a, h_isU64_b,
            h_immc_zero_facts, h_op_a_0_imp, h_immc_eq⟩
    have h_z0 : cols.op_a_0 * op_a_write_value[0] = 0 := by
      by_cases h0 : cols.op_a_0 = 0
      · rw [h0]; ring
      · rw [(h_op_a_0_imp h0).1]; ring
    have h_z1 : cols.op_a_0 * op_a_write_value[1] = 0 := by
      by_cases h0 : cols.op_a_0 = 0
      · rw [h0]; ring
      · rw [(h_op_a_0_imp h0).2.1]; ring
    have h_z2 : cols.op_a_0 * op_a_write_value[2] = 0 := by
      by_cases h0 : cols.op_a_0 = 0
      · rw [h0]; ring
      · rw [(h_op_a_0_imp h0).2.2.1]; ring
    have h_z3 : cols.op_a_0 * op_a_write_value[3] = 0 := by
      by_cases h0 : cols.op_a_0 = 0
      · rw [h0]; ring
      · rw [(h_op_a_0_imp h0).2.2.2]; ring
    have h_imc0 : cols.imm_c * (cols.op_c_memory.prev_value[0] - cols.op_c[0]) = 0 := by
      by_cases h0 : cols.imm_c = 0
      · rw [h0]; ring
      · have h_eq := (h_immc_eq h0).1
        linear_combination cols.imm_c * h_eq
    have h_imc1 : cols.imm_c * (cols.op_c_memory.prev_value[1] - cols.op_c[1]) = 0 := by
      by_cases h0 : cols.imm_c = 0
      · rw [h0]; ring
      · have h_eq := (h_immc_eq h0).2.1
        linear_combination cols.imm_c * h_eq
    have h_imc2 : cols.imm_c * (cols.op_c_memory.prev_value[2] - cols.op_c[2]) = 0 := by
      by_cases h0 : cols.imm_c = 0
      · rw [h0]; ring
      · have h_eq := (h_immc_eq h0).2.2.1
        linear_combination cols.imm_c * h_eq
    have h_imc3 : cols.imm_c * (cols.op_c_memory.prev_value[3] - cols.op_c[3]) = 0 := by
      by_cases h0 : cols.imm_c = 0
      · rw [h0]; ring
      · have h_eq := (h_immc_eq h0).2.2.2
        linear_combination cols.imm_c * h_eq
    refine ⟨by ring, ?_, ?_, ?_, ?_,
            h_z0, h_z1, h_z2, h_z3, h_imc0, h_imc1, h_imc2, h_imc3⟩
    -- ProgramGated.Spec ⟨..., 1⟩ = `1 = 0 ∨ ProgramSpec entry` ↔ ProgramSpec entry.
    · right
      exact ⟨h_ti, h_op_a,
             ⟨h_op_b, h_0_lt_65536, h_0_lt_65536, h_0_lt_65536⟩,
             ⟨h_oc0, h_oc1, h_oc2, h_oc3⟩,
             h_op_a_0_bin, h_op_a_0_iff, Or.inl trivial, h_immc_bin,
             h_pc0_mod, h_pc0_lt, h_pc1_lt, h_pc2_lt⟩
    -- RegisterAccess.Spec ⟨..., 1⟩ for op_a (offset +4).
    · right
      exact ⟨h_diff_a, h_ts_a,
             (SP1Clean.ALUTypeReader.Assertion.isU64_iff_index_form _).mpr h_isU64_a⟩
    -- RegisterAccess.Spec ⟨..., 1⟩ for op_b (offset +3).
    · right
      exact ⟨h_diff_b, h_ts_b,
             (SP1Clean.ALUTypeReader.Assertion.isU64_iff_index_form _).mpr h_isU64_b⟩
    -- RegisterAccess.Spec ⟨..., 1 - imm_c⟩ for op_c (offset +2).
    · by_cases h_imm_c_one : (1 : ZMod p) - cols.imm_c = 0
      · exact Or.inl h_imm_c_one
      · right
        -- 1 - imm_c ≠ 0 ↔ imm_c ≠ 1 ↔ imm_c = 0 (under binary).
        have h_imm_c_zero : cols.imm_c = 0 := by
          rcases h_immc_bin with h | h
          · exact h
          · exfalso; apply h_imm_c_one; rw [h]; ring
        obtain ⟨h_ts_c, h_diff_c, h_isU64_c⟩ := h_immc_zero_facts h_imm_c_zero
        exact ⟨h_diff_c, h_ts_c,
               (SP1Clean.ALUTypeReader.Assertion.isU64_iff_index_form _).mpr h_isU64_c⟩
  -- ← direction.
  · rintro ⟨_h_ir_bin, h_prog_disj, h_ra_a_disj, h_ra_b_disj, h_ra_c_disj,
            h_z0, h_z1, h_z2, h_z3, h_imc0, h_imc1, h_imc2, h_imc3⟩
    -- Resolve ProgramGated.Spec: 1 ≠ 0, so disjunct gives ProgramSpec.
    have h_one_ne_zero : (1 : ZMod p) ≠ 0 := one_ne_zero
    have h_ps := h_prog_disj.resolve_left h_one_ne_zero
    obtain ⟨h_ti, h_op_a, ⟨h_op_b, _, _, _⟩, ⟨h_oc0, h_oc1, h_oc2, h_oc3⟩,
            h_op_a_0_bin, h_op_a_0_iff, _h_imm_b_bin, h_immc_bin,
            h_pc0_mod, h_pc0_lt, h_pc1_lt, h_pc2_lt⟩ := h_ps
    -- Resolve op_a/op_b RegisterAccess.Specs (mult = 1 ≠ 0).
    have h_a := h_ra_a_disj.resolve_left h_one_ne_zero
    have h_b := h_ra_b_disj.resolve_left h_one_ne_zero
    -- op_a_0 zero-tuple from 4× mul gates.
    have h_op_a_0_imp : cols.op_a_0 ≠ 0 →
        op_a_write_value[0] = 0 ∧ op_a_write_value[1] = 0 ∧
        op_a_write_value[2] = 0 ∧ op_a_write_value[3] = 0 := by
      intro h_op_a_0_ne
      exact ⟨(mul_eq_zero.mp h_z0).resolve_left h_op_a_0_ne,
             (mul_eq_zero.mp h_z1).resolve_left h_op_a_0_ne,
             (mul_eq_zero.mp h_z2).resolve_left h_op_a_0_ne,
             (mul_eq_zero.mp h_z3).resolve_left h_op_a_0_ne⟩
    -- imm_c → op_c = prev_value: from 4× imm_c mul gates.
    have h_immc_eq : ¬cols.imm_c = 0 →
        cols.op_c_memory.prev_value[0] = cols.op_c[0] ∧
        cols.op_c_memory.prev_value[1] = cols.op_c[1] ∧
        cols.op_c_memory.prev_value[2] = cols.op_c[2] ∧
        cols.op_c_memory.prev_value[3] = cols.op_c[3] := by
      intro h_immc_ne
      have h0 : cols.op_c_memory.prev_value[0] - cols.op_c[0] = 0 :=
        (mul_eq_zero.mp h_imc0).resolve_left h_immc_ne
      have h1 : cols.op_c_memory.prev_value[1] - cols.op_c[1] = 0 :=
        (mul_eq_zero.mp h_imc1).resolve_left h_immc_ne
      have h2 : cols.op_c_memory.prev_value[2] - cols.op_c[2] = 0 :=
        (mul_eq_zero.mp h_imc2).resolve_left h_immc_ne
      have h3 : cols.op_c_memory.prev_value[3] - cols.op_c[3] = 0 :=
        (mul_eq_zero.mp h_imc3).resolve_left h_immc_ne
      exact ⟨sub_eq_zero.mp h0, sub_eq_zero.mp h1, sub_eq_zero.mp h2,
             sub_eq_zero.mp h3⟩
    -- imm_c = 0 → op_c facts: extract from op_c's RegisterAccess.Spec.
    have h_immc_zero_facts : cols.imm_c = 0 →
        (clk_low + 2 - cols.op_c_memory.access_timestamp.prev_low - 1 -
              cols.op_c_memory.access_timestamp.diff_low_limb) *
            (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
        cols.op_c_memory.access_timestamp.diff_low_limb.val < 65536 ∧
        Word.isU64 #v[cols.op_c_memory.prev_value[0], cols.op_c_memory.prev_value[1],
          cols.op_c_memory.prev_value[2], cols.op_c_memory.prev_value[3]] := by
      intro h_imm_c_zero
      -- Under imm_c = 0, `1 - imm_c = 1 ≠ 0`, resolves op_c disjunct.
      have h_one_sub_ne : (1 : ZMod p) - cols.imm_c ≠ 0 := by
        rw [h_imm_c_zero, sub_zero]; exact one_ne_zero
      have h_c := h_ra_c_disj.resolve_left h_one_sub_ne
      exact ⟨h_c.2.1, h_c.1,
             (SP1Clean.ALUTypeReader.Assertion.isU64_iff_index_form _).mp h_c.2.2⟩
    exact ⟨h_ti, h_op_a, h_op_b, ⟨h_oc0, h_oc1, h_oc2, h_oc3⟩,
           h_op_a_0_bin, h_op_a_0_iff, h_immc_bin,
           h_pc0_mod, h_pc0_lt, h_pc1_lt, h_pc2_lt,
           h_a.1, h_b.1, h_b.2.1, h_a.2.1,
           (SP1Clean.ALUTypeReader.Assertion.isU64_iff_index_form _).mp h_a.2.2,
           (SP1Clean.ALUTypeReader.Assertion.isU64_iff_index_form _).mp h_b.2.2,
           h_immc_zero_facts, h_op_a_0_imp, h_immc_eq⟩

/-- Extract `Word.isU64` of `op_b_memory.prev_value` from a witness of
`Gated.Assertion.Spec` under `is_real = 1`. The bound lives inside the
4th conjunct (op_b `RegisterAccess.Assertion.Spec`, offset 3), which
unfolds to an `OperandAccess.AssertionGated.Spec` disjunction `mult = 0
∨ (… ∧ … ∧ Word.isU64 prev_value)`; under `is_real ≠ 0` (forced by
`is_real = 1`) the disjunction's left branch is closed and the
`Word.isU64` projection falls out by `.2.2`.

Mirrors `RTypeReader.Gated.Assertion.isU64_operands_of_spec`, but only
the `op_b` extraction (the analogous `op_c` extraction needs a case
split on `imm_c`; see `isU64_op_c_memory_of_spec`). Shared by every ALU
chip whose `FormalAssertion` composes `ALUTypeReader.Gated.assertion`. -/
lemma Assertion.isU64_op_b_of_spec
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {op_a_write_value : Vector (ZMod p) 4}
    {cols : _root_.ALUTypeReader (ZMod p)}
    {is_real is_trusted : ZMod p}
    (h_is_real : is_real = 1)
    (h_spec : Assertion.Spec
        ⟨clk_high, clk_low, opcode, pc, op_a_write_value,
         cols, is_real, is_trusted⟩) :
    Word.isU64 cols.op_b_memory.prev_value := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_ne : is_real ≠ 0 := by rw [h_is_real]; exact one_ne_zero
  exact (h_spec.2.2.2.1.resolve_left h_ne).2.2

/-- Extract `Word.isU64` of `op_c_memory.prev_value` from a witness of
`Gated.Assertion.Spec` under `is_real = 1` ∧ `is_trusted = 1`. The
bound is derived by case-splitting on `imm_c ∈ {0, 1}` (binary fact
from `ProgramSpec`):
- `imm_c = 0`: op_c is a register operand, gate `is_real - imm_c = 1 ≠
  0` resolves the 5th conjunct's `RegisterAccess.Spec` disjunction and
  yields `Word.isU64 prev_value` directly via `.2.2`.
- `imm_c = 1`: the four trailing `imm_c * (prev_value[i] - op_c[i]) = 0`
  gates force `prev_value = op_c`, and `op_c`'s byte bounds (from
  `ProgramSpec.op_c_lt`) reconstruct `Word.isU64 op_c` via
  `Word.isU64_of_cases`. Both branches yield the same conclusion.

The `h_trusted` hypothesis (`is_trusted = 1`) is needed to navigate the
`ProgramGated.Spec` disjunction so the inner `ProgramSpec`'s op_c byte
bounds and `imm_c` binary fact are accessible. Used by every ALU-type
chip's `FormalAssertion` to discharge `AddwOp.Assumptions` /
`SubwOp.Assumptions` `Word.isU64 c` obligations. -/
lemma Assertion.isU64_op_c_memory_of_spec
    {clk_high clk_low opcode : ZMod p}
    {pc : Vector (ZMod p) 3}
    {op_a_write_value : Vector (ZMod p) 4}
    {cols : _root_.ALUTypeReader (ZMod p)}
    {is_real is_trusted : ZMod p}
    (h_is_real : is_real = 1)
    (h_trusted : is_trusted = 1)
    (h_spec : Assertion.Spec
        ⟨clk_high, clk_low, opcode, pc, op_a_write_value,
         cols, is_real, is_trusted⟩) :
    Word.isU64 cols.op_c_memory.prev_value := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h_t_ne : is_trusted ≠ 0 := by rw [h_trusted]; exact one_ne_zero
  -- Unpack to expose the named sub-conjuncts.
  obtain ⟨_h_ir_bin, h_prog, _h_ra_a, _h_ra_b, h_ra_c, _, _, _, _,
          h_im0, h_im1, h_im2, h_im3⟩ := h_spec
  have h_ps := h_prog.resolve_left h_t_ne
  obtain ⟨_h_ti, _h_op_a_lt, _h_op_b_lt, h_op_c_lt,
          _, _, _h_imm_b_bin, h_imm_c_bin, _⟩ := h_ps
  obtain ⟨h_oc0_lt, h_oc1_lt, h_oc2_lt, h_oc3_lt⟩ := h_op_c_lt
  by_cases h_imm_c : cols.imm_c = 0
  · -- imm_c = 0: op_c is a register operand; gate `is_real - imm_c = 1` ≠ 0.
    have h_ir_imm_ne_zero : is_real - cols.imm_c ≠ 0 := by
      rw [h_is_real, h_imm_c]; simp
    exact (h_ra_c.resolve_left h_ir_imm_ne_zero).2.2
  · -- imm_c = 1: prev_value = op_c via the four imm_c masked gates; op_c
    -- byte bounds give Word.isU64 op_c.
    have h_imm_c_one : cols.imm_c = (1 : ZMod p) := by
      rcases h_imm_c_bin with h | h
      · exact absurd (by simpa using h) h_imm_c
      · simpa using h
    have h_pv0 : cols.op_c_memory.prev_value[0] = cols.op_c[0] := by
      rw [h_imm_c_one, one_mul] at h_im0; linear_combination h_im0
    have h_pv1 : cols.op_c_memory.prev_value[1] = cols.op_c[1] := by
      rw [h_imm_c_one, one_mul] at h_im1; linear_combination h_im1
    have h_pv2 : cols.op_c_memory.prev_value[2] = cols.op_c[2] := by
      rw [h_imm_c_one, one_mul] at h_im2; linear_combination h_im2
    have h_pv3 : cols.op_c_memory.prev_value[3] = cols.op_c[3] := by
      rw [h_imm_c_one, one_mul] at h_im3; linear_combination h_im3
    have h_65536_val : (65536 : ZMod p).val = 65536 := by
      rw [show (65536 : ZMod p) = ((65536 : ℕ) : ZMod p) from by push_cast; rfl]
      have hp : 2 ^ 17 < p := Fact.out
      rw [ZMod.val_natCast_of_lt (by omega)]
    apply Word.isU64_of_cases
    · simp only [h_pv0]
      have : cols.op_c[0].val < (65536 : ZMod p).val := h_oc0_lt
      rw [h_65536_val] at this; exact (by simpa using this)
    · simp only [h_pv1]
      have : cols.op_c[1].val < (65536 : ZMod p).val := h_oc1_lt
      rw [h_65536_val] at this; exact (by simpa using this)
    · simp only [h_pv2]
      have : cols.op_c[2].val < (65536 : ZMod p).val := h_oc2_lt
      rw [h_65536_val] at this; exact (by simpa using this)
    · simp only [h_pv3]
      have : cols.op_c[3].val < (65536 : ZMod p).val := h_oc3_lt
      rw [h_65536_val] at this; exact (by simpa using this)

end Gated

end SP1Clean.ALUTypeReader
