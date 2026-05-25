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

/-! # Reusable `ALUTypeReader` Spec helper + FormalAssertion

Packages the RHS of `_root_.ALUTypeReader.allHold_constraints_iff_is_real`
as a named predicate `aluTypeReaderSpec`. Differs from `rtypeReaderSpec` by
having `op_c` as a 4-limb `Word` and carrying an `imm_c` flag that gates the
op_c memory access (`imm_c = 0` ⇒ register read; `imm_c = 1` ⇒ immediate, with
`op_c_memory.prev_value` constrained to equal `op_c`).

Also provides a partial `FormalAssertion` bundle that covers the
unconditional portion of the spec: `ProgramTable.assertion` (covers
`trusted_instr`, register bounds, the 4 op_c limb bounds, `op_a_0`
binary/iff, `imm_c` binary, PC alignment), two unconditional
`OperandAccess.assertion` calls for op_a/+4 and op_b/+3, and four
`op_a_0 * op_a_write_value[i] = 0` gates.

**Not included** in the assertion bundle (deferred to chip-level
`Assertion.main`):
- The op_c memory-bus `OperandAccess` (SP1 emits it gated by `is_real - imm_c`,
  so it doesn't fire in the I-type case; clean mirroring requires conditional
  emission which the existing chip-level patterns handle directly).
- The 4 `imm_c * (op_c_memory.prev_value[i] - op_c[i]) = 0` gates (likewise
  carried inline at the chip level, matching the flat `SP1Clean.Addw.Assertion`
  pattern).

The Spec the assertion bundle exposes (`aluTypeReaderSpecCore`) is therefore
strictly weaker than `aluTypeReaderSpec`; the chip-level FormalSpec composes
both. -/

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

/-! ## `FormalAssertion` promotion (partial — `core` slice only)

The bundle covers ProgramTable + 2 unconditional OperandAccess (op_a, op_b)
+ 4 op_a_0 gates. The op_c memory access and the imm_c-equality gates are
left to chip-level `Assertion.main` because they're conditionally gated in
the SP1 source and don't lift cleanly through `OperandAccess.assertion`
(which has no gating). -/

/-- Bundled inputs for the ALUTypeReader assertion. -/
structure Inputs (F : Type) where
  clk_low : F
  opcode : F
  pc : Vector F 3
  op_a_write_value : Vector F 4
  cols : _root_.ALUTypeReader F
deriving ProvableStruct

/-- The "core" portion of `aluTypeReaderSpec` derivable from a single
ProgramTable + 2 unconditional OperandAccess + 4 `op_a_0 * op_a_write_value[i]`
gates. Drops the op_c memory bounds (conditionally gated in SP1) and the
imm_c-equality clause. The chip-level FormalSpec composes this with the
extra clauses. -/
def aluTypeReaderSpecCore
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
  (¬cols.op_a_0 = 0 →
    op_a_write_value[0] = 0 ∧ op_a_write_value[1] = 0 ∧
    op_a_write_value[2] = 0 ∧ op_a_write_value[3] = 0)

namespace Assertion

open Circuit

/-- Clean-side circuit: ProgramTable + 2 OperandAccess + 4 op_a_0 gates.
The op_c OperandAccess and 4 imm_c gates are emitted at the chip level. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨clk_low, opcode, pc, op_a_write_value,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, _op_c_memory, imm_c⟩⟩ := input
  -- Program-bus interaction (covers trusted_instr + register bounds +
  -- 4 op_c limb bounds + op_a_0 binary/iff + imm_c binary + PC alignment+bounds).
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode, op_a, #v[op_b, 0, 0, 0], op_c, op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Two per-operand byte-bus assertions. Sub-clock offsets follow the
  -- ALU-type convention: op_a at +4, op_b at +3.
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
  -- Four assertZero gates: op_a_0 * op_a_write_value[i] = 0.
  op_a_0 * op_a_write_value[0] === 0
  op_a_0 * op_a_write_value[1] === 0
  op_a_0 * op_a_write_value[2] === 0
  op_a_0 * op_a_write_value[3] === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.ALUTypeReader"
  main := main
  localLength _ := 0

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The "core" portion of `aluTypeReaderSpec` — same as the RHS of
`aluTypeReaderSpec_iff_sp1` minus the imm_c-gated clauses. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  aluTypeReaderSpecCore input.clk_low input.opcode input.pc
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
  obtain ⟨h_prog_sub, h_oa_a_sub, h_oa_b_sub,
          h_z0, h_z1, h_z2, h_z3⟩ := h_holds
  have h_prog := h_prog_sub trivial
  have h_oa_a := h_oa_a_sub trivial
  have h_oa_b := h_oa_b_sub trivial
  simp only [SP1Clean.ProgramTable.assertion, SP1Clean.ProgramTable.Spec,
             SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
  simp only [SP1Clean.OperandAccess.assertion, SP1Clean.OperandAccess.Assertion.Spec]
    at h_oa_a h_oa_b
  obtain ⟨h_ti, h_op_a_lt, ⟨h_op_b_lt, _, _, _⟩,
          ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
          h_op_a_0_bin, h_op_a_0_iff, _, h_imm_c_bin,
          h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩ := h_prog
  simp only [Spec, aluTypeReaderSpecCore]
  refine ⟨h_ti, h_op_a_lt, h_op_b_lt,
          ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
          h_op_a_0_bin, h_op_a_0_iff, h_imm_c_bin,
          h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt,
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
          ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oc,
          ⟨e_pv_c, e_pl_c, e_dll_c⟩, e_immc⟩ := h_input
  subst_eqs
  simp only [Spec, aluTypeReaderSpecCore] at h_spec
  obtain ⟨h_ti, h_op_a_lt, h_op_b_lt,
          ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
          h_op_a_0_bin, h_op_a_0_iff, h_imm_c_bin,
          h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt,
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
           h_op_a_0_bin, h_op_a_0_iff, Or.inl trivial, h_imm_c_bin,
           h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩
  -- OperandAccess for op_a (offset 4)
  · refine ⟨trivial, ?_⟩
    simp only [SP1Clean.OperandAccess.assertion, SP1Clean.OperandAccess.Assertion.Spec]
    exact ⟨h_diff_a, h_ts_a, (isU64_iff_index_form _).mpr h_isU64_a⟩
  -- OperandAccess for op_b (offset 3)
  · refine ⟨trivial, ?_⟩
    simp only [SP1Clean.OperandAccess.assertion, SP1Clean.OperandAccess.Assertion.Spec]
    exact ⟨h_diff_b, h_ts_b, (isU64_iff_index_form _).mpr h_isU64_b⟩
  -- 4 assertZero gates: op_a_0 * op_a_write_value[i] = 0
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

end Assertion

/-- The Clean `FormalAssertion` for the "core" ALU-type reader spec
(`aluTypeReaderSpecCore`). Composes `ProgramTable.assertion`, two
`OperandAccess.assertion` calls, and four `op_a_0 * op_a_write_value[i] = 0`
scalar gates. The op_c memory access and the imm_c-equality gates are
emitted at the chip level. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.ALUTypeReader
