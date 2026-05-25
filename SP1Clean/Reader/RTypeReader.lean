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
import SP1Clean.Reader.RegisterAccess

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
cols 1 1` modulo the pinned `is_real = is_trusted = 1`. `clk_high` is
threaded through to the memory-bus emissions inside `RegisterAccess.assertion`. -/
structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  opcode : F
  pc : Vector F 3
  op_a_write_value : Vector F 4
  cols : _root_.RTypeReader F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Clean-side circuit. Emits the byte/program/memory lookups inside
`_root_.RTypeReader.constraints` under `is_real = is_trusted = 1`.

The 3 per-operand sub-circuits use `RegisterAccess.assertion` with
`mult := 1`. Each `RegisterAccess.assertion` call bundles the byte-bus
content (via `OperandAccess.assertionGated`) with the two memory-bus
interactions (a send of `prev_value` and a receive of `write_value`).
For read-only operands (op_b, op_c) the receive uses `prev_value` as
the write — the value passes through unchanged. For op_a the receive
uses `op_a_write_value` (the chip's computed result).

External chips calling `RTypeReader.assertion` see the same
unconditional `rtypeReaderSpec` as before — the memory-bus emissions
don't add row-level facts (per-key multiplicity balance is enforced at
the trace level). -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨clk_high, clk_low, opcode, pc, op_a_write_value,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory⟩⟩ := input
  -- Program-bus interaction.
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode, op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Three per-operand register-access subcircuits (byte bus + memory bus).
  -- op_a: read prev_value, write op_a_write_value (the result).
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 4, op_a, op_a_memory.prev_value, op_a_write_value,
       op_a_memory.access_timestamp.prev_low,
       op_a_memory.access_timestamp.diff_low_limb, 1⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  -- op_b: read prev_value, write prev_value (read-only, value passes through).
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 3, op_b, op_b_memory.prev_value, op_b_memory.prev_value,
       op_b_memory.access_timestamp.prev_low,
       op_b_memory.access_timestamp.diff_low_limb, 1⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  -- op_c: read prev_value, write prev_value (read-only).
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 2, op_c, op_c_memory.prev_value, op_c_memory.prev_value,
       op_c_memory.access_timestamp.prev_low,
       op_c_memory.access_timestamp.diff_low_limb, 1⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
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
  -- Computed from main: 3 assertionGated × 24 witnesses = 72.
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

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
to bridge `rtypeReaderSpec` extracts back to whole-`Vector` `memoryAccessSpec`.
TODO: move this to Word.lean or something like that -/
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
  -- assertionGated.Spec ⟨..., 1⟩ = (1 = 0 ∨ <byte facts>); 1 ≠ 0 so right disjunct.
  have h_oa_a := (h_oa_a_sub trivial).resolve_left one_ne_zero
  have h_oa_b := (h_oa_b_sub trivial).resolve_left one_ne_zero
  have h_oa_c := (h_oa_c_sub trivial).resolve_left one_ne_zero
  simp only [SP1Clean.ProgramTable.assertion, SP1Clean.ProgramTable.Spec,
             SP1Clean.ProgramSpec, Vector.getElem_mk, List.getElem_toArray,
             List.getElem_cons_zero, List.getElem_cons_succ] at h_prog
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
  -- OperandAccess for op_a (offset 4) — right disjunct of assertionGated.Spec
  · refine ⟨trivial, ?_⟩
    right
    exact ⟨h_diff_a, h_ts_a, (isU64_iff_index_form _).mpr h_isU64_a⟩
  -- OperandAccess for op_b (offset 3)
  · refine ⟨trivial, ?_⟩
    right
    exact ⟨h_diff_b, h_ts_b, (isU64_iff_index_form _).mpr h_isU64_b⟩
  -- OperandAccess for op_c (offset 2)
  · refine ⟨trivial, ?_⟩
    right
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

/-! ## Flag-threaded variant (`Gated`)

Mirrors Rust's `eval_r_type(cols, ..., is_real, is_trusted)`. `is_real` and
`is_trusted` are first-class `Inputs` fields; sub-circuit emissions are
gated by the appropriate flag (`is_trusted` for the program-bus lookup;
`is_real` for the three per-operand `RegisterAccess` calls).

The FormalAssertion's `Spec` is the **literal conjunction of sub-circuit
`Spec`s** (per CLAUDE.md's "Faithful sub-circuit composition" principle).
Chip consumers destructure this 9-tuple:

1. `is_real * (is_real - 1) = 0` — binary gate (collapses the 4 redundant
   SP1-native copies into one Clean emission).
2. `programGated.Spec` = `is_trusted = 0 ∨ ProgramSpec entry`.
3–5. Three `RegisterAccess.assertion.Spec` = `is_real = 0 ∨ <byte facts>`
   (each delegates to `OperandAccess.AssertionGated.Spec`).
6–9. Four scalar `op_a_0 * op_a_write_value[i] = 0` gates (not gated by
   `is_real` in SP1).

This is a parallel API to the legacy `assertion` above — the unconditional
form (pinned at `is_real = is_trusted = 1`) continues to serve any chips
that haven't migrated to the gated form yet. -/

namespace Gated

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Bundled inputs. Mirrors `_root_.RTypeReader.constraints(... is_real
is_trusted)` with the flags as first-class fields. -/
structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  opcode : F
  pc : Vector F 3
  op_a_write_value : Vector F 4
  cols : _root_.RTypeReader F
  is_real : F
  is_trusted : F
deriving ProvableStruct

namespace Assertion

open Circuit

/-- Clean-side flag-threaded R-type reader circuit. Mirrors Rust
`eval_r_type` shape: one `programGated` (gated by `is_trusted`) + three
`RegisterAccess.assertion` calls (gated by `is_real`) + binary gate +
four `op_a_0` zeroing gates. -/
@[reducible]
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨clk_high, clk_low, opcode, pc, op_a_write_value,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory⟩,
       is_real, is_trusted⟩ := input
  -- Binary gate (single emission collapses SP1-native's 4 redundant copies).
  is_real * (is_real - 1) === 0
  -- Program-bus lookup, gated by is_trusted.
  SP1Clean.programGated
    (⟨#v[pc[0], pc[1], pc[2], opcode, op_a, op_b, 0, 0, 0,
         op_c, 0, 0, 0, op_a_0, 0, 0],
       is_trusted⟩ : Var SP1Clean.ProgramGated.Inputs (ZMod p))
  -- Three per-operand register-access subcircuits, gated by is_real.
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 4, op_a, op_a_memory.prev_value, op_a_write_value,
       op_a_memory.access_timestamp.prev_low,
       op_a_memory.access_timestamp.diff_low_limb, is_real⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 3, op_b, op_b_memory.prev_value, op_b_memory.prev_value,
       op_b_memory.access_timestamp.prev_low,
       op_b_memory.access_timestamp.diff_low_limb, is_real⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  SP1Clean.RegisterAccess.assertion
    (⟨clk_high, clk_low, 2, op_c, op_c_memory.prev_value, op_c_memory.prev_value,
       op_c_memory.access_timestamp.prev_low,
       op_c_memory.access_timestamp.diff_low_limb, is_real⟩ :
      Var SP1Clean.RegisterAccess.Assertion.Inputs (ZMod p))
  -- Four op_a_0 zeroing gates (not gated by is_real per SP1).
  op_a_0 * op_a_write_value[0] === 0
  op_a_0 * op_a_write_value[1] === 0
  op_a_0 * op_a_write_value[2] === 0
  op_a_0 * op_a_write_value[3] === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit where
  name := "SP1Clean.RTypeReader.Gated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : Inputs (ZMod p)) : Prop := True

/-- The `Spec` is the literal conjunction of sub-circuit `Spec`s — one
per emission in `main`. -/
def Spec (input : Inputs (ZMod p)) : Prop :=
  let ⟨clk_high, clk_low, opcode, pc, op_a_write_value,
       cols, is_real, is_trusted⟩ := input
  is_real * (is_real - 1) = 0 ∧
  SP1Clean.ProgramGated.Spec
    ⟨#v[pc[0], pc[1], pc[2], opcode, cols.op_a, cols.op_b, 0, 0, 0,
        cols.op_c, 0, 0, 0, cols.op_a_0, 0, 0],
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
    ⟨clk_high, clk_low, 2, cols.op_c, cols.op_c_memory.prev_value,
     cols.op_c_memory.prev_value, cols.op_c_memory.access_timestamp.prev_low,
     cols.op_c_memory.access_timestamp.diff_low_limb, is_real⟩ ∧
  cols.op_a_0 * op_a_write_value[0] = 0 ∧
  cols.op_a_0 * op_a_write_value[1] = 0 ∧
  cols.op_a_0 * op_a_write_value[2] = 0 ∧
  cols.op_a_0 * op_a_write_value[3] = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨e_ckh, e_cl, e_opc, e_pc, e_oawv, e_oa,
          ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
          ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oc,
          ⟨e_pv_c, e_pl_c, e_dll_c⟩, e_ir, e_it⟩ := h_input
  subst_eqs
  obtain ⟨h_gate, h_prog_sub, h_ra_a_sub, h_ra_b_sub, h_ra_c_sub,
          h_z0, h_z1, h_z2, h_z3⟩ := h_holds
  -- Normalize `a - b` ↔ `a + -b` and `(map f v)[i]` ↔ `f v[i]` so the
  -- Spec target's destructured-Inputs form matches the sub-circuit hyps.
  simp only [Spec, sub_eq_add_neg, Vector.getElem_map]
  exact ⟨h_gate, h_prog_sub trivial, h_ra_a_sub trivial, h_ra_b_sub trivial,
         h_ra_c_sub trivial, h_z0, h_z1, h_z2, h_z3⟩

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions Spec := by
  circuit_proof_start
  obtain ⟨e_ckh, e_cl, e_opc, e_pc, e_oawv, e_oa,
          ⟨e_pv_a, e_pl_a, e_dll_a⟩, e_oa0, e_ob,
          ⟨e_pv_b, e_pl_b, e_dll_b⟩, e_oc,
          ⟨e_pv_c, e_pl_c, e_dll_c⟩, e_ir, e_it⟩ := h_input
  subst_eqs
  simp only [Spec, sub_eq_add_neg, Vector.getElem_map] at h_spec
  obtain ⟨h_gate, h_prog, h_ra_a, h_ra_b, h_ra_c, h_z0, h_z1, h_z2, h_z3⟩ := h_spec
  exact ⟨h_gate, ⟨trivial, h_prog⟩, ⟨trivial, h_ra_a⟩, ⟨trivial, h_ra_b⟩,
         ⟨trivial, h_ra_c⟩, h_z0, h_z1, h_z2, h_z3⟩

end Assertion

/-- The flag-threaded Clean `FormalAssertion` for the R-type reader.
Spec is the literal conjunction of sub-circuit Specs. -/
def assertion : FormalAssertion (ZMod p) Inputs :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.Spec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end Gated

end SP1Clean.RTypeReader
