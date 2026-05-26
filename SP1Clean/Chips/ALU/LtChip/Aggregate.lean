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
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ALUTypeReader.ALUTypeReader
import SP1Chips.Lt.LtChip
import SP1Chips.Soundness
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ALUTypeReader
import SP1Clean.Compare.LtOperationSigned
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec

/-! # Chip-level `LtChip` mirror — bundled signed/unsigned compare

The Lt chip bundles four RV64I variants — `slt` / `sltu` (R-type) and
`slti` / `sltiu` (I-type) — into a single 44-column trace. Variants
distinguished by selectors `is_slt`/`is_sltu` (Main[32..33]) and
`imm_c` (Main[31]). The signed/unsigned distinction is carried into the
`LtOperationSigned` sub-fragment via `is_signed := Main[32]`.

Structural mirror discipline (Spec only). The `LtOperationSigned`
constraint clause is left in raw `allHold` form — no Clean
operation wrapper yet for this Compare-family sub-fragment.

Opcode encoding: `is_slt * 9 + is_sltu * 10` (SLT=9, SLTU=10).
Result is a 1-bit boolean written into `op_a_write_value[0]` (via
`Main[34]`), with the other 3 limbs zero.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Lt

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Emits CPUState range lookups, the program-bus
interaction (opcode = `is_slt * 9 + is_sltu * 10`), and the trailing
assertZero gates (the two opcode-selector booleans, the sum-boolean,
and the op_a_0 = 0 forcing). The `LtOperationSigned` sub-fragment
constraints are captured propositionally in `Spec` below. -/
def main (cols : Var LtCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c, _op_c_memory, imm_c⟩, is_slt, is_sltu, lt_operation,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_slt * 9 + is_sltu * 10,
      op_a, #v[op_b, 0, 0, 0], op_c,
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  let _ := lt_operation.result.u16_compare_operation.bit
  -- Trailing assertZero gates.
  is_slt * (is_slt - 1) === 0
  is_sltu * (is_sltu - 1) === 0
  (is_slt + is_sltu) * (is_slt + is_sltu - 1) === 0
  op_a_0 === 0

/-- Pilot Spec, expressed over field-valued `LtCols (ZMod p)`. The
`LtOperationSigned` clause is left in raw `allHold` form (it
internally fans out into `U16MSBOperation` and `LtOperationUnsigned`
sub-fragments). The chip-level `is_signed` argument is `is_slt`; the
chip-level `is_real` argument is `is_slt + is_sltu`. -/
def TraceSpec (cols : LtCols (ZMod p)) : Prop :=
  let is_real : ZMod p := cols.is_slt + cols.is_sltu
  (_root_.LtOperationSigned.constraints (F := ZMod p)
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_memory.prev_value
      cols.lt_operation cols.is_slt is_real).allHold ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ALUTypeReader.aluTypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
      (cols.is_slt * 9 + cols.is_sltu * 10) cols.state.pc
      #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0]
      { op_a := cols.adapter.op_a,
        op_a_memory :=
          { prev_value := cols.adapter.op_a_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
                diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb } },
        op_a_0 := cols.adapter.op_a_0, op_b := cols.adapter.op_b,
        op_b_memory :=
          { prev_value := cols.adapter.op_b_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
                diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb } },
        op_c := cols.adapter.op_c,
        op_c_memory :=
          { prev_value := cols.adapter.op_c_memory.prev_value,
            access_timestamp :=
              { prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
                diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb } },
        imm_c := cols.adapter.imm_c } ∧
  cols.is_slt * (cols.is_slt - 1) = 0 ∧
  cols.is_sltu * (cols.is_sltu - 1) = 0 ∧
  (cols.is_slt + cols.is_sltu) * (cols.is_slt + cols.is_sltu - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  cols.adapter_cols.is_trusted = 1

set_option maxHeartbeats 800000 in
-- Two-arm case-split (slt vs sltu) under is_real_sum = 1 + boolean gates,
-- each arm rewrites via the Lt._iff_slt/_iff_sltu polymorphic iff lemmas
-- and bridges three sub-allHolds via the *Spec_iff_sp1 helpers.
/-- The chip-level half-iff bridge (Lt): under
`is_slt + is_sltu = 1 ∧ op_a_0 = 0 ∧ imm_c = 0`, the Clean `Spec` implies
SP1's `allHold`. Used by `correct_slt`/`correct_sltu` wrappers. -/
theorem traceSpec_implies_allHold (Main : Vector (ZMod p) 44)
    (h_is_real : Main[32] + Main[33] = 1) (h_op_a_0 : Main[13] = 0)
    (h_imm_c : Main[31] = 0)
    (h_spec : TraceSpec (fromMain Main)) :
    (_root_.Lt.constraints Main).allHold := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [TraceSpec, fromMain] at h_spec
  obtain ⟨h_lt_op, h_cpu_spec, h_alu_spec,
          h_slt_bin, h_sltu_bin, _h_sum_bin, _h_a0, h_trusted⟩ := h_spec
  -- The aggregate is_real sum = 1 + slt/sltu boolean gates ⇒ exactly one variant active.
  have h_slt_or : Main[32] = 0 ∨ Main[32] = 1 := by
    rcases mul_eq_zero.mp h_slt_bin with h | h
    · exact Or.inl h
    · exact Or.inr (by linear_combination h)
  -- Bridge to the SP1ConstraintList.allHold form (definitionally List.Forall toProp).
  change List.Forall SP1Constraint.toProp (_root_.Lt.constraints Main)
  rcases h_slt_or with h_slt_zero | h_slt_one
  · -- sltu case: Main[32] = 0, so Main[33] = 1 from h_is_real.
    have h_sltu_one : Main[33] = 1 := by linear_combination h_is_real - h_slt_zero
    have h_is_sltu : _root_.Lt.is_sltu Main := ⟨h_sltu_one, h_imm_c⟩
    rw [_root_.Lt.allHold_constraints_iff_sltu Main h_is_sltu]
    -- Bridge each iff-RHS conjunct from Spec components, with Main[33] = 1 substituted.
    refine ⟨?_, ?_, ?_, h_slt_zero, h_op_a_0⟩
    · -- LtOperationSigned.constraints.allHold — directly from Spec.
      change List.Forall SP1Constraint.toProp _
      convert h_lt_op using 2
    · -- CPUState.constraints.allHold under is_real = 1.
      change List.Forall SP1Constraint.toProp _
      rw [show (Main[32] + Main[33] : ZMod p) = 1 from h_is_real] at *
      exact (SP1Clean.CPUState.cpuStateSpec_iff_sp1).mpr h_cpu_spec
    · -- ALUTypeReader.constraints.allHold under is_real = is_trusted = 1.
      change List.Forall SP1Constraint.toProp _
      -- aluTypeReaderSpec_iff_sp1 expects both gating args to be literally 1.
      rw [show (Main[32] + Main[33] : ZMod p) = 1 from h_is_real]
      exact (SP1Clean.ALUTypeReader.aluTypeReaderSpec_iff_sp1).mpr h_alu_spec
  · -- slt case: Main[32] = 1, so Main[33] = 0 from h_is_real.
    have h_sltu_zero : Main[33] = 0 := by linear_combination h_is_real - h_slt_one
    have h_is_slt : _root_.Lt.is_slt Main := ⟨h_slt_one, h_imm_c⟩
    rw [_root_.Lt.allHold_constraints_iff_slt Main h_is_slt]
    refine ⟨?_, ?_, ?_, h_sltu_zero, h_op_a_0⟩
    · change List.Forall SP1Constraint.toProp _
      convert h_lt_op using 2
    · change List.Forall SP1Constraint.toProp _
      rw [show (Main[32] + Main[33] : ZMod p) = 1 from h_is_real]
      exact (SP1Clean.CPUState.cpuStateSpec_iff_sp1).mpr h_cpu_spec
    · change List.Forall SP1Constraint.toProp _
      rw [show (Main[32] + Main[33] : ZMod p) = 1 from h_is_real]
      exact (SP1Clean.ALUTypeReader.aluTypeReaderSpec_iff_sp1).mpr h_alu_spec

/-- Clean-side `correct_slt`: signed less-than (R-type). -/
theorem correct_slt
    (Main : Vector (ZMod p) 44) (s : SailState)
    (h_is_slt : Main[32] = 1) (h_imm_c : Main[31] = 0) (h_op_a_0 : Main[13] = 0)
    (h_sltu_zero : Main[33] = 0)
    (h_spec : TraceSpec (fromMain Main))
    (state_cstrs : (_root_.Lt.constraints Main).initialState s) :
    let op_c := _root_.Slt.sp1_op_c Main
    let op_b := _root_.Slt.sp1_op_b Main
    let op_a := _root_.Slt.sp1_op_a Main
    (_root_.Slt.spec_slt (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Lt.sp1_lt Main).run s :=
  _root_.Slt.correct_slt Main s
    (traceSpec_implies_allHold Main (by rw [h_is_slt, h_sltu_zero]; ring) h_op_a_0 h_imm_c h_spec)
    ⟨h_is_slt, h_imm_c⟩ state_cstrs

/-- Clean-side `correct_sltu`: unsigned less-than (R-type). -/
theorem correct_sltu
    (Main : Vector (ZMod p) 44) (s : SailState)
    (h_is_sltu : Main[33] = 1) (h_imm_c : Main[31] = 0) (h_op_a_0 : Main[13] = 0)
    (h_slt_zero : Main[32] = 0)
    (h_spec : TraceSpec (fromMain Main))
    (state_cstrs : (_root_.Lt.constraints Main).initialState s) :
    let op_c := _root_.Sltu.sp1_op_c Main
    let op_b := _root_.Sltu.sp1_op_b Main
    let op_a := _root_.Sltu.sp1_op_a Main
    (_root_.Sltu.spec_sltu (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Lt.sp1_lt Main).run s :=
  _root_.Sltu.correct_sltu Main s
    (traceSpec_implies_allHold Main (by rw [h_is_sltu, h_slt_zero]; ring) h_op_a_0 h_imm_c h_spec)
    ⟨h_is_sltu, h_imm_c⟩ state_cstrs

/-! ## RawSpec / SemanticSpec POC -/

@[reducible]
def RawSpec (Main : Vector (ZMod p) 44) : Prop :=
  List.Forall SP1Constraint.toProp (_root_.Lt.constraints Main)

omit [Fact (2 ^ 17 < p)] in
theorem rawSpec_iff_allHold (Main : Vector (ZMod p) 44) :
    (_root_.Lt.constraints Main).allHold ↔ RawSpec Main := Iff.rfl

def SemanticSpec (Main : Vector (ZMod p) 44) : Prop :=
  TraceSpec (fromMain Main) ∧
  (∀ s : SailState, (_root_.Lt.constraints Main).initialState s →
    (_root_.Lt.sp1_lt Main).run s =
      (if _root_.Lt.is_slt Main then
        (_root_.Slt.spec_slt (.Regidx (_root_.Slt.sp1_op_c Main))
          (.Regidx (_root_.Slt.sp1_op_b Main))
          (.Regidx (_root_.Slt.sp1_op_a Main))).run s
      else if _root_.Lt.is_sltu Main then
        (_root_.Sltu.spec_sltu (.Regidx (_root_.Sltu.sp1_op_c Main))
          (.Regidx (_root_.Sltu.sp1_op_b Main))
          (.Regidx (_root_.Sltu.sp1_op_a Main))).run s
      else if _root_.Lt.is_slti Main then
        (_root_.Slti.spec_slti (_root_.Slti.sp1_op_c Main)
          (.Regidx (_root_.Slti.sp1_op_b Main))
          (.Regidx (_root_.Slti.sp1_op_a Main))).run s
      else if _root_.Lt.is_sltiu Main then
        (_root_.Sltiu.spec_sltiu (_root_.Sltiu.sp1_op_c Main)
          (.Regidx (_root_.Sltiu.sp1_op_b Main))
          (.Regidx (_root_.Sltiu.sp1_op_a Main))).run s
      else (_root_.Lt.sp1_lt Main).run s))

theorem raw_to_semantic (Main : Vector (ZMod p) 44)
    (_h_is_real_sum : Main[32] + Main[33] = 1) (_h_op_a_0 : Main[13] = 0)
    (_h_imm_c : Main[31] = 0) (h_spec : TraceSpec (fromMain Main))
    (h_raw : RawSpec Main) : SemanticSpec Main := by
  refine ⟨h_spec, ?_⟩
  intro s state_cstrs
  exact soundness_lt Main s ((rawSpec_iff_allHold Main).mpr h_raw) state_cstrs

/-- The op_a / op_b / op_c register accesses, exposed for trace-level
OfflineMemory aggregation. op_a writes the 4-limb boolean result
`#v[compare_bit, 0, 0, 0]`. -/
def opAMemoryAccess (cols : LtCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_a, 0, 0],
    prev_value := cols.adapter.op_a_memory.prev_value,
    prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }

def opBMemoryAccess (cols : LtCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_b, 0, 0],
    prev_value := cols.adapter.op_b_memory.prev_value,
    prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb }

def opCMemoryAccess (cols : LtCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_c[0], 0, 0],
    prev_value := cols.adapter.op_c_memory.prev_value,
    prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb }

/-! ## Full `FormalAssertion` promotion (Path-2)

Wraps the chip-level constraint surface into a Clean `FormalAssertion`.
Composes `SP1Clean.CPUState.assertion` and `SP1Clean.ProgramTable.assertion`
as subcircuits, plus the four scalar trailing assertZero gates
(`is_slt` binary, `is_sltu` binary, sum binary, `op_a_0 = 0`).

**Path-2 drops.** The `LtOperationSigned` `allHold` clause is NOT
promoted here — no Clean operation wrapper exists yet for the
Compare-family sub-fragment. The memory-bus side of `aluTypeReaderSpec`
is also deferred to the legacy chip-level `Spec` / `traceSpec_iff_allHold` route.
Same Path-2 design as `SP1Clean.Addi.Assertion`. -/

namespace Assertion

open Circuit

/-- Refactored chip-level circuit using subcircuit composition. Drops
the `LtOperationSigned` byte lookups and `ALUTypeReader` memory accesses. -/
@[reducible]
def main (cols : Var LtCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory, imm_c⟩, is_slt, is_sltu, _lt_operation,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_slt * 9 + is_sltu * 10,
      op_a, #v[op_b, 0, 0, 0], op_c,
      op_a_0, 0, imm_c⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_slt * (is_slt - 1) === 0
  is_sltu * (is_sltu - 1) === 0
  (is_slt + is_sltu) * (is_slt + is_sltu - 1) === 0
  op_a_0 === 0
  -- Iter-8 sub-task E: per-operand memory-bus byte content.
  -- R-type-shaped: op_a at +4, op_b at +3, op_c at +2.
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low, op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low, op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 2, op_c_memory.access_timestamp.prev_low, op_c_memory.access_timestamp.diff_low_limb,
       op_c_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LtCols unit where
  name := "SP1Clean.Lt"
  main := main
  localLength _ := 0

def Assumptions (_ : LtCols (ZMod p)) : Prop := True

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_isslt, h_issltu, h_sum,
          h_op_a_0, h_oa_a, h_oa_b, h_oa_c⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_isslt
  · linear_combination h_issltu
  · linear_combination h_sum
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial
  · exact h_oa_c trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_isslt, h_issltu, h_sum, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_isslt
  · linear_combination h_issltu
  · linear_combination h_sum
  · exact h_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩

end Assertion

/-- The full Clean `FormalAssertion` for the byte- and program-lookup-
derivable subset of `LtChip`'s constraint surface (Path-2 design;
drops the `LtOperationSigned` byte lookups and memory-bus side of
`ALUTypeReader`). -/
def assertion : FormalAssertion (ZMod p) LtCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Lt
