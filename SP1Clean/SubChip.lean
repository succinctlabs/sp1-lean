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
import SP1Operations.Operation.SubOperation.SubOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.Sub.SubChip
import SP1Chips.Sub.Common
import SP1Chips.Soundness
import SP1Clean.MemoryAccess
import SP1Clean.Operations.SubOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode

/-! # Chip-level `SubChip` mirror — R-type, operation-swap of `AddChip`

The R-type Sub chip: 33 columns, identical in shape to `SP1Clean.Add`
except for the operation fragment (`SubOp` instead of `AddOp`) and the
opcode index (`2` for `SUB` instead of `0` for `ADD`) flowing into
`RTypeReader`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Sub

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `SubCols<T, M: TrustMode>`.
Identical to `SP1Clean.Add.AddCols`. -/
structure SubCols (T : Type) where
  state : CPUState T
  adapter : RTypeReader T
  op_a_write_value : Vector T 4
  is_real : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Clean-side circuit. Mirrors SP1 Rust's `SubChip::eval(builder, cols)`. -/
def main (cols : Var SubCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory⟩, op_a_write_value, is_real,
       _adapter_cols⟩ := cols
  -- SubOperation: op_b_memory.prev_value - op_c_memory.prev_value = op_a_write_value.
  SP1Clean.SubOp.main op_b_memory.prev_value op_c_memory.prev_value op_a_write_value
  -- CPUState: clk_0_16 progression and clk_16_24 byte bound.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), (clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), clk_16_24, 8, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Program-bus interaction (opcode = 2 = SUB; R-type discipline).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 2, op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Trailing assertZero gates.
  is_real * (is_real - 1) === 0
  op_a_0 === 0

/-- Pilot Spec, expressed over field-valued `SubCols (ZMod p)`. Uses the
helper Specs from `SP1Clean.SubOp`, `SP1Clean.CPUState`, and
`SP1Clean.RTypeReader`. Opcode index `2` (`SUB`) flows into the
RTypeReader fragment. -/
def TraceSpec (cols : SubCols (ZMod p)) : Prop :=
  SP1Clean.SubOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_memory.prev_value
      cols.op_a_write_value ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.RTypeReader.rtypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 2 cols.state.pc
      cols.op_a_write_value
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
                diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb } } } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  cols.adapter_cols.is_trusted = 1

/-- Project a raw SP1 row into the structured `SubCols` view. Mirrors the
index map in `SP1Chips/Sub/Constraints.lean`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 33) : SubCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
   ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    Main[21],
    ⟨#v[Main[22], Main[23], Main[24], Main[25]], ⟨Main[26], Main[27]⟩⟩⟩,
   #v[Main[28], Main[29], Main[30], Main[31]],
   Main[32],
   ⟨Main[32]⟩⟩

/-- The chip-level bridge: SP1's `allHold` over the flat row
`Sub.constraints Main` is exactly `TraceSpec (fromMain Main)`, under
`is_real = Main[32] = 1`. -/
theorem traceSpec_iff_allHold
    (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1) :
    (_root_.Sub.constraints Main).allHold ↔ TraceSpec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [fromMain, TraceSpec, SP1Clean.SubOp.Spec,
    SP1Clean.CPUState.cpuStateSpec, SP1Clean.RTypeReader.rtypeReaderSpec]
  rw [show (_root_.Sub.constraints Main).allHold ↔
        ((SubOperation.constraints (F := ZMod p)
            #v[Main[15], Main[16], Main[17], Main[18]]
            #v[Main[22], Main[23], Main[24], Main[25]]
            { value := #v[Main[28], Main[29], Main[30], Main[31]] }
            Main[32]).allHold ∧
          (CPUState.constraints (F := ZMod p)
            { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
              pc := #v[Main[3], Main[4], Main[5]] }
            #v[Main[3] + 4, Main[4], Main[5]] 8 Main[32]).allHold ∧
          (RTypeReader.constraints (F := ZMod p)
            Main[0] (Main[2] + Main[1] * 65536)
            #v[Main[3], Main[4], Main[5]] 2
            #v[Main[28], Main[29], Main[30], Main[31]]
            { op_a := Main[6],
              op_a_memory :=
                { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                  access_timestamp :=
                    { prev_low := Main[11], diff_low_limb := Main[12] } },
              op_a_0 := Main[13], op_b := Main[14],
              op_b_memory :=
                { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
                  access_timestamp :=
                    { prev_low := Main[19], diff_low_limb := Main[20] } },
              op_c := Main[21],
              op_c_memory :=
                { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
                  access_timestamp :=
                    { prev_low := Main[26], diff_low_limb := Main[27] } } }
            Main[32] Main[32]).allHold ∧
          (Main[32] * (Main[32] - 1) = 0 ∧ Main[13] = 0)) from by
      simp [_root_.Sub.constraints, SP1ConstraintList.allHold,
        List.forall_append, List.Forall, SP1Constraint.toProp]]
  rw [h_is_real]
  rw [SubOperation.allHold_constraints_iff,
      SP1Clean.CPUState.cpuStateSpec_iff_sp1,
      SP1Clean.RTypeReader.rtypeReaderSpec_iff_sp1]
  simp [SP1Clean.CPUState.cpuStateSpec, SP1Clean.RTypeReader.rtypeReaderSpec, and_assoc]

/-- Clean-side `correct_sub`: same Sail equivalence statement as SP1's
`Sub.correct_sub`, but with the constraint hypothesis re-expressed against
the Clean-flavored `Spec` predicate over a structured `SubCols` view.
Pure composition with the SP1 proof via `traceSpec_iff_allHold.mpr`. -/
theorem correct_sub
    (Main : Vector (ZMod p) 33) (s : SailState)
    (h_is_real : Main[32] = 1)
    (h_spec : TraceSpec (fromMain Main))
    (state_cstrs : (_root_.Sub.constraints Main).initialState s) :
    let op_c := _root_.Sub.sp1_op_c Main
    let op_b := _root_.Sub.sp1_op_b Main
    let op_a := _root_.Sub.sp1_op_a Main
    (_root_.Sub.spec_sub (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Sub.sp1_sub Main).run s :=
  _root_.Sub.correct_sub Main s ((traceSpec_iff_allHold Main h_is_real).mpr h_spec)
    h_is_real state_cstrs

/-! ## RawSpec / SemanticSpec POC (sibling of AddChip) -/

/-- Structural mirror of `Sub.constraints.allHold`; iff-RHS of
`Sub.allHold_constraints_iff`. -/
def RawSpec (Main : Vector (ZMod p) 33) : Prop :=
  (SubOperation.constraints (F := ZMod p)
      #v[Main[15], Main[16], Main[17], Main[18]]
      #v[Main[22], Main[23], Main[24], Main[25]]
      { value := #v[Main[28], Main[29], Main[30], Main[31]] } Main[32]).allHold ∧
  (CPUState.constraints (F := ZMod p)
      { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
        pc := #v[Main[3], Main[4], Main[5]] }
      #v[Main[3] + 4, Main[4], Main[5]] 8 Main[32]).allHold ∧
  (RTypeReader.constraints (F := ZMod p)
      Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] 2
      #v[Main[28], Main[29], Main[30], Main[31]]
      { op_a := Main[6],
        op_a_memory :=
          { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
            access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
        op_a_0 := Main[13], op_b := Main[14],
        op_b_memory :=
          { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
            access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
        op_c := Main[21],
        op_c_memory :=
          { prev_value := #v[Main[22], Main[23], Main[24], Main[25]],
            access_timestamp := { prev_low := Main[26], diff_low_limb := Main[27] } } }
      Main[32] Main[32]).allHold ∧
  Main[32] * (Main[32] - 1) = 0 ∧
  Main[13] = 0

theorem rawSpec_iff_allHold (Main : Vector (ZMod p) 33) :
    (_root_.Sub.constraints Main).allHold ↔ RawSpec Main := by
  rw [_root_.Sub.allHold_constraints_iff]
  rfl

def SemanticSpec (Main : Vector (ZMod p) 33) : Prop :=
  let cols := fromMain Main
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 4
      (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_a
        { prev_value := cols.adapter.op_a_memory.prev_value,
          access_timestamp :=
            { prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
              diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 3
      (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_b
        { prev_value := cols.adapter.op_b_memory.prev_value,
          access_timestamp :=
            { prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
              diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.memoryAccessSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 2
      (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_c
        { prev_value := cols.adapter.op_c_memory.prev_value,
          access_timestamp :=
            { prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
              diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.ProgramTable.Spec
      { pc := cols.state.pc, opcode := 2, op_a := cols.adapter.op_a,
        op_b := #v[cols.adapter.op_b, 0, 0, 0],
        op_c := #v[cols.adapter.op_c, 0, 0, 0],
        op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 0 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  (∀ s : SailState, (_root_.Sub.constraints Main).initialState s →
    (_root_.Sub.sp1_sub Main).run s =
      (_root_.Sub.spec_sub (.Regidx (_root_.Sub.sp1_op_c Main))
        (.Regidx (_root_.Sub.sp1_op_b Main))
        (.Regidx (_root_.Sub.sp1_op_a Main))).run s)

theorem raw_to_semantic (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1)
    (h_raw : RawSpec Main) : SemanticSpec Main := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_subop, h_cpu_raw, h_rtr_raw, h_real_bin, h_a0⟩ := h_raw
  have h_allHold : (_root_.Sub.constraints Main).allHold :=
    (rawSpec_iff_allHold Main).mpr ⟨h_subop, h_cpu_raw, h_rtr_raw, h_real_bin, h_a0⟩
  rw [h_is_real] at h_cpu_raw h_rtr_raw
  have h_cpu_spec := SP1Clean.CPUState.cpuStateSpec_iff_sp1.mp h_cpu_raw
  have h_rtr_spec := SP1Clean.RTypeReader.rtypeReaderSpec_iff_sp1.mp h_rtr_raw
  obtain ⟨h_ti, h_op_a_lt, h_op_b_lt, h_op_c_lt, h_a0_bin, h_a0_iff,
          ⟨h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩,
          ⟨⟨h_diff_a, h_diff_b, h_diff_c⟩,
           ⟨h_ts_c, h_ts_b, h_ts_a⟩,
           ⟨h_isU64_a, h_isU64_b, h_isU64_c⟩⟩,
          _h_a0_implies⟩ := h_rtr_spec
  have h_zero_lt : (0 : ZMod p) < (65536 : ZMod p) := by
    have h65536_lt : (65536 : ℕ) < p := by
      have := Fact.out (p := 2 ^ 17 < p); omega
    have h65536_val : (65536 : ZMod p).val = 65536 := ZMod.val_natCast_of_lt h65536_lt
    change (0 : ZMod p).val < (65536 : ZMod p).val
    rw [ZMod.val_zero, h65536_val]; omega
  refine ⟨h_cpu_spec,
          ⟨h_diff_a, h_ts_a, h_isU64_a⟩,
          ⟨h_diff_b, h_ts_b, h_isU64_b⟩,
          ⟨h_diff_c, h_ts_c, h_isU64_c⟩,
          ?_, h_real_bin, ?_⟩
  · simp only [SP1Clean.ProgramTable.Spec, SP1Clean.ProgramSpec,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    have h2_lt : (2 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
    have h2_val : (2 : ZMod p).val = 2 := ZMod.val_natCast_of_lt h2_lt
    refine ⟨?_, h_op_a_lt, ⟨h_op_b_lt, h_zero_lt, h_zero_lt, h_zero_lt⟩,
            ⟨h_op_c_lt, h_zero_lt, h_zero_lt, h_zero_lt⟩,
            h_a0_bin, h_a0_iff, Or.inl trivial, Or.inl trivial,
            h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩
    convert h_ti using 1
  · intro s state_cstrs
    exact soundness_sub Main s h_allHold h_is_real state_cstrs

/-! ## Full `FormalAssertion` promotion (Path-2 design)

Wraps the chip-level constraint surface into a Clean `FormalAssertion`,
mirroring `SP1Clean.Addw.Assertion`'s Path-2 design: drops `SubOp.main`
from `Assertion.main` (no `SubOp.assertion` exists yet — see Phase A1 of
the iter-4 scaling plan), so the FormalSpec covers `CPUState`,
`ProgramTable`, and the boolean asserts only. The borrow/natural-form
SubOp surface continues to be carried by the legacy chip-level `Spec` /
`traceSpec_iff_allHold` / `correct_sub` route. -/

namespace Assertion

open Circuit

/-- Refactored chip-level circuit using subcircuit composition. Drops
the `SubOp.main` borrow-form carry chain (see Scope note above). -/
@[reducible]
def main (cols : Var SubCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory⟩, _op_a_write_value, is_real,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Program-bus interaction (opcode = 2 = SUB; R-type discipline).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 2, op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Iter-8 sub-task E: per-operand memory-bus byte content.
  -- R-type offsets: op_a at +4, op_b at +3, op_c at +2.
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
  is_real * (is_real - 1) === 0
  op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) SubCols unit where
  name := "SP1Clean.Sub"
  main := main
  localLength _ := 0

def Assumptions (_ : SubCols (ZMod p)) : Prop := True

/-- The chip's Circuit-derivable spec: the clock-decomposition byte
lookups, the program-bus existential witness, and the two trailing
assertZero gates. The SubOp arithmetic surface and the memory-bus side
of `rtypeReaderSpec` are deferred to the legacy chip-level `Spec` /
`traceSpec_iff_allHold`. -/
def FormalSpec (cols : SubCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 2, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := #v[cols.adapter.op_c, 0, 0, 0],
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 0 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- R-type: op_a/+4, op_b/+3, op_c/+2.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 2, cols.adapter.op_c_memory.access_timestamp.prev_low, cols.adapter.op_c_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_c_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_oa_a, h_oa_b, h_oa_c,
          h_isreal, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_isreal
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial
  · exact h_oa_c trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_isreal, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩
  · linear_combination h_isreal
  · exact h_op_a_0

end Assertion

/-- The full Clean `FormalAssertion` for the lookup-derivable subset of
`SubChip`'s constraint surface (Path-2 design: drops the SubOp surface;
see Scope note above). Composes `CPUState.assertion`,
`ProgramTable.assertion`, plus two trailing assertZero gates. -/
def assertion : FormalAssertion (ZMod p) SubCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Sub
