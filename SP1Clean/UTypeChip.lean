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
import SP1Operations.Operation.AddOperation.AddOperation
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.JTypeReader.JTypeReader
import SP1Chips.UType.UTypeChip
import SP1Chips.UType.Constraints
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.JTypeReader

/-! # Chip-level `UTypeChip` mirror — bundled U-type (LUI/AUIPC)

The U-type chip bundles two RV64IM variants (`auipc` and `lui`) into a
single 31-column trace, distinguished by the `is_auipc` selector at
`Main[29]`. The chip's `AddOperation` adds a conditional addend
(`is_auipc * pc` — i.e., `pc` for AUIPC, `0` for LUI) to the 32-bit
immediate, producing the 64-bit value written to `op_a`.

Structural mirror discipline (same as JalChip / MulChip / ShiftLeftChip):
defines `UTypeCols`, `main`, and `Spec`; no `iff_sp1` / `correct_*`
bridges, no `FormalAssertion` promotion. The chip-level Spec composes
`AddOperation.constraints.allHold` (kept in raw form because the
operation's is_real arg is the conditional `is_real - op_a_0`),
`cpuStateSpec`, `jtypeReaderSpec`, and the chip's selector + alignment
trailing asserts.
-/

namespace SP1Clean.UType

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `UTypeCols<T>`.
`pc_addend` is the conditional `is_auipc * pc` carried into the
AddOperation, and `add_result` is the 64-bit AddOp output written to
op_a. -/
structure UTypeCols (T : Type) where
  clk_high : T
  clk_16_24 : T
  clk_0_16 : T
  pc : Vector T 3
  op_a : T
  op_a_memory_prev_value : Vector T 4
  op_a_memory_prev_low : T
  op_a_memory_diff_low : T
  op_a_0 : T
  op_b_imm : Vector T 4
  op_c_imm : Vector T 4
  pc_addend : Vector T 3
  add_result : Vector T 4
  is_auipc : T
  is_real : T
  next_pc_carry_value : Vector T 3
deriving ProvableStruct

/-- Clean-side circuit. Emits CPUState range lookups (via subcircuit),
the program-bus interaction with the selector-weighted opcode
(`is_auipc * 48 + (1 - is_auipc) * 49` — AUIPC=48, LUI=49), and the
trailing assertZero gates (is_real boolean, is_auipc boolean, three
`pc_addend = is_auipc * pc` clauses, the `(is_real - 1) * op_a_0 = 0`
gate). The AddOperation sub-fragment (operating on `pc_addend` and
`op_b_imm`) is intentionally not emitted as a subcircuit — its
constraints are captured propositionally in `Spec` below. -/
def main (cols : Var UTypeCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a, _op_a_memory_prev_value,
       _op_a_memory_prev_low, _op_a_memory_diff_low, op_a_0, op_b_imm,
       op_c_imm, pc_addend, _add_result, is_auipc, is_real,
       _next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_auipc * 48 + (1 - is_auipc) * 49,
      op_a, op_b_imm, op_c_imm,
      op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  is_auipc * (is_auipc - 1) === 0
  pc_addend[0] - is_auipc * pc[0] === 0
  pc_addend[1] - is_auipc * pc[1] === 0
  pc_addend[2] - is_auipc * pc[2] === 0
  (is_real - 1) * op_a_0 === 0

/-- Pilot Spec, expressed over field-valued `UTypeCols (ZMod p)`. Conjunct
order matches the SP1 constraint list emission (CPUState ∧ AddOperation ∧
JTypeReader ∧ trailing assertZero gates) so `iff_sp1` reshapes by `and_assoc`
without needing `and_comm`. The `AddOperation` clause is left in raw `allHold`
form (under is_real arg `is_real - op_a_0`) because the iff lemma is only
stated for `is_real arg = 1`. -/
def Spec (cols : UTypeCols (ZMod p)) : Prop :=
  let opcode_e : ZMod p := cols.is_auipc * 48 + (1 - cols.is_auipc) * 49
  let addend : Word (ZMod p) :=
    #v[cols.pc_addend[0], cols.pc_addend[1], cols.pc_addend[2], 0]
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  (_root_.AddOperation.constraints (F := ZMod p)
      addend cols.op_b_imm { value := cols.add_result }
      (cols.is_real - cols.op_a_0)).allHold ∧
  SP1Clean.JTypeReader.jtypeReaderSpec
      (cols.clk_0_16 + cols.clk_16_24 * 65536) opcode_e cols.pc
      cols.add_result
      { op_a := cols.op_a,
        op_a_memory :=
          { prev_value := cols.op_a_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_a_memory_prev_low,
                diff_low_limb := cols.op_a_memory_diff_low } },
        op_a_0 := cols.op_a_0,
        op_b_imm := cols.op_b_imm, op_c_imm := cols.op_c_imm } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.is_auipc * (cols.is_auipc - 1) = 0 ∧
  cols.pc_addend[0] - cols.is_auipc * cols.pc[0] = 0 ∧
  cols.pc_addend[1] - cols.is_auipc * cols.pc[1] = 0 ∧
  cols.pc_addend[2] - cols.is_auipc * cols.pc[2] = 0 ∧
  (cols.is_real - 1) * cols.op_a_0 = 0

/-- The op_a register access (read prior, write result), exposed for
trace-level OfflineMemory aggregation. `write_value` at aggregation
time is `cols.add_result`. -/
def opAMemoryAccess (cols : UTypeCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_a, 0, 0],
    prev_value := cols.op_a_memory_prev_value,
    prev_low := cols.op_a_memory_prev_low,
    diff_low_limb := cols.op_a_memory_diff_low }

/-- Project a raw SP1 row into the structured `UTypeCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 31) : UTypeCols (ZMod p) :=
  ⟨Main[0], Main[1], Main[2],
   #v[Main[3], Main[4], Main[5]],
   Main[6],
   #v[Main[7], Main[8], Main[9], Main[10]],
   Main[11], Main[12], Main[13],
   #v[Main[14], Main[15], Main[16], Main[17]],
   #v[Main[18], Main[19], Main[20], Main[21]],
   #v[Main[22], Main[23], Main[24]],
   #v[Main[25], Main[26], Main[27], Main[28]],
   Main[29], Main[30], #v[0, 0, 0]⟩

set_option maxHeartbeats 800000 in
-- Higher heartbeats: the iff destructure unfolds the full UType constraint
-- list (CPUState ++ AddOperation ++ JTypeReader ++ 7 trailing assertZeros).
/-- The chip-level bridge: SP1's `allHold` over the flat row
`UType.constraints Main` is exactly the Clean-flavored `Spec (fromMain Main)`,
under `is_real = Main[30] = 1`. The AddOperation clause is preserved in raw
`allHold` form on both sides (the is_real argument `Main[30] - Main[13]` is
the conditional `is_real - op_a_0` rather than the bare `1`, so the
operation-level iff lemma cannot fire). -/
theorem iff_sp1
    (Main : Vector (ZMod p) 31) (h_is_real : Main[30] = 1) :
    (_root_.UType.constraints Main).allHold ↔ Spec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [fromMain, Spec, SP1Clean.CPUState.cpuStateSpec,
    SP1Clean.JTypeReader.jtypeReaderSpec]
  rw [show (_root_.UType.constraints Main).allHold ↔
        ((CPUState.constraints (F := ZMod p)
            { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
              pc := #v[Main[3], Main[4], Main[5]] }
            #v[Main[3] + 4, Main[4], Main[5]] 8 Main[30]).allHold ∧
          (AddOperation.constraints (F := ZMod p)
              #v[Main[22], Main[23], Main[24], 0]
              #v[Main[14], Main[15], Main[16], Main[17]]
              { value := #v[Main[25], Main[26], Main[27], Main[28]] }
              (Main[30] - Main[13])).allHold ∧
          (JTypeReader.constraints (F := ZMod p)
              Main[0] (Main[2] + Main[1] * 65536)
              #v[Main[3], Main[4], Main[5]]
              (Main[29] * 48 + (1 - Main[29]) * 49)
              #v[Main[25], Main[26], Main[27], Main[28]]
              { op_a := Main[6],
                op_a_memory :=
                  { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
                    access_timestamp :=
                      { prev_low := Main[11], diff_low_limb := Main[12] } },
                op_a_0 := Main[13],
                op_b_imm := #v[Main[14], Main[15], Main[16], Main[17]],
                op_c_imm := #v[Main[18], Main[19], Main[20], Main[21]] }
              Main[30] Main[30]).allHold ∧
          (Main[30] * (Main[30] - 1) = 0 ∧
           Main[29] * (Main[29] - 1) = 0 ∧
           Main[22] - (Main[29] * Main[3] + (1 - Main[29]) * 0) = 0 ∧
           Main[23] - (Main[29] * Main[4] + (1 - Main[29]) * 0) = 0 ∧
           Main[24] - (Main[29] * Main[5] + (1 - Main[29]) * 0) = 0 ∧
           (Main[30] - 1) * Main[13] = 0)) from by
      simp [_root_.UType.constraints, SP1ConstraintList.allHold,
        List.forall_append, List.Forall, SP1Constraint.toProp]]
  rw [h_is_real]
  rw [SP1Clean.CPUState.cpuStateSpec_iff_sp1,
      SP1Clean.JTypeReader.jtypeReaderSpec_iff_sp1]
  simp [SP1Clean.CPUState.cpuStateSpec, SP1Clean.JTypeReader.jtypeReaderSpec,
    and_assoc]

/-! ## Full `FormalAssertion` promotion (Path-2)

Wraps the chip-level constraint surface into a Clean `FormalAssertion`.
Composes `SP1Clean.CPUState.assertion` and `SP1Clean.ProgramTable.assertion`
as subcircuits, plus the three scalar trailing assertZero gates
(`is_real` binary, `is_auipc` binary, `(is_real - 1) * op_a_0 = 0`).

**Path-2 drops.** The `AddOperation` clause and the three Vector-indexed
`pc_addend[i] - is_auipc * pc[i] = 0` gates are NOT promoted here. The
Vector-indexed clauses hit the FormalAssertion friction noted in memory
`feedback_formal_assertion_friction` (completeness goals on
`Expression.eval env input_var_pc_addend[i]` don't bridge cleanly to
`cols.pc_addend[i]`). They remain in the legacy chip-level `Spec` /
`iff_sp1` route. Same Path-2 design as `SP1Clean.Jalr.Assertion`. -/

namespace Assertion

open Circuit

/-- Refactored chip-level circuit using subcircuit composition. Drops
the AddOperation byte lookups and the 3 Vector-indexed `pc_addend`
clauses (see Scope note above). -/
@[reducible]
def main (cols : Var UTypeCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a, _op_a_memory_prev_value,
       _op_a_memory_prev_low, _op_a_memory_diff_low, op_a_0, op_b_imm,
       op_c_imm, _pc_addend, _add_result, is_auipc, is_real,
       next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_auipc * 48 + (1 - is_auipc) * 49,
      op_a, op_b_imm, op_c_imm, op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_carry_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  is_auipc * (is_auipc - 1) === 0
  (is_real - 1) * op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) UTypeCols unit where
  name := "SP1Clean.UType"
  main := main
  localLength _ := 0

def Assumptions (_ : UTypeCols (ZMod p)) : Prop := True

/-- The chip's Circuit-derivable spec: byte-lookup consequences for the
clock-decomposition gadget, the program-bus existential witness, and the
three scalar trailing assertZero gates. -/
def FormalSpec (cols : UTypeCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc,
      opcode := cols.is_auipc * 48 + (1 + -cols.is_auipc) * 49,
      op_a := cols.op_a,
      op_b := cols.op_b_imm,
      op_c := cols.op_c_imm,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 0 } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.pc[0], cols.pc[1], cols.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.is_auipc * (cols.is_auipc - 1) = 0 ∧
  (cols.is_real - 1) * cols.op_a_0 = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
          e16⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_isreal, h_isauipc, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · simp only [Vector.getElem_map]
    exact h_addr_sub trivial
  · linear_combination h_isreal
  · linear_combination h_isauipc
  · linear_combination h_op_a_0

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15,
          e16⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_addr, h_isreal, h_isauipc, h_op_a_0⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr
    exact h_addr
  · linear_combination h_isreal
  · linear_combination h_isauipc
  · linear_combination h_op_a_0

end Assertion

/-- The full Clean `FormalAssertion` for the byte- and program-lookup-
derivable subset of `UTypeChip`'s constraint surface (Path-2 design;
drops the `AddOperation` byte lookups). -/
def assertion : FormalAssertion (ZMod p) UTypeCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.UType
