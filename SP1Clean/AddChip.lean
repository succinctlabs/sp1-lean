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
import SP1Operations.Operation.AddOperation
import SP1Operations.Reader.CPUState
import SP1Operations.Reader.RTypeReader
import SP1Chips.AddChip
import SP1Clean.AddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader

/-! # Chip-level `AddChip` mirror — R-type sibling of `AddiChip`

The R-type Add chip: 33 columns, composes `SP1Clean.AddOp` with
`CPUState` and `RTypeReader` Spec helpers. Differs from `AddiChip` by
having `op_c` as a register (with full memory-access substruct) rather
than the four immediate-byte limbs `op_c_imm`, and by carrying opcode
index `0` (`ADD`) into `RTypeReader`.

The chip's `Spec` is stated over a structured `AddCols (ZMod p)` view of
the flat row — same `ProvableStruct` discipline as `AddiCols` — with the
sub-fragment surfaces packaged as `SP1Clean.AddOp.Spec`,
`SP1Clean.CPUState.cpuStateSpec`, and `SP1Clean.RTypeReader.rtypeReaderSpec`.
-/

namespace SP1Clean.Add

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `AddCols<T>`. -/
structure AddCols (T : Type) where
  clk_high : T
  clk_16_24 : T
  clk_0_16 : T
  pc : Vector T 3
  op_a : T
  op_a_memory_prev_value : Vector T 4
  op_a_memory_prev_low : T
  op_a_memory_diff_low : T
  op_a_0 : T
  op_b : T
  op_b_memory_prev_value : Vector T 4
  op_b_memory_prev_low : T
  op_b_memory_diff_low : T
  op_c : T
  op_c_memory_prev_value : Vector T 4
  op_c_memory_prev_low : T
  op_c_memory_diff_low : T
  op_a_write_value : Vector T 4
  is_real : T
deriving ProvableStruct

/-- Clean-side circuit. Mirrors SP1 Rust's `AddChip::eval(builder, cols)`:
takes a `Var AddCols (ZMod p)`, destructures it, and emits constraints for
each sub-component. -/
def main (cols : Var AddCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a, _op_a_memory_prev_value,
       _op_a_memory_prev_low, _op_a_memory_diff_low, op_a_0, op_b,
       op_b_memory_prev_value, _op_b_memory_prev_low, _op_b_memory_diff_low,
       op_c, op_c_memory_prev_value, _op_c_memory_prev_low,
       _op_c_memory_diff_low, op_a_write_value, is_real⟩ := cols
  -- AddOperation: op_b_memory.prev_value + op_c_memory.prev_value = op_a_write_value.
  SP1Clean.AddOp.main op_b_memory_prev_value op_c_memory_prev_value op_a_write_value
  -- CPUState: clk_0_16 progression and clk_16_24 byte bound.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), (clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), clk_16_24, 8, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Program-bus interaction for ADD (opcode 0): one lookup into the
  -- 16-tuple program ROM table. R-type discipline: op_b/op_c each carry a
  -- single-limb register index (limbs 1-3 zero), and imm_b = imm_c = 0.
  lookup ProgramTable
    (#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p)),
        op_a, op_b, 0, 0, 0,
        op_c, 0, 0, 0,
        op_a_0, 0, 0]
      : Vector (Expression (ZMod p)) 16)
  -- Trailing assertZero gates.
  is_real * (is_real - 1) === 0
  op_a_0 === 0

/-- Pilot Spec, expressed over field-valued `AddCols (ZMod p)`. Each clause
mirrors one sub-component's constraint surface under `is_real = 1`, using
the reusable helper Specs from `SP1Clean.AddOp`, `SP1Clean.CPUState`, and
`SP1Clean.RTypeReader`. -/
def Spec (cols : AddCols (ZMod p)) : Prop :=
  SP1Clean.AddOp.Spec
      cols.op_b_memory_prev_value cols.op_c_memory_prev_value
      cols.op_a_write_value ∧
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.RTypeReader.rtypeReaderSpec
      (cols.clk_0_16 + cols.clk_16_24 * 65536) 0 cols.pc
      cols.op_a_write_value
      { op_a := cols.op_a,
        op_a_memory :=
          { prev_value := cols.op_a_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_a_memory_prev_low,
                diff_low_limb := cols.op_a_memory_diff_low } },
        op_a_0 := cols.op_a_0, op_b := cols.op_b,
        op_b_memory :=
          { prev_value := cols.op_b_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_b_memory_prev_low,
                diff_low_limb := cols.op_b_memory_diff_low } },
        op_c := cols.op_c,
        op_c_memory :=
          { prev_value := cols.op_c_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_c_memory_prev_low,
                diff_low_limb := cols.op_c_memory_diff_low } } } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.op_a_0 = 0

/-- Project a raw SP1 row into the structured `AddCols` view. Mirrors the
index map in `SP1Chips/Add/Constraints.lean`. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 33) : AddCols (ZMod p) :=
  ⟨Main[0], Main[1], Main[2],
   #v[Main[3], Main[4], Main[5]],
   Main[6],
   #v[Main[7], Main[8], Main[9], Main[10]],
   Main[11], Main[12], Main[13], Main[14],
   #v[Main[15], Main[16], Main[17], Main[18]],
   Main[19], Main[20], Main[21],
   #v[Main[22], Main[23], Main[24], Main[25]],
   Main[26], Main[27],
   #v[Main[28], Main[29], Main[30], Main[31]],
   Main[32]⟩

/-- The chip-level bridge: SP1's `allHold_poly` over the flat row
`Add.constraints Main` is exactly `Spec (fromMain Main)`, under
`is_real = Main[32] = 1`. -/
theorem iff_sp1
    (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1) :
    (_root_.Add.constraints Main).allHold_poly ↔ Spec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [fromMain, Spec, SP1Clean.AddOp.Spec,
    SP1Clean.CPUState.cpuStateSpec, SP1Clean.RTypeReader.rtypeReaderSpec]
  rw [show (_root_.Add.constraints Main).allHold_poly ↔
        ((AddOperation.constraints (F := ZMod p)
            #v[Main[15], Main[16], Main[17], Main[18]]
            #v[Main[22], Main[23], Main[24], Main[25]]
            { value := #v[Main[28], Main[29], Main[30], Main[31]] }
            Main[32]).allHold_poly ∧
          (CPUState.constraints (F := ZMod p)
            { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
              pc := #v[Main[3], Main[4], Main[5]] }
            #v[Main[3] + 4, Main[4], Main[5]] 8 Main[32]).allHold_poly ∧
          (RTypeReader.constraints (F := ZMod p)
            Main[0] (Main[2] + Main[1] * 65536)
            #v[Main[3], Main[4], Main[5]] 0
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
            Main[32] Main[32]).allHold_poly ∧
          (Main[32] * (Main[32] - 1) = 0 ∧ Main[13] = 0)) from by
      simp [_root_.Add.constraints, SP1ConstraintList.allHold_poly,
        List.forall_append, List.Forall, SP1Constraint.toProp_poly]]
  rw [h_is_real]
  rw [AddOperation.allHold_constraints_iff_poly,
      SP1Clean.CPUState.cpuStateSpec_iff_sp1,
      SP1Clean.RTypeReader.rtypeReaderSpec_iff_sp1]
  simp [SP1Clean.CPUState.cpuStateSpec, SP1Clean.RTypeReader.rtypeReaderSpec, and_assoc]

/-- Clean-side `correct_add`: same Sail equivalence statement as SP1's
`Add.correct_add`, but with the constraint hypothesis re-expressed against
the Clean-flavored `Spec` predicate over a structured `AddCols` view.
Pure composition with the SP1 proof via `iff_sp1.mpr`. -/
theorem correct_add
    (Main : Vector (ZMod p) 33) (s : SailState)
    (h_is_real : Main[32] = 1)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Add.constraints Main).initialState_poly s) :
    let op_c := _root_.Add.sp1_op_c Main
    let op_b := _root_.Add.sp1_op_b Main
    let op_a := _root_.Add.sp1_op_a Main
    (_root_.Add.spec_add (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Add.sp1_add Main).run s :=
  _root_.Add.correct_add Main s ((iff_sp1 Main h_is_real).mpr h_spec)
    h_is_real state_cstrs

/-! ## Full `FormalAssertion` promotion

Wraps the chip-level constraint surface into a Clean `FormalAssertion`.
Composes `SP1Clean.AddOp.assertion` and `SP1Clean.CPUState.assertion` as
subcircuits, emits an explicit `lookup ProgramTable` for the program-bus
interaction, and finishes with the two trailing assertZero gates.

**Scope note (memory).** `SP1Clean.RTypeReader.rtypeReaderSpec` carries
two interaction surfaces: program (now covered by `ProgramTable`) and
memory (3 register-read accesses with timestamp + U64 bounds). The
memory clauses are not enforced inside `Assertion.main` because the
required reader-level byte lookups (6 for timestamps + 12 for U64 limbs)
aren't yet lifted into Clean. `FormalSpec` therefore captures the
program-bus consequence (`ProgramSpec`) but defers memory-bus consequences
to the trace-level `SP1Clean.Soundness.MemoryConsistency` bridge, which
threads each chip's emitted `MemoryAccess` records into Clean's
`OfflineMemory` consistency theorem. The full `Spec` above and
`correct_add` continue to consume the legacy `rtypeReaderSpec`. -/

namespace Assertion

open Circuit

/-- Refactored chip-level circuit using subcircuit composition. -/
@[reducible]
def main (cols : Var AddCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a, _op_a_memory_prev_value,
       _op_a_memory_prev_low, _op_a_memory_diff_low, op_a_0, op_b,
       op_b_memory_prev_value, _op_b_memory_prev_low, _op_b_memory_diff_low,
       op_c, op_c_memory_prev_value, _op_c_memory_prev_low,
       _op_c_memory_diff_low, op_a_write_value, is_real⟩ := cols
  SP1Clean.AddOp.assertion
    (⟨op_b_memory_prev_value, op_c_memory_prev_value, op_a_write_value⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Program-bus interaction (opcode = 0 = ADD; R-type discipline:
  -- op_b/op_c are single-limb register indices with limbs 1-3 zero,
  -- imm_b = imm_c = 0).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 0, op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) AddCols unit where
  name := "SP1Clean.Add"
  main := main
  localLength _ := 0

def Assumptions (_ : AddCols (ZMod p)) : Prop := True

/-- The chip's Circuit-derivable spec: byte-lookup consequences for the
addition + clock-decomposition gadgets, the program-bus existential
witness, and the two trailing assertZero gates. The memory-bus side of
`rtypeReaderSpec` is deferred to the trace-level OfflineMemory bridge. -/
def FormalSpec (cols : AddCols (ZMod p)) : Prop :=
  SP1Clean.AddOp.Spec
      cols.op_b_memory_prev_value cols.op_c_memory_prev_value
      cols.op_a_write_value ∧
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc, opcode := 0, op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := #v[cols.op_c, 0, 0, 0],
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 0 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.op_a_0 = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_addop_sub, h_cpu_sub, h_prog_sub, h_isreal, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h_addop_sub trivial
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_isreal
  · exact h_op_a_0

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_addop, h_cpu, h_prog, h_isreal, h_op_a_0⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_addop⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_isreal
  · exact h_op_a_0

end Assertion

/-- The full Clean `FormalAssertion` for the byte- and program-lookup-
derivable subset of `AddChip`'s constraint surface. Composes
`AddOp.assertion` and `CPUState.assertion`, the `ProgramTable` lookup,
and two trailing assertZero gates. -/
def assertion : FormalAssertion (ZMod p) AddCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Add
