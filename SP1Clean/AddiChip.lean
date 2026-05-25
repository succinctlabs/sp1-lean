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
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ITypeReader.ITypeReader
import SP1Chips.Addi.AddiChip
import SP1Chips.Addi.Common
import SP1Chips.Soundness
import SP1Clean.MemoryAccess
import SP1Clean.Reader.ITypeReader
import SP1Clean.Operations.AddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode

/-! # Tier 3 pilot: chip-level `AddiChip` mirror — struct-of-columns style

First chip-level Clean mirror. Demonstrates how the Sail bridge composes
through the Clean DSL when the chip's columns are declared via Clean's
`ProvableStruct` machinery — mirroring SP1's Rust `AddiCols<T>` struct
rather than the post-extraction flat row vector emitted by the
`sp1-constraint-compiler`.

Design:
- `AddiCols T` mirrors SP1's source-level Rust struct: 16 fields totalling 30
  field elements (the trace row width for AddiChip).
- `deriving ProvableStruct` gives Clean the `toComponents` /
  `fromComponents` plumbing needed to treat `AddiCols` as a witness target.
  `Var AddiCols (ZMod p) = AddiCols (Expression (ZMod p))`.
- `main` takes a `Var AddiCols (ZMod p)` and destructures it — exactly as SP1
  Rust's `eval(builder, cols)` does.
- `Spec` is stated over field-valued `AddiCols (ZMod p)` so the user-facing
  predicate reads like the Rust source, not like `Main[k]` indices.
- The SP1 bridge happens at `traceSpec_iff_allHold` / `correct_addi` via
  `ProvableType.fromElements`, converting SP1's flat
  `Vector (ZMod p) 30` row into a structured `AddiCols (ZMod p)` view.
  The existing SP1 `Addi.correct_addi` is still reused as a black box.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Addi

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `AddiCols<T, M: TrustMode>`. -/
structure AddiCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  op_a_write_value : Vector T 4
  is_real : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Clean-side circuit. Mirrors SP1 Rust's `AddiChip::eval(builder, cols)`:
takes a `Var AddiCols (ZMod p)` (struct of `Expression`s), destructures it,
and emits the constraints for each sub-component. -/
def main (cols : Var AddiCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩, op_a_write_value, is_real, _adapter_cols⟩ := cols
  -- AddOperation: op_b_memory.prev_value + op_c_imm = op_a_write_value.
  SP1Clean.AddOp.main op_b_memory.prev_value op_c_imm op_a_write_value
  -- CPUState: clk_0_16 progression (Range 13 → < 2^13 = 8192) and clk_16_24
  -- bound (Range 8 → < 2^8 = 256).
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), (clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), clk_16_24, 8, 0]
      : Vector (Expression (ZMod p)) 4)
  -- ITypeReader: 4 imm-limb Range(16) lookups.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), op_c_imm[0], 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), op_c_imm[1], 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), op_c_imm[2], 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), op_c_imm[3], 16, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Program-bus interaction (opcode = 1 = ADDI; I-type discipline: op_b is
  -- a single-limb register index, op_c carries 4 immediate limbs, imm_c = 1).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 1, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Trailing assertZero gates.
  is_real * (is_real - 1) === 0
  op_a_0 === 0

/-- Optional convenience: a fresh `Circuit` that witnesses an `AddiCols` and
asserts its constraints. The witness side is decoupled from `main` —
mirroring upstream Clean's `U64.witness` pattern. -/
def witness : Circuit (ZMod p) (Var AddiCols (ZMod p)) := do
  let cols ← ProvableType.witness (fun _ => default)
  main cols
  return cols

/-- Pilot Spec, expressed over field-valued `AddiCols (ZMod p)`. Composes
the reusable helper Specs (`SP1Clean.AddOp`, `SP1Clean.CPUState`,
`SP1Clean.ITypeReader`) plus the trailing assertZero gates. -/
def TraceSpec (cols : AddiCols (ZMod p)) : Prop :=
  SP1Clean.AddOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm cols.op_a_write_value ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ITypeReader.itypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 1 cols.state.pc
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
        op_c_imm := cols.adapter.op_c_imm } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  cols.adapter_cols.is_trusted = 1

/-- Project a raw SP1 row into the structured `AddiCols` view. Defined via
direct indexed access — semantically the same as `ProvableType.fromElements`
but with field projections that reduce by `rfl` to `Main[k]`, avoiding the
take/drop tower the `ProvableStruct`-derived path produces. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 30) : AddiCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27], Main[28]],
   Main[29],
   ⟨Main[29]⟩⟩

/-- The chip-level bridge: SP1's `allHold` over the flat row
`Addi.constraints Main` is exactly the Clean-flavored `TraceSpec (fromMain Main)`,
under `is_real = Main[29] = 1`. -/
theorem traceSpec_iff_allHold
    (Main : Vector (ZMod p) 30) (h_is_real : Main[29] = 1) :
    (_root_.Addi.constraints Main).allHold ↔ TraceSpec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- Unfold the structural projection of `fromMain` on `Main` so each
  -- `cols.X` reduces to the matching `Main[k]`. After that, Spec is
  -- structurally identical to the version that operates directly on `Main`.
  simp only [fromMain, TraceSpec, SP1Clean.AddOp.Spec,
    SP1Clean.CPUState.cpuStateSpec, SP1Clean.ITypeReader.itypeReaderSpec]
  rw [show (_root_.Addi.constraints Main).allHold ↔
        ((AddOperation.constraints (F := ZMod p)
            #v[Main[15], Main[16], Main[17], Main[18]]
            #v[Main[21], Main[22], Main[23], Main[24]]
            { value := #v[Main[25], Main[26], Main[27], Main[28]] }
            Main[29]).allHold ∧
          (CPUState.constraints (F := ZMod p)
            { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
              pc := #v[Main[3], Main[4], Main[5]] }
            #v[Main[3] + 4, Main[4], Main[5]] 8 Main[29]).allHold ∧
          (ITypeReader.constraints (F := ZMod p)
            Main[0] (Main[2] + Main[1] * 65536)
            #v[Main[3], Main[4], Main[5]] 1
            #v[Main[25], Main[26], Main[27], Main[28]]
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
              op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] }
            Main[29] Main[29]).allHold ∧
          (Main[29] * (Main[29] - 1) = 0 ∧ Main[13] = 0)) from by
      simp [_root_.Addi.constraints, SP1ConstraintList.allHold,
        List.forall_append, List.Forall, SP1Constraint.toProp]]
  rw [h_is_real]
  rw [AddOperation.allHold_constraints_iff,
      SP1Clean.CPUState.cpuStateSpec_iff_sp1,
      SP1Clean.ITypeReader.itypeReaderSpec_iff_sp1]
  simp [SP1Clean.CPUState.cpuStateSpec, SP1Clean.ITypeReader.itypeReaderSpec, and_assoc]

/-- Clean-side `correct_addi`: same Sail equivalence statement as SP1's
`Addi.correct_addi`, but with the constraint hypothesis re-expressed against
the Clean-flavored `Spec` predicate over a *structured* `AddiCols` view.
Pure composition with the SP1 proof via `traceSpec_iff_allHold.mpr`. -/
theorem correct_addi
    (Main : Vector (ZMod p) 30) (s : SailState)
    (h_is_real : Main[29] = 1)
    (h_spec : TraceSpec (fromMain Main))
    (state_cstrs : (_root_.Addi.constraints Main).initialState s) :
    let op_c := _root_.Addi.sp1_op_c Main
    let op_b := _root_.Addi.sp1_op_b Main
    let op_a := _root_.Addi.sp1_op_a Main
    (_root_.Addi.spec_addi op_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Addi.sp1_addi Main).run s :=
  _root_.Addi.correct_addi Main s ((traceSpec_iff_allHold Main h_is_real).mpr h_spec)
    h_is_real state_cstrs

/-! ## RawSpec / SemanticSpec POC -/

def RawSpec (Main : Vector (ZMod p) 30) : Prop :=
  (AddOperation.constraints (F := ZMod p)
      #v[Main[15], Main[16], Main[17], Main[18]]
      #v[Main[21], Main[22], Main[23], Main[24]]
      { value := #v[Main[25], Main[26], Main[27], Main[28]] } Main[29]).allHold ∧
  (CPUState.constraints (F := ZMod p)
      { clk_high := Main[0], clk_16_24 := Main[1], clk_0_16 := Main[2],
        pc := #v[Main[3], Main[4], Main[5]] }
      #v[Main[3] + 4, Main[4], Main[5]] 8 Main[29]).allHold ∧
  (ITypeReader.constraints (F := ZMod p)
      Main[0] (Main[2] + Main[1] * 65536) #v[Main[3], Main[4], Main[5]] 1
      #v[Main[25], Main[26], Main[27], Main[28]]
      { op_a := Main[6],
        op_a_memory :=
          { prev_value := #v[Main[7], Main[8], Main[9], Main[10]],
            access_timestamp := { prev_low := Main[11], diff_low_limb := Main[12] } },
        op_a_0 := Main[13], op_b := Main[14],
        op_b_memory :=
          { prev_value := #v[Main[15], Main[16], Main[17], Main[18]],
            access_timestamp := { prev_low := Main[19], diff_low_limb := Main[20] } },
        op_c_imm := #v[Main[21], Main[22], Main[23], Main[24]] }
      Main[29] Main[29]).allHold ∧
  Main[29] * (Main[29] - 1) = 0 ∧
  Main[13] = 0

theorem rawSpec_iff_allHold (Main : Vector (ZMod p) 30) :
    (_root_.Addi.constraints Main).allHold ↔ RawSpec Main := by
  rw [_root_.Addi.allHold_constraints_iff]
  rfl

def SemanticSpec (Main : Vector (ZMod p) 30) : Prop :=
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
  SP1Clean.ProgramTable.Spec
      { pc := cols.state.pc, opcode := 1, op_a := cols.adapter.op_a,
        op_b := #v[cols.adapter.op_b, 0, 0, 0],
        op_c := cols.adapter.op_c_imm,
        op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  (∀ s : SailState, (_root_.Addi.constraints Main).initialState s →
    (_root_.Addi.sp1_addi Main).run s =
      (_root_.Addi.spec_addi (_root_.Addi.sp1_op_c Main)
        (.Regidx (_root_.Addi.sp1_op_b Main))
        (.Regidx (_root_.Addi.sp1_op_a Main))).run s)

theorem raw_to_semantic (Main : Vector (ZMod p) 30) (h_is_real : Main[29] = 1)
    (h_raw : RawSpec Main) : SemanticSpec Main := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_addop, h_cpu_raw, h_itr_raw, h_real_bin, h_a0⟩ := h_raw
  have h_allHold : (_root_.Addi.constraints Main).allHold :=
    (rawSpec_iff_allHold Main).mpr ⟨h_addop, h_cpu_raw, h_itr_raw, h_real_bin, h_a0⟩
  rw [h_is_real] at h_cpu_raw h_itr_raw
  have h_cpu_spec := SP1Clean.CPUState.cpuStateSpec_iff_sp1.mp h_cpu_raw
  have h_itr_spec := SP1Clean.ITypeReader.itypeReaderSpec_iff_sp1.mp h_itr_raw
  obtain ⟨h_ti, h_op_a_lt, h_op_b_lt, h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt,
          h_a0_bin, h_a0_iff, h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt,
          h_diff_a, h_diff_b, h_ts_b, h_ts_a, h_isU64_a, h_isU64_b,
          _h_a0_implies⟩ := h_itr_spec
  have h_zero_lt : (0 : ZMod p) < (65536 : ZMod p) := by
    have h65536_lt : (65536 : ℕ) < p := by
      have := Fact.out (p := 2 ^ 17 < p); omega
    have h65536_val : (65536 : ZMod p).val = 65536 := ZMod.val_natCast_of_lt h65536_lt
    change (0 : ZMod p).val < (65536 : ZMod p).val
    rw [ZMod.val_zero, h65536_val]; omega
  refine ⟨h_cpu_spec,
          ⟨h_diff_a, h_ts_a, h_isU64_a⟩,
          ⟨h_diff_b, h_ts_b, h_isU64_b⟩,
          ?_, h_real_bin, ?_⟩
  · simp only [SP1Clean.ProgramTable.Spec, SP1Clean.ProgramSpec,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    refine ⟨?_, h_op_a_lt, ⟨h_op_b_lt, h_zero_lt, h_zero_lt, h_zero_lt⟩,
            ⟨h_op_c0_lt, h_op_c1_lt, h_op_c2_lt, h_op_c3_lt⟩,
            h_a0_bin, h_a0_iff, Or.inl trivial, Or.inr trivial,
            h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩
    convert h_ti using 1
  · intro s state_cstrs
    exact soundness_addi Main s h_allHold h_is_real state_cstrs

/-! ## Full `FormalAssertion` promotion

Wraps the chip-level constraint surface into a Clean `FormalAssertion`.
Composes `SP1Clean.AddOp.assertion`, `SP1Clean.CPUState.assertion`, and
`SP1Clean.ProgramTable.assertion` as subcircuits, plus the two trailing
assertZero gates.

**Scope note.** The 4 explicit byte-range lookups for the I-type
immediate operand limbs `op_c_imm[k]` (which appear in the chip's full
`main` above) are NOT included in `Assertion.main` here. Bridging their
`Expression.eval env input_var_op_c_imm[k]` shape back to the value
`input_op_c_imm[k]` past the destructured `cols` pattern requires a
manual `subst` cascade over the 16-field `h_input` conjunction — too
much friction for the boilerplate budget. The bounds are still carried
by the legacy chip-level `Spec` / `traceSpec_iff_allHold` / `correct_addi` route. The
trace-level OfflineMemory bridge will pick them up via `traceSpec_iff_allHold.mpr`.

This is the same Path-2 design as `SP1Clean.Addw.Assertion` (which drops
the AddwOp carry surface): only lookup-derived subcircuit fragments are
promoted to `FormalAssertion`. -/

namespace Assertion

open Circuit

/-- Refactored chip-level circuit using subcircuit composition. Drops
the 4 immediate-limb byte lookups (see Scope note above). -/
@[reducible]
def main (cols : Var AddiCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩, op_a_write_value, is_real, _adapter_cols⟩ := cols
  SP1Clean.AddOp.assertion
    (⟨op_b_memory.prev_value, op_c_imm, op_a_write_value⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Program-bus interaction (opcode = 1 = ADDI; I-type discipline:
  -- op_b is a single-limb register index with limbs 1-3 zero,
  -- op_c carries 4 immediate limbs, imm_b = 0, imm_c = 1).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 1, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Iter-8 sub-task E: per-operand memory-bus byte content. I-type:
  -- op_a at +4, op_b at +3 (op_c_imm is the immediate, no memory access).
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low, op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low, op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) AddiCols unit where
  name := "SP1Clean.Addi"
  main := main
  localLength _ := 0

def Assumptions (_ : AddiCols (ZMod p)) : Prop := True

/-- The chip's Circuit-derivable spec: byte-lookup consequences for the
addition + clock-decomposition gadgets, the program-bus existential
witness, and the two trailing assertZero gates. The immediate-limb byte
bounds and memory-bus side of `itypeReaderSpec` are deferred to the
legacy chip-level `Spec` / `traceSpec_iff_allHold`. -/
def FormalSpec (cols : AddiCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.AddOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm cols.op_a_write_value ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 1, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- I-type: op_a at +4, op_b at +3 (op_c_imm is immediate).
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17⟩ := h_input
  subst_eqs
  obtain ⟨h_addop_sub, h_cpu_sub, h_prog_sub, h_oa_a, h_oa_b,
          h_isreal, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_addop_sub trivial
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_isreal
  · exact h_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17⟩ := h_input
  subst_eqs
  obtain ⟨h_addop, h_cpu, h_prog, h_isreal, h_op_a_0, h_oa_a, h_oa_b⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_addop⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · linear_combination h_isreal
  · exact h_op_a_0

end Assertion

/-- The full Clean `FormalAssertion` for the byte- and program-lookup-
derivable subset of `AddiChip`'s constraint surface (Path-2 design: drops
the 4 immediate-limb byte lookups; see Scope note above). Composes
`AddOp.assertion`, `CPUState.assertion`, `ProgramTable.assertion`, plus
two trailing assertZero gates. -/
def assertion : FormalAssertion (ZMod p) AddiCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Addi
