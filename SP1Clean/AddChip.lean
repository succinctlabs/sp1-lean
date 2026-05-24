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
import SP1Operations.Reader.RTypeReader.RTypeReader
import SP1Chips.Add.AddChip
import SP1Chips.Soundness
import SP1Clean.AddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.Reader.OperandAccess
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.RTypeReader
import SP1Clean.TrustMode

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

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Add

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `AddCols<T, M: TrustMode>`
(`sp1/crates/core/machine/src/alu/add_sub/add.rs:47-62`). The
`adapter_cols : UserModeReaderCols T` slot is the last field, matching Rust
under `M = UserMode`. We don't carry an explicit `M` type parameter on the
struct because `deriving ProvableStruct` can't reduce through an abstract
`M`; future SupervisorMode chips would use a separate `*ColsSupervisor`
struct with `adapter_cols : EmptyCols T`. -/
structure AddCols (T : Type) where
  state : CPUState T
  adapter : RTypeReader T
  op_a_write_value : Vector T 4
  is_real : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

/-- Project a raw SP1 row into the structured `AddCols` view. Mirrors the
index map in `SP1Chips/Add/Constraints.lean`. `adapter_cols.is_trusted`
aliases `Main[32]` (= `is_real`) because the current extractor passes
`Main[32] Main[32]` to `RTypeReader.constraints` (see
`SP1Chips/Add/Constraints.lean:21`). When upstream regen lands a separate
`is_trusted` Main column, switch to that index. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 33) : AddCols (ZMod p) :=
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

/-- Clean-side circuit. Mirrors SP1 Rust's `AddChip::eval(builder, cols)`:
takes a `Var AddCols (ZMod p)`, destructures it, and emits constraints for
each sub-component. -/
def AddCircuit (cols : Var AddCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory⟩,
       op_a_write_value, is_real, _adapter_cols⟩ := cols
  -- AddOperation: op_b_memory.prev_value + op_c_memory.prev_value = op_a_write_value.
  SP1Clean.AddOp.main op_b_memory.prev_value op_c_memory.prev_value op_a_write_value
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

/-- Pilot Spec, expressed over field-valued `AddCols (ZMod p)`.
Each clause mirrors one sub-component's constraint surface under
`is_real = 1`, using the reusable helper Specs from `SP1Clean.AddOp`,
`SP1Clean.CPUState`, and `SP1Clean.RTypeReader`. The trailing
`cols.adapter_cols.is_trusted = 1` conjunct pins the
`UserModeReaderCols<T>` payload to the trusted-row case we verify. -/
def TraceSpec (cols : AddCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.RTypeReader.rtypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 0 cols.state.pc
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

def ArithSpec (cols : AddCols (ZMod p)) : Prop :=
  SP1Clean.AddOp.Spec
    cols.adapter.op_b_memory.prev_value cols.adapter.op_c_memory.prev_value
    cols.op_a_write_value

/-- The chip-level bridge: SP1's `allHold` over the flat row
`Add.constraints Main` is exactly `TraceSpec (fromMain Main)`, under
`is_real = Main[32] = 1`. -/
theorem traceSpec_iff_allHold
    (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1) :
    (_root_.Add.constraints Main).allHold ↔
      ArithSpec (fromMain Main) ∧ TraceSpec (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [fromMain, TraceSpec, ArithSpec, SP1Clean.AddOp.Spec,
    SP1Clean.CPUState.cpuStateSpec, SP1Clean.RTypeReader.rtypeReaderSpec]
  rw [show (_root_.Add.constraints Main).allHold ↔
        ((AddOperation.constraints (F := ZMod p)
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
            Main[32] Main[32]).allHold ∧
          (Main[32] * (Main[32] - 1) = 0 ∧ Main[13] = 0)) from by
      simp [_root_.Add.constraints, SP1ConstraintList.allHold,
        List.forall_append, List.Forall, SP1Constraint.toProp]]
  rw [h_is_real]
  rw [AddOperation.allHold_constraints_iff,
      SP1Clean.CPUState.cpuStateSpec_iff_sp1,
      SP1Clean.RTypeReader.rtypeReaderSpec_iff_sp1]
  simp [SP1Clean.CPUState.cpuStateSpec, SP1Clean.RTypeReader.rtypeReaderSpec, and_assoc]

/-- Clean-side `correct_add`: same Sail equivalence statement as SP1's
`Add.correct_add`, but with the constraint hypothesis re-expressed against
the Clean-flavored `Spec` predicate over a structured `AddCols` view.
Pure composition with the SP1 proof via `traceSpec_iff_allHold.mpr`. -/
theorem correct_add
    (Main : Vector (ZMod p) 33) (s : SailState)
    (h_is_real : Main[32] = 1)
    (h_arith : ArithSpec (fromMain Main))
    (h_trace : TraceSpec (fromMain Main))
    (state_cstrs : (_root_.Add.constraints Main).initialState s) :
    let op_c := _root_.Add.sp1_op_c Main
    let op_b := _root_.Add.sp1_op_b Main
    let op_a := _root_.Add.sp1_op_a Main
    (_root_.Add.spec_add (.Regidx op_c) (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Add.sp1_add Main).run s :=
  _root_.Add.correct_add Main s ((traceSpec_iff_allHold Main h_is_real).mpr ⟨h_arith, h_trace⟩)
    h_is_real state_cstrs

/-! ## RawSpec / SemanticSpec POC

A two-layer alternative to the legacy `Spec` + `traceSpec_iff_allHold` pair. The split:

- **`RawSpec Main`** is a structural mirror of `(Add.constraints Main).allHold`
  flattened into named sub-`allHold`s. Pure transcription of the chip-list
  shape — no arithmetic reasoning. `rawSpec_iff_allHold` discharges via the
  same `simp` recipe the legacy `traceSpec_iff_allHold` uses.
- **`SemanticSpec Main`** is the user-facing contract: trace-facing data
  (`cpuStateSpec`, three `memoryAccessSpec` records, `ProgramTable.Spec`,
  is-real-binary) **plus** the per-row Sail equivalence as a Prop.
- **`raw_to_semantic`** does the bridging work — the only place where the
  chip-internal arithmetic (here `AddOperation.allHold`'s carry-chain content,
  bridged via the operation-level Specs and `Add.correct_add`) is referenced.

Downstream consumers see only `SemanticSpec`; they never touch the chip-list
flattening or carry-chain assertions. POC scope: additive only, the legacy
`Spec` + `traceSpec_iff_allHold` + `correct_add` remain in place. -/

/-- Structural mirror of `Add.constraints.allHold`. Iff-RHS over `Main`. -/
def RawSpec (Main : Vector (ZMod p) 33) : Prop :=
  (AddOperation.constraints (F := ZMod p)
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
      Main[32] Main[32]).allHold ∧
  Main[32] * (Main[32] - 1) = 0 ∧
  Main[13] = 0

omit [Fact (2 ^ 17 < p)] in
/-- `RawSpec` is exactly `allHold`. Pure restatement; no arithmetic. -/
theorem rawSpec_iff_allHold (Main : Vector (ZMod p) 33) :
    (_root_.Add.constraints Main).allHold ↔ RawSpec Main := by
  simp only [RawSpec]
  simp [_root_.Add.constraints, SP1ConstraintList.allHold,
    List.forall_append, List.Forall, SP1Constraint.toProp, and_assoc]

/-- The row's user-facing contract: trace-facing structural specs + Sail
equivalence as a Prop. Downstream consumers (trace soundness, etc.) see only
this; the chip-internal arithmetic is hidden behind `raw_to_semantic`. -/
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
      { pc := cols.state.pc, opcode := 0, op_a := cols.adapter.op_a,
        op_b := #v[cols.adapter.op_b, 0, 0, 0],
        op_c := #v[cols.adapter.op_c, 0, 0, 0],
        op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 0 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  -- Per-row Sail equivalence as a Prop. Trace level can chain these.
  (∀ s : SailState, (_root_.Add.constraints Main).initialState s →
    (_root_.Add.sp1_add Main).run s =
      (_root_.Add.spec_add (.Regidx (_root_.Add.sp1_op_c Main))
        (.Regidx (_root_.Add.sp1_op_b Main))
        (.Regidx (_root_.Add.sp1_op_a Main))).run s)

/-- The bridge: `RawSpec → SemanticSpec` under `is_real = 1`. Confines all
chip-internal arithmetic (carry chain via `AddOperation`'s spec, byte ranges
via `rtypeReaderSpec`, Sail equivalence via `soundness_add`) to this one proof.
Callers see only `SemanticSpec`. -/
theorem raw_to_semantic (Main : Vector (ZMod p) 33) (h_is_real : Main[32] = 1)
    (h_raw : RawSpec Main) : SemanticSpec Main := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  obtain ⟨h_addop, h_cpu_raw, h_rtr_raw, h_real_bin, h_a0⟩ := h_raw
  have h_allHold : (_root_.Add.constraints Main).allHold :=
    (rawSpec_iff_allHold Main).mpr ⟨h_addop, h_cpu_raw, h_rtr_raw, h_real_bin, h_a0⟩
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
  -- ProgramTable.Spec: assemble from rtypeReaderSpec's program-bus pieces
  -- + trivial 0 < 65536 for the unused op_b/op_c high limbs.
  · simp only [SP1Clean.ProgramTable.Spec, SP1Clean.ProgramSpec,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ]
    have h_op_c0_val : ((0 : ZMod p).val : ℕ) = 0 := by rw [ZMod.val_zero]
    have h_zero_val_opcode : (0 : ZMod p).val = 0 := ZMod.val_zero
    refine ⟨?_, h_op_a_lt, ⟨h_op_b_lt, h_zero_lt, h_zero_lt, h_zero_lt⟩,
            ⟨h_op_c_lt, h_zero_lt, h_zero_lt, h_zero_lt⟩,
            h_a0_bin, h_a0_iff, Or.inl trivial, Or.inl trivial,
            h_pc_mod, h_pc_0_lt, h_pc_1_lt, h_pc_2_lt⟩
    -- trusted_instr: opcode = 0 ⇒ Opcode.ofNat 0 = ADD; matches rtypeReader's `opcode = 0`
    convert h_ti using 1
  -- Sail equivalence — single call to soundness_add
  · intro s state_cstrs
    exact soundness_add Main s h_allHold h_is_real state_cstrs

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
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c, op_c_memory⟩,
       op_a_write_value, is_real, _adapter_cols⟩ := cols
  SP1Clean.AddOp.assertion
    (⟨op_b_memory.prev_value, op_c_memory.prev_value, op_a_write_value⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Program-bus interaction (opcode = 0 = ADD; R-type discipline:
  -- op_b/op_c are single-limb register indices with limbs 1-3 zero,
  -- imm_b = imm_c = 0).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 0, op_a, #v[op_b, 0, 0, 0], #v[op_c, 0, 0, 0], op_a_0, 0, 0⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Iter-8 sub-task E: per-operand memory-bus byte content. Each call
  -- emits 6 byte lookups (Range 16 on diff_low + U8Range on timestamp +
  -- 4 Range 16 lookups on prev_value limbs) ⇒ `memoryAccessSpec`.
  -- R-type offsets: op_a at +4, op_b at +3, op_c at +2.
  let clk_low := clk_0_16 + clk_16_24 * 65536
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
`rtypeReaderSpec` is deferred to the trace-level OfflineMemory bridge.
Per-row PC carry was lifted out — the trace-level state-bus chain
(`StateConsistency.pcChainProp`) now derives `next_pc` literally as
`#v[pc[0]+4, pc[1], pc[2]]` per Rust's design at `adapter/state.rs:75`. -/
def FormalSpec (cols : AddCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.AddOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_memory.prev_value
      cols.op_a_write_value ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 0, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := #v[cols.adapter.op_c, 0, 0, 0],
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 0 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- Each OperandAccess.assertion's Spec is exactly the `memoryAccessSpec`
  -- for that operand's `(diff_low_limb, prev_low, prev_value)` triple.
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
  -- Substitute all input-eval equations to put the goal in the same form as
  -- the subcircuit specs (which use `Expression.eval env input_var_X`).
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20⟩ := h_input
  subst_eqs
  obtain ⟨h_addop_sub, h_cpu_sub, h_prog_sub, h_oa_a, h_oa_b, h_oa_c,
          h_isreal, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_addop_sub trivial
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
  obtain ⟨h_addop, h_cpu, h_prog, h_isreal, h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h_spec
  unfold id at *
  -- Completeness obligations follow main's emission order: 3 subcircuit
  -- arms, then the 3 OperandAccess arms, then the 2 scalar gates.
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_addop⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩
  · exact ⟨trivial, h_oa_c⟩
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
