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
import SP1Chips.Jalr.JalrChip
import SP1Chips.Jalr.Common
import SP1Chips.Soundness
import SP1Clean.Operations.AddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec

/-! # Chip-level `JalrChip` mirror — JALR (I-type indirect jump)

The Jalr chip implements the RV64I `jalr` indirect jump: computes
`next_pc = (op_b + sign_ext(op_c_imm)) &~ 1` and writes the
return-address `pc + 4` to op_a. 35 columns. Two `AddOperation`
sub-fragments fire: one for the jump-target sum (`op_b + op_c_imm`),
one for the return address (`pc + 4`).

Structural mirror discipline (Spec only, no traceSpec_iff_allHold / correct_*). The
`AddOperation` for the return address is gated on `is_real - op_a_0`
(vacuous when op_a is x0); the jump-target `AddOperation` is gated
on `is_real`.

Opcode: `47 = JALR`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Jalr

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Emits CPUState range lookups, the program-bus
interaction (opcode 47 = JALR), the alignment lookup for the next-PC's
low limb, byte lookups for the memory-access timestamps, and the
trailing assertZero gates (is_real boolean, lsb boolean,
next_pc[3] = 0, op_a_write_value[3] = 0, vacuous op_a gates).

The two `AddOperation` sub-fragments are not emitted as subcircuits
here — their constraints are captured propositionally in `Spec`. -/
def main (cols : Var JalrCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c_imm⟩, is_real, jump_target, op_a_write_value, lsb, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Program-bus interaction. Opcode is 47 = JALR; I-type discipline
  -- (op_b is a 1-limb register index, op_c carries the 4-limb immediate,
  -- imm_b = 0, imm_c = 1).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 47, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Alignment lookup: (jump_target[0] - lsb) / 4 must fit in Range(14).
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), (jump_target[0] - lsb) * (4 : ZMod p)⁻¹, 14, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Trailing asserts.
  is_real * (is_real - 1) === 0
  jump_target[3] === 0
  lsb * (lsb - 1) === 0
  (is_real - 1) * op_a_0 === 0
  op_a_write_value[3] === 0
  op_a_0 * op_a_write_value[0] === 0
  op_a_0 * op_a_write_value[1] === 0
  op_a_0 * op_a_write_value[2] === 0

/-- Pilot Spec, expressed over field-valued `JalrCols (ZMod p)`. The
two `AddOperation` clauses are left in raw `allHold` form
(one gated on `is_real`, the other on `is_real - op_a_0`). -/
def TraceSpec (cols : JalrCols (ZMod p)) : Prop :=
  (_root_.AddOperation.constraints (F := ZMod p)
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
      { value := cols.jump_target }
      cols.is_real).allHold ∧
  (_root_.AddOperation.constraints (F := ZMod p)
      #v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0]
      #v[4, 0, 0, 0]
      { value := cols.op_a_write_value }
      (cols.is_real - cols.adapter.op_a_0)).allHold ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ITypeReader.itypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 47 cols.state.pc
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
  cols.jump_target[3] = 0 ∧
  cols.lsb * (cols.lsb - 1) = 0 ∧
  (cols.is_real - 1) * cols.adapter.op_a_0 = 0 ∧
  cols.op_a_write_value[3] = 0 ∧
  cols.adapter.op_a_0 * cols.op_a_write_value[0] = 0 ∧
  cols.adapter.op_a_0 * cols.op_a_write_value[1] = 0 ∧
  cols.adapter.op_a_0 * cols.op_a_write_value[2] = 0 ∧
  -- iter-9 strengthening: PC alignment byte-send consequence
  -- ((jump_target[0] - lsb) / 4 in Range(14) — the bit-0-cleared
  -- jump target is 4-aligned in the low limb).
  ((cols.jump_target[0] - cols.lsb) * (4 : ZMod p)⁻¹).val < 16384 ∧
  cols.adapter_cols.is_trusted = 1

/-- The op_a register access (read prior, write return address),
exposed for trace-level OfflineMemory aggregation. -/
def opAMemoryAccess (cols : JalrCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_a, 0, 0],
    prev_value := cols.adapter.op_a_memory.prev_value,
    prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }

/-- The op_b register access (read; no write — op_b is a source register
read for the jump-target sum). -/
def opBMemoryAccess (cols : JalrCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_b, 0, 0],
    prev_value := cols.adapter.op_b_memory.prev_value,
    prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb }

set_option maxHeartbeats 1200000 in
-- Heartbeats elevated for the 35-col inline-flatten + 4-sub-op bridge dance.
/-- The chip-level half-iff bridge: under `is_real = 1 ∧ op_a_0 = 0`,
the Clean-flavored `Spec` implies SP1's `allHold` over the flat row.
Used by `correct_jalr` to thread the Clean Spec into the dirty-side
`JALR_correct` proof.

Single-opcode chip (is_real = Main[25]). Proof: inline-flatten Jalr's
constraint-list to expose the 4 sub-`allHold`s + 9 chip-side asserts/sends,
then bridge each conjunct via the Spec components and the cpuState/itypeReader
spec_iff_sp1 helpers. -/
theorem traceSpec_implies_allHold (Main : Vector (ZMod p) 35)
    (h_is_real : Main[25] = 1) (_h_op_a_0 : Main[13] = 0)
    (h_spec : TraceSpec (fromMain Main)) :
    (_root_.Jalr.constraints Main).allHold := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [TraceSpec, fromMain] at h_spec
  obtain ⟨h_add_jump, h_add_ret, h_cpu_spec, h_reader_spec,
          h_is_real_bin, h_jump3, h_lsb_bin, h_op_a0_gated,
          h_op_a_w3, h_a0_w0, h_a0_w1, h_a0_w2, h_pc_align, _h_trusted⟩ := h_spec
  change List.Forall SP1Constraint.toProp (_root_.Jalr.constraints Main)
  simp only [_root_.Jalr.constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp, and_assoc]
  -- 13-conjunct right-associated structure: 4 sub-allHolds + 9 chip props.
  refine ⟨?_, ?_, ?_, ?_, h_is_real_bin, h_jump3, h_lsb_bin,
          ?_, h_op_a0_gated, h_op_a_w3, h_a0_w0, h_a0_w1, h_a0_w2⟩
  -- 1: AddOperation (jump target) — direct from Spec.
  · exact h_add_jump
  -- 2: CPUState — bridge via cpuStateSpec_iff_sp1 under is_real = 1.
  · rw [h_is_real]
    exact (SP1Clean.CPUState.cpuStateSpec_iff_sp1).mpr h_cpu_spec
  -- 3: ITypeReader — bridge via itypeReaderSpec_iff_sp1 under is_real = is_trusted = 1.
  · rw [h_is_real]
    exact (SP1Clean.ITypeReader.itypeReaderSpec_iff_sp1).mpr h_reader_spec
  -- 4: AddOperation (return address) — direct from Spec.
  · exact h_add_ret
  -- 8: byte send for PC alignment — Range constraint ⇔ `.val < 2^14 = 16384`.
  · intro _h_ne
    have h14 : ((14 : ℕ) : ZMod p).val = 14 := by
      have hp : 2 ^ 17 < p := Fact.out
      exact ZMod.val_natCast_of_lt (by omega)
    have h14_eq : (14 : ZMod p).val = 14 := by
      rw [show (14 : ZMod p) = ((14 : ℕ) : ZMod p) from by push_cast; rfl, h14]
    simp only [show (ByteOpcode.ofNat 6 : ByteOpcode) = .Range from rfl,
      ByteOpcode.constrain_Range, h14_eq, Vector.getElem_mk,
      List.getElem_toArray, List.getElem_cons_zero] at h_pc_align ⊢
    exact h_pc_align

/-- Clean-side `correct_jalr`: same Sail equivalence statement as the
dirty `_root_.Jalr.JALR_correct`, with the constraint hypothesis
re-expressed against the Clean `Spec` predicate via `traceSpec_implies_allHold`. -/
theorem correct_jalr
    (Main : Vector (ZMod p) 35) (s : SailState)
    (h_is_real : Main[25] = 1) (h_op_a_0 : Main[13] = 0)
    (h_spec : TraceSpec (fromMain Main))
    (hs : SailState.isInitialized s)
    (state_cstrs : (_root_.Jalr.constraints Main).initialState s)
    (hv : SailState.isValidMemConfig s hs) :
    let op_b := _root_.Jalr.sp1_op_b Main
    let op_a := _root_.Jalr.sp1_op_a Main
    let op_c := _root_.Jalr.sp1_op_c Main
    (_root_.Jalr.spec_jalr op_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Jalr.sp1_jalr Main).run s :=
  _root_.Jalr.JALR_correct Main s
    (traceSpec_implies_allHold Main h_is_real h_op_a_0 h_spec)
    h_is_real hs state_cstrs hv

/-! ## RawSpec / SemanticSpec POC -/

@[reducible]
def RawSpec (Main : Vector (ZMod p) 35) : Prop :=
  List.Forall SP1Constraint.toProp (_root_.Jalr.constraints Main)

omit [Fact (2 ^ 17 < p)] in
theorem rawSpec_iff_allHold (Main : Vector (ZMod p) 35) :
    (_root_.Jalr.constraints Main).allHold ↔ RawSpec Main := Iff.rfl

def SemanticSpec (Main : Vector (ZMod p) 35) : Prop :=
  TraceSpec (fromMain Main) ∧
  (∀ (s : SailState) (_hs : SailState.isInitialized s)
     (_state_cstrs : (_root_.Jalr.constraints Main).initialState s)
     (_hv : SailState.isValidMemConfig s _hs),
    (_root_.Jalr.sp1_jalr Main).run s =
      (_root_.Jalr.spec_jalr (_root_.Jalr.sp1_op_c Main)
        (.Regidx (_root_.Jalr.sp1_op_b Main))
        (.Regidx (_root_.Jalr.sp1_op_a Main))).run s)

theorem raw_to_semantic (Main : Vector (ZMod p) 35) (h_is_real : Main[25] = 1)
    (_h_op_a_0 : Main[13] = 0) (h_spec : TraceSpec (fromMain Main))
    (h_raw : RawSpec Main) : SemanticSpec Main := by
  refine ⟨h_spec, ?_⟩
  intro s hs state_cstrs hv
  exact soundness_jalr Main s ((rawSpec_iff_allHold Main).mpr h_raw)
    h_is_real hs state_cstrs hv

/-! ## Full `FormalAssertion` promotion

JalrChip's `Assertion.main` emits `CPUState.assertion`,
`ProgramTable.assertion` (opcode 47 = JALR), `AddOp.assertion` for the
jump-target sum (gated by `is_real`), the three scalar boolean asserts
(`is_real`, `lsb`, `(is_real - 1) * op_a_0`), and two
`OperandAccess.assertion` subcircuits for the op_a/op_b register
accesses. The return-address `AddOperation` (`pc + 4 = op_a_write_value`,
gated by `is_real - op_a_0`) is not emitted at the FormalAssertion
level — its discharge stays in the legacy chip-level
`traceSpec_implies_allHold` bridge, where the multi-factor gate can be
discharged from `(is_real - 1) * op_a_0 = 0` under `is_real = 1`. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var JalrCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩, is_real, jump_target, _op_a_write_value, lsb, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, 47, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Jump-target sum: `op_b + op_c_imm = jump_target`. `AddOp.assertion`'s
  -- gated FormalSpec is the semantic shape (`is_real = 1 → isU64 result ∧
  -- result.toBitVec64 = a + b`), matching the chip-level `FormalSpec`
  -- semantic conjunct directly.
  SP1Clean.AddOp.assertion
    (⟨op_b_memory.prev_value, op_c_imm, jump_target, is_real⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  lsb * (lsb - 1) === 0
  (is_real - 1) * op_a_0 === 0
  -- Iter-8 sub-task E: per-operand memory-bus byte content. Jalr emits
  -- 2 register accesses: op_a/+4 (return-address write), op_b/+3
  -- (jump-target base register read). op_c is the I-type immediate.
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low, op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low, op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) JalrCols unit where
  name := "SP1Clean.Jalr"
  main := main
  -- Computed from main; AddOp.assertion allocates 16 hint witnesses.
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

/-- Strengthened Assumptions: non-padding row (`is_real = 1`) plus the
two operand-isU64 bounds needed by the gated `AddOp.assertion`. The bounds
are easy at the trace level (R/I-type operands are < 65536 by the SP1
column conventions) but are not derivable from the chip-level sub-circuit
Specs (`ProgramTable`, `OperandAccess`) without a verbose ZMod-`<`-to-
`.val`-`<` conversion. Surfacing them here keeps the chip's own
soundness/completeness clean while pushing the bounds discharge into the
trace-soundness driver. -/
def Assumptions (cols : JalrCols (ZMod p)) : Prop :=
  cols.is_real = 1 ∧
  Word.isU64 cols.adapter.op_b_memory.prev_value ∧
  Word.isU64 cols.adapter.op_c_imm

/-- Soundness of `Jalr.assertion`. Mirrors JalChip's canonical recipe
(commit `186a456`): the AddOp sub-circuit Spec under `is_real = 1` is
exactly the corresponding `FormalSpec` semantic conjunct, so the jump-
target discharge is a direct passthrough of `h_add_sub`. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu_sub, h_prog_sub, h_add_sub, h_isreal, h_lowbit, h_isreal_op_a_0,
          h_oa_a, h_oa_b⟩ := h_holds
  obtain ⟨h_is_real, h_isU64_b, h_isU64_c⟩ := h_assumptions
  unfold id at *
  -- Discharge AddOp.assertion's Assumptions (`is_real ∈ {0,1}` + operand
  -- bounds under `is_real = 1`) from the chip-level Assumptions.
  have h_add := h_add_sub ⟨Or.inr h_is_real, fun _ => ⟨h_isU64_b, h_isU64_c⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · -- Jump-target semantic conjunct: AddOp.assertion gives exactly this
    -- form under `is_real = 1`.
    exact h_add
  · linear_combination h_isreal
  · linear_combination h_lowbit
  · linear_combination h_isreal_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial

/-- Completeness of `Jalr.assertion`. The AddOp.assertion sub-circuit's
Assumptions (`is_real ∈ {0,1}` + `is_real = 1 → isU64 a ∧ isU64 b`) plus
Spec are discharged from the chip-level `h_assumptions` (which carries
the operand isU64 bounds) and the matching `FormalSpec` semantic conjunct. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu, h_prog, h_add, h_isreal, h_lowbit, h_isreal_op_a_0,
          h_oa_a, h_oa_b⟩ := h_spec
  obtain ⟨h_is_real, h_isU64_b, h_isU64_c⟩ := h_assumptions
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · -- AddOp.assertion (jump-target): supply Assumptions (binary + bounds)
    -- and Spec from h_add.
    refine ⟨⟨Or.inr h_is_real, ?_⟩, h_add⟩
    intro _
    exact ⟨h_isU64_b, h_isU64_c⟩
  · linear_combination h_isreal
  · linear_combination h_lowbit
  · linear_combination h_isreal_op_a_0
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩

end Assertion

def assertion : FormalAssertion (ZMod p) JalrCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Jalr
