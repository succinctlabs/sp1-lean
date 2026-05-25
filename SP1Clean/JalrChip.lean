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
import SP1Clean.Operations.GatedAddOp
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode

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

/-- The chip's column struct, mirroring SP1's Rust `JalrCols<T>`. -/
structure JalrCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  is_real : T
  jump_target : Vector T 4
  op_a_write_value : Vector T 4
  lsb : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

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

/-- Project a raw SP1 row into the structured `JalrCols` view. Mirrors
the index map in `SP1Chips/Jalr/Constraints.lean` (35 columns). -/
@[reducible] def fromMain (Main : Vector (ZMod p) 35) : JalrCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   Main[25],
   #v[Main[26], Main[27], Main[28], Main[29]],
   #v[Main[30], Main[31], Main[32], Main[33]],
   Main[34],
   ⟨Main[25]⟩⟩

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

/-! ## Full `FormalAssertion` promotion (Path-2 + single-gate Phase-A)

**Tier-2 probe history.** JalrChip has two `AddOperation.constraints
... allHold` clauses in its legacy `Spec` (one gated on `is_real`,
one gated on `is_real - op_a_0`). Iter-4 dropped both from
`Assertion.main` because Clean's unconditional `AddOp.assertion`
subcircuit would force the carry chain on padding / op_a=x0 rows where
completeness can't hold.

**Iter-5 update (Phase-A first demonstration).** The `is_real`-gated
jump-target AddOp is now promoted via `SP1Clean.GatedAddOp.assertion`:
its `main` emits `is_real * carry_k * (carry_k - 1) === 0` for each
of 4 carries (the inner `Range(16)` byte-bound lookups are dropped —
gating a lookup by field multiplication isn't sound; see
`SP1Clean/Gated.lean` for the lookup-restriction rationale). The
matching FormalSpec clause is `is_real = 0 ∨ GatedAddOp.Spec ...`,
satisfied vacuously on padding rows.

The second AddOp (gated on `is_real - op_a_0`) stays as a Path-2 drop
for now — it needs a multi-factor gate (essentially a 2-element gate
combinator since `is_real - op_a_0` is itself a difference of two
boolean selectors). Picking that up is iter-6 work.

What survives in `Assertion.main` today: `CPUState.assertion`,
`ProgramTable.assertion`, `GatedAddOp.assertion` for the jump-target
sum, and the three scalar boolean asserts (`is_real`, `lsb`,
`(is_real - 1) * op_a_0`). The alignment lookup, the second AddOp
clause, and the four Vector-indexed asserts on `jump_target[3]` /
`op_a_write_value[3]` / `op_a_0 * op_a_write_value[k]` remain in the
legacy chip-level `Spec`. -/

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
  -- Gated jump-target sum: `is_real * carry_k * (carry_k - 1) === 0` for
  -- each of 4 carries, encoded via the `GatedAddOp` FormalAssertion (Phase-A
  -- gating combinator, iter-5 first demonstration). The matching range
  -- checks on `jump_target[k]` are dropped from the gated form — they
  -- remain in the legacy chip-level `Spec` (see `Jalr.Spec`).
  SP1Clean.GatedAddOp.assertion
    (⟨op_b_memory.prev_value, op_c_imm, jump_target, is_real⟩ :
      Var SP1Clean.GatedAddOp.Inputs (ZMod p))
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
  localLength _ := 0

def Assumptions (_ : JalrCols (ZMod p)) : Prop := True

def FormalSpec (cols : JalrCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 47, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  (cols.is_real = 0 ∨ SP1Clean.GatedAddOp.Spec
    cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm cols.jump_target) ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.lsb * (cols.lsb - 1) = 0 ∧
  (cols.is_real - 1) * cols.adapter.op_a_0 = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequences.
  -- Jalr emits 2 register accesses: op_a/+4 and op_b/+3.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu_sub, h_prog_sub, h_gated_sub, h_isreal, h_lowbit, h_isreal_op_a_0,
          h_oa_a, h_oa_b⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · exact h_gated_sub trivial
  · linear_combination h_isreal
  · linear_combination h_lowbit
  · linear_combination h_isreal_op_a_0
  · exact h_oa_a trivial
  · exact h_oa_b trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu, h_prog, h_gated, h_isreal, h_lowbit, h_isreal_op_a_0,
          h_oa_a, h_oa_b⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · exact ⟨trivial, h_gated⟩
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
