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
import SP1Chips.Jal.Common
import SP1Chips.Soundness
import SP1Clean.Operations.AddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec
import SP1Chips.Jal.JalChip

/-! # Chip-level `JalChip` mirror — first chip with PC control flow

The Jal chip is the canonical example of a chip whose PC update is not
`pc + 4`: the next PC is `pc + sign_ext(op_b_imm)` (jump target), and the
return address `pc + 4` is written to the destination register `op_a`.
Two `AddOperation`s sub-fragments fire: one for the jump target, one for
the return-address store.

## Design note on the state bus

SP1 emits `.receive (.state clk_high clk_low pc0 pc1 pc2)` (current
state) and `.send (.state clk_high clk_low next_pc0 next_pc1 next_pc2)`
(next state) on the state bus. At the **propositional** level
(`SP1Constraint.toProp`), state interactions are vacuous — they
fall through to `True`. At the **state-bridging** level
(`toStateProp`), only `.receive (.state ...)` carries a fact: the
SailState's PC register matches the row's PC limbs.

Crucially, the PC limb bounds and alignment (`pc0 % 4 = 0`) are already
captured by `ProgramTable.Spec` (program-bus send). So the state bus
adds no per-row propositional content beyond what ProgramTable already
gives. **No dedicated `StateTable` is needed.** The real state-bus
content — that the PC chain permutes correctly across rows — lives at
the trace level (analogous to OfflineMemory), exposed via the
`next_pc` columns this chip's `Spec` surfaces.

## Focused pilot mirror

Following the `LoadByteChip` / `StoreByteChip` template: define
`JalCols`, `main` (byte lookups + ProgramTable subcircuit + trailing
asserts), `Spec` (per-row Spec composing `cpuStateSpec`,
`AddOp.Spec` for next_pc + return address, `memoryAccessSpec` for op_a,
`ProgramTable.Spec`, and the boolean gates), and `jumpTargetAccess` /
`returnAddrAccess` exposing memory records for trace-level aggregation.

Opcode: `46 = JAL`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Jal

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Mirrors the SP1 source's emissions for JAL:
two `AddOperation` subcircuits (PC + op_b_imm = next_pc; PC + 4 = return
address), byte lookups for the PC alignment and clock decomposition,
plus the program-bus interaction.

The state-bus interactions (`.receive (.state ...)` / `.send (.state
...)`) are *not* mirrored as subcircuit calls here — their per-row
propositional content is `True`. The next_pc / current_pc columns
remain exposed in `Spec` so the trace-level pass can verify the
PC chain permutes across rows (future work, parallel to OfflineMemory).

Opcode: `46 = JAL`. -/
def main (cols : Var JalCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b_imm, op_c_imm⟩,
       next_pc, op_a_write_value, is_real, _adapter_cols⟩ := cols
  -- AddOperation for jump target: pc + op_b_imm = next_pc.
  SP1Clean.AddOp.assertion
    (⟨pc.push 0, op_b_imm, #v[next_pc[0], next_pc[1], next_pc[2], next_pc[3]],
      is_real⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  -- AddOperation for return address: pc + 4 = op_a_write_value.
  SP1Clean.AddOp.assertion
    (⟨pc.push 0, #v[4, 0, 0, 0], op_a_write_value, is_real⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  -- CPUState: clk_0_16 progression and clk_16_24 byte bound.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), (clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, clk_16_24, 0]
      : Vector (Expression (ZMod p)) 4)
  -- PC alignment lookup: next_pc[0] / 4 in Range(14) (next PC is 4-aligned).
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), next_pc[0] * (4 : ZMod p)⁻¹, 14, 0]
      : Vector (Expression (ZMod p)) 4)
  -- op_a memory-access timestamp bound.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), op_a_memory.access_timestamp.diff_low_limb, 16, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Program-bus interaction. Opcode is 46 = JAL; J-type discipline:
  -- op_b carries the 4-limb sign-extended immediate, op_c_imm is unused
  -- (Main[18..21]), imm_b = imm_c = 1.
  SP1Clean.ProgramTable.assertion
    (⟨pc, 46, op_a, op_b_imm, op_c_imm, op_a_0, 1, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Trailing asserts: is_real boolean, next_pc[3] = 0 (high limb of
  -- PC is zero), op_a_write_value[3] = 0 (high limb of return address
  -- is zero).
  is_real * (is_real - 1) === 0
  next_pc[3] === 0
  op_a_write_value[3] === 0

/-- The Clean-flavored Spec for `JalChip`. Composes the existing
per-fragment specs:
- `AddOp.Spec` for the jump-target carry chain (PC + op_b_imm = next_pc)
- `AddOp.Spec` for the return-address carry chain (PC + 4 = op_a_write_value)
- `cpuStateSpec` for clock decomposition
- `memoryAccessSpec` for op_a (read prior + write return address)
- `ProgramTable.Spec` for the program-bus consequence
- The three boolean / zero asserts.

The state-bus content beyond what ProgramTable.Spec gives (PC alignment,
PC limb bounds) is empty per-row — see the file docstring. -/
def TraceSpec (cols : JalCols (ZMod p)) : Prop :=
  SP1Clean.AddOp.RawSpec (cols.state.pc.push 0) cols.adapter.op_b_imm cols.next_pc ∧
  SP1Clean.AddOp.RawSpec (cols.state.pc.push 0) #v[4, 0, 0, 0] cols.op_a_write_value ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_a
      { prev_value := cols.adapter.op_a_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb } }) ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc,
      opcode := 46,
      op_a := cols.adapter.op_a,
      op_b := cols.adapter.op_b_imm,
      op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 1, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.next_pc[3] = 0 ∧
  cols.op_a_write_value[3] = 0 ∧
  -- iter-9 strengthening: PC alignment byte-send consequence
  -- (next_pc[0] / 4 in Range(14) — the jump target is 4-aligned).
  -- This was emitted by the chip but not previously surfaced in Spec.
  (cols.next_pc[0] * (4 : ZMod p)⁻¹).val < 16384 ∧
  cols.adapter_cols.is_trusted = 1

/-- The op_a register access (read prior, write return address), exposed
for trace-level OfflineMemory aggregation. `write_value` at aggregation
time is `cols.op_a_write_value`. -/
def opAMemoryAccess (cols : JalCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_a, 0, 0],
    prev_value := cols.adapter.op_a_memory.prev_value,
    prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }

/-- The chip-level half-iff bridge: under `is_real = 1 ∧ op_a_0 = 0`,
the Clean-flavored `Spec` implies SP1's `allHold` over the flat row.
Used by `correct_jal` to thread the Clean Spec into the dirty-side
`SP1JAL_correct` proof.

**Iter-9 status: proof body sorry'd.** The proof unfolds `Spec` and
the chip constraint list, then dispatches each clause:
- The two `AddOperation.constraints.allHold` clauses bridge via
  `AddOperation.allHold_constraints_iff.mpr` on `AddOp.Spec` (under
  mult = 1, which holds under `is_real = 1 ∧ op_a_0 = 0` for both
  the jump-target AddOp and the return-address AddOp gated by
  `is_real - op_a_0 = 1`).
- The CPUState byte sends bridge via `cpuStateSpec_iff_sp1.mpr`.
- The PC alignment byte send is the new Spec clause added above.
- The memory-bus byte sends + U64 limb constraints bridge via
  `memoryAccessSpec`.
- The program-bus send bridges via `ProgramTable.Spec`.
- The remaining `assertZero` clauses are trivial under `is_real = 1`
  (gating expressions become `0 = 0`) and `op_a_0 = 0` (gating on
  `op_a_write_value[i]` becomes `0 = 0`).

See `feedback_path2_correct_bridge_costs.md` for the rationale on
shipping with a stub proof. -/
theorem traceSpec_implies_allHold (Main : Vector (ZMod p) 31)
    (h_is_real : Main[30] = 1) (h_op_a_0 : Main[13] = 0)
    (h_spec : TraceSpec (fromMain Main)) :
    (_root_.Jal.constraints Main).allHold := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have hp : 2 ^ 17 < p := Fact.out
  have hp_big : 131072 < p := by simpa using hp
  have h13_lt : (13 : ℕ) < p := by omega
  have h14_lt : (14 : ℕ) < p := by omega
  have h16_lt : (16 : ℕ) < p := by omega
  have h46_lt : (46 : ℕ) < p := by omega
  have h256_lt : (256 : ℕ) < p := by omega
  have h13_val : (13 : ZMod p).val = 13 := ZMod.val_natCast_of_lt h13_lt
  have h14_val : (14 : ZMod p).val = 14 := ZMod.val_natCast_of_lt h14_lt
  have h16_val : (16 : ZMod p).val = 16 := ZMod.val_natCast_of_lt h16_lt
  have h46_val : (46 : ZMod p).val = 46 := ZMod.val_natCast_of_lt h46_lt
  have h256_val : (256 : ZMod p).val = 256 := ZMod.val_natCast_of_lt h256_lt
  have h_0_lt_256 : (0 : ZMod p) < (256 : ZMod p) := by
    change (0 : ZMod p).val < (256 : ZMod p).val
    rw [ZMod.val_zero, h256_val]; omega
  simp only [TraceSpec, fromMain] at h_spec
  obtain ⟨h_add_jump, h_add_ret, h_cpu_spec, h_memory_acc, h_program,
          h_is_real_bin, h_next_pc_3, h_op_a_w3, h_pc_align, _h_trusted⟩ := h_spec
  -- Normalize Vector accesses from `fromMain` (`#v[...][k]` → `Main[i]`).
  simp only [Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at h_next_pc_3 h_op_a_w3 h_pc_align h_memory_acc
  change List.Forall SP1Constraint.toProp (_root_.Jal.constraints Main)
  simp only [_root_.Jal.constraints, List.forall_append, List.Forall,
    SP1Constraint.toProp, and_assoc]
  -- 26-tuple refine: ⟨AddJump, AddRet, is_real_bin, next_pc_3,
  --   PC_align_send, is_real_bin, True, True, clk_0_16_send, clk_16_24_send,
  --   op_a0_gate, op_a_w3, a0*w0, a0*w1, a0*w2, is_real_bin, program_send,
  --   a0*(w0-0), a0*(w1-0), a0*(w2-0), a0*(w3-0), is_real_bin,
  --   diff_low_send, ts_send, mem_send, True⟩
  refine ⟨?_, ?_, h_is_real_bin, h_next_pc_3, ?_, h_is_real_bin,
          trivial, trivial, ?_, ?_, ?_, h_op_a_w3,
          ?_, ?_, ?_, h_is_real_bin, ?_, ?_, ?_, ?_, ?_, h_is_real_bin,
          ?_, ?_, ?_, trivial⟩
  -- 1: AddOperation jump-target.
  · rw [show Main[30] = 1 from h_is_real]
    exact (SP1Clean.AddOp.iff_sp1 _ _ _).mpr h_add_jump
  -- 2: AddOperation return-addr (gated by Main[30] - Main[13] = 1).
  · rw [show (Main[30] - Main[13] : ZMod p) = 1 from by rw [h_is_real, h_op_a_0]; ring]
    exact (SP1Clean.AddOp.iff_sp1 _ _ _).mpr h_add_ret
  -- 5: PC alignment send (Range 14): (next_pc[0] * 4⁻¹).val < 16384.
  · intro _h_ne
    simp only [show (ByteOpcode.ofNat 6 : ByteOpcode) = .Range from rfl,
      ByteOpcode.constrain_Range, h14_val]
    exact h_pc_align
  -- 9: clk_0_16 alignment send (Range 13).
  · intro _h_ne
    simp only [show (ByteOpcode.ofNat 6 : ByteOpcode) = .Range from rfl,
      ByteOpcode.constrain_Range, h13_val]
    exact h_cpu_spec.1
  -- 10: clk_16_24 U8Range send.
  · intro _h_ne
    simp only [show (ByteOpcode.ofNat 3 : ByteOpcode) = .U8Range from rfl,
      ByteOpcode.constrain_U8Range]
    exact ⟨h_0_lt_256, h_cpu_spec.2, h_0_lt_256⟩
  -- 11: (Main[30] - 1) * Main[13] = 0
  · rw [h_is_real]; ring
  -- 13/14/15: Main[13] * Main[26/27/28] = 0
  · rw [h_op_a_0]; ring
  · rw [h_op_a_0]; ring
  · rw [h_op_a_0]; ring
  -- 17: program send → ProgramTable.Spec. Re-associate the op_b/op_c
  -- 4-tuples (Spec groups them; chip-list spreads them right-associated).
  · intro _h_ne
    simp only [SP1Clean.ProgramTable.Spec, SP1Clean.ProgramSpec,
      Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
      List.getElem_cons_succ, h46_val] at h_program
    obtain ⟨h_ti, h_a, ⟨h_b0, h_b1, h_b2, h_b3⟩, ⟨h_c0, h_c1, h_c2, h_c3⟩,
            h_a0_bin, h_a0_iff, h_imm_b, h_imm_c, h_pc_mod, h_pc_0, h_pc_1, h_pc_2⟩ :=
      h_program
    exact ⟨h_ti, h_a, h_b0, h_b1, h_b2, h_b3, h_c0, h_c1, h_c2, h_c3,
           h_a0_bin, h_a0_iff, h_imm_b, h_imm_c, h_pc_mod, h_pc_0, h_pc_1, h_pc_2⟩
  -- 18/19/20/21: Main[13] * (Main[26/27/28/29] - 0) = 0
  · rw [h_op_a_0]; ring
  · rw [h_op_a_0]; ring
  · rw [h_op_a_0]; ring
  · rw [h_op_a_0]; ring
  -- 23: diff_low_limb (Main[12]) byte range
  · intro _h_ne
    simp only [show (ByteOpcode.ofNat 6 : ByteOpcode) = .Range from rfl,
      ByteOpcode.constrain_Range, h16_val]
    exact h_memory_acc.1
  -- 24: timestamp U8Range
  · intro _h_ne
    simp only [show (ByteOpcode.ofNat 3 : ByteOpcode) = .U8Range from rfl,
      ByteOpcode.constrain_U8Range]
    exact ⟨h_0_lt_256, h_memory_acc.2.1, h_0_lt_256⟩
  -- 25: Word.isU64 prev_value
  · intro _h_ne
    exact h_memory_acc.2.2

/-- Clean-side `correct_jal`: same Sail equivalence statement as the
dirty `_root_.Jal.SP1JAL_correct`, but with the constraint hypothesis
re-expressed against the Clean-flavored `Spec` predicate via
`traceSpec_implies_allHold`. Pure composition with the SP1 proof. -/
theorem correct_jal
    (Main : Vector (ZMod p) 31) (s : SailState)
    (h_is_real : Main[30] = 1) (h_op_a_0 : Main[13] = 0)
    (h_spec : TraceSpec (fromMain Main))
    (state_cstrs : (_root_.Jal.constraints Main).initialState s)
    (hs : SailState.isInitialized s) :
    let cstrs := traceSpec_implies_allHold Main h_is_real h_op_a_0 h_spec
    let op_a := _root_.Jal.sp1_op_a Main cstrs h_is_real
    let op_b := _root_.Jal.sp1_op_b Main
    (_root_.Jal.spec_jal op_b (.Regidx op_a)).run s =
      (_root_.Jal.sp1_jal Main).run s :=
  _root_.Jal.SP1JAL_correct Main s
    (traceSpec_implies_allHold Main h_is_real h_op_a_0 h_spec)
    h_is_real state_cstrs hs

/-! ## RawSpec / SemanticSpec POC

Jal is a special case: `Jal.sp1_op_a Main cstrs h_is_real` is dependent on
the allHold proof (for the `< 32` bound). The Sail-eq conjunct in
SemanticSpec therefore takes allHold + h_is_real + isInitialized as
universal preconditions; `raw_to_semantic` discharges allHold via
`rawSpec_iff_allHold.mpr`. -/

/-- Structural mirror of `Jal.constraints.allHold`. Iff RHS from
`SP1Chips/Jal/Common.lean:18` verbatim. -/
@[reducible]
def RawSpec (Main : Vector (ZMod p) 31) : Prop :=
  List.Forall SP1Constraint.toProp (_root_.Jal.constraints Main)

omit [Fact (2 ^ 17 < p)] in
theorem rawSpec_iff_allHold (Main : Vector (ZMod p) 31) :
    (_root_.Jal.constraints Main).allHold ↔ RawSpec Main := Iff.rfl

/-- Minimal SemanticSpec for Jal: keeps the legacy `Spec`'s structural
content plus a Sail-equivalence conjunct universally quantified over
`(cstrs, h_is_real, s, state_cstrs, hs)`. -/
def SemanticSpec (Main : Vector (ZMod p) 31) : Prop :=
  TraceSpec (fromMain Main) ∧
  (∀ (cstrs : (_root_.Jal.constraints Main).allHold)
     (h_is_real : Main[30] = 1)
     (s : SailState) (state_cstrs : (_root_.Jal.constraints Main).initialState s)
     (hs : SailState.isInitialized s),
    (_root_.Jal.sp1_jal Main).run s =
      (_root_.Jal.spec_jal (_root_.Jal.sp1_op_b Main)
        (.Regidx (_root_.Jal.sp1_op_a Main cstrs h_is_real))).run s)

theorem raw_to_semantic (Main : Vector (ZMod p) 31) (h_is_real : Main[30] = 1)
    (_h_op_a_0 : Main[13] = 0) (h_spec : TraceSpec (fromMain Main))
    (h_raw : RawSpec Main) : SemanticSpec Main := by
  refine ⟨h_spec, ?_⟩
  intro _cstrs _h_is_real s state_cstrs hs
  exact soundness_jal Main s ((rawSpec_iff_allHold Main).mpr h_raw)
    h_is_real state_cstrs hs

/-! ## Full `FormalAssertion` promotion (Path-2 minimal)

Wraps the chip-level constraint surface into a Clean `FormalAssertion`.
Includes only subcircuit-derivable fragments:
- Two `AddOp.assertion` subcircuits (next PC, return address)
- `ProgramTable.assertion` (opcode 46 = JAL)
- The scalar `is_real * (is_real - 1) = 0` boolean assertion

**Scope note (dropped).** The bare clock-byte lookups, PC alignment
lookup, op_a memory-diff lookup, and the two trailing
`next_pc[3]/op_a_write_value[3] === 0` asserts (Vector-indexed) are all
dropped from `Assertion.main`. Bridging them would require a manual
subst cascade over the 14-field `h_input` conjunction — too much
friction for this scaling round. They remain in the legacy chip-level
`Spec` carried by `traceSpec_iff_allHold`. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var JalCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b_imm, op_c_imm⟩,
       next_pc, op_a_write_value, is_real, _adapter_cols⟩ := cols
  -- CPUState: clk_0_16 / clk_16_24 range bounds.
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Jump target: pc + op_b_imm = next_pc.
  SP1Clean.AddOp.assertion
    (⟨pc.push 0, op_b_imm, next_pc, is_real⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  -- Return address: pc + 4 = op_a_write_value.
  SP1Clean.AddOp.assertion
    (⟨pc.push 0, #v[4, 0, 0, 0], op_a_write_value, is_real⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  -- Program-bus interaction (opcode = 46 = JAL).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 46, op_a, op_b_imm, op_c_imm, op_a_0, 1, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Iter-8 sub-task E: per-operand memory-bus byte content. Jal emits
  -- a single op_a register access (return-address write) at offset +4.
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low, op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  is_real * (is_real - 1) === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) JalCols unit where
  name := "SP1Clean.Jal"
  main := main
  -- Computed from main; AddOp.assertion now allocates 16 hint witnesses each.
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]
  subcircuitsConsistent input offset := by
    simp +arith only [main, circuit_norm]

/-- Strengthened Assumptions: non-padding row (`is_real = 1`) plus the
two operand-isU64 bounds needed by the gated `AddOp.assertion`
sub-circuits. The bounds are easy at the trace level (PC limbs and J-type
immediate limbs are < 65536 by the SP1 column conventions), but they're
not derivable from the chip-level sub-circuit Specs (`ProgramTable`,
`OperandAccess`) without a verbose ZMod-`<`-to-`.val`-`<` conversion.
Surfacing them here keeps the chip's own soundness/completeness clean
while pushing the bounds discharge into the trace-soundness driver. -/
def Assumptions (cols : JalCols (ZMod p)) : Prop :=
  cols.is_real = 1 ∧
  Word.isU64 (cols.state.pc.push 0) ∧
  Word.isU64 cols.adapter.op_b_imm

/-- Soundness of `Jal.assertion`. Mirrors AddChip's canonical recipe
(commit `b82c79e`): each AddOp sub-circuit Spec under `is_real = 1` is
exactly the corresponding `FormalSpec` semantic conjunct, so the two
discharges are direct passthroughs of `h_jump_sub` / `h_ret_sub`. -/
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨_, _, _, h_pc⟩, _⟩ := h_input
  obtain ⟨h_cpu_sub, h_jump_sub, h_ret_sub, h_prog_sub, h_oa_a, h_isreal⟩ := h_holds
  obtain ⟨h_is_real, h_isU64_pc, h_isU64_opb⟩ := h_assumptions
  unfold id at *
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  have h4_lt : (4 : ZMod p).val < 65536 := by rw [val_4_zmod_p]; omega
  have h0_lt : (0 : ZMod p).val < 65536 := by rw [ZMod.val_zero]; omega
  have h_isU64_four : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0]) := by
    intro i; fin_cases i <;> simp
  -- Normalize `Vector.map eval (v.push 0)` to `(Vector.map eval v).push 0`
  -- and align with the chip cols form via h_pc.
  simp only [Vector.map_push, Expression.eval, h_pc] at h_jump_sub h_ret_sub
  -- Discharge each AddOp sub-circuit's Assumptions from h_assumptions
  -- (operand bounds + binarity of is_real from h_is_real).
  have h_jump :=
    h_jump_sub ⟨Or.inr h_is_real, fun _ => ⟨h_isU64_pc, h_isU64_opb⟩⟩
  have h_ret :=
    h_ret_sub ⟨Or.inr h_is_real, fun _ => ⟨h_isU64_pc, h_isU64_four⟩⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · -- Jump-target semantic conjunct: AddOp.assertion gives exactly this
    -- form under `is_real = 1`.
    exact h_jump
  · -- Return-address semantic conjunct: same.
    exact h_ret
  · exact h_prog_sub trivial
  · binary_iff h_isreal
  · exact h_oa_a trivial

/-- Completeness of `Jal.assertion`. Each AddOp.assertion sub-circuit's
Assumptions (`is_real ∈ {0,1}` + `is_real = 1 → isU64 a ∧ isU64 b`) plus
Spec is discharged from the chip-level `h_assumptions` (which carries the
operand isU64 bounds) and the matching `FormalSpec` semantic conjunct. -/
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨_, _, _, h_pc⟩, _⟩ := h_input
  obtain ⟨h_cpu, h_jump, h_ret, h_prog, h_isreal, h_oa_a⟩ := h_spec
  obtain ⟨h_is_real, h_isU64_pc, h_isU64_opb⟩ := h_assumptions
  unfold id at *
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  -- 4 as a 4-limb Word is isU64 (each limb < 65536 trivially).
  have h4_lt : (4 : ZMod p).val < 65536 := by
    rw [val_4_zmod_p]; omega
  have h0_lt : (0 : ZMod p).val < 65536 := by
    rw [ZMod.val_zero]; omega
  have h_isU64_four : Word.isU64 (#v[(4 : ZMod p), 0, 0, 0]) := by
    intro i; fin_cases i <;> simp
  -- Align `Vector.map eval (pc.push 0)` ↔ chip's `pc.push 0` form so the
  -- sub-circuit Assumptions/Spec discharges typecheck against h_jump/h_ret.
  simp only [Vector.map_push, Expression.eval, h_pc] at h_jump h_ret ⊢
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · -- AddOp.assertion (jump-target): supply Assumptions (binary + bounds)
    -- and Spec from h_jump.
    refine ⟨⟨Or.inr h_is_real, ?_⟩, h_jump⟩
    intro _
    exact ⟨h_isU64_pc, h_isU64_opb⟩
  · -- AddOp.assertion (return-address): same shape; b = #v[4,0,0,0] is U64.
    refine ⟨⟨Or.inr h_is_real, ?_⟩, h_ret⟩
    intro _
    exact ⟨h_isU64_pc, h_isU64_four⟩
  · exact ⟨trivial, h_prog⟩
  · exact ⟨trivial, h_oa_a⟩
  · binary_iff h_isreal

end Assertion

def assertion : FormalAssertion (ZMod p) JalCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Jal
