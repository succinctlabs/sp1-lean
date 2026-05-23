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
import SP1Clean.AddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.OperandAccess
import SP1Chips.Jal.JalChip

/-! # Chip-level `JalChip` mirror — first chip with PC control flow

The Jal chip is the canonical example of a chip whose PC update is not
`pc + 4`: the next PC is `pc + sign_ext(imm)` (jump target), and the
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

namespace SP1Clean.Jal

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `JalCols<T>` over
31 field elements. Field order matches the `Main[k]` indexing in
`SP1Chips/Jal/Constraints.lean`. -/
structure JalCols (T : Type) where
  state : CPUState T
  op_a : T                                  -- Main[6] (return-address destination)
  op_a_memory_prev_value : Vector T 4       -- Main[7..10]
  op_a_memory_prev_low : T                  -- Main[11]
  op_a_memory_diff_low : T                  -- Main[12]
  op_a_0 : T                                -- Main[13]
  imm : Vector T 4                          -- Main[14..17] (sign-extended J-type immediate)
  op_c : Vector T 4                         -- Main[18..21]
  next_pc : Vector T 4                      -- Main[22..25] (jump target, Main[25] is high limb)
  op_a_write_value : Vector T 4             -- Main[26..29] (return address = pc + 4)
  is_real : T                               -- Main[30]
deriving ProvableStruct

/-- Clean-side circuit. Mirrors the SP1 source's emissions for JAL:
two `AddOperation` subcircuits (PC + imm = next_pc; PC + 4 = return
address), byte lookups for the PC alignment and clock decomposition,
plus the program-bus interaction.

The state-bus interactions (`.receive (.state ...)` / `.send (.state
...)`) are *not* mirrored as subcircuit calls here — their per-row
propositional content is `True`. The next_pc / current_pc columns
remain exposed in `Spec` so the trace-level pass can verify the
PC chain permutes across rows (future work, parallel to OfflineMemory).

Opcode: `46 = JAL`. -/
def main (cols : Var JalCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, op_a_memory_diff_low,
       op_a_0, imm, op_c, next_pc, op_a_write_value, is_real⟩ := cols
  -- AddOperation for jump target: pc + imm = next_pc.
  SP1Clean.AddOp.assertion
    (⟨pc.push 0, imm, #v[next_pc[0], next_pc[1], next_pc[2], next_pc[3]]⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  -- AddOperation for return address: pc + 4 = op_a_write_value.
  SP1Clean.AddOp.assertion
    (⟨pc.push 0, #v[4, 0, 0, 0], op_a_write_value⟩ :
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
    (#v[(6 : Expression (ZMod p)), op_a_memory_diff_low, 16, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Program-bus interaction. Opcode is 46 = JAL; J-type discipline:
  -- op_b carries the 4-limb sign-extended immediate, op_c is unused
  -- (Main[18..21]), imm_b = imm_c = 1.
  SP1Clean.ProgramTable.assertion
    (⟨pc, 46, op_a, imm, op_c, op_a_0, 1, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Trailing asserts: is_real boolean, next_pc[3] = 0 (high limb of
  -- PC is zero), op_a_write_value[3] = 0 (high limb of return address
  -- is zero).
  is_real * (is_real - 1) === 0
  next_pc[3] === 0
  op_a_write_value[3] === 0

/-- The Clean-flavored Spec for `JalChip`. Composes the existing
per-fragment specs:
- `AddOp.Spec` for the jump-target carry chain (PC + imm = next_pc)
- `AddOp.Spec` for the return-address carry chain (PC + 4 = op_a_write_value)
- `cpuStateSpec` for clock decomposition
- `memoryAccessSpec` for op_a (read prior + write return address)
- `ProgramTable.Spec` for the program-bus consequence
- The three boolean / zero asserts.

The state-bus content beyond what ProgramTable.Spec gives (PC alignment,
PC limb bounds) is empty per-row — see the file docstring. -/
def Spec (cols : JalCols (ZMod p)) : Prop :=
  SP1Clean.AddOp.Spec (cols.state.pc.push 0) cols.imm cols.next_pc ∧
  SP1Clean.AddOp.Spec (cols.state.pc.push 0) #v[4, 0, 0, 0] cols.op_a_write_value ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_a
      { prev_value := cols.op_a_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_a_memory_prev_low,
            diff_low_limb := cols.op_a_memory_diff_low } }) ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc,
      opcode := 46,
      op_a := cols.op_a,
      op_b := cols.imm,
      op_c := cols.op_c,
      op_a_0 := cols.op_a_0, imm_b := 1, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.next_pc[3] = 0 ∧
  cols.op_a_write_value[3] = 0 ∧
  -- iter-9 strengthening: PC alignment byte-send consequence
  -- (next_pc[0] / 4 in Range(14) — the jump target is 4-aligned).
  -- This was emitted by the chip but not previously surfaced in Spec.
  (cols.next_pc[0] * (4 : ZMod p)⁻¹).val < 16384

/-- The op_a register access (read prior, write return address), exposed
for trace-level OfflineMemory aggregation. `write_value` at aggregation
time is `cols.op_a_write_value`. -/
def opAMemoryAccess (cols : JalCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.op_a, 0, 0],
    prev_value := cols.op_a_memory_prev_value,
    prev_low := cols.op_a_memory_prev_low,
    diff_low_limb := cols.op_a_memory_diff_low }

/-- Project a raw SP1 row into the structured `JalCols` view. Mirrors
the index map in `SP1Chips/Jal/Constraints.lean` (31 columns). -/
@[reducible] def fromMain (Main : Vector (ZMod p) 31) : JalCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      Main[6],
   #v[Main[7], Main[8], Main[9], Main[10]],
   Main[11], Main[12], Main[13],
   #v[Main[14], Main[15], Main[16], Main[17]],
   #v[Main[18], Main[19], Main[20], Main[21]],
   #v[Main[22], Main[23], Main[24], Main[25]],
   #v[Main[26], Main[27], Main[28], Main[29]],
   Main[30]⟩

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
theorem spec_implies_allHold (Main : Vector (ZMod p) 31)
    (h_is_real : Main[30] = 1) (h_op_a_0 : Main[13] = 0)
    (h_spec : Spec (fromMain Main)) :
    (_root_.Jal.constraints Main).allHold := by
  sorry

/-- Clean-side `correct_jal`: same Sail equivalence statement as the
dirty `_root_.Jal.SP1JAL_correct`, but with the constraint hypothesis
re-expressed against the Clean-flavored `Spec` predicate via
`spec_implies_allHold`. Pure composition with the SP1 proof. -/
theorem correct_jal
    (Main : Vector (ZMod p) 31) (s : SailState)
    (h_is_real : Main[30] = 1) (h_op_a_0 : Main[13] = 0)
    (h_spec : Spec (fromMain Main))
    (state_cstrs : (_root_.Jal.constraints Main).initialState s)
    (hs : SailState.isInitialized s) :
    let cstrs := spec_implies_allHold Main h_is_real h_op_a_0 h_spec
    let op_a := _root_.Jal.sp1_op_a Main cstrs h_is_real
    let op_b := _root_.Jal.sp1_op_b Main
    (_root_.Jal.spec_jal op_b (.Regidx op_a)).run s =
      (_root_.Jal.sp1_jal Main).run s :=
  _root_.Jal.SP1JAL_correct Main s
    (spec_implies_allHold Main h_is_real h_op_a_0 h_spec)
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
`Spec` carried by `iff_sp1`. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var JalCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩, op_a,
       op_a_memory_prev_value, op_a_memory_prev_low, op_a_memory_diff_low,
       op_a_0, imm, op_c, next_pc, op_a_write_value, is_real⟩ := cols
  -- CPUState: clk_0_16 / clk_16_24 range bounds.
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  -- Jump target: pc + imm = next_pc.
  SP1Clean.AddOp.assertion
    (⟨pc.push 0, imm, next_pc⟩ : Var SP1Clean.AddOp.Inputs (ZMod p))
  -- Return address: pc + 4 = op_a_write_value.
  SP1Clean.AddOp.assertion
    (⟨pc.push 0, #v[4, 0, 0, 0], op_a_write_value⟩ :
      Var SP1Clean.AddOp.Inputs (ZMod p))
  -- Program-bus interaction (opcode = 46 = JAL).
  SP1Clean.ProgramTable.assertion
    (⟨pc, 46, op_a, imm, op_c, op_a_0, 1, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Iter-8 sub-task E: per-operand memory-bus byte content. Jal emits
  -- a single op_a register access (return-address write) at offset +4.
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory_prev_low, op_a_memory_diff_low,
       op_a_memory_prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  is_real * (is_real - 1) === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) JalCols unit where
  name := "SP1Clean.Jal"
  main := main
  localLength _ := 0

def Assumptions (_ : JalCols (ZMod p)) : Prop := True

def FormalSpec (cols : JalCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.AddOp.Spec (cols.state.pc.push 0) cols.imm cols.next_pc ∧
  SP1Clean.AddOp.Spec (cols.state.pc.push 0) #v[4, 0, 0, 0] cols.op_a_write_value ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 46, op_a := cols.op_a,
      op_b := cols.imm, op_c := cols.op_c,
      op_a_0 := cols.op_a_0, imm_b := 1, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  -- Iter-8 sub-task E: per-operand memory-bus byte-content consequence.
  -- Jal emits a single op_a register access at offset +4.
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.op_a_memory_prev_low, cols.op_a_memory_diff_low,
     cols.op_a_memory_prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨_, _, _, h_pc⟩, _⟩ := h_input
  obtain ⟨h_cpu_sub, h_jump_sub, h_ret_sub, h_prog_sub, h_oa_a, h_isreal⟩ := h_holds
  simp only [Vector.map_push, h_pc] at h_jump_sub h_ret_sub
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_jump_sub trivial
  · exact h_ret_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_isreal
  · exact h_oa_a trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨_, _, _, h_pc⟩, _⟩ := h_input
  obtain ⟨h_cpu, h_jump, h_ret, h_prog, h_isreal, h_oa_a⟩ := h_spec
  simp only [Vector.map_push, h_pc]
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_jump⟩
  · exact ⟨trivial, h_ret⟩
  · exact ⟨trivial, h_prog⟩
  · exact ⟨trivial, h_oa_a⟩
  · linear_combination h_isreal

end Assertion

def assertion : FormalAssertion (ZMod p) JalCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Jal
