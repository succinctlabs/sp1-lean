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
import SP1Operations.Reader.ITypeReaderImmutable.ITypeReaderImmutable
import SP1Chips.Branch.BranchChip
import SP1Clean.Operations.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.Operations.GatedAddOp
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Compare.LtOperationSigned
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec

/-! # Chip-level `BranchChip` mirror — bundled 6-variant conditional branch

The Branch chip bundles six RV64I conditional-branch variants
(`beq`/`bne`/`blt`/`bge`/`bltu`/`bgeu`) into a single 45-column trace.
Variants are distinguished by selectors at `Main[28..33]`. Uses
`ITypeReaderImmutable` (op_a / op_b read, no write) plus an inline
`LtOperationSigned` sub-fragment to compute the comparison result.

Structural mirror discipline (Spec only). The `LtOperationSigned`
constraint clause is left in raw `allHold` form. The next_pc
chain is state-bus content (per-row `True`); cross-row PC consistency
is a separate trace-level concern.

Opcode encoding: `is_beq * 40 + is_bne * 41 + is_blt * 42 + is_bge * 43
+ is_bltu * 44 + is_bgeu * 45` (40-45 = BEQ/BNE/BLT/BGE/BLTU/BGEU).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Branch

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Aggregate is-real flag: sum of 6 selectors. -/
def isRealExpr (cols : Var BranchCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
    cols.is_bltu + cols.is_bgeu

/-- Selector-weighted opcode expression. -/
def opcodeExpr (cols : Var BranchCols (ZMod p)) : Expression (ZMod p) :=
  cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
    cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45

def main (cols : Var BranchCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c_imm⟩, _next_pc,
       is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu,
       _is_branching, _compare_operation,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let opcode_e := is_beq * 40 + is_bne * 41 + is_blt * 42 +
                    is_bge * 43 + is_bltu * 44 + is_bgeu * 45
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Six opcode-selector boolean gates plus the aggregate-is-real boolean.
  is_beq * (is_beq - 1) === 0
  is_bne * (is_bne - 1) === 0
  is_blt * (is_blt - 1) === 0
  is_bge * (is_bge - 1) === 0
  is_bltu * (is_bltu - 1) === 0
  is_bgeu * (is_bgeu - 1) === 0
  let sum := is_beq + is_bne + is_blt + is_bge + is_bltu + is_bgeu
  sum * (sum - 1) === 0

/-- The branch-arithmetic Spec content. Bundles the iff-RHS conjuncts of
`_root_.Branch.allHold_constraints_iff` that aren't otherwise carried by
the chip-level Spec (cpuStateSpec / LtOperationSigned / ProgramTable.Spec /
opcode boolean gates). Includes:
  - `ITypeReaderImmutable.constraints.allHold` (the full reader content,
    subsumes the ProgramTable.Spec in Spec)
  - `is_branching` boolean and outcome equation
  - 4 branch-taken carry assertZeros (gated by `is_branching`)
  - 4 branch-not-taken carry assertZeros (gated by `is_real - is_branching`)
  - 3 PC alignment byte sends (next_pc[0..2])
-/
def branchSpec (cols : BranchCols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu
  let opcode_e : ZMod p :=
    cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
      cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45
  let u16_sum : ZMod p :=
    cols.compare_operation.result.u16_flags[0] +
    cols.compare_operation.result.u16_flags[1] +
    cols.compare_operation.result.u16_flags[2] +
    cols.compare_operation.result.u16_flags[3]
  let bit : ZMod p := cols.compare_operation.result.u16_compare_operation.bit
  -- ITypeReaderImmutable.constraints.allHold with the chip's args.
  (_root_.ITypeReaderImmutable.constraints cols.state.clk_high
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) cols.state.pc
      opcode_e cols.adapter is_real is_real).allHold ∧
  -- is_branching boolean
  cols.is_branching * (cols.is_branching - 1) = 0 ∧
  -- is_branching outcome equation (gated by is_real)
  is_real * (cols.is_branching -
    (0 + cols.is_beq * (1 - u16_sum) +
         cols.is_bne * (1 - (1 - u16_sum)) +
         (cols.is_bge + cols.is_bgeu) * (1 - bit) +
         (cols.is_blt + cols.is_bltu) * bit)) = 0 ∧
  -- 4 branch-taken carry assertZeros (PC + op_c_imm = next_pc)
  cols.is_branching *
    ((0 + cols.state.pc[0] + cols.adapter.op_c_imm[0] - cols.next_pc[0]) *
        (65536 : ZMod p)⁻¹ *
      ((0 + cols.state.pc[0] + cols.adapter.op_c_imm[0] - cols.next_pc[0]) *
          (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
  cols.is_branching *
    (((0 + cols.state.pc[0] + cols.adapter.op_c_imm[0] - cols.next_pc[0]) *
          (65536 : ZMod p)⁻¹ + cols.state.pc[1] + cols.adapter.op_c_imm[1] -
          cols.next_pc[1]) * (65536 : ZMod p)⁻¹ *
      (((0 + cols.state.pc[0] + cols.adapter.op_c_imm[0] - cols.next_pc[0]) *
          (65536 : ZMod p)⁻¹ + cols.state.pc[1] + cols.adapter.op_c_imm[1] -
          cols.next_pc[1]) * (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
  cols.is_branching *
    ((((0 + cols.state.pc[0] + cols.adapter.op_c_imm[0] - cols.next_pc[0]) *
            (65536 : ZMod p)⁻¹ + cols.state.pc[1] + cols.adapter.op_c_imm[1] -
            cols.next_pc[1]) * (65536 : ZMod p)⁻¹ + cols.state.pc[2] +
          cols.adapter.op_c_imm[2] - cols.next_pc[2]) * (65536 : ZMod p)⁻¹ *
      ((((0 + cols.state.pc[0] + cols.adapter.op_c_imm[0] - cols.next_pc[0]) *
              (65536 : ZMod p)⁻¹ + cols.state.pc[1] + cols.adapter.op_c_imm[1] -
              cols.next_pc[1]) * (65536 : ZMod p)⁻¹ + cols.state.pc[2] +
            cols.adapter.op_c_imm[2] - cols.next_pc[2]) *
          (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
  cols.is_branching *
    (((((0 + cols.state.pc[0] + cols.adapter.op_c_imm[0] - cols.next_pc[0]) *
              (65536 : ZMod p)⁻¹ + cols.state.pc[1] + cols.adapter.op_c_imm[1] -
              cols.next_pc[1]) * (65536 : ZMod p)⁻¹ + cols.state.pc[2] +
            cols.adapter.op_c_imm[2] - cols.next_pc[2]) *
          (65536 : ZMod p)⁻¹ + 0 + cols.adapter.op_c_imm[3] - 0) *
        (65536 : ZMod p)⁻¹ *
      (((((0 + cols.state.pc[0] + cols.adapter.op_c_imm[0] - cols.next_pc[0]) *
                (65536 : ZMod p)⁻¹ + cols.state.pc[1] + cols.adapter.op_c_imm[1] -
                cols.next_pc[1]) * (65536 : ZMod p)⁻¹ + cols.state.pc[2] +
              cols.adapter.op_c_imm[2] - cols.next_pc[2]) *
            (65536 : ZMod p)⁻¹ + 0 + cols.adapter.op_c_imm[3] - 0) *
          (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
  -- 4 branch-not-taken carry assertZeros (PC + 4 = next_pc) gated by is_real - is_branching
  (is_real - cols.is_branching) *
    ((0 + cols.state.pc[0] + 4 - cols.next_pc[0]) * (65536 : ZMod p)⁻¹ *
      ((0 + cols.state.pc[0] + 4 - cols.next_pc[0]) * (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
  (is_real - cols.is_branching) *
    (((0 + cols.state.pc[0] + 4 - cols.next_pc[0]) * (65536 : ZMod p)⁻¹ +
          cols.state.pc[1] + 0 - cols.next_pc[1]) * (65536 : ZMod p)⁻¹ *
      (((0 + cols.state.pc[0] + 4 - cols.next_pc[0]) * (65536 : ZMod p)⁻¹ +
            cols.state.pc[1] + 0 - cols.next_pc[1]) * (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
  (is_real - cols.is_branching) *
    ((((0 + cols.state.pc[0] + 4 - cols.next_pc[0]) * (65536 : ZMod p)⁻¹ +
            cols.state.pc[1] + 0 - cols.next_pc[1]) * (65536 : ZMod p)⁻¹ +
          cols.state.pc[2] + 0 - cols.next_pc[2]) * (65536 : ZMod p)⁻¹ *
      ((((0 + cols.state.pc[0] + 4 - cols.next_pc[0]) * (65536 : ZMod p)⁻¹ +
              cols.state.pc[1] + 0 - cols.next_pc[1]) * (65536 : ZMod p)⁻¹ +
            cols.state.pc[2] + 0 - cols.next_pc[2]) *
          (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
  (is_real - cols.is_branching) *
    (((((0 + cols.state.pc[0] + 4 - cols.next_pc[0]) * (65536 : ZMod p)⁻¹ +
              cols.state.pc[1] + 0 - cols.next_pc[1]) * (65536 : ZMod p)⁻¹ +
            cols.state.pc[2] + 0 - cols.next_pc[2]) * (65536 : ZMod p)⁻¹ +
          0 + 0 - 0) * (65536 : ZMod p)⁻¹ *
      (((((0 + cols.state.pc[0] + 4 - cols.next_pc[0]) * (65536 : ZMod p)⁻¹ +
                cols.state.pc[1] + 0 - cols.next_pc[1]) * (65536 : ZMod p)⁻¹ +
              cols.state.pc[2] + 0 - cols.next_pc[2]) * (65536 : ZMod p)⁻¹ +
            0 + 0 - 0) * (65536 : ZMod p)⁻¹ - 1)) = 0 ∧
  -- 3 PC alignment byte sends
  (is_real ≠ 0 → (ByteOpcode.ofNat 6).constrain (cols.next_pc[0] * (4 : ZMod p)⁻¹) 14 0) ∧
  (is_real ≠ 0 → (ByteOpcode.ofNat 6).constrain cols.next_pc[1] 16 0) ∧
  (is_real ≠ 0 → (ByteOpcode.ofNat 6).constrain cols.next_pc[2] 16 0)

def TraceSpec (cols : BranchCols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
      cols.is_bltu + cols.is_bgeu
  let opcode_e : ZMod p :=
    cols.is_beq * 40 + cols.is_bne * 41 + cols.is_blt * 42 +
      cols.is_bge * 43 + cols.is_bltu * 44 + cols.is_bgeu * 45
  (_root_.LtOperationSigned.constraints (F := ZMod p)
      cols.adapter.op_a_memory.prev_value cols.adapter.op_b_memory.prev_value
      cols.compare_operation (cols.is_blt + cols.is_bge) is_real).allHold ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := opcode_e,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_beq * (cols.is_beq - 1) = 0 ∧
  cols.is_bne * (cols.is_bne - 1) = 0 ∧
  cols.is_blt * (cols.is_blt - 1) = 0 ∧
  cols.is_bge * (cols.is_bge - 1) = 0 ∧
  cols.is_bltu * (cols.is_bltu - 1) = 0 ∧
  cols.is_bgeu * (cols.is_bgeu - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  branchSpec cols ∧
  cols.adapter_cols.is_trusted = 1

/-- The op_a / op_b register accesses (both reads; no writes — Branch
doesn't update any register, only PC). -/
def opAMemoryAccess (cols : BranchCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_a, 0, 0],
    prev_value := cols.adapter.op_a_memory.prev_value,
    prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }

def opBMemoryAccess (cols : BranchCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := #v[cols.adapter.op_b, 0, 0],
    prev_value := cols.adapter.op_b_memory.prev_value,
    prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
    diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb }

set_option maxHeartbeats 2400000 in
-- Heartbeats elevated for the ~24-conjunct iff RHS refine on 45 cols.
/-- The chip-level half-iff bridge (Branch). -/
theorem traceSpec_implies_allHold (Main : Vector (ZMod p) 45)
    (h_is_real : Main[28] + Main[29] + Main[30] + Main[31] +
                 Main[32] + Main[33] = 1)
    (h_spec : TraceSpec (fromMain Main)) :
    (_root_.Branch.constraints Main).allHold := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  simp only [TraceSpec, fromMain, branchSpec,
    Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ] at h_spec
  obtain ⟨h_lt_op, h_cpu_spec, _h_program,
          h_beq_bin, h_bne_bin, h_blt_bin, h_bge_bin, h_bltu_bin, h_bgeu_bin,
          h_aggregate,
          h_bs, _h_trusted⟩ := h_spec
  obtain ⟨h_iti, h_brn_bin, h_brn_eq,
          h_bt0, h_bt1, h_bt2, h_bt3,
          h_nt0, h_nt1, h_nt2, h_nt3,
          h_pc0_send, h_pc1_send, h_pc2_send⟩ := h_bs
  change List.Forall SP1Constraint.toProp (_root_.Branch.constraints Main)
  rw [_root_.Branch.allHold_constraints_iff]
  -- Boolean conversion helper
  have bool_of : ∀ {x : ZMod p}, x * (x - 1) = 0 → x = 0 ∨ x = 1 := fun h =>
    (mul_eq_zero.mp h).imp_right (by intro h'; linear_combination h')
  -- iff RHS order: 3 sub-allHolds + 6 booleans + aggregate + is_branching boolean
  -- + outcome eq + 4 BT carries + 4 NT carries + 3 byte sends
  refine ⟨?_, ?_, h_lt_op,
          h_beq_bin, h_bne_bin, h_blt_bin, h_bge_bin, h_bltu_bin, h_bgeu_bin,
          h_aggregate,
          h_brn_bin, ?_,
          ?_, ?_, ?_, ?_,
          ?_, ?_, ?_, ?_,
          h_pc0_send, h_pc1_send, h_pc2_send⟩
  -- 1: CPUState bridge via cpuStateSpec_iff_sp1
  · rw [show (Main[28] + Main[29] + Main[30] + Main[31] + Main[32] + Main[33] : ZMod p) = 1
        from h_is_real]
    exact (SP1Clean.CPUState.cpuStateSpec_iff_sp1).mpr h_cpu_spec
  -- 2: ITypeReaderImmutable.constraints.allHold — directly from branchSpec
  · exact h_iti
  -- 3+: is_branching outcome equation and 8 carry-chain assertZeros — push_cast
  -- normalizes the `↑0` and `↑1` casts the iff lemma's `push_cast; rfl` introduced.
  · convert h_brn_eq using 2; push_cast; ring
  · exact h_bt0
  · exact h_bt1
  · exact h_bt2
  · exact h_bt3
  · exact h_nt0
  · exact h_nt1
  · exact h_nt2
  · exact h_nt3
/-- Clean-side `correct_beq`: branch-if-equal. -/
theorem correct_beq
    (Main : Vector (ZMod p) 45) (s : SailState) (hs : s.isInitialized)
    (h_is_beq : Main[28] = 1)
    (h_others_zero : Main[29] = 0 ∧ Main[30] = 0 ∧ Main[31] = 0 ∧
                     Main[32] = 0 ∧ Main[33] = 0)
    (h_spec : TraceSpec (fromMain Main))
    (state_cstrs : (_root_.Branch.constraints Main).initialState s) :
    let imm := _root_.Branch.sp1_imm Main
    let op_b := regidx.Regidx (_root_.Branch.sp1_op_b Main)
    let op_a := regidx.Regidx (_root_.Branch.sp1_op_a Main)
    (_root_.Branch.BEQ.spec_beq imm op_b op_a).run s =
      (_root_.Branch.sp1_branch Main).run s :=
  _root_.Branch.BEQ.correct_beq Main s hs h_is_beq
    (traceSpec_implies_allHold Main
      (by obtain ⟨h29, h30, h31, h32, h33⟩ := h_others_zero
          rw [h_is_beq, h29, h30, h31, h32, h33]; ring)
      h_spec)
    state_cstrs

/-! ## Full `FormalAssertion` promotion (Path-2)

`Assertion.main` is identical to the chip's `main` (no byte lookups
to drop). The `LtOperationSigned.constraints` clause that drives the
branch-taken comparison stays in legacy `Spec` and is deferred to the
trace-level OfflineMemory + state-bus bridge. Memory-bus consistency
likewise deferred. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var BranchCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩, next_pc,
       is_beq, is_bne, is_blt, is_bge, is_bltu, is_bgeu,
       is_branching, _compare_operation,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let opcode_e := is_beq * 40 + is_bne * 41 + is_blt * 42 +
                    is_bge * 43 + is_bltu * 44 + is_bgeu * 45
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_beq * (is_beq - 1) === 0
  is_bne * (is_bne - 1) === 0
  is_blt * (is_blt - 1) === 0
  is_bge * (is_bge - 1) === 0
  is_bltu * (is_bltu - 1) === 0
  is_bgeu * (is_bgeu - 1) === 0
  let sum := is_beq + is_bne + is_blt + is_bge + is_bltu + is_bgeu
  sum * (sum - 1) === 0
  is_branching * (is_branching - 1) === 0
  -- State-bus next_pc grounding. Mirrors upstream's `when(is_branching) /
  -- when(is_real - is_branching)` per-limb carry chain in
  -- `../sp1/.../control_flow/branch/air.rs`. Two gated carry chains
  -- target the same committed `next_pc` (3 limbs, padded to 4 with high
  -- limb 0): one gated by `is_branching` for the `pc + op_c_imm` arm,
  -- one by `1 - is_branching` for the `pc + 4` arm.
  SP1Clean.GatedAddOp.assertion
    (⟨pc.push 0, op_c_imm, next_pc.push 0, is_branching⟩ :
      Var SP1Clean.GatedAddOp.Inputs (ZMod p))
  SP1Clean.GatedAddOp.assertion
    (⟨pc.push 0, #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc.push 0, 1 - is_branching⟩ :
      Var SP1Clean.GatedAddOp.Inputs (ZMod p))
  -- Range bounds on `next_pc[i]` (replaces the lookups previously
  -- emitted by `AddrAddOp.assertion`; `GatedAddOp` drops them per
  -- the lookup-restriction discussion in SP1Clean/Gated.lean).
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), next_pc[0], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), next_pc[1], 16, 0] : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), next_pc[2], 16, 0] : Vector (Expression (ZMod p)) 4)
  -- Iter-8 sub-task E: per-operand memory-bus byte content. Branch
  -- emits 2 register accesses (op_a at +4, op_b at +3) — both pure
  -- reads (no register writes; only PC is updated).
  let clk_low := clk_0_16 + clk_16_24 * 65536
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 4, op_a_memory.access_timestamp.prev_low, op_a_memory.access_timestamp.diff_low_limb,
       op_a_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))
  SP1Clean.OperandAccess.assertion
    (⟨clk_low, 3, op_b_memory.access_timestamp.prev_low, op_b_memory.access_timestamp.diff_low_limb,
       op_b_memory.prev_value⟩ :
      Var SP1Clean.OperandAccess.Assertion.Inputs (ZMod p))

set_option maxHeartbeats 800000 in
-- Higher heartbeats: Branch has 26 input fields + 4 subcircuit calls
-- + 2 OperandAccess calls; localLength_eq synthesis hits the 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) BranchCols unit where
  name := "SP1Clean.Branch"
  main := main
  localLength _ := 0

def Assumptions (_ : BranchCols (ZMod p)) : Prop := True

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨_, _, _, h_pc⟩, _, h_next_pc, _⟩ := h_input
  subst h_next_pc
  obtain ⟨h_cpu_sub, h_prog_sub, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu,
          h_sum, h_branching_bool, h_gated_b, h_gated_u,
          h_l0, h_l1, h_l2, h_oa_a, h_oa_b⟩ := h_holds
  simp only [Vector.map_push, h_pc] at h_gated_b h_gated_u
  simp only [circuit_norm, Lookup.Soundness, Table.toRaw, SP1Clean.ByteOpcodeTable]
    at h_l0 h_l1 h_l2
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_beq
  · linear_combination h_bne
  · linear_combination h_blt
  · linear_combination h_bge
  · linear_combination h_bltu
  · linear_combination h_bgeu
  · linear_combination h_sum
  · linear_combination h_branching_bool
  · exact h_gated_b trivial
  · rcases h_gated_u trivial with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr h
  · simp only [Vector.getElem_map]
    exact SP1Clean.AddrAddOp.Assertion.byteOpcodeSpec_range16 _ h_l0
  · simp only [Vector.getElem_map]
    exact SP1Clean.AddrAddOp.Assertion.byteOpcodeSpec_range16 _ h_l1
  · simp only [Vector.getElem_map]
    exact SP1Clean.AddrAddOp.Assertion.byteOpcodeSpec_range16 _ h_l2
  · exact h_oa_a trivial
  · exact h_oa_b trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨_, _, _, h_pc⟩, _, h_next_pc, _⟩ := h_input
  subst h_next_pc
  obtain ⟨h_cpu, h_prog, h_beq, h_bne, h_blt, h_bge, h_bltu, h_bgeu, h_sum,
          h_branching_bool, h_gated_b, h_gated_u,
          h_l0, h_l1, h_l2, h_oa_a, h_oa_b⟩ := h_spec
  simp only [Vector.map_push, h_pc]
  simp only [circuit_norm, Lookup.Completeness, Table.toRaw, SP1Clean.ByteOpcodeTable]
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_beq
  · linear_combination h_bne
  · linear_combination h_blt
  · linear_combination h_bge
  · linear_combination h_bltu
  · linear_combination h_bgeu
  · linear_combination h_sum
  · linear_combination h_branching_bool
  · exact ⟨trivial, h_gated_b⟩
  · refine ⟨trivial, ?_⟩
    rcases h_gated_u with h | h
    · exact Or.inl (by linear_combination h)
    · exact Or.inr h
  · simp only [Vector.getElem_map] at h_l0
    exact SP1Clean.AddrAddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_l0
  · simp only [Vector.getElem_map] at h_l1
    exact SP1Clean.AddrAddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_l1
  · simp only [Vector.getElem_map] at h_l2
    exact SP1Clean.AddrAddOp.Assertion.byteOpcodeSpec_range16_of_lt _ h_l2
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩

end Assertion

def assertion : FormalAssertion (ZMod p) BranchCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.Branch
