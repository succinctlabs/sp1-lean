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
import SP1Operations.Reader.ITypeReaderImmutable.ITypeReaderImmutable
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Operations.Reader.CPUState.CPUState
import SP1Clean.Operations.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Operations.AddrAddOperation
import SP1Clean.Operations.AddressShape
import SP1Clean.Operations.LoadMemoryAccessGated
import SP1Clean.Operations.LoadByteSelector
import SP1Clean.Operations.LoadHalfSelector
import SP1Clean.Operations.LoadWordSelector
import SP1Clean.Reader.OperandAccess
import SP1Chips.Load.LoadX0.LoadX0Chip
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec

/-! # Chip-level `LoadX0Chip` mirror — load-when-op_a-is-x0 fast path

The LoadX0 chip handles the special case where the destination register
of a load is `x0` (the always-zero register): the load still emits a
memory read but no register write is needed. The chip bundles all 7
load sub-opcodes (LB/LBU/LH/LHU/LW/LWU/LD) into a single 48-column
trace, distinguished by selectors at `Main[41..47]`.

Structural mirror discipline (iff-only structural per heavy-chip
plan). The full sub-word selection / sign-extension machinery is
captured propositionally in `Spec`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LoadX0

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def isRealExpr (cols : Var LoadX0Cols (ZMod p)) : Expression (ZMod p) :=
  cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
    cols.is_lw + cols.is_lwu + cols.is_ld

/-- Selector-weighted opcode: LB=29, LBU=32, LH=30, LHU=33, LW=31,
LWU=34, LD=35. -/
def opcodeExpr (cols : Var LoadX0Cols (ZMod p)) : Expression (ZMod p) :=
  cols.is_lb * 29 + cols.is_lbu * 32 + cols.is_lh * 30 + cols.is_lhu * 33 +
    cols.is_lw * 31 + cols.is_lwu * 34 + cols.is_ld * 35

def main (cols : Var LoadX0Cols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c_imm⟩, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, load_memory_diff_low, load_memory_diff_high,
       _offset_bit, is_lb, is_lbu, is_lh, is_lhu, is_lw,
       is_lwu, is_ld, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), load_memory_diff_low, 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, load_memory_diff_high, 0]
      : Vector (Expression (ZMod p)) 4)
  let opcode_e := is_lb * 29 + is_lbu * 32 + is_lh * 30 + is_lhu * 33 +
                    is_lw * 31 + is_lwu * 34 + is_ld * 35
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_lb * (is_lb - 1) === 0
  is_lbu * (is_lbu - 1) === 0
  is_lh * (is_lh - 1) === 0
  is_lhu * (is_lhu - 1) === 0
  is_lw * (is_lw - 1) === 0
  is_lwu * (is_lwu - 1) === 0
  is_ld * (is_ld - 1) === 0
  let sum := is_lb + is_lbu + is_lh + is_lhu + is_lw + is_lwu + is_ld
  sum * (sum - 1) === 0

def TraceSpec (cols : LoadX0Cols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
      cols.is_lw + cols.is_lwu + cols.is_ld
  let opcode_e : ZMod p :=
    cols.is_lb * 29 + cols.is_lbu * 32 + cols.is_lh * 30 + cols.is_lhu * 33 +
      cols.is_lw * 31 + cols.is_lwu * 34 + cols.is_ld * 35
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
    (cols.load_memory_prev_high * (2 ^ 24) + cols.load_memory_prev_low) 1
    { addr := cols.addr_value,
      prev_value := cols.load_prev_value,
      prev_low := cols.load_memory_prev_low,
      diff_low_limb := cols.load_memory_diff_low } ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := opcode_e,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_lb * (cols.is_lb - 1) = 0 ∧
  cols.is_lbu * (cols.is_lbu - 1) = 0 ∧
  cols.is_lh * (cols.is_lh - 1) = 0 ∧
  cols.is_lhu * (cols.is_lhu - 1) = 0 ∧
  cols.is_lw * (cols.is_lw - 1) = 0 ∧
  cols.is_lwu * (cols.is_lwu - 1) = 0 ∧
  cols.is_ld * (cols.is_ld - 1) = 0 ∧
  is_real * (is_real - 1) = 0 ∧
  cols.adapter_cols.is_trusted = 1

def loadMemoryAccess (cols : LoadX0Cols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := cols.addr_value,
    prev_value := cols.load_prev_value,
    prev_low := cols.load_memory_prev_low,
    diff_low_limb := cols.load_memory_diff_low }

/-! ## Cols-level wrappers around the 7 `_root_.Load.LoadX0.correct_loadX0_*`
proofs.

Mirrors the Phase 2-4 pattern (LoadDouble/LoadByte etc.): each
`correct_loadX0_<variant>` is a thin wrapper that takes
`(LoadX0.constraints Main).allHold` directly (trace-level callers
discharge this) plus the Sail-side preconditions, and forwards to the
corresponding SP1Chips correctness theorem.

Each variant is keyed off `Main[i] = 1` for the appropriate sub-opcode
index (LB:41, LBU:42, LH:43, LHU:44, LW:45, LWU:46, LD:47). All 7
share the same `sp1_loadX0` projector — the destination is x0, so the
write is a no-op and only `nextPC := PC + 4` is observable. -/

/-- Clean-side `correct_loadX0_ld`: 64-bit doubleword load to x0. -/
theorem correct_loadX0_ld
    (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (_root_.Load.LoadX0.constraints Main).allHold)
    (state_cstrs : (_root_.Load.LoadX0.constraints Main).initialState s)
    (h_is_loadX0_ld : Main[47] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (_root_.Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 8 < 2 ^ 64)
    (h_is_aligned : LeanRV64D.Functions.is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 8 = true) :
    let op_a := _root_.Load.LoadX0.sp1_op_a Main
    let op_b := _root_.Load.LoadX0.sp1_ob_b Main
    let imm_c := _root_.Load.LoadX0.sp1_imm_c Main
    (_root_.Load.LoadX0.spec_loadX0_ld imm_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Load.LoadX0.sp1_loadX0 Main).run s :=
  _root_.Load.LoadX0.correct_loadX0_ld Main s hs hs_config h_cstrs
    state_cstrs h_is_loadX0_ld h_fits_in_mem h_is_aligned

/-- Clean-side `correct_loadX0_lwu`: 32-bit unsigned word load to x0. -/
theorem correct_loadX0_lwu
    (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (_root_.Load.LoadX0.constraints Main).allHold)
    (state_cstrs : (_root_.Load.LoadX0.constraints Main).initialState s)
    (h_is_loadX0_lwu : Main[46] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (_root_.Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 4 < 2 ^ 64)
    (h_is_aligned : LeanRV64D.Functions.is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 4 = true) :
    let op_a := _root_.Load.LoadX0.sp1_op_a Main
    let op_b := _root_.Load.LoadX0.sp1_ob_b Main
    let imm_c := _root_.Load.LoadX0.sp1_imm_c Main
    (_root_.Load.LoadX0.spec_loadX0_lwu imm_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Load.LoadX0.sp1_loadX0 Main).run s :=
  _root_.Load.LoadX0.correct_loadX0_lwu Main s hs hs_config h_cstrs
    state_cstrs h_is_loadX0_lwu h_fits_in_mem h_is_aligned

/-- Clean-side `correct_loadX0_lw`: 32-bit signed word load to x0. -/
theorem correct_loadX0_lw
    (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (_root_.Load.LoadX0.constraints Main).allHold)
    (state_cstrs : (_root_.Load.LoadX0.constraints Main).initialState s)
    (h_is_loadX0_lw : Main[45] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (_root_.Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 4 < 2 ^ 64)
    (h_is_aligned : LeanRV64D.Functions.is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 4 = true) :
    let op_a := _root_.Load.LoadX0.sp1_op_a Main
    let op_b := _root_.Load.LoadX0.sp1_ob_b Main
    let imm_c := _root_.Load.LoadX0.sp1_imm_c Main
    (_root_.Load.LoadX0.spec_loadX0_lw imm_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Load.LoadX0.sp1_loadX0 Main).run s :=
  _root_.Load.LoadX0.correct_loadX0_lw Main s hs hs_config h_cstrs
    state_cstrs h_is_loadX0_lw h_fits_in_mem h_is_aligned

/-- Clean-side `correct_loadX0_lhu`: 16-bit unsigned halfword load to x0. -/
theorem correct_loadX0_lhu
    (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (_root_.Load.LoadX0.constraints Main).allHold)
    (state_cstrs : (_root_.Load.LoadX0.constraints Main).initialState s)
    (h_is_loadX0_lhu : Main[44] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (_root_.Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned : LeanRV64D.Functions.is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 2 = true) :
    let op_a := _root_.Load.LoadX0.sp1_op_a Main
    let op_b := _root_.Load.LoadX0.sp1_ob_b Main
    let imm_c := _root_.Load.LoadX0.sp1_imm_c Main
    (_root_.Load.LoadX0.spec_loadX0_lhu imm_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Load.LoadX0.sp1_loadX0 Main).run s :=
  _root_.Load.LoadX0.correct_loadX0_lhu Main s hs hs_config h_cstrs
    state_cstrs h_is_loadX0_lhu h_fits_in_mem h_is_aligned

/-- Clean-side `correct_loadX0_lh`: 16-bit signed halfword load to x0. -/
theorem correct_loadX0_lh
    (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (_root_.Load.LoadX0.constraints Main).allHold)
    (state_cstrs : (_root_.Load.LoadX0.constraints Main).initialState s)
    (h_is_loadX0_lh : Main[43] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (_root_.Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 2 < 2 ^ 64)
    (h_is_aligned : LeanRV64D.Functions.is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 2 = true) :
    let op_a := _root_.Load.LoadX0.sp1_op_a Main
    let op_b := _root_.Load.LoadX0.sp1_ob_b Main
    let imm_c := _root_.Load.LoadX0.sp1_imm_c Main
    (_root_.Load.LoadX0.spec_loadX0_lh imm_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Load.LoadX0.sp1_loadX0 Main).run s :=
  _root_.Load.LoadX0.correct_loadX0_lh Main s hs hs_config h_cstrs
    state_cstrs h_is_loadX0_lh h_fits_in_mem h_is_aligned

/-- Clean-side `correct_loadX0_lbu`: 8-bit unsigned byte load to x0. -/
theorem correct_loadX0_lbu
    (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (_root_.Load.LoadX0.constraints Main).allHold)
    (state_cstrs : (_root_.Load.LoadX0.constraints Main).initialState s)
    (h_is_loadX0_lbu : Main[42] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (_root_.Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    (h_is_aligned : LeanRV64D.Functions.is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 1 = true) :
    let op_a := _root_.Load.LoadX0.sp1_op_a Main
    let op_b := _root_.Load.LoadX0.sp1_ob_b Main
    let imm_c := _root_.Load.LoadX0.sp1_imm_c Main
    (_root_.Load.LoadX0.spec_loadX0_lbu imm_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Load.LoadX0.sp1_loadX0 Main).run s :=
  _root_.Load.LoadX0.correct_loadX0_lbu Main s hs hs_config h_cstrs
    state_cstrs h_is_loadX0_lbu h_fits_in_mem h_is_aligned

/-- Clean-side `correct_loadX0_lb`: 8-bit signed byte load to x0. -/
theorem correct_loadX0_lb
    (Main : Vector (ZMod p) 48) (s : SailState)
    (hs : SailState.isInitialized s)
    (hs_config : SailState.isValidMemConfig s hs)
    (h_cstrs : (_root_.Load.LoadX0.constraints Main).allHold)
    (state_cstrs : (_root_.Load.LoadX0.constraints Main).initialState s)
    (h_is_loadX0_lb : Main[41] = 1)
    (h_fits_in_mem :
      let reg_val := (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]]).toNat
      let offset := (BitVec.signExtend 64 (_root_.Load.LoadX0.sp1_imm_c Main)).toNat
      reg_val + offset + 1 < 2 ^ 64)
    (h_is_aligned : LeanRV64D.Functions.is_aligned_vaddr (virtaddr.Virtaddr
      (Word.toBitVec64 #v[Main[15], Main[16], Main[17], Main[18]] + BitVec.signExtend 64
        (BitVec.ofNat 12 Main[21].val))) 1 = true) :
    let op_a := _root_.Load.LoadX0.sp1_op_a Main
    let op_b := _root_.Load.LoadX0.sp1_ob_b Main
    let imm_c := _root_.Load.LoadX0.sp1_imm_c Main
    (_root_.Load.LoadX0.spec_loadX0_lb imm_c (.Regidx op_b) (.Regidx op_a)).run s =
      (_root_.Load.LoadX0.sp1_loadX0 Main).run s :=
  _root_.Load.LoadX0.correct_loadX0_lb Main s hs hs_config h_cstrs
    state_cstrs h_is_loadX0_lb h_fits_in_mem h_is_aligned

/-! ## Full `FormalAssertion` promotion (Path-2)

Drops the two bare `load_memory_diff_{low,high}` byte lookups; covers
`CPUState`, `ProgramTable`, and the 8 boolean asserts (7 sub-opcode +
aggregate is_real). Memory bridge content is deferred to the
trace-level OfflineMemory pass. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var LoadX0Cols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, _load_memory_diff_low, _load_memory_diff_high,
       _offset_bit, is_lb, is_lbu, is_lh, is_lhu, is_lw,
       is_lwu, is_ld, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  let opcode_e := is_lb * 29 + is_lbu * 32 + is_lh * 30 + is_lhu * 33 +
                    is_lw * 31 + is_lwu * 34 + is_ld * 35
  SP1Clean.ProgramTable.assertion
    (⟨pc, opcode_e, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_lb * (is_lb - 1) === 0
  is_lbu * (is_lbu - 1) === 0
  is_lh * (is_lh - 1) === 0
  is_lhu * (is_lhu - 1) === 0
  is_lw * (is_lw - 1) === 0
  is_lwu * (is_lwu - 1) === 0
  is_ld * (is_ld - 1) === 0
  let sum := is_lb + is_lbu + is_lh + is_lhu + is_lw + is_lwu + is_ld
  sum * (sum - 1) === 0
  -- Iter-8 sub-task E (partial): register-side OperandAccess only.
  -- Load RAM access deferred (see `load-store-ram-access-deferred`).
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
-- Higher heartbeats: 31 input fields + 4 subcircuit calls + 2 OperandAccess
-- calls pushes localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LoadX0Cols unit where
  name := "SP1Clean.LoadX0"
  main := main
  localLength _ := 0

def Assumptions (_ : LoadX0Cols (ZMod p)) : Prop := True

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_lb, h_lbu, h_lh, h_lhu, h_lw,
          h_lwu, h_ld, h_sum, h_oa_a, h_oa_b⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · binary_iff h_lb
  · binary_iff h_lbu
  · binary_iff h_lh
  · binary_iff h_lhu
  · binary_iff h_lw
  · binary_iff h_lwu
  · binary_iff h_ld
  · binary_iff h_sum
  · exact h_oa_a trivial
  · exact h_oa_b trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_lb, h_lbu, h_lh, h_lhu, h_lw, h_lwu, h_ld,
          h_sum, h_oa_a, h_oa_b⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · binary_iff h_lb
  · binary_iff h_lbu
  · binary_iff h_lh
  · binary_iff h_lhu
  · binary_iff h_lw
  · binary_iff h_lwu
  · binary_iff h_ld
  · binary_iff h_sum
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩

end Assertion

def assertion : FormalAssertion (ZMod p) LoadX0Cols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-! ## `AssertionGated` — full sub-circuit composition with gated multiplicities

LoadX0 covers all 7 load variants (LB/LBU/LH/LHU/LW/LWU/LD) where the
destination register is `x0` (so the load is a no-op effectively).
Composes CPUState, AddrAddOp, AddressShape, ITypeReader,
LoadMemoryAccessGated, and all three selectors (gated by their respective
opcode flags). Multiplicity for the load-memory access is `is_real`
(sum of all 7 opcode flags). -/

namespace AssertionGated

open Circuit

@[reducible]
def main (cols : Var LoadX0Cols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩,
       addr_value, addr_top_two_limb_inv,
       load_prev_value, load_memory_prev_high, load_memory_prev_low,
       load_memory_flag, load_memory_diff_low, load_memory_diff_high,
       offset_bit, is_lb, is_lbu, is_lh, is_lhu, is_lw, is_lwu, is_ld,
       _adapter_cols⟩ := cols
  let is_real : Expression (ZMod p) :=
    is_lb + is_lbu + is_lh + is_lhu + is_lw + is_lwu + is_ld
  let clk_low : Expression (ZMod p) := clk_0_16 + clk_16_24 * 65536
  let opcode : Expression (ZMod p) :=
    is_lb * 29 + is_lbu * 32 + is_lh * 30 + is_lhu * 33 +
      is_lw * 31 + is_lwu * 34 + is_ld * 35
  -- For LoadX0, op_a_write_value is constrained to all-zero (x0 stays 0).
  let op_a_write_value : Vector (Expression (ZMod p)) 4 := #v[0, 0, 0, 0]
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨op_b_memory.prev_value, op_c_imm, addr_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  SP1Clean.AddressShape.assertion
    (⟨addr_value, addr_top_two_limb_inv,
       offset_bit[0], offset_bit[1], offset_bit[2]⟩ :
      Var SP1Clean.AddressShape.Inputs (ZMod p))
  SP1Clean.ITypeReader.assertion
    (⟨clk_high, clk_low, opcode, pc, op_a_write_value,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩⟩ :
      Var SP1Clean.ITypeReader.Inputs (ZMod p))
  SP1Clean.LoadMemoryAccessGated.assertion
    (⟨clk_high, clk_low, addr_value, load_prev_value,
       load_memory_prev_high, load_memory_prev_low,
       load_memory_diff_low, load_memory_diff_high,
       load_memory_flag, is_real⟩ :
      Var SP1Clean.LoadMemoryAccessGated.Inputs (ZMod p))
  -- Boolean and sum gates.
  is_lb * (is_lb - 1) === 0
  is_lbu * (is_lbu - 1) === 0
  is_lh * (is_lh - 1) === 0
  is_lhu * (is_lhu - 1) === 0
  is_lw * (is_lw - 1) === 0
  is_lwu * (is_lwu - 1) === 0
  is_ld * (is_ld - 1) === 0
  is_real * (is_real - 1) === 0
  op_a_0 === 1  -- destination is x0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LoadX0Cols unit where
  name := "SP1Clean.LoadX0.Gated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

/-- Chip-level Assumptions: the load-memory contract for the multi-opcode
LoadX0 chip. No selector contracts (LoadX0 doesn't carry sub-word
extraction). `is_real` is the sum of all 7 opcode flags. -/
def Assumptions (cols : LoadX0Cols (ZMod p)) : Prop :=
  let clk_low : ZMod p := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let is_real : ZMod p :=
    cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
      cols.is_lw + cols.is_lwu + cols.is_ld
  SP1Clean.LoadMemoryAccessGated.Assertion.Contract
    ⟨cols.state.clk_high, clk_low, cols.addr_value, cols.load_prev_value,
     cols.load_memory_prev_high, cols.load_memory_prev_low,
     cols.load_memory_diff_low, cols.load_memory_diff_high,
     cols.load_memory_flag, is_real⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_addr_sub, h_addr_shape_sub, h_itr_sub, h_lmag_sub,
          h_lb, h_lbu, h_lh, h_lhu, h_lw, h_lwu, h_ld, h_sum, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_addr_sub trivial
  -- AddressShape arm: offset_bit[i] vector indexing requires convert,
  -- plus `Vector.getElem_map` to unfold the residual indexed-projection.
  · convert h_addr_shape_sub trivial using 5
    all_goals simp [Vector.getElem_map]
  · exact h_itr_sub trivial
  · exact h_lmag_sub h_assumptions
  · binary_iff h_lb
  · binary_iff h_lbu
  · binary_iff h_lh
  · binary_iff h_lhu
  · binary_iff h_lw
  · binary_iff h_lwu
  · binary_iff h_ld
  · binary_iff h_sum
  · exact h_op_a_0

set_option maxHeartbeats 800000 in
-- Mirrors soundness destructure.
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_addr, h_addr_shape, h_itr, h_lmag, h_lb, h_lbu, h_lh,
          h_lhu, h_lw, h_lwu, h_ld, h_sum, h_op_a_0⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_addr⟩
  · refine ⟨trivial, ?_⟩
    convert h_addr_shape using 5
    all_goals simp [Vector.getElem_map]
  · exact ⟨trivial, h_itr⟩
  · exact ⟨h_lmag, h_lmag⟩
  · binary_iff h_lb
  · binary_iff h_lbu
  · binary_iff h_lh
  · binary_iff h_lhu
  · binary_iff h_lw
  · binary_iff h_lwu
  · binary_iff h_ld
  · binary_iff h_sum
  · exact h_op_a_0

end AssertionGated

def assertionGated : FormalAssertion (ZMod p) LoadX0Cols :=
  { AssertionGated.elaborated with
    Assumptions := AssertionGated.Assumptions,
    Spec := AssertionGated.FormalSpec,
    soundness := AssertionGated.soundness,
    completeness := AssertionGated.completeness }

end SP1Clean.LoadX0
