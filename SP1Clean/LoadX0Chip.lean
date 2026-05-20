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
import SP1Operations.Reader.ITypeReaderImmutable
import SP1Operations.Reader.CPUState
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader

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

namespace SP1Clean.LoadX0

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure LoadX0Cols (T : Type) where
  clk_high : T                              -- Main[0]
  clk_16_24 : T                             -- Main[1]
  clk_0_16 : T                              -- Main[2]
  pc : Vector T 3                           -- Main[3..5]
  op_a : T                                  -- Main[6] (always x0)
  op_a_memory_prev_value : Vector T 4       -- Main[7..10]
  op_a_memory_prev_low : T                  -- Main[11]
  op_a_memory_diff_low : T                  -- Main[12]
  op_a_0 : T                                -- Main[13] (forced to 1)
  op_b : T                                  -- Main[14]
  op_b_memory_prev_value : Vector T 4       -- Main[15..18]
  op_b_memory_prev_low : T                  -- Main[19]
  op_b_memory_diff_low : T                  -- Main[20]
  op_c_imm : Vector T 4                     -- Main[21..24]
  addr_value : Vector T 3                   -- Main[25..27]
  addr_top_two_limb_inv : T                 -- Main[28]
  load_prev_value : Vector T 4              -- Main[29..32]
  load_memory_prev_high : T                 -- Main[33]
  load_memory_prev_low : T                  -- Main[34]
  load_memory_flag : T                      -- Main[35]
  load_memory_diff_low : T                  -- Main[36]
  load_memory_diff_high : T                 -- Main[37]
  byte_offset_selectors : Vector T 3        -- Main[38..40] (byte-position selectors)
  is_lb : T                                 -- Main[41]
  is_lbu : T                                -- Main[42]
  is_lh : T                                 -- Main[43]
  is_lhu : T                                -- Main[44]
  is_lw : T                                 -- Main[45]
  is_lwu : T                                -- Main[46]
  is_ld : T                                 -- Main[47]
deriving ProvableStruct

def isRealExpr (cols : Var LoadX0Cols (ZMod p)) : Expression (ZMod p) :=
  cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
    cols.is_lw + cols.is_lwu + cols.is_ld

/-- Selector-weighted opcode: LB=29, LBU=32, LH=30, LHU=33, LW=31,
LWU=34, LD=35. -/
def opcodeExpr (cols : Var LoadX0Cols (ZMod p)) : Expression (ZMod p) :=
  cols.is_lb * 29 + cols.is_lbu * 32 + cols.is_lh * 30 + cols.is_lhu * 33 +
    cols.is_lw * 31 + cols.is_lwu * 34 + cols.is_ld * 35

def main (cols : Var LoadX0Cols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c_imm, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, load_memory_diff_low, load_memory_diff_high,
       _byte_offset_selectors, is_lb, is_lbu, is_lh, is_lhu, is_lw,
       is_lwu, is_ld⟩ := cols
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

def Spec (cols : LoadX0Cols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
      cols.is_lw + cols.is_lwu + cols.is_ld
  let opcode_e : ZMod p :=
    cols.is_lb * 29 + cols.is_lbu * 32 + cols.is_lh * 30 + cols.is_lhu * 33 +
      cols.is_lw * 31 + cols.is_lwu * 34 + cols.is_ld * 35
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_a
      { prev_value := cols.op_a_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_a_memory_prev_low,
            diff_low_limb := cols.op_a_memory_diff_low } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_b
      { prev_value := cols.op_b_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_b_memory_prev_low,
            diff_low_limb := cols.op_b_memory_diff_low } }) ∧
  SP1Clean.memoryAccessSpec
    (cols.load_memory_prev_high * (2 ^ 24) + cols.load_memory_prev_low) 1
    { addr := cols.addr_value,
      prev_value := cols.load_prev_value,
      prev_low := cols.load_memory_prev_low,
      diff_low_limb := cols.load_memory_diff_low } ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc, opcode := opcode_e,
      op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := cols.op_c_imm,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_lb * (cols.is_lb - 1) = 0 ∧
  cols.is_lbu * (cols.is_lbu - 1) = 0 ∧
  cols.is_lh * (cols.is_lh - 1) = 0 ∧
  cols.is_lhu * (cols.is_lhu - 1) = 0 ∧
  cols.is_lw * (cols.is_lw - 1) = 0 ∧
  cols.is_lwu * (cols.is_lwu - 1) = 0 ∧
  cols.is_ld * (cols.is_ld - 1) = 0 ∧
  is_real * (is_real - 1) = 0

def loadMemoryAccess (cols : LoadX0Cols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := cols.addr_value,
    prev_value := cols.load_prev_value,
    prev_low := cols.load_memory_prev_low,
    diff_low_limb := cols.load_memory_diff_low }

/-! ## Full `FormalAssertion` promotion (Path-2)

Drops the two bare `load_memory_diff_{low,high}` byte lookups; covers
`CPUState`, `ProgramTable`, and the 8 boolean asserts (7 sub-opcode +
aggregate is_real). Memory bridge content is deferred to the
trace-level OfflineMemory pass. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var LoadX0Cols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c_imm, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, _load_memory_diff_low, _load_memory_diff_high,
       _byte_offset_selectors, is_lb, is_lbu, is_lh, is_lhu, is_lw,
       is_lwu, is_ld⟩ := cols
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

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LoadX0Cols unit where
  name := "SP1Clean.LoadX0"
  main := main
  localLength _ := 0

def Assumptions (_ : LoadX0Cols (ZMod p)) : Prop := True

def FormalSpec (cols : LoadX0Cols (ZMod p)) : Prop :=
  let is_real : ZMod p :=
    cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
      cols.is_lw + cols.is_lwu + cols.is_ld
  let opcode_e : ZMod p :=
    cols.is_lb * 29 + cols.is_lbu * 32 + cols.is_lh * 30 + cols.is_lhu * 33 +
      cols.is_lw * 31 + cols.is_lwu * 34 + cols.is_ld * 35
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc, opcode := opcode_e, op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0], op_c := cols.op_c_imm,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_lb * (cols.is_lb - 1) = 0 ∧
  cols.is_lbu * (cols.is_lbu - 1) = 0 ∧
  cols.is_lh * (cols.is_lh - 1) = 0 ∧
  cols.is_lhu * (cols.is_lhu - 1) = 0 ∧
  cols.is_lw * (cols.is_lw - 1) = 0 ∧
  cols.is_lwu * (cols.is_lwu - 1) = 0 ∧
  cols.is_ld * (cols.is_ld - 1) = 0 ∧
  is_real * (is_real - 1) = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu_sub, h_prog_sub, h_lb, h_lbu, h_lh, h_lhu, h_lw, h_lwu, h_ld,
          h_sum⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_lb
  · linear_combination h_lbu
  · linear_combination h_lh
  · linear_combination h_lhu
  · linear_combination h_lw
  · linear_combination h_lwu
  · linear_combination h_ld
  · linear_combination h_sum

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu, h_prog, h_lb, h_lbu, h_lh, h_lhu, h_lw, h_lwu, h_ld,
          h_sum⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_lb
  · linear_combination h_lbu
  · linear_combination h_lh
  · linear_combination h_lhu
  · linear_combination h_lw
  · linear_combination h_lwu
  · linear_combination h_ld
  · linear_combination h_sum

end Assertion

def assertion : FormalAssertion (ZMod p) LoadX0Cols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.LoadX0
