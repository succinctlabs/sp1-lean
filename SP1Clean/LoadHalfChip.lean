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
import SP1Operations.Reader.ITypeReader
import SP1Operations.Reader.CPUState
import SP1Operations.Operation.U16MSBOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader

/-! # Chip-level `LoadHalfChip` mirror — 16-bit signed/unsigned load

Sibling of `LoadByteChip` for half-word (16-bit) loads (`lh` signed /
`lhu` unsigned). 44 columns: two opcode selectors plus the sub-word
selector machinery for half-word position within the 8-byte aligned
double.

Opcodes: `30 = LH`, `33 = LHU`.
-/

namespace SP1Clean.LoadHalf

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure LoadHalfCols (T : Type) where
  clk_high : T                              -- Main[0]
  clk_16_24 : T                             -- Main[1]
  clk_0_16 : T                              -- Main[2]
  pc : Vector T 3                           -- Main[3..5]
  op_a : T                                  -- Main[6]
  op_a_memory_prev_value : Vector T 4       -- Main[7..10]
  op_a_memory_prev_low : T                  -- Main[11]
  op_a_memory_diff_low : T                  -- Main[12]
  op_a_0 : T                                -- Main[13]
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
  half_offset_flag : T                      -- Main[38]
  op_a_write_value : Vector T 4             -- Main[39..42] (loaded + sign-ext'd half)
  signed_extension_flag : T                 -- (msb of loaded half, used for LH sign-ext)
  is_lh : T                                 -- Main[?]
  is_lhu : T                                -- Main[?]
deriving ProvableStruct

def main (cols : Var LoadHalfCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c_imm, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, load_memory_diff_low, load_memory_diff_high,
       _half_offset_flag, _op_a_write_value, _signed_extension_flag,
       is_lh, is_lhu⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), load_memory_diff_low, 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, load_memory_diff_high, 0]
      : Vector (Expression (ZMod p)) 4)
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_lh * 30 + is_lhu * 33,
      op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_lh * (is_lh - 1) === 0
  is_lhu * (is_lhu - 1) === 0
  (is_lh + is_lhu) * (is_lh + is_lhu - 1) === 0

def Spec (cols : LoadHalfCols (ZMod p)) : Prop :=
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
    { pc := cols.pc, opcode := cols.is_lh * 30 + cols.is_lhu * 33,
      op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := cols.op_c_imm,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_lh * (cols.is_lh - 1) = 0 ∧
  cols.is_lhu * (cols.is_lhu - 1) = 0 ∧
  (cols.is_lh + cols.is_lhu) * (cols.is_lh + cols.is_lhu - 1) = 0

def loadMemoryAccess (cols : LoadHalfCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := cols.addr_value,
    prev_value := cols.load_prev_value,
    prev_low := cols.load_memory_prev_low,
    diff_low_limb := cols.load_memory_diff_low }

end SP1Clean.LoadHalf
