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
import SP1Operations.Operation.AddrAddOperation
import SP1Chips.Store.StoreDouble.Common
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Reader.ITypeReaderImmutable

/-! # Chip-level `StoreDoubleChip` mirror — 64-bit store

Sibling of `StoreWordChip` for 64-bit doubleword stores (`sd`). 39
columns. Distinguishes from SW by storing the entire `op_a` register
value (the 4-limb `op_a_memory_prev_value`) at the computed address —
no explicit `store_write_value` columns since the chip just routes
op_a's current value to RAM.

Opcode: `39 = SD` (Store Double).
-/

namespace SP1Clean.StoreDouble

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure StoreDoubleCols (T : Type) where
  clk_high : T                              -- Main[0]
  clk_16_24 : T                             -- Main[1]
  clk_0_16 : T                              -- Main[2]
  pc : Vector T 3                           -- Main[3..5]
  op_a : T                                  -- Main[6]
  op_a_memory_prev_value : Vector T 4       -- Main[7..10] (also the write data)
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
  store_prev_value : Vector T 4             -- Main[29..32]
  store_memory_prev_high : T                -- Main[33]
  store_memory_prev_low : T                 -- Main[34]
  store_memory_flag : T                     -- Main[35]
  store_memory_diff_low : T                 -- Main[36]
  store_memory_diff_high : T                -- Main[37]
  is_real : T                               -- Main[38]
deriving ProvableStruct

def main (cols : Var StoreDoubleCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c_imm, _addr_value, _addr_top_two_limb_inv,
       _store_prev_value, _store_memory_prev_high, _store_memory_prev_low,
       _store_memory_flag, store_memory_diff_low, store_memory_diff_high,
       is_real⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), store_memory_diff_low, 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, store_memory_diff_high, 0]
      : Vector (Expression (ZMod p)) 4)
  SP1Clean.ProgramTable.assertion
    (⟨pc, 39, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_real * (is_real - 1) === 0

def Spec (cols : StoreDoubleCols (ZMod p)) : Prop :=
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
    (cols.store_memory_prev_high * (2 ^ 24) + cols.store_memory_prev_low) 0
    { addr := cols.addr_value,
      prev_value := cols.store_prev_value,
      prev_low := cols.store_memory_prev_low,
      diff_low_limb := cols.store_memory_diff_low } ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc, opcode := 39,
      op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := cols.op_c_imm,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0

def storeMemoryAccess (cols : StoreDoubleCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := cols.addr_value,
    prev_value := cols.store_prev_value,
    prev_low := cols.store_memory_prev_low,
    diff_low_limb := cols.store_memory_diff_low }

/-- For SD, the write data is the full `op_a_memory_prev_value` (the
chip routes the entire current op_a register to RAM, no sub-word
selection). -/
def storeWriteValue (cols : StoreDoubleCols (ZMod p)) : Word (ZMod p) :=
  cols.op_a_memory_prev_value

/-- Project a raw SP1 row into the structured `StoreDoubleCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 39) : StoreDoubleCols (ZMod p) :=
  ⟨Main[0], Main[1], Main[2],
   #v[Main[3], Main[4], Main[5]],
   Main[6],
   #v[Main[7], Main[8], Main[9], Main[10]],
   Main[11], Main[12], Main[13],
   Main[14],
   #v[Main[15], Main[16], Main[17], Main[18]],
   Main[19], Main[20],
   #v[Main[21], Main[22], Main[23], Main[24]],
   #v[Main[25], Main[26], Main[27]],
   Main[28],
   #v[Main[29], Main[30], Main[31], Main[32]],
   Main[33], Main[34], Main[35], Main[36], Main[37],
   Main[38]⟩

/-- Iff RHS for the Store Double (SD) variant, mirroring
`_root_.Store.StoreDouble.allHold_constraints_iff_of_is_real`. SD has a
single `is_real` opcode (no sub-width variants). The full 4-limb
`op_a_memory_prev_value` is routed to RAM as the store data (no
sub-word selection or sign extension). -/
def SpecForIff_of_is_real (cols : StoreDoubleCols (ZMod p)) : Prop :=
  SP1Clean.AddrAddOp.Spec
      cols.op_b_memory_prev_value cols.op_c_imm
      { value := cols.addr_value } ∧
  cols.addr_top_two_limb_inv * (cols.addr_value[1] + cols.addr_value[2]) = 1 ∧
  (cols.addr_value[0] * (8 : ZMod p)⁻¹).val < 2 ^ ZMod.val (13 : ZMod p) ∧
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ITypeReaderImmutable.itypeReaderImmutableSpec
      (cols.clk_0_16 + cols.clk_16_24 * 65536) 39 cols.pc
      { op_a := cols.op_a,
        op_a_memory :=
          { prev_value := cols.op_a_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_a_memory_prev_low,
                diff_low_limb := cols.op_a_memory_diff_low } },
        op_a_0 := cols.op_a_0, op_b := cols.op_b,
        op_b_memory :=
          { prev_value := cols.op_b_memory_prev_value,
            access_timestamp :=
              { prev_low := cols.op_b_memory_prev_low,
                diff_low_limb := cols.op_b_memory_diff_low } },
        op_c_imm := cols.op_c_imm } ∧
  (cols.store_memory_flag = 0 ∨ cols.store_memory_flag = 1) ∧
  (cols.store_memory_flag = 0 ∨ cols.clk_high = cols.store_memory_prev_high) ∧
  cols.store_memory_flag * (cols.clk_0_16 + cols.clk_16_24 * 65536 + 1) +
      (1 - cols.store_memory_flag) * cols.clk_high -
      (cols.store_memory_flag * cols.store_memory_prev_low +
        (1 - cols.store_memory_flag) * cols.store_memory_prev_high) - 1 =
    cols.store_memory_diff_low + cols.store_memory_diff_high * 65536 ∧
  cols.store_memory_diff_low.val < 65536 ∧
  ((0 : ZMod p) < 256 ∧ cols.store_memory_diff_high < (256 : ZMod p) ∧
    (0 : ZMod p) < 256) ∧
  Word.isU64 cols.store_prev_value

set_option maxHeartbeats 800000 in
-- Higher heartbeats: the iff destructure unfolds the full constraint list
-- via the SP1-side `_of_is_real` helper.
/-- The chip-level bridge for the Store Double variant. -/
theorem iff_sp1_of_is_real (Main : Vector (ZMod p) 39) (h_is_real : Main[38] = 1) :
    (_root_.Store.StoreDouble.constraints Main).allHold ↔
      SpecForIff_of_is_real (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  change List.Forall SP1Constraint.toProp (_root_.Store.StoreDouble.constraints Main) ↔ _
  rw [_root_.Store.StoreDouble.allHold_constraints_iff_of_is_real Main h_is_real]
  simp only [show ∀ (a : SP1ConstraintList (ZMod p)),
      List.Forall SP1Constraint.toProp a = a.allHold from fun _ => rfl,
    SP1Clean.CPUState.cpuStateSpec_iff_sp1,
    SP1Clean.ITypeReaderImmutable.itypeReaderImmutableSpec_iff_sp1,
    SP1Clean.AddrAddOp.iff_sp1]
  simp [SpecForIff_of_is_real, fromMain]

end SP1Clean.StoreDouble
