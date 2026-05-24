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
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Chips.Store.StoreDouble.Common
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Reader.ITypeReaderImmutable
import SP1Clean.Reader.OperandAccess

/-! # Chip-level `StoreDoubleChip` mirror — 64-bit store

Sibling of `StoreWordChip` for 64-bit doubleword stores (`sd`). 39
columns. Distinguishes from SW by storing the entire `op_a` register
value (the 4-limb `op_a_memory.prev_value`) at the computed address —
no explicit `store_value` columns since the chip just routes
op_a's current value to RAM.

Opcode: `39 = SD` (Store Double).
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.StoreDouble

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure StoreDoubleCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  addr_value : Vector T 3                   -- Main[25..27]
  addr_top_two_limb_inv : T                 -- Main[28]
  store_prev_value : Vector T 4             -- Main[29..32]
  store_memory_prev_high : T                -- Main[33]
  store_memory_prev_low : T                 -- Main[34]
  store_memory_flag : T                     -- Main[35]
  store_memory_diff_low : T                 -- Main[36]
  store_memory_diff_high : T                -- Main[37]
  is_real : T                               -- Main[38]
  next_pc_carry_value : Vector T 3
deriving ProvableStruct

def main (cols : Var StoreDoubleCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c_imm⟩, _addr_value, _addr_top_two_limb_inv,
       _store_prev_value, _store_memory_prev_high, _store_memory_prev_low,
       _store_memory_flag, store_memory_diff_low, store_memory_diff_high,
       is_real, _next_pc_carry_value⟩ := cols
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
    (cols.store_memory_prev_high * (2 ^ 24) + cols.store_memory_prev_low) 0
    { addr := cols.addr_value,
      prev_value := cols.store_prev_value,
      prev_low := cols.store_memory_prev_low,
      diff_low_limb := cols.store_memory_diff_low } ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 39,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0

def storeMemoryAccess (cols : StoreDoubleCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := cols.addr_value,
    prev_value := cols.store_prev_value,
    prev_low := cols.store_memory_prev_low,
    diff_low_limb := cols.store_memory_diff_low }

/-- For SD, the write data is the full `op_a_memory.prev_value` (the
chip routes the entire current op_a register to RAM, no sub-word
selection). -/
def storeWriteValue (cols : StoreDoubleCols (ZMod p)) : Word (ZMod p) :=
  cols.adapter.op_a_memory.prev_value

/-- Project a raw SP1 row into the structured `StoreDoubleCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 39) : StoreDoubleCols (ZMod p) :=
  ⟨⟨Main[0], Main[1], Main[2], #v[Main[3], Main[4], Main[5]]⟩,
      ⟨Main[6],
    ⟨#v[Main[7], Main[8], Main[9], Main[10]], ⟨Main[11], Main[12]⟩⟩,
    Main[13],
    Main[14],
    ⟨#v[Main[15], Main[16], Main[17], Main[18]], ⟨Main[19], Main[20]⟩⟩,
    #v[Main[21], Main[22], Main[23], Main[24]]⟩,
   #v[Main[25], Main[26], Main[27]],
   Main[28],
   #v[Main[29], Main[30], Main[31], Main[32]],
   Main[33], Main[34], Main[35], Main[36], Main[37],
   Main[38], #v[0, 0, 0]⟩

/-- Iff RHS for the Store Double (SD) variant, mirroring
`_root_.Store.StoreDouble.allHold_constraints_iff_of_is_real`. SD has a
single `is_real` opcode (no sub-width variants). The full 4-limb
`op_a_memory.prev_value` is routed to RAM as the store data (no
sub-word selection or sign extension). -/
def SpecForIff_of_is_real (cols : StoreDoubleCols (ZMod p)) : Prop :=
  SP1Clean.AddrAddOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
      { value := cols.addr_value } ∧
  cols.addr_top_two_limb_inv * (cols.addr_value[1] + cols.addr_value[2]) = 1 ∧
  (cols.addr_value[0] * (8 : ZMod p)⁻¹).val < 2 ^ ZMod.val (13 : ZMod p) ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ITypeReaderImmutable.itypeReaderImmutableSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 39 cols.state.pc
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
  (cols.store_memory_flag = 0 ∨ cols.store_memory_flag = 1) ∧
  (cols.store_memory_flag = 0 ∨ cols.state.clk_high = cols.store_memory_prev_high) ∧
  cols.store_memory_flag * (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 1) +
      (1 - cols.store_memory_flag) * cols.state.clk_high -
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

/-! ## Full `FormalAssertion` promotion (Path-2)

Drops the two bare byte lookups on `store_memory_diff_low` /
`store_memory_diff_high`; covers `CPUState`, `ProgramTable`, and the
`is_real` boolean. Memory-bus consistency is deferred to OfflineMemory. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var StoreDoubleCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩, _addr_value, _addr_top_two_limb_inv,
       _store_prev_value, _store_memory_prev_high, _store_memory_prev_low,
       _store_memory_flag, _store_memory_diff_low, _store_memory_diff_high,
       is_real, next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, 39, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_carry_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  -- Iter-8 sub-task E (partial): register-side OperandAccess only.
  -- Store RAM access deferred (see `load-store-ram-access-deferred`).
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
instance elaborated : ElaboratedCircuit (ZMod p) StoreDoubleCols unit where
  name := "SP1Clean.StoreDouble"
  main := main
  localLength _ := 0

def Assumptions (_ : StoreDoubleCols (ZMod p)) : Prop := True

def FormalSpec (cols : StoreDoubleCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := 39, op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.state.pc[0], cols.state.pc[1], cols.state.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.is_real * (cols.is_real - 1) = 0 ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 4, cols.adapter.op_a_memory.access_timestamp.prev_low, cols.adapter.op_a_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_a_memory.prev_value⟩ ∧
  SP1Clean.OperandAccess.Assertion.Spec
    ⟨clk_low, 3, cols.adapter.op_b_memory.access_timestamp.prev_low, cols.adapter.op_b_memory.access_timestamp.diff_low_limb,
     cols.adapter.op_b_memory.prev_value⟩

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_isreal, h_oa_a, h_oa_b⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · simp only [Vector.getElem_map]
    exact h_addr_sub trivial
  · linear_combination h_isreal
  · exact h_oa_a trivial
  · exact h_oa_b trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_addr, h_isreal, h_oa_a, h_oa_b⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr
    exact h_addr
  · linear_combination h_isreal
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩

end Assertion

def assertion : FormalAssertion (ZMod p) StoreDoubleCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.StoreDouble
