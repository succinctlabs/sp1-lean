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
import SP1Operations.Reader.ITypeReader.ITypeReader
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Chips.Load.LoadDouble.Common
import SP1Clean.AddrAddOperation
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader

/-! # Chip-level `LoadDoubleChip` mirror — 64-bit load

Sibling of `LoadByteChip` for 64-bit doubleword loads (`ld`). 39
columns. No byte-selector machinery — LD loads the entire 4-limb word
at the computed address into op_a.

Opcode: `35 = LD` (Load Double).
-/

namespace SP1Clean.LoadDouble

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

structure LoadDoubleCols (T : Type) where
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
  load_prev_value : Vector T 4              -- Main[29..32] (loaded doubleword)
  load_memory_prev_high : T                 -- Main[33]
  load_memory_prev_low : T                  -- Main[34]
  load_memory_flag : T                      -- Main[35]
  load_memory_diff_low : T                  -- Main[36]
  load_memory_diff_high : T                 -- Main[37]
  is_real : T                               -- Main[38]
  next_pc_carry_value : Vector T 3
deriving ProvableStruct

def main (cols : Var LoadDoubleCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c_imm, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, load_memory_diff_low, load_memory_diff_high,
       is_real, _next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), load_memory_diff_low, 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, load_memory_diff_high, 0]
      : Vector (Expression (ZMod p)) 4)
  SP1Clean.ProgramTable.assertion
    (⟨pc, 35, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_real * (is_real - 1) === 0

def Spec (cols : LoadDoubleCols (ZMod p)) : Prop :=
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
    { pc := cols.pc, opcode := 35,
      op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := cols.op_c_imm,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0

/-- The load-side memory access (read of the 4-limb doubleword at
addr_value; the chip itself doesn't modify RAM, write_value = prev_value
at aggregation time). -/
def loadMemoryAccess (cols : LoadDoubleCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := cols.addr_value,
    prev_value := cols.load_prev_value,
    prev_low := cols.load_memory_prev_low,
    diff_low_limb := cols.load_memory_diff_low }

/-- Project a raw SP1 row into the structured `LoadDoubleCols` view. -/
@[reducible] def fromMain (Main : Vector (ZMod p) 39) : LoadDoubleCols (ZMod p) :=
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
   Main[38], #v[0, 0, 0]⟩

/-- Iff RHS for the Load Double (LD) variant, mirroring
`_root_.Load.LoadDouble.allHold_constraints_iff_of_is_ld`. LD has only
one opcode (no LDU — RV64IM has no unsigned doubleword load), so a
single iff_sp1 lemma per chip. The full 4-limb loaded word goes
directly into op_a_write_value (no sub-word selection or sign
extension). -/
def SpecForIff_of_is_ld (cols : LoadDoubleCols (ZMod p)) : Prop :=
  SP1Clean.AddrAddOp.Spec
      cols.op_b_memory_prev_value cols.op_c_imm
      { value := cols.addr_value } ∧
  cols.addr_top_two_limb_inv * (cols.addr_value[1] + cols.addr_value[2]) = 1 ∧
  (cols.addr_value[0] * (8 : ZMod p)⁻¹).val < 2 ^ ZMod.val (13 : ZMod p) ∧
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ITypeReader.itypeReaderSpec
      (cols.clk_0_16 + cols.clk_16_24 * 65536) 35 cols.pc
      cols.load_prev_value
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
  (cols.load_memory_flag = 0 ∨ cols.load_memory_flag = 1) ∧
  (cols.load_memory_flag = 0 ∨ cols.clk_high = cols.load_memory_prev_high) ∧
  cols.load_memory_flag * (cols.clk_0_16 + cols.clk_16_24 * 65536 + 1) +
      (1 - cols.load_memory_flag) * cols.clk_high -
      (cols.load_memory_flag * cols.load_memory_prev_low +
        (1 - cols.load_memory_flag) * cols.load_memory_prev_high) - 1 =
    cols.load_memory_diff_low + cols.load_memory_diff_high * 65536 ∧
  cols.load_memory_diff_low.val < 65536 ∧
  ((0 : ZMod p) < 256 ∧ cols.load_memory_diff_high < (256 : ZMod p) ∧
    (0 : ZMod p) < 256) ∧
  Word.isU64 cols.load_prev_value ∧
  cols.op_a_0 = 0

set_option maxHeartbeats 800000 in
-- Higher heartbeats: the iff destructure unfolds the full constraint list
-- via the SP1-side `_of_is_ld` helper.
/-- The chip-level bridge for the Load Double variant. -/
theorem iff_sp1_of_is_ld (Main : Vector (ZMod p) 39) (h_is_ld : Main[38] = 1) :
    (_root_.Load.LoadDouble.constraints Main).allHold ↔
      SpecForIff_of_is_ld (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  change List.Forall SP1Constraint.toProp (_root_.Load.LoadDouble.constraints Main) ↔ _
  rw [_root_.Load.LoadDouble.allHold_constraints_iff_of_is_ld Main h_is_ld]
  simp only [show ∀ (a : SP1ConstraintList (ZMod p)),
      List.Forall SP1Constraint.toProp a = a.allHold from fun _ => rfl,
    SP1Clean.CPUState.cpuStateSpec_iff_sp1,
    SP1Clean.ITypeReader.itypeReaderSpec_iff_sp1,
    SP1Clean.AddrAddOp.iff_sp1]
  simp [SpecForIff_of_is_ld, fromMain]

/-! ## Full `FormalAssertion` promotion (Path-2)

Drops the two bare byte lookups on `load_memory_diff_low` /
`load_memory_diff_high`; covers `CPUState`, `ProgramTable`, and the
`is_real` boolean. Memory-bus consistency is deferred to OfflineMemory. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var LoadDoubleCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b, _op_b_memory_prev_value, _op_b_memory_prev_low,
       _op_b_memory_diff_low, op_c_imm, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, _load_memory_diff_low, _load_memory_diff_high,
       is_real, next_pc_carry_value⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, 35, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨#v[pc[0], pc[1], pc[2], (0 : Expression (ZMod p))],
       #v[(4 : Expression (ZMod p)), 0, 0, 0],
       next_pc_carry_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  is_real * (is_real - 1) === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LoadDoubleCols unit where
  name := "SP1Clean.LoadDouble"
  main := main
  localLength _ := 0

def Assumptions (_ : LoadDoubleCols (ZMod p)) : Prop := True

def FormalSpec (cols : LoadDoubleCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc, opcode := 35, op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0], op_c := cols.op_c_imm,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 1 } ∧
  SP1Clean.AddrAddOp.assertion.Spec
    ⟨#v[cols.pc[0], cols.pc[1], cols.pc[2], 0],
     #v[(4 : ZMod p), 0, 0, 0],
     cols.next_pc_carry_value⟩ ∧
  cols.is_real * (cols.is_real - 1) = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_addr_sub, h_isreal⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · simp only [Vector.getElem_map]
    exact h_addr_sub trivial
  · linear_combination h_isreal

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_addr, h_isreal⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · refine ⟨trivial, ?_⟩
    simp only [Vector.getElem_map] at h_addr
    exact h_addr
  · linear_combination h_isreal

end Assertion

def assertion : FormalAssertion (ZMod p) LoadDoubleCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.LoadDouble
