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
import SP1Operations.Operation.U16MSBOperation.U16MSBOperation
import SP1Operations.Operation.AddrAddOperation.AddrAddOperation
import SP1Chips.Load.LoadHalf.Common
import SP1Clean.Operations.AddrAddOperation
import SP1Clean.Operations.AddressShape
import SP1Clean.Operations.LoadMemoryAccessGated
import SP1Clean.Operations.LoadHalfSelector
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs

/-! # Chip-level `LoadHalfChip` mirror — 16-bit signed/unsigned load

Sibling of `LoadByteChip` for half-word (16-bit) loads (`lh` signed /
`lhu` unsigned). 44 columns: two opcode selectors plus the sub-word
selector machinery for half-word position within the 8-byte aligned
double.

Opcodes: `30 = LH`, `33 = LHU`.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.LoadHalf

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def main (cols : Var LoadHalfCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c_imm⟩, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, load_memory_diff_low, load_memory_diff_high,
       _offset_bit_1, _offset_bit_0, _op_a_write_value_lo,
       _signed_extension_msb, is_lh, is_lhu, _adapter_cols⟩ := cols
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

def TraceSpec (cols : LoadHalfCols (ZMod p)) : Prop :=
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
    { pc := cols.state.pc, opcode := cols.is_lh * 30 + cols.is_lhu * 33,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_lh * (cols.is_lh - 1) = 0 ∧
  cols.is_lhu * (cols.is_lhu - 1) = 0 ∧
  (cols.is_lh + cols.is_lhu) * (cols.is_lh + cols.is_lhu - 1) = 0 ∧
  cols.adapter_cols.is_trusted = 1

def loadMemoryAccess (cols : LoadHalfCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := cols.addr_value,
    prev_value := cols.load_prev_value,
    prev_low := cols.load_memory_prev_low,
    diff_low_limb := cols.load_memory_diff_low }

/-- Iff RHS for the signed Load Half (LH) variant, mirroring
`_root_.Load.LoadHalf.allHold_constraints_iff_of_is_lh`. -/
def SpecForIff_of_is_lh (cols : LoadHalfCols (ZMod p)) : Prop :=
  SP1Clean.AddrAddOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
      { value := cols.addr_value } ∧
  (cols.offset_bit_1 = 0 ∨ cols.offset_bit_1 = 1) ∧
  (cols.offset_bit_0 = 0 ∨ cols.offset_bit_0 = 1) ∧
  cols.addr_top_two_limb_inv * (cols.addr_value[1] + cols.addr_value[2]) = 1 ∧
  ((cols.addr_value[0] - 4 * cols.offset_bit_0 - 2 * cols.offset_bit_1)
      * (8 : ZMod p)⁻¹).val < 2 ^ ZMod.val (13 : ZMod p) ∧
  (U16MSBOperation.constraints cols.op_a_write_value_lo
      { msb := cols.signed_extension_msb } 1).allHold ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ITypeReader.itypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 30 cols.state.pc
      #v[cols.op_a_write_value_lo,
         65535 * cols.signed_extension_msb,
         65535 * cols.signed_extension_msb,
         65535 * cols.signed_extension_msb]
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
  (cols.load_memory_flag = 0 ∨ cols.load_memory_flag = 1) ∧
  (cols.load_memory_flag = 0 ∨ cols.state.clk_high = cols.load_memory_prev_high) ∧
  cols.load_memory_flag * (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 1) +
      (1 - cols.load_memory_flag) * cols.state.clk_high -
      (cols.load_memory_flag * cols.load_memory_prev_low +
        (1 - cols.load_memory_flag) * cols.load_memory_prev_high) - 1 =
    cols.load_memory_diff_low + cols.load_memory_diff_high * 65536 ∧
  cols.load_memory_diff_low.val < 65536 ∧
  ((0 : ZMod p) < 256 ∧ cols.load_memory_diff_high < (256 : ZMod p) ∧
    (0 : ZMod p) < 256) ∧
  Word.isU64 cols.load_prev_value ∧
  cols.is_lhu = 0 ∧ cols.adapter.op_a_0 = 0 ∧
  (cols.offset_bit_1 = 1 ∨ cols.offset_bit_0 = 1 ∨
    cols.op_a_write_value_lo = cols.load_prev_value[0]) ∧
  (cols.offset_bit_1 = 0 ∨ cols.offset_bit_0 = 1 ∨
    cols.op_a_write_value_lo = cols.load_prev_value[1]) ∧
  (cols.offset_bit_1 = 1 ∨ cols.offset_bit_0 = 0 ∨
    cols.op_a_write_value_lo = cols.load_prev_value[2]) ∧
  (cols.offset_bit_1 = 0 ∨ cols.offset_bit_0 = 0 ∨
    cols.op_a_write_value_lo = cols.load_prev_value[3])

/-- Iff RHS for the unsigned Load Half (LHU) variant. Differs from the
signed variant in the ITypeReader opcode (33 vs 30), the forced-zero
selector (`is_lh = 0` vs `is_lhu = 0`), the U16MSB constraint's is_real
arg (0 vs 1; forces msb=0 trivially), and the trailing
`signed_extension_msb = 0` clause. -/
def SpecForIff_of_is_lhu (cols : LoadHalfCols (ZMod p)) : Prop :=
  SP1Clean.AddrAddOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
      { value := cols.addr_value } ∧
  (cols.offset_bit_1 = 0 ∨ cols.offset_bit_1 = 1) ∧
  (cols.offset_bit_0 = 0 ∨ cols.offset_bit_0 = 1) ∧
  cols.addr_top_two_limb_inv * (cols.addr_value[1] + cols.addr_value[2]) = 1 ∧
  ((cols.addr_value[0] - 4 * cols.offset_bit_0 - 2 * cols.offset_bit_1)
      * (8 : ZMod p)⁻¹).val < 2 ^ ZMod.val (13 : ZMod p) ∧
  (U16MSBOperation.constraints cols.op_a_write_value_lo
      { msb := cols.signed_extension_msb } 0).allHold ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ITypeReader.itypeReaderSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 33 cols.state.pc
      #v[cols.op_a_write_value_lo,
         65535 * cols.signed_extension_msb,
         65535 * cols.signed_extension_msb,
         65535 * cols.signed_extension_msb]
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
  (cols.load_memory_flag = 0 ∨ cols.load_memory_flag = 1) ∧
  (cols.load_memory_flag = 0 ∨ cols.state.clk_high = cols.load_memory_prev_high) ∧
  cols.load_memory_flag * (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536 + 1) +
      (1 - cols.load_memory_flag) * cols.state.clk_high -
      (cols.load_memory_flag * cols.load_memory_prev_low +
        (1 - cols.load_memory_flag) * cols.load_memory_prev_high) - 1 =
    cols.load_memory_diff_low + cols.load_memory_diff_high * 65536 ∧
  cols.load_memory_diff_low.val < 65536 ∧
  ((0 : ZMod p) < 256 ∧ cols.load_memory_diff_high < (256 : ZMod p) ∧
    (0 : ZMod p) < 256) ∧
  Word.isU64 cols.load_prev_value ∧
  cols.is_lh = 0 ∧ cols.adapter.op_a_0 = 0 ∧
  (cols.offset_bit_1 = 1 ∨ cols.offset_bit_0 = 1 ∨
    cols.op_a_write_value_lo = cols.load_prev_value[0]) ∧
  (cols.offset_bit_1 = 0 ∨ cols.offset_bit_0 = 1 ∨
    cols.op_a_write_value_lo = cols.load_prev_value[1]) ∧
  (cols.offset_bit_1 = 1 ∨ cols.offset_bit_0 = 0 ∨
    cols.op_a_write_value_lo = cols.load_prev_value[2]) ∧
  (cols.offset_bit_1 = 0 ∨ cols.offset_bit_0 = 0 ∨
    cols.op_a_write_value_lo = cols.load_prev_value[3]) ∧
  cols.signed_extension_msb = 0

set_option maxHeartbeats 800000 in
-- Higher heartbeats: the iff destructure unfolds the full constraint list
-- via the SP1-side `_of_is_lh` helper.
/-- The chip-level bridge for the signed Load Half variant. -/
theorem iff_sp1_of_is_lh (Main : Vector (ZMod p) 44) (h_is_lh : Main[42] = 1) :
    (_root_.Load.LoadHalf.constraints Main).allHold ↔
      SpecForIff_of_is_lh (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  change List.Forall SP1Constraint.toProp (_root_.Load.LoadHalf.constraints Main) ↔ _
  rw [_root_.Load.LoadHalf.allHold_constraints_iff_of_is_lh Main h_is_lh]
  simp only [show ∀ (a : SP1ConstraintList (ZMod p)),
      List.Forall SP1Constraint.toProp a = a.allHold from fun _ => rfl,
    SP1Clean.CPUState.cpuStateSpec_iff_sp1,
    SP1Clean.ITypeReader.itypeReaderSpec_iff_sp1,
    SP1Clean.AddrAddOp.iff_sp1]
  simp [SpecForIff_of_is_lh, fromMain]

set_option maxHeartbeats 800000 in
-- Higher heartbeats: same reason as `iff_sp1_of_is_lh`.
/-- The chip-level bridge for the unsigned Load Half variant. -/
theorem iff_sp1_of_is_lhu (Main : Vector (ZMod p) 44) (h_is_lhu : Main[43] = 1) :
    (_root_.Load.LoadHalf.constraints Main).allHold ↔
      SpecForIff_of_is_lhu (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  change List.Forall SP1Constraint.toProp (_root_.Load.LoadHalf.constraints Main) ↔ _
  rw [_root_.Load.LoadHalf.allHold_constraints_iff_of_is_lhu Main h_is_lhu]
  simp only [show ∀ (a : SP1ConstraintList (ZMod p)),
      List.Forall SP1Constraint.toProp a = a.allHold from fun _ => rfl,
    SP1Clean.CPUState.cpuStateSpec_iff_sp1,
    SP1Clean.ITypeReader.itypeReaderSpec_iff_sp1,
    SP1Clean.AddrAddOp.iff_sp1]
  simp [SpecForIff_of_is_lhu, fromMain]

/-! ## Full `FormalAssertion` promotion (Path-2)

Drops the two bare byte lookups on `load_memory_diff_low` /
`load_memory_diff_high`; covers `CPUState`, `ProgramTable`, and the
three boolean gates (`is_lh`, `is_lhu`, and the aggregate sum).
Memory-bus consistency is deferred to OfflineMemory. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var LoadHalfCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩, _addr_value, _addr_top_two_limb_inv,
       _load_prev_value, _load_memory_prev_high, _load_memory_prev_low,
       _load_memory_flag, _load_memory_diff_low, _load_memory_diff_high,
       _offset_bit_1, _offset_bit_0, _op_a_write_value_lo,
       _signed_extension_msb, is_lh, is_lhu, _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, is_lh * 30 + is_lhu * 33,
      op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_lh * (is_lh - 1) === 0
  is_lhu * (is_lhu - 1) === 0
  (is_lh + is_lhu) * (is_lh + is_lhu - 1) === 0
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
-- Higher heartbeats: 29 input fields + 4 subcircuit calls + 2 OperandAccess
-- calls pushes localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LoadHalfCols unit where
  name := "SP1Clean.LoadHalf"
  main := main
  localLength _ := 0

def Assumptions (_ : LoadHalfCols (ZMod p)) : Prop := True

def FormalSpec (cols : LoadHalfCols (ZMod p)) : Prop :=
  let clk_low := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc, opcode := cols.is_lh * 30 + cols.is_lhu * 33,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0], op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_lh * (cols.is_lh - 1) = 0 ∧
  cols.is_lhu * (cols.is_lhu - 1) = 0 ∧
  (cols.is_lh + cols.is_lhu) * (cols.is_lh + cols.is_lhu - 1) = 0 ∧
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
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26⟩ :=
    h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_lh, h_lhu, h_sum,
          h_oa_a, h_oa_b⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_lh
  · linear_combination h_lhu
  · linear_combination h_sum
  · exact h_oa_a trivial
  · exact h_oa_b trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26⟩ :=
    h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_lh, h_lhu, h_sum, h_oa_a, h_oa_b⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_lh
  · linear_combination h_lhu
  · linear_combination h_sum
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩

end Assertion

def assertion : FormalAssertion (ZMod p) LoadHalfCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-! ## `AssertionGated` — full sub-circuit composition with gated multiplicities

Sister of `Assertion`. Composes `CPUState`, `AddrAddOp`, `AddressShape`,
`ITypeReader`, `LoadMemoryAccessGated`, and `LoadHalfSelector` as
`FormalAssertion` sub-circuits. Multiplicity for gated parts is
`is_real = is_lh + is_lhu`. -/

namespace AssertionGated

open Circuit

@[reducible]
def main (cols : Var LoadHalfCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩,
       addr_value, addr_top_two_limb_inv,
       load_prev_value, load_memory_prev_high, load_memory_prev_low,
       load_memory_flag, load_memory_diff_low, load_memory_diff_high,
       offset_bit_1, offset_bit_0, op_a_write_value_lo,
       signed_extension_msb, is_lh, is_lhu, _adapter_cols⟩ := cols
  let is_real : Expression (ZMod p) := is_lh + is_lhu
  let clk_low : Expression (ZMod p) := clk_0_16 + clk_16_24 * 65536
  let opcode : Expression (ZMod p) := is_lh * 30 + is_lhu * 33
  -- LoadHalf assembles op_a_write_value as: low 16-bit limb = op_a_write_value_lo,
  -- and the upper limbs sign-extended via signed_extension_msb.
  let op_a_write_value : Vector (Expression (ZMod p)) 4 :=
    #v[op_a_write_value_lo,
       65535 * signed_extension_msb,
       65535 * signed_extension_msb,
       65535 * signed_extension_msb]
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨op_b_memory.prev_value, op_c_imm, addr_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  SP1Clean.AddressShape.assertion
    (⟨addr_value, addr_top_two_limb_inv,
       0, offset_bit_1, offset_bit_0⟩ :
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
  SP1Clean.LoadHalfSelector.assertion
    (⟨load_prev_value, 0, offset_bit_1, offset_bit_0,
       op_a_write_value_lo, signed_extension_msb, is_lhu⟩ :
      Var SP1Clean.LoadHalfSelector.Inputs (ZMod p))
  is_lh * (is_lh - 1) === 0
  is_lhu * (is_lhu - 1) === 0
  (is_lh + is_lhu) * (is_lh + is_lhu - 1) === 0
  op_a_0 === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) LoadHalfCols unit where
  name := "SP1Clean.LoadHalf.Gated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : LoadHalfCols (ZMod p)) : Prop := True

def FormalSpec (cols : LoadHalfCols (ZMod p)) : Prop :=
  let is_real : ZMod p := cols.is_lh + cols.is_lhu
  let clk_low : ZMod p := cols.state.clk_0_16 + cols.state.clk_16_24 * 65536
  let opcode : ZMod p := cols.is_lh * 30 + cols.is_lhu * 33
  let op_a_write_value : Vector (ZMod p) 4 :=
    #v[cols.op_a_write_value_lo,
       65535 * cols.signed_extension_msb,
       65535 * cols.signed_extension_msb,
       65535 * cols.signed_extension_msb]
  SP1Clean.CPUState.Assertion.Spec ⟨cols.state.clk_0_16, cols.state.clk_16_24⟩ ∧
  SP1Clean.AddrAddOp.Assertion.Spec
    ⟨cols.adapter.op_b_memory.prev_value, cols.adapter.op_c_imm, cols.addr_value⟩ ∧
  SP1Clean.AddressShape.Assertion.Spec
    ⟨cols.addr_value, cols.addr_top_two_limb_inv,
     0, cols.offset_bit_1, cols.offset_bit_0⟩ ∧
  SP1Clean.ITypeReader.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, opcode, cols.state.pc, op_a_write_value, cols.adapter⟩ ∧
  SP1Clean.LoadMemoryAccessGated.Assertion.Spec
    ⟨cols.state.clk_high, clk_low, cols.addr_value, cols.load_prev_value,
     cols.load_memory_prev_high, cols.load_memory_prev_low,
     cols.load_memory_diff_low, cols.load_memory_diff_high,
     cols.load_memory_flag, is_real⟩ ∧
  SP1Clean.LoadHalfSelector.Assertion.Spec
    ⟨cols.load_prev_value, 0, cols.offset_bit_1, cols.offset_bit_0,
     cols.op_a_write_value_lo, cols.signed_extension_msb, cols.is_lhu⟩ ∧
  cols.is_lh * (cols.is_lh - 1) = 0 ∧
  cols.is_lhu * (cols.is_lhu - 1) = 0 ∧
  (cols.is_lh + cols.is_lhu) * (cols.is_lh + cols.is_lhu - 1) = 0 ∧
  cols.adapter.op_a_0 = 0

set_option maxHeartbeats 800000 in
-- Six sub-circuits + 4 inline gates; LoadMemoryAccessGated and LoadHalfSelector
-- arms are placeholders (Spec @[reducible]). Mirrors LoadByteChip.AssertionGated.
theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_addr_sub, h_addr_shape_sub, h_itr_sub,
          _h_lmag_sub, _h_lhs_sub,
          h_is_lh, h_is_lhu, h_sum, h_op_a_0⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_addr_sub trivial
  · exact h_addr_shape_sub trivial
  · exact h_itr_sub trivial
  · exact Or.inr trivial
  · trivial
  · linear_combination h_is_lh
  · linear_combination h_is_lhu
  · linear_combination h_sum
  · exact h_op_a_0

set_option maxHeartbeats 800000 in
-- Mirrors soundness destructure; circuit_proof_start unfolds 6 sub-circuits + 4 gates.
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_addr, h_addr_shape, h_itr, _h_lmag, _h_lhs,
          h_is_lh, h_is_lhu, h_sum, h_op_a_0⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_addr⟩
  · exact ⟨trivial, h_addr_shape⟩
  · exact ⟨trivial, h_itr⟩
  · exact ⟨trivial, Or.inr trivial⟩
  · exact ⟨trivial, trivial⟩
  · linear_combination h_is_lh
  · linear_combination h_is_lhu
  · linear_combination h_sum
  · exact h_op_a_0

end AssertionGated

def assertionGated : FormalAssertion (ZMod p) LoadHalfCols :=
  { AssertionGated.elaborated with
    Assumptions := AssertionGated.Assumptions,
    Spec := AssertionGated.FormalSpec,
    soundness := AssertionGated.soundness,
    completeness := AssertionGated.completeness }

end SP1Clean.LoadHalf
