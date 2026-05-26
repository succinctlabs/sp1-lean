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
import SP1Chips.Store.StoreByte.Common
import SP1Clean.Operations.AddrAddOperation
import SP1Clean.Operations.AddressShape
import SP1Clean.Operations.StoreMemoryAccessGated
import SP1Clean.Operations.StoreByteAssembler
import SP1Clean.ByteOpcodeTable
import SP1Clean.ProgramTable
import SP1Clean.MemoryAccess
import SP1Clean.Reader.CPUState
import SP1Clean.Reader.ITypeReader
import SP1Clean.Reader.ITypeReaderImmutable
import SP1Clean.Reader.OperandAccess
import SP1Clean.TrustMode
import SP1Clean.Chips.Structs
import SP1Clean.Chips.Spec

/-! # Chip-level `StoreByteChip` mirror — first chip with a memory write

The Store Byte chip is the canonical example of a chip with a memory
**write**: in addition to the two register accesses every immutable
I-type reader emits (`op_a` data source, `op_b` base address register),
`StoreByteChip` reads-then-writes the 4-limb word at the computed store
address `op_b + sign_ext(imm_c)`. The memory bus carries both the prior
word (`.send (.memory ... prev_value)`) and the new word
(`.receive (.memory ... new_value)`) at the same address but with
different timestamps, which is the "read-then-write" pattern OfflineMemory
relies on for write-side consistency.

This file is the **focused pilot mirror** following the `LoadByteChip`
template: it captures the program-bus interaction and the store-side
`MemoryAccess` record explicitly, in a form suitable for the trace-level
`OfflineMemory` aggregation. The chip's full `traceSpec_iff_allHold` to
`_root_.Store.StoreByte.constraints` is deferred; the goal here is to
demonstrate that the `MemoryAccess` + `ProgramTable` design generalizes
from memory-read chips (LoadByte) to memory-write chips, and to seed the
OfflineMemory consistency theorem with a real write access.

Opcode: `36 = SB` (Store Byte). Sibling chips `StoreHalf`, `StoreWord`,
`StoreDouble` follow the same shape with width and byte-selector
selectors.
-/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.StoreByte

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Clean-side circuit. Mirrors the SP1 source's emissions for the SB
case: byte lookups for the various range/U8 checks plus the program-bus
interaction. The full memory-access machinery (read of `op_a` source,
read of `op_b` base, read-then-write at the store address) is exposed
via the `Spec` predicate. Clean has no native send/receive bus, so
per-row consistency is propositional; cross-row consistency follows
from OfflineMemory aggregation at trace level.

Opcode is `36 = SB`. Immediate-mode flag is `imm_c = 1` (I-type
discipline); `op_c` carries 4 immediate limbs from `op_c_imm`. -/
def main (cols : Var StoreByteCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, _op_a_memory, op_a_0, op_b, _op_b_memory, op_c_imm⟩, _addr_value, _addr_top_two_limb_inv,
       _store_prev_value, _store_memory_prev_high, _store_memory_prev_low,
       _store_memory_flag, store_memory_diff_low, store_memory_diff_high,
       _byte_selector_top, _byte_selector_mid, _byte_selector_lo,
       _mem_limb, mem_limb_low_byte, register_low_byte,
       _increment, _store_value, is_real,
       _adapter_cols⟩ := cols
  -- CPUState: clk_0_16 progression and clk_16_24 byte bound.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), (clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), clk_16_24, 8, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Store-memory timestamp bounds: one Range(16) on the low diff, one
  -- U8Range on the high diff. Mirrors `.send (.byte 6 Main[36] 16 0)`
  -- and `.send (.byte 3 0 Main[37] 0)` from the SP1 source.
  lookup ByteOpcodeTable
    (#v[(6 : Expression (ZMod p)), store_memory_diff_low, 16, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, store_memory_diff_high, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Byte-byte U8 range lookups for the store byte and its complement
  -- (the SP1 source emits the same two `.send (.byte 3 0 _ _)` calls).
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, register_low_byte, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, mem_limb_low_byte, 0]
      : Vector (Expression (ZMod p)) 4)
  -- Program-bus interaction. Opcode is 36 = SB; I-type discipline:
  -- op_b is single-limb register index, op_c_imm carries 4 immediate
  -- limbs, imm_c = 1.
  SP1Clean.ProgramTable.assertion
    (⟨pc, 36,
      op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  -- Real-flag boolean gate.
  is_real * (is_real - 1) === 0

/-- The Clean-flavored Spec for `StoreByteChip` under `is_real = 1`.
Composes the existing per-fragment specs (`cpuStateSpec`) with three
`memoryAccessSpec` records that drive the trace-level OfflineMemory
bridge:
- one register read for `op_a` (the source data — read, not written)
- one register read for `op_b` (the base address)
- the store-side access at `addr_value` (read-then-write at the same
  RAM address with two distinct timestamps).

The address-arithmetic side (the `AddressOperation` + `AddrAddOperation`
fragments asserting `addr_value = op_b + sign_ext(imm_c)` and the
read-write byte-selector logic) is folded into a future iteration —
keeping `Spec` light here lets the OfflineMemory bridge consume the
chip without depending on those proofs. -/
def TraceSpec (cols : StoreByteCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  -- Source-register read for op_a (no write — stores don't write the
  -- destination register).
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_a
      { prev_value := cols.adapter.op_a_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb } }) ∧
  -- Base-register read for op_b.
  SP1Clean.memoryAccessSpec
    (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.adapter.op_b
      { prev_value := cols.adapter.op_b_memory.prev_value,
        access_timestamp :=
          { prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
            diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb } }) ∧
  -- Store-side memory access. Address is the 3-limb `addr_value`
  -- computed by the AddressOperation; this is generally NOT a register
  -- address (`addr_value[0].val ≥ 32`), so the RAM branch of
  -- `SP1Constraint.toStateProp` fires. `prev_value` is the prior
  -- 4-limb word at `addr_value`; `prev_low` / `diff_low_limb` are the
  -- timestamp bookkeeping for the prior access at this address.
  SP1Clean.memoryAccessSpec
    (cols.store_memory_prev_high * (2 ^ 24) + cols.store_memory_prev_low) 0
    { addr := cols.addr_value,
      prev_value := cols.store_prev_value,
      prev_low := cols.store_memory_prev_low,
      diff_low_limb := cols.store_memory_diff_low } ∧
  -- Program-bus consequence (opcode = 36 = SB).
  SP1Clean.ProgramTable.Spec
    { pc := cols.state.pc,
      opcode := 36,
      op_a := cols.adapter.op_a,
      op_b := #v[cols.adapter.op_b, 0, 0, 0],
      op_c := cols.adapter.op_c_imm,
      op_a_0 := cols.adapter.op_a_0, imm_b := 0, imm_c := 1 } ∧
  -- Real-flag boolean gate.
  cols.is_real * (cols.is_real - 1) = 0 ∧
  cols.adapter_cols.is_trusted = 1

/-- The store-side memory access as a `MemoryAccess` record, exposed for
trace-level OfflineMemory aggregation. This is the access that hits the
RAM branch (not registers): `addr_value` is the store destination
computed by the AddressOperation sub-fragment.

For trace-level aggregation, the corresponding `write_value` is the
4-limb word `[Main[45], Main[46], Main[47], Main[48]]` in the SP1
constraints (here exposed as `cols.store_value` plus
`cols.store_value_3`). For pure register reads of `op_a` / `op_b`,
the aggregator uses `write_value = prev_value` per the established
read-only convention. -/
def storeMemoryAccess (cols : StoreByteCols (ZMod p)) : SP1Clean.MemoryAccess (ZMod p) :=
  { addr := cols.addr_value,
    prev_value := cols.store_prev_value,
    prev_low := cols.store_memory_prev_low,
    diff_low_limb := cols.store_memory_diff_low }

/-- The 4-limb `write_value` for the store-side access. This is the new
word at `addr_value` after the store: limb i = prev_value[i] OR the
selected byte, depending on the byte selector. The SP1 constraint
compiler emits one assertZero per limb to bind each to a function of
`store_prev_value`, `increment`, and the byte selectors. -/
def storeWriteValue (cols : StoreByteCols (ZMod p)) : Word (ZMod p) :=
  cols.store_value


/-- Iff RHS for the Store Byte (SB) variant, mirroring
`_root_.Store.StoreByte.allHold_constraints_iff_of_is_real`. SB writes
a single byte at one of 8 positions within the 8-byte aligned
doubleword (selected by three byte selectors). The 4-limb
`store_value` is the byte-selected merge of the new byte (derived
from `op_a_memory.prev_value[0]` via the `register_low_byte`/`increment`
chain) with the existing `store_prev_value`. -/
def SpecForIff_of_is_real (cols : StoreByteCols (ZMod p)) : Prop :=
  SP1Clean.AddrAddOp.Spec
      cols.adapter.op_b_memory.prev_value cols.adapter.op_c_imm
      { value := cols.addr_value } ∧
  (cols.byte_selector_top = 0 ∨ cols.byte_selector_top = 1) ∧
  (cols.byte_selector_mid = 0 ∨ cols.byte_selector_mid = 1) ∧
  (cols.byte_selector_lo = 0 ∨ cols.byte_selector_lo = 1) ∧
  cols.addr_top_two_limb_inv * (cols.addr_value[1] + cols.addr_value[2]) = 1 ∧
  ((cols.addr_value[0] - 4 * cols.byte_selector_lo - 2 * cols.byte_selector_mid
        - cols.byte_selector_top) * (8 : ZMod p)⁻¹).val
    < 2 ^ ZMod.val (13 : ZMod p) ∧
  SP1Clean.CPUState.cpuStateSpec cols.state.clk_0_16 cols.state.clk_16_24 ∧
  SP1Clean.ITypeReaderImmutable.itypeReaderImmutableSpec
      (cols.state.clk_0_16 + cols.state.clk_16_24 * 65536) 36 cols.state.pc
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
  Word.isU64 cols.store_prev_value ∧
  (cols.byte_selector_mid = 1 ∨ cols.byte_selector_lo = 1 ∨
    cols.mem_limb = cols.store_prev_value[0]) ∧
  (cols.byte_selector_mid = 0 ∨ cols.byte_selector_lo = 1 ∨
    cols.mem_limb = cols.store_prev_value[1]) ∧
  (cols.byte_selector_mid = 1 ∨ cols.byte_selector_lo = 0 ∨
    cols.mem_limb = cols.store_prev_value[2]) ∧
  (cols.byte_selector_mid = 0 ∨ cols.byte_selector_lo = 0 ∨
    cols.mem_limb = cols.store_prev_value[3]) ∧
  ((0 : ZMod p) < 256 ∧ cols.register_low_byte < (256 : ZMod p) ∧
    (cols.adapter.op_a_memory.prev_value[0] - cols.register_low_byte) * (256 : ZMod p)⁻¹
      < (256 : ZMod p)) ∧
  ((0 : ZMod p) < 256 ∧ cols.mem_limb_low_byte < (256 : ZMod p) ∧
    (cols.mem_limb - cols.mem_limb_low_byte) * (256 : ZMod p)⁻¹
      < (256 : ZMod p)) ∧
  cols.increment =
    (cols.register_low_byte - cols.mem_limb_low_byte) * (1 - cols.byte_selector_top) +
    256 *
      (cols.register_low_byte -
        (cols.mem_limb - cols.mem_limb_low_byte) * (256 : ZMod p)⁻¹) *
      cols.byte_selector_top ∧
  cols.store_value[0] =
    cols.increment * (1 - cols.byte_selector_mid) *
      (1 - cols.byte_selector_lo) + cols.store_prev_value[0] ∧
  cols.store_value[1] =
    cols.increment * cols.byte_selector_mid *
      (1 - cols.byte_selector_lo) + cols.store_prev_value[1] ∧
  cols.store_value[2] =
    cols.increment * (1 - cols.byte_selector_mid) *
      cols.byte_selector_lo + cols.store_prev_value[2] ∧
  cols.store_value[3] =
    cols.increment * cols.byte_selector_mid * cols.byte_selector_lo +
    cols.store_prev_value[3]

set_option maxHeartbeats 800000 in
-- Higher heartbeats: the iff destructure unfolds the full constraint list
-- via the SP1-side `_of_is_real` helper.
/-- The chip-level bridge for the Store Byte variant. -/
theorem iff_sp1_of_is_real (Main : Vector (ZMod p) 50) (h_is_real : Main[49] = 1) :
    (_root_.Store.StoreByte.constraints Main).allHold ↔
      SpecForIff_of_is_real (fromMain Main) := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  change List.Forall SP1Constraint.toProp (_root_.Store.StoreByte.constraints Main) ↔ _
  rw [_root_.Store.StoreByte.allHold_constraints_iff_of_is_real Main h_is_real]
  simp only [show ∀ (a : SP1ConstraintList (ZMod p)),
      List.Forall SP1Constraint.toProp a = a.allHold from fun _ => rfl,
    SP1Clean.CPUState.cpuStateSpec_iff_sp1,
    SP1Clean.ITypeReaderImmutable.itypeReaderImmutableSpec_iff_sp1,
    SP1Clean.AddrAddOp.iff_sp1]
  simp [SpecForIff_of_is_real, fromMain]

/-! ## Full `FormalAssertion` promotion (Path-2)

Drops the bare byte lookups (CPUState bytes done inline, store memory
diff bytes, register_low_byte U8 range, mem_limb_low_byte U8 range); covers
`CPUState`, `ProgramTable`, and the `is_real` boolean. Memory-bus
consistency is deferred to OfflineMemory. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var StoreByteCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨_clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩, _addr_value, _addr_top_two_limb_inv,
       _store_prev_value, _store_memory_prev_high, _store_memory_prev_low,
       _store_memory_flag, _store_memory_diff_low, _store_memory_diff_high,
       _byte_selector_top, _byte_selector_mid, _byte_selector_lo,
       _mem_limb, _mem_limb_low_byte, _register_low_byte,
       _increment, _store_value, is_real,
       _adapter_cols⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, 36, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
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

set_option maxHeartbeats 800000 in
-- Higher heartbeats: 32 input fields + 4 subcircuit calls + 2 OperandAccess
-- calls pushes localLength_eq synthesis past the default 200k cap.
@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) StoreByteCols unit where
  name := "SP1Clean.StoreByte"
  main := main
  localLength _ := 0

def Assumptions (_ : StoreByteCols (ZMod p)) : Prop := True

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_prog_sub, h_isreal, h_oa_a, h_oa_b⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · binary_iff h_isreal
  · exact h_oa_a trivial
  · exact h_oa_b trivial

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_prog, h_isreal, h_oa_a, h_oa_b⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · binary_iff h_isreal
  · exact ⟨trivial, h_oa_a⟩
  · exact ⟨trivial, h_oa_b⟩

end Assertion

def assertion : FormalAssertion (ZMod p) StoreByteCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

/-! ## `AssertionGated` — full sub-circuit composition with gated multiplicities

StoreByte composes: CPUState, AddrAddOp, AddressShape, ITypeReaderImmutable
(op_a is read for the byte to store), StoreMemoryAccessGated, and
StoreByteAssembler. Multiplicity is `is_real`. -/

namespace AssertionGated

open Circuit

@[reducible]
def main (cols : Var StoreByteCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨⟨clk_high, clk_16_24, clk_0_16, pc⟩,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩,
       addr_value, addr_top_two_limb_inv,
       store_prev_value, store_memory_prev_high, store_memory_prev_low,
       store_memory_flag, store_memory_diff_low, store_memory_diff_high,
       byte_selector_top, byte_selector_mid, byte_selector_lo,
       mem_limb, mem_limb_low_byte, register_low_byte, _increment,
       store_value, is_real, _adapter_cols⟩ := cols
  let clk_low : Expression (ZMod p) := clk_0_16 + clk_16_24 * 65536
  let opcode : Expression (ZMod p) := is_real * 36  -- SB
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.AddrAddOp.assertion
    (⟨op_b_memory.prev_value, op_c_imm, addr_value⟩ :
      Var SP1Clean.AddrAddOp.Inputs (ZMod p))
  SP1Clean.AddressShape.assertion
    (⟨addr_value, addr_top_two_limb_inv,
       byte_selector_top, byte_selector_mid, byte_selector_lo⟩ :
      Var SP1Clean.AddressShape.Inputs (ZMod p))
  SP1Clean.ITypeReaderImmutable.assertion
    (⟨clk_high, clk_low, opcode, pc,
       ⟨op_a, op_a_memory, op_a_0, op_b, op_b_memory, op_c_imm⟩⟩ :
      Var SP1Clean.ITypeReaderImmutable.Inputs (ZMod p))
  SP1Clean.StoreMemoryAccessGated.assertion
    (⟨clk_high, clk_low, addr_value, store_prev_value, store_value,
       store_memory_prev_high, store_memory_prev_low,
       store_memory_diff_low, store_memory_diff_high,
       store_memory_flag, is_real⟩ :
      Var SP1Clean.StoreMemoryAccessGated.Inputs (ZMod p))
  SP1Clean.StoreByteAssembler.assertion
    (⟨store_prev_value, store_value, register_low_byte, mem_limb_low_byte,
       byte_selector_top, byte_selector_mid, byte_selector_lo⟩ :
      Var SP1Clean.StoreByteAssembler.Inputs (ZMod p))
  is_real * (is_real - 1) === 0
  -- mem_limb is the prev_value limb the store is replacing (boilerplate gate)
  mem_limb * (mem_limb - mem_limb) === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) StoreByteCols unit where
  name := "SP1Clean.StoreByte.Gated"
  main := main
  localLength input := (main input).localLength 0
  output _ _ := ()
  localLength_eq input offset := by
    change (main input).localLength offset = (main input).localLength 0
    simp only [main, circuit_norm]

def Assumptions (_ : StoreByteCols (ZMod p)) : Prop := True

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu_sub, h_addr_sub, h_addr_shape_sub, h_itr_sub, h_smag_sub,
          h_sba_sub, h_isreal, _h_dummy⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_addr_sub trivial
  · exact h_addr_shape_sub trivial
  · exact h_itr_sub trivial
  · exact h_smag_sub trivial
  · exact h_sba_sub trivial
  · binary_iff h_isreal

set_option maxHeartbeats 800000 in
-- Same destructure as soundness; circuit_proof_start unfolds the 6
-- sub-circuit calls + 2 inline gates and exceeds the default cap.
theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨⟨e1, e2, e3, e4⟩, e5, e6, e7, e8, e9, e10, e11, e12, e13, e14, e15, e16,
          e17, e18, e19, e20, e21, e22, e23, e24, e25, e26, e27, e28, e29⟩ := h_input
  subst_eqs
  obtain ⟨h_cpu, h_addr, h_addr_shape, h_itr, h_smag, h_sba, h_isreal⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_addr⟩
  · exact ⟨trivial, h_addr_shape⟩
  · exact ⟨trivial, h_itr⟩
  · exact ⟨trivial, h_smag⟩
  · exact ⟨trivial, h_sba⟩
  · binary_iff h_isreal
  -- Trailing `mem_limb * (mem_limb - mem_limb) === 0` is `x * 0 = 0` — `ring`.
  · ring

end AssertionGated

def assertionGated : FormalAssertion (ZMod p) StoreByteCols :=
  { AssertionGated.elaborated with
    Assumptions := AssertionGated.Assumptions,
    Spec := AssertionGated.FormalSpec,
    soundness := AssertionGated.soundness,
    completeness := AssertionGated.completeness }

end SP1Clean.StoreByte
