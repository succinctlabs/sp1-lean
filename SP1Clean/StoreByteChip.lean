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
`OfflineMemory` aggregation. The chip's full `iff_sp1` to
`_root_.Store.StoreByte.constraints` is deferred; the goal here is to
demonstrate that the `MemoryAccess` + `ProgramTable` design generalizes
from memory-read chips (LoadByte) to memory-write chips, and to seed the
OfflineMemory consistency theorem with a real write access.

Opcode: `36 = SB` (Store Byte). Sibling chips `StoreHalf`, `StoreWord`,
`StoreDouble` follow the same shape with width and byte-selector
selectors.
-/

namespace SP1Clean.StoreByte

open Circuit ProvableType

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `StoreByteCols<T>` over
50 field elements. Field order matches the `Main[k]` indexing in
`SP1Chips/Store/StoreByte/Constraints.lean`. -/
structure StoreByteCols (T : Type) where
  clk_high : T                              -- Main[0]
  clk_16_24 : T                             -- Main[1]
  clk_0_16 : T                              -- Main[2]
  pc : Vector T 3                           -- Main[3..5]
  op_a : T                                  -- Main[6]
  op_a_memory_prev_value : Vector T 4       -- Main[7..10] (source data)
  op_a_memory_prev_low : T                  -- Main[11]
  op_a_memory_diff_low : T                  -- Main[12]
  op_a_0 : T                                -- Main[13]
  op_b : T                                  -- Main[14]
  op_b_memory_prev_value : Vector T 4       -- Main[15..18] (base address)
  op_b_memory_prev_low : T                  -- Main[19]
  op_b_memory_diff_low : T                  -- Main[20]
  op_c_imm : Vector T 4                     -- Main[21..24] (immediate offset)
  addr_value : Vector T 3                   -- Main[25..27] (computed store addr)
  addr_top_two_limb_inv : T                 -- Main[28]
  store_prev_value : Vector T 4             -- Main[29..32] (prior word at store addr)
  store_memory_prev_high : T                -- Main[33]
  store_memory_prev_low : T                 -- Main[34]
  store_memory_flag : T                     -- Main[35]
  store_memory_diff_low : T                 -- Main[36]
  store_memory_diff_high : T                -- Main[37]
  byte_selector_top : T                     -- Main[38] (selects which byte half)
  byte_selector_mid : T                     -- Main[39]
  byte_selector_lo : T                      -- Main[40]
  selected_byte : T                         -- Main[41] (byte being stored)
  selected_byte_alt : T                     -- Main[42]
  result_byte : T                           -- Main[43] (the new byte at the offset)
  selected_combined : T                     -- Main[44] (intermediate: combined byte at offset)
  store_write_value : Vector T 4            -- Main[45..48] (new 4-limb word)
  is_real : T                               -- Main[49]
deriving ProvableStruct

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
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b,
       _op_b_memory_prev_value, _op_b_memory_prev_low, _op_b_memory_diff_low,
       op_c_imm, _addr_value, _addr_top_two_limb_inv,
       _store_prev_value, _store_memory_prev_high, _store_memory_prev_low,
       _store_memory_flag, store_memory_diff_low, store_memory_diff_high,
       _byte_selector_top, _byte_selector_mid, _byte_selector_lo,
       _selected_byte, selected_byte_alt, result_byte,
       _selected_combined, _store_write_value, is_real⟩ := cols
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
    (#v[(3 : Expression (ZMod p)), 0, result_byte, 0]
      : Vector (Expression (ZMod p)) 4)
  lookup ByteOpcodeTable
    (#v[(3 : Expression (ZMod p)), 0, selected_byte_alt, 0]
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
def Spec (cols : StoreByteCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  -- Source-register read for op_a (no write — stores don't write the
  -- destination register).
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 4
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_a
      { prev_value := cols.op_a_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_a_memory_prev_low,
            diff_low_limb := cols.op_a_memory_diff_low } }) ∧
  -- Base-register read for op_b.
  SP1Clean.memoryAccessSpec
    (cols.clk_0_16 + cols.clk_16_24 * 65536) 3
    (SP1Clean.MemoryAccess.ofRegisterShared cols.op_b
      { prev_value := cols.op_b_memory_prev_value,
        access_timestamp :=
          { prev_low := cols.op_b_memory_prev_low,
            diff_low_limb := cols.op_b_memory_diff_low } }) ∧
  -- Store-side memory access. Address is the 3-limb `addr_value`
  -- computed by the AddressOperation; this is generally NOT a register
  -- address (`addr_value[0].val ≥ 32`), so the RAM branch of
  -- `SP1Constraint.toStateProp_poly` fires. `prev_value` is the prior
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
    { pc := cols.pc,
      opcode := 36,
      op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0],
      op_c := cols.op_c_imm,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 1 } ∧
  -- Real-flag boolean gate.
  cols.is_real * (cols.is_real - 1) = 0

/-- The store-side memory access as a `MemoryAccess` record, exposed for
trace-level OfflineMemory aggregation. This is the access that hits the
RAM branch (not registers): `addr_value` is the store destination
computed by the AddressOperation sub-fragment.

For trace-level aggregation, the corresponding `write_value` is the
4-limb word `[Main[45], Main[46], Main[47], Main[48]]` in the SP1
constraints (here exposed as `cols.store_write_value` plus
`cols.store_write_value_3`). For pure register reads of `op_a` / `op_b`,
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
`store_prev_value`, `selected_combined`, and the byte selectors. -/
def storeWriteValue (cols : StoreByteCols (ZMod p)) : Word (ZMod p) :=
  cols.store_write_value

/-! ## Full `FormalAssertion` promotion (Path-2)

Drops the bare byte lookups (CPUState bytes done inline, store memory
diff bytes, result_byte U8 range, selected_byte_alt U8 range); covers
`CPUState`, `ProgramTable`, and the `is_real` boolean. Memory-bus
consistency is deferred to OfflineMemory. -/

namespace Assertion

open Circuit

@[reducible]
def main (cols : Var StoreByteCols (ZMod p)) : Circuit (ZMod p) Unit := do
  let ⟨_clk_high, clk_16_24, clk_0_16, pc, op_a,
       _op_a_memory_prev_value, _op_a_memory_prev_low, _op_a_memory_diff_low,
       op_a_0, op_b,
       _op_b_memory_prev_value, _op_b_memory_prev_low, _op_b_memory_diff_low,
       op_c_imm, _addr_value, _addr_top_two_limb_inv,
       _store_prev_value, _store_memory_prev_high, _store_memory_prev_low,
       _store_memory_flag, _store_memory_diff_low, _store_memory_diff_high,
       _byte_selector_top, _byte_selector_mid, _byte_selector_lo,
       _selected_byte, _selected_byte_alt, _result_byte,
       _selected_combined, _store_write_value, is_real⟩ := cols
  SP1Clean.CPUState.assertion
    (⟨clk_0_16, clk_16_24⟩ : Var SP1Clean.CPUState.Inputs (ZMod p))
  SP1Clean.ProgramTable.assertion
    (⟨pc, 36, op_a, #v[op_b, 0, 0, 0], op_c_imm, op_a_0, 0, 1⟩ :
      Var SP1Clean.ProgramTable.Inputs (ZMod p))
  is_real * (is_real - 1) === 0

@[reducible]
instance elaborated : ElaboratedCircuit (ZMod p) StoreByteCols unit where
  name := "SP1Clean.StoreByte"
  main := main
  localLength _ := 0

def Assumptions (_ : StoreByteCols (ZMod p)) : Prop := True

def FormalSpec (cols : StoreByteCols (ZMod p)) : Prop :=
  SP1Clean.CPUState.cpuStateSpec cols.clk_0_16 cols.clk_16_24 ∧
  SP1Clean.ProgramTable.Spec
    { pc := cols.pc, opcode := 36, op_a := cols.op_a,
      op_b := #v[cols.op_b, 0, 0, 0], op_c := cols.op_c_imm,
      op_a_0 := cols.op_a_0, imm_b := 0, imm_c := 1 } ∧
  cols.is_real * (cols.is_real - 1) = 0

theorem soundness :
    FormalAssertion.Soundness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu_sub, h_prog_sub, h_isreal⟩ := h_holds
  unfold id at *
  refine ⟨?_, ?_, ?_⟩
  · exact h_cpu_sub trivial
  · exact h_prog_sub trivial
  · linear_combination h_isreal

theorem completeness :
    FormalAssertion.Completeness (ZMod p) elaborated Assumptions FormalSpec := by
  circuit_proof_start
  obtain ⟨h_cpu, h_prog, h_isreal⟩ := h_spec
  unfold id at *
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨trivial, h_cpu⟩
  · exact ⟨trivial, h_prog⟩
  · linear_combination h_isreal

end Assertion

def assertion : FormalAssertion (ZMod p) StoreByteCols :=
  { Assertion.elaborated with
    Assumptions := Assertion.Assumptions,
    Spec := Assertion.FormalSpec,
    soundness := Assertion.soundness,
    completeness := Assertion.completeness }

end SP1Clean.StoreByte
