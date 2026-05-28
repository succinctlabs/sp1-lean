import Clean.Utils.OfflineMemory
import SP1Clean.MemoryAccess
import SP1Clean.Chips.ALU.AddChip.Circuit
import SP1Clean.Chips.Memory.LoadByteChip
import SP1Clean.Chips.Memory.StoreByteChip
import SP1Clean.Chips.Control.JalChip.Circuit
import SP1Clean.Chips.ALU.MulChip.Aggregate
import SP1Clean.Chips.ALU.ShiftLeftChip.Aggregate
import SP1Clean.Chips.ALU.AddwChip.SailBridge
import SP1Clean.Chips.ALU.UTypeChip.SailBridge
import SP1Clean.Chips.Control.JalrChip.Aggregate
import SP1Clean.Chips.ALU.LtChip.SailBridge
import SP1Clean.Chips.Memory.StoreWordChip
import SP1Clean.Chips.Memory.StoreDoubleChip
import SP1Clean.Chips.Memory.StoreHalfChip
import SP1Clean.Chips.Memory.LoadDoubleChip
import SP1Clean.Chips.Memory.LoadWordChip
import SP1Clean.Chips.Memory.LoadHalfChip
import SP1Clean.Chips.Control.BranchChip.Aggregate
import SP1Clean.Chips.Memory.LoadX0Chip
import SP1Clean.Chips.ALU.ShiftRightChip.Aggregate
import SP1Clean.Chips.ALU.DivRemChip.Aggregate
import SP1Clean.Chips.ALU.AddiChip.SailBridge
import SP1Clean.Chips.ALU.BitwiseChip.Aggregate
import SP1Clean.Chips.ALU.SubChip.SailBridge
import SP1Clean.Chips.ALU.SubwChip.SailBridge
import SP1Clean.Chips.Memory.MemoryGlobalChip

/-! # Trace-level OfflineMemory bridge

This file wires per-chip `MemoryAccess` records into the
`Clean.Utils.OfflineMemory` consistency theorem
(`MemoryAccessList.isConsistentOnline_iff_isConsistentOffline`).

`MemoryAccessTuple` / `MemoryAccessList` are transparent aliases for
the upstream `_root_.MemoryAccess` / `_root_.MemoryAccessList`
(`Clean.Utils.OfflineMemory`).

The design (per `docs/CLEAN_OVERVIEW.md` "What SP1Clean adds — composable
interaction layer" and the plan
`/home/dtumad/.claude/plans/make-a-plan-to-stateful-cookie.md`):

1. Each chip's `Spec` includes one or more `SP1Clean.memoryAccessSpec`
   conjuncts. The corresponding `MemoryAccess` records encode the
   per-row read side of the memory bus.
2. Per row, the chip also carries a write-side word: for register
   writes (`op_a` on arithmetic chips, `op_a_write_value` after Load
   completes) this is a distinct value from `prev_value`; for pure
   reads it's identical.
3. This file aggregates per-row records across a heterogenous list of
   chip rows into a single global `MemoryAccessList`. OfflineMemory's
   main theorem then tells us per-row consistency plus a permutation
   witness gives offline trace consistency.

Per-chip aggregators emit accesses in `(timestamp, addr, read, write)`
form via `SP1Clean.MemoryAccess.toAccessTuple`. -/

namespace SP1Clean.Soundness

open SP1Clean

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The 4-tuple OfflineMemory representation:
`(timestamp, address, readValue, writeValue)`. Transparent alias for
`_root_.MemoryAccess` from `Clean.Utils.OfflineMemory`. -/
abbrev MemoryAccessTuple := _root_.MemoryAccess

/-- Time-ordered list of memory accesses (canonically reverse-ordered:
most-recent at head). Transparent alias for `_root_.MemoryAccessList`
from `Clean.Utils.OfflineMemory`. -/
abbrev MemoryAccessList := _root_.MemoryAccessList

/-- A chip row in the heterogenous aggregation. Each constructor wraps
one chip's column struct so the aggregator can pattern-match on chip
identity to extract the right `MemoryAccess` records and write-values.

Each new chip the pilot covers adds one constructor here. The two
shipping in this iteration are `add` (3 register accesses, 1 write to
op_a) and `loadByte` (2 register accesses + 1 RAM read at the load
address). -/
inductive ChipRow (p : ℕ) [Fact p.Prime] [Fact (2 ^ 17 < p)] where
  | add (cols : SP1Clean.Add.AddCols (ZMod p))
  | loadByte (cols : SP1Clean.LoadByte.LoadByteCols (ZMod p))
  | storeByte (cols : SP1Clean.StoreByte.StoreByteCols (ZMod p))
  | jal (cols : SP1Clean.Jal.JalCols (ZMod p))
  | mul (cols : SP1Clean.Mul.MulCols (ZMod p))
  | shiftLeft (cols : SP1Clean.ShiftLeft.ShiftLeftCols (ZMod p))
  | addw (cols : SP1Clean.Addw.AddwCols (ZMod p))
  | uType (cols : SP1Clean.UType.UTypeCols (ZMod p))
  | jalr (cols : SP1Clean.Jalr.JalrCols (ZMod p))
  | lt (cols : SP1Clean.Lt.LtCols (ZMod p))
  | storeWord (cols : SP1Clean.StoreWord.StoreWordCols (ZMod p))
  | storeDouble (cols : SP1Clean.StoreDouble.StoreDoubleCols (ZMod p))
  | storeHalf (cols : SP1Clean.StoreHalf.StoreHalfCols (ZMod p))
  | loadDouble (cols : SP1Clean.LoadDouble.LoadDoubleCols (ZMod p))
  | loadWord (cols : SP1Clean.LoadWord.LoadWordCols (ZMod p))
  | loadHalf (cols : SP1Clean.LoadHalf.LoadHalfCols (ZMod p))
  | branch (cols : SP1Clean.Branch.BranchCols (ZMod p))
  | loadX0 (cols : SP1Clean.LoadX0.LoadX0Cols (ZMod p))
  | shiftRight (cols : SP1Clean.ShiftRight.ShiftRightCols (ZMod p))
  | divRem (cols : SP1Clean.DivRem.DivRemCols (ZMod p))
  | addi (cols : SP1Clean.Addi.AddiCols (ZMod p))
  | bitwise (cols : SP1Clean.Bitwise.BitwiseCols (ZMod p))
  | sub (cols : SP1Clean.Sub.SubCols (ZMod p))
  | subw (cols : SP1Clean.Subw.SubwCols (ZMod p))
  /-- Memory-bus boundary: initialization records. Closes the bus at
  the lowest timestamp by claiming `prev_value = 0` for each address
  the trace ever accesses. See `SP1Clean/MemoryGlobalChip.lean`. -/
  | memInit (cols : SP1Clean.MemoryGlobal.MemoryGlobalCols (ZMod p))
  /-- Memory-bus boundary: finalization records. Closes the bus at
  the trace's last timestamp per-address by reading the final value
  out. See `SP1Clean/MemoryGlobalChip.lean`. -/
  | memFinalize (cols : SP1Clean.MemoryGlobal.MemoryGlobalCols (ZMod p))

namespace ChipRow

/-- The list of memory accesses emitted by one chip row, paired with
the write-side value. Each `(MemoryAccess, write_value)` pair flattens
into one OfflineMemory tuple via
`SP1Clean.MemoryAccess.toAccessTuple`. -/
def memoryAccesses : ChipRow p → List ((SP1Clean.MemoryAccess (ZMod p)) × Word (ZMod p))
  | .add _ =>
      -- AddChip's three register accesses (op_a R+W, op_b/op_c reads) now
      -- flow through the multiplicity-aware memory bus emitted inside
      -- `RTypeReader.Gated.assertion` via `RegisterAccess.assertion`.
      -- Parallel to `.addw` / Load/Store.
      []
  | .loadByte _ =>
      -- LoadByteChip's memory contributions are routed through the
      -- multiplicity-aware lookup bus, parallel to `.addw` / `.storeByte`.
      -- The disjunctive multiplicity `mult = is_lb + is_lbu` gates the
      -- shared byte/memory lookups; `mult = is_lb` gates the MSB
      -- sign-extension byte lookup. Per-row contributions move to the
      -- bus aggregator; trace-level balance closes the global theorem.
      []
  | .storeByte _ =>
      -- StoreByteChip's memory contributions are routed through the
      -- multiplicity-aware lookup bus (see `SP1Clean/SP1Lookup.lean`),
      -- mirroring the AddwChip Phase-5 migration. The op_a / op_b
      -- register reads and the store-side RAM read-then-write all
      -- become `memoryBusGated` contributions at the chip level;
      -- per-key multiplicity balance is enforced at the trace level.
      -- See `docs/MULTIPLICITY_BUS.md` Phase 4 for the parallel
      -- `lookupAccesses` aggregator design.
      []
  | .jal _ =>
      -- JalChip's memory contributions now flow through the multiplicity-aware
      -- lookup bus emitted inside `JTypeReader.Gated.assertion` (parallel to
      -- `.uType _` after the canonical-(a) FormalSpec migration). The
      -- state-bus PC chain is still tracked at trace level.
      []
  | .mul cols =>
      -- Three register accesses. op_a is read AND written (write_value =
      -- op_a_write_value, holding whatever the carry-chain produced —
      -- correctness of that value is the MulOperation surface, which the
      -- pilot's iff-only mirror leaves at `True`). op_b and op_c are pure
      -- reads.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_a, 0, 0],
          prev_value := cols.adapter.op_a_memory.prev_value,
          prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_b, 0, 0],
          prev_value := cols.adapter.op_b_memory.prev_value,
          prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_c, 0, 0],
          prev_value := cols.adapter.op_c_memory.prev_value,
          prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb }
      [(op_a_mem, cols.op_a_write_value),
       (op_b_mem, cols.adapter.op_b_memory.prev_value),
       (op_c_mem, cols.adapter.op_c_memory.prev_value)]
  | .shiftLeft cols =>
      -- Three register accesses. op_a is read AND written (write_value =
      -- `cols.result`, the 4-limb shifted output). op_b and op_c are pure
      -- reads.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_a, 0, 0],
          prev_value := cols.adapter.op_a_memory.prev_value,
          prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_b, 0, 0],
          prev_value := cols.adapter.op_b_memory.prev_value,
          prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_c[0], 0, 0],
          prev_value := cols.adapter.op_c_memory.prev_value,
          prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb }
      [(op_a_mem, cols.result),
       (op_b_mem, cols.adapter.op_b_memory.prev_value),
       (op_c_mem, cols.adapter.op_c_memory.prev_value)]
  | .addw _ =>
      -- AddwChip's memory-access contributions are now routed through the
      -- multiplicity-aware lookup bus (see `SP1Clean/SP1Lookup.lean`'s
      -- `byteOpcodeGated`). The op_c access in particular is genuinely
      -- gated by `is_real - imm_c` (vacuous on ADDIW rows), which the
      -- unconditional `memoryAccesses` aggregator cannot express. Drop the
      -- contribution here; a parallel `lookupAccesses` accessor (Phase 4
      -- of MULTIPLICITY_BUS.md) is the canonical home.
      []
  | .uType _ =>
      -- UType memory-access contributions are now routed through the
      -- multiplicity-aware lookup bus (per the canonical-(a) FormalSpec
      -- migration: `JTypeReader.Gated.assertion` composes an `OperandAccess`
      -- subcircuit for op_a write). Parallel to `.addw _`'s bus-routing.
      []
  | .jalr cols =>
      -- Two register accesses: op_a write (return address), op_b read
      -- (jump-target base register). op_c is an I-type immediate.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Jalr.opAMemoryAccess cols
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Jalr.opBMemoryAccess cols
      [(op_a_mem, cols.op_a_write_value),
       (op_b_mem, cols.adapter.op_b_memory.prev_value)]
  | .lt cols =>
      -- Three register accesses. op_a writes a 1-bit boolean result
      -- (write_value = `#v[compare_bit, 0, 0, 0]`); op_b / op_c are
      -- pure reads (write_value = prev_value).
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Lt.opAMemoryAccess cols
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Lt.opBMemoryAccess cols
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Lt.opCMemoryAccess cols
      [(op_a_mem, #v[cols.lt_operation.result.u16_compare_operation.bit, 0, 0, 0]),
       (op_b_mem, cols.adapter.op_b_memory.prev_value),
       (op_c_mem, cols.adapter.op_c_memory.prev_value)]
  -- Store{Word,Double,Half} memory contributions are routed through the
  -- multiplicity-aware lookup bus, parallel to `.storeByte` and `.addw`
  -- (see `docs/MULTIPLICITY_BUS.md`).
  | .storeWord _ => []
  | .storeDouble _ => []
  | .storeHalf _ => []
  -- Load{Double,Word} memory contributions are routed through the
  -- multiplicity-aware lookup bus (parallel to `.loadByte` / `.storeByte`).
  -- LoadDouble: single `is_real` (LD only). LoadWord: disjunctive
  -- `is_lw + is_lwu` (shared) and `is_lw`-only MSB.
  | .loadDouble _ => []
  | .loadWord _ => []
  | .branch cols =>
      -- Two register reads (op_a / op_b as comparison operands); no
      -- writes. PC chain is state-bus, trace-level.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Branch.opAMemoryAccess cols
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Branch.opBMemoryAccess cols
      [(op_a_mem, cols.adapter.op_a_memory.prev_value),
       (op_b_mem, cols.adapter.op_b_memory.prev_value)]
  -- LoadX0 memory contributions are routed through the multiplicity-aware
  -- lookup bus. Multiplicity here is the 7-way sum
  -- `is_lb + is_lbu + is_lh + is_lhu + is_lw + is_lwu + is_ld` (a single
  -- variant is active per row; chip's `is_real` is the boolean sum).
  -- op_a's write_value is zero (destination is x0), absorbed in the
  -- write-side of the bus tuple.
  | .loadX0 _ => []
  | .shiftRight cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_a, 0, 0],
          prev_value := cols.adapter.op_a_memory.prev_value,
          prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_b, 0, 0],
          prev_value := cols.adapter.op_b_memory.prev_value,
          prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_c[0], 0, 0],
          prev_value := cols.adapter.op_c_memory.prev_value,
          prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb }
      [(op_a_mem, cols.op_a_write_value),
       (op_b_mem, cols.adapter.op_b_memory.prev_value),
       (op_c_mem, cols.adapter.op_c_memory.prev_value)]
  | .divRem cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_a, 0, 0],
          prev_value := cols.adapter.op_a_memory.prev_value,
          prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_b, 0, 0],
          prev_value := cols.adapter.op_b_memory.prev_value,
          prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_c, 0, 0],
          prev_value := cols.adapter.op_c_memory.prev_value,
          prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb }
      [(op_a_mem, cols.op_a_write_value),
       (op_b_mem, cols.adapter.op_b_memory.prev_value),
       (op_c_mem, cols.adapter.op_c_memory.prev_value)]
  | .loadHalf cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_a, 0, 0],
          prev_value := cols.adapter.op_a_memory.prev_value,
          prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_b, 0, 0],
          prev_value := cols.adapter.op_b_memory.prev_value,
          prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb }
      let load_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.LoadHalf.loadMemoryAccess cols
      -- op_a is written with the sign-extended loaded half: the stored
      -- limb `op_a_write_value_lo` plus three sign-extension limbs
      -- derived from `signed_extension_msb`.
      [(op_a_mem,
        #v[cols.op_a_write_value_lo,
           65535 * cols.signed_extension_msb,
           65535 * cols.signed_extension_msb,
           65535 * cols.signed_extension_msb]),
       (op_b_mem, cols.adapter.op_b_memory.prev_value),
       (load_mem, cols.load_prev_value)]
  | .addi _ =>
      -- AddiChip's two register accesses (op_a R+W, op_b read) now flow
      -- through the multiplicity-aware memory bus inside
      -- `ITypeReader.Gated.assertion`. Parallel to `.add`.
      []
  | .bitwise cols =>
      -- Three register accesses (op_a write, op_b/op_c pure reads). The
      -- op_a write value is the 4-limb word reconstruction from the chip's
      -- 8-limb `bitwise_result` (mirrors the `E19/E21/E23/E25` halfword
      -- packs in `BitwiseU16Operation.constraints`).
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_a, 0, 0],
          prev_value := cols.adapter.op_a_memory.prev_value,
          prev_low := cols.adapter.op_a_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_a_memory.access_timestamp.diff_low_limb }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_b, 0, 0],
          prev_value := cols.adapter.op_b_memory.prev_value,
          prev_low := cols.adapter.op_b_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_b_memory.access_timestamp.diff_low_limb }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.adapter.op_c[0], 0, 0],
          prev_value := cols.adapter.op_c_memory.prev_value,
          prev_low := cols.adapter.op_c_memory.access_timestamp.prev_low,
          diff_low_limb := cols.adapter.op_c_memory.access_timestamp.diff_low_limb }
      [(op_a_mem,
        #v[cols.bitwise_operation.bitwise_operation.result[0] +
             cols.bitwise_operation.bitwise_operation.result[1] * 256,
           cols.bitwise_operation.bitwise_operation.result[2] +
             cols.bitwise_operation.bitwise_operation.result[3] * 256,
           cols.bitwise_operation.bitwise_operation.result[4] +
             cols.bitwise_operation.bitwise_operation.result[5] * 256,
           cols.bitwise_operation.bitwise_operation.result[6] +
             cols.bitwise_operation.bitwise_operation.result[7] * 256]),
       (op_b_mem, cols.adapter.op_b_memory.prev_value),
       (op_c_mem, cols.adapter.op_c_memory.prev_value)]
  | .sub _ =>
      -- SubChip's three register accesses route through the
      -- multiplicity-aware memory bus inside `RTypeReader.Gated.assertion`.
      -- Parallel to `.add`.
      []
  | .subw _ =>
      -- SubwChip's three register accesses route through the
      -- multiplicity-aware memory bus inside `RTypeReader.Gated.assertion`.
      -- Parallel to `.addw`.
      []
  -- Boundary chips: Phase 4 placeholder — emit empty accesses. Full
  -- boundary-record emission is a Phase 4.5 follow-up.
  | .memInit cols => SP1Clean.MemoryGlobal.initMemoryAccesses cols
  | .memFinalize cols => SP1Clean.MemoryGlobal.finalizeMemoryAccesses cols

/-- The chip-row's `clk_high` and (composed) `clk_low` for the per-access
timestamp encoding `clk_high * 2^24 + clk_low + offset`. -/
def clockComponents : ChipRow p → ZMod p × ZMod p
  | .add cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .loadByte cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .storeByte cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .jal cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .mul cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .shiftLeft cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .addw cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .uType cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .jalr cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .lt cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .storeWord cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .storeDouble cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .storeHalf cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .loadDouble cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .loadWord cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .loadHalf cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .branch cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .loadX0 cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .shiftRight cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .divRem cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .addi cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .bitwise cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .sub cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .subw cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  -- Boundary chips: clk_low is raw (no clk_0_16 / clk_16_24 decomposition).
  | .memInit cols => (cols.clk_high, cols.clk_low)
  | .memFinalize cols => (cols.clk_high, cols.clk_low)

/-- The chip-row's natural Spec predicate (the propositional content the
chip's FormalAssertion / iff_sp1 establishes). The `Fact (2 ^ 24 < p)`
instance is required by `SP1Clean.Mul.assertion` and
`SP1Clean.DivRem.assertion` (transitive via their `MulOp.assertion`
sub-circuit). -/
def Spec [Fact (2 ^ 24 < p)] : ChipRow p → Prop
  | .add cols => SP1Clean.Add.assertion.Spec cols
  | .loadByte cols => SP1Clean.LoadByte.assertion.Spec cols
  | .storeByte cols => SP1Clean.StoreByte.assertion.Spec cols
  | .jal cols => SP1Clean.Jal.assertion.Spec cols
  | .mul cols => SP1Clean.Mul.assertion.Spec cols
  | .shiftLeft cols => SP1Clean.ShiftLeft.assertion.Spec cols
  | .addw cols => SP1Clean.Addw.assertion.Spec cols
  | .uType cols => SP1Clean.UType.assertion.Spec cols
  | .jalr cols => SP1Clean.Jalr.assertion.Spec cols
  | .lt cols => SP1Clean.Lt.assertion.Spec cols
  | .storeWord cols => SP1Clean.StoreWord.assertion.Spec cols
  | .storeDouble cols => SP1Clean.StoreDouble.assertion.Spec cols
  | .storeHalf cols => SP1Clean.StoreHalf.assertion.Spec cols
  | .loadDouble cols => SP1Clean.LoadDouble.assertion.Spec cols
  | .loadWord cols => SP1Clean.LoadWord.assertion.Spec cols
  | .loadHalf cols => SP1Clean.LoadHalf.assertion.Spec cols
  | .branch cols => SP1Clean.Branch.assertion.Spec cols
  | .loadX0 cols => SP1Clean.LoadX0.assertion.Spec cols
  | .shiftRight cols => SP1Clean.ShiftRight.assertion.Spec cols
  | .divRem cols => SP1Clean.DivRem.assertion.Spec cols
  | .addi cols => SP1Clean.Addi.assertion.Spec cols
  | .bitwise cols => SP1Clean.Bitwise.assertion.Spec cols
  | .sub cols => SP1Clean.Sub.assertion.Spec cols
  | .subw cols => SP1Clean.Subw.assertion.Spec cols
  -- Boundary chips: Phase 4 placeholder Spec := True.
  | .memInit cols => SP1Clean.MemoryGlobal.Spec cols
  | .memFinalize cols => SP1Clean.MemoryGlobal.Spec cols

/-- Per-row, per-access sub-clock offsets. R-type and I-type readers
emit accesses at `clk_low + 4` (op_a), `clk_low + 3` (op_b), and
`clk_low + 2` (op_c); `LoadByte` adds an access at `clk_low + 1` for
the RAM load. The offset list mirrors `memoryAccesses` above. -/
def offsets : ChipRow p → List (ZMod p)
  -- Add memory accesses now flow through the lookup bus.
  | .add _ => []
  -- LoadByte memory accesses also flow through the lookup bus.
  | .loadByte _ => []
  -- StoreByte memory accesses now flow through the lookup bus (parallel
  -- to `.addw _`); offset list is empty.
  | .storeByte _ => []
  -- Jal: memory contributions flow through the lookup bus (parallel to
  -- `.uType _` after canonical-(a) FormalSpec migration); offsets empty.
  | .jal _ => []
  -- Mul and ShiftLeft: same R-type-reader pattern as Add (3 register
  -- accesses at +4 / +3 / +2). No RAM accesses.
  | .mul _ => [4, 3, 2]
  | .shiftLeft _ => [4, 3, 2]
  | .addw _ => []  -- parallel to `memoryAccesses (.addw _) := []`
  | .uType _ => []  -- parallel to `memoryAccesses (.addw _) := []`
  | .jalr _ => [4, 3]
  | .lt _ => [4, 3, 2]
  -- Store{Word,Double,Half} memory accesses also flow through the lookup
  -- bus (parallel to `.storeByte`); offset lists are empty.
  | .storeWord _ => []
  | .storeDouble _ => []
  | .storeHalf _ => []
  -- Load{Double,Word,Half} memory accesses also flow through the lookup bus.
  | .loadDouble _ => []
  | .loadWord _ => []
  | .loadHalf _ => []
  | .branch _ => [4, 3]
  -- LoadX0 memory accesses also flow through the lookup bus.
  | .loadX0 _ => []
  | .shiftRight _ => [4, 3, 2]
  | .divRem _ => [4, 3, 2]
  -- Addi/Sub/Subw memory accesses now flow through the lookup bus.
  | .addi _ => []
  | .bitwise _ => [4, 3, 2]
  | .sub _ => []
  | .subw _ => []
  -- Boundary chips: empty offset list (no per-access offsets — the
  -- boundary record's timestamp is the row's own `(clk_high, clk_low)`).
  | .memInit _ => []
  | .memFinalize _ => []

end ChipRow

/-- The per-row access-tuple list. Each chip row's memory accesses
paired with their per-access offsets and write-values, encoded via
`SP1Clean.MemoryAccess.toAccessTuple` into the `(timestamp, addr, read,
write)` 4-tuple form expected by `Clean.Utils.OfflineMemory`. -/
def ChipRow.rowAccessTuples (row : ChipRow p) : List _root_.MemoryAccess :=
  let (clk_high, clk_low) := row.clockComponents
  let accesses := row.memoryAccesses
  let offs := row.offsets
  (accesses.zip offs).map fun ((acc, write_value), offset) =>
    acc.toAccessTuple clk_high clk_low offset write_value

/-- The `is_real` field of each chip row, computed as a single field
expression. For chips with an `is_real` column, this is just `cols.is_real`;
for chips with multi-arm opcode selectors (Branch, Mul, Lt, ShiftLeft,
ShiftRight, LoadByte, LoadHalf, LoadWord, LoadX0, Bitwise), this is the
sum of the opcode-selector flags.

This mirrors the `is_real` arm of `ChipRow.stateAccess` in
`SP1Clean/Soundness/StateConsistency.lean` (which depends on this file
and so cannot be referenced upstream). The padding-row predicate
`(row.isRealField) = 0` is what drives the filtered aggregator below. -/
def ChipRow.isRealField : ChipRow p → ZMod p
  | .add cols => cols.is_real
  | .addi cols => cols.is_real
  | .addw cols => cols.is_real
  | .bitwise cols => cols.is_xor + cols.is_or + cols.is_and
  | .branch cols =>
      cols.is_beq + cols.is_bne + cols.is_blt + cols.is_bge +
        cols.is_bltu + cols.is_bgeu
  | .divRem cols => cols.is_real
  | .jal cols => cols.is_real
  | .jalr cols => cols.is_real
  | .loadByte cols => cols.is_lb + cols.is_lbu
  | .loadDouble cols => cols.is_real
  | .loadHalf cols => cols.is_lh + cols.is_lhu
  | .loadWord cols => cols.is_lw + cols.is_lwu
  | .loadX0 cols =>
      cols.is_lb + cols.is_lbu + cols.is_lh + cols.is_lhu +
        cols.is_lw + cols.is_lwu + cols.is_ld
  | .lt cols => cols.is_slt + cols.is_sltu
  | .mul cols =>
      cols.is_mul + cols.is_mulh + cols.is_mulw +
        cols.is_mulhsu + cols.is_mulhu
  | .shiftLeft cols => cols.is_sll + cols.is_sllw
  | .shiftRight cols =>
      cols.is_srl + cols.is_sra + cols.is_srlw + cols.is_sraw
  | .storeByte cols => cols.is_real
  | .storeDouble cols => cols.is_real
  | .storeHalf cols => cols.is_real
  | .storeWord cols => cols.is_real
  | .sub cols => cols.is_real
  | .subw cols => cols.is_real
  -- Boundary chips: their `is_real` column directly.
  | .memInit cols => cols.is_real
  | .memFinalize cols => cols.is_real
  | .uType cols => cols.is_real

/-- Aggregate a list of chip rows into a single `MemoryAccessList`.
Each row contributes its memory-access tuples via `ChipRow.rowAccessTuples`.

Rows are iterated in **reverse trace order** (latest row first) to match
`Clean.Utils.OfflineMemory`'s canonical "most-recent at head" convention
for `MemoryAccessList`. Each row's internal `offsets` list is already
decreasing (e.g. `[4, 3, 2]`), so the resulting list is in strictly
decreasing timestamp order under the trace-shape clock invariant.

Note: trace input `rows` is in **chronological** order (row 0 = earliest,
row n-1 = latest). The reversal here is purely a presentation choice for
the OfflineMemory bridge. -/
def aggregateMemoryAccesses (rows : List (ChipRow p)) : MemoryAccessList :=
  rows.reverse.flatMap ChipRow.rowAccessTuples

/-! ### Padding-aware aggregator (iter-8 Phase 3)

SP1's memory bus assigns padding rows `is_real = 0`, which drops them
from the bus digest entirely (multiplicity 0 contribution). The
unfiltered `aggregateMemoryAccesses` above does NOT distinguish padding
— every row contributes its tuples. For SP1-faithful trace-soundness,
the bus should see only the real rows.

`aggregateMemoryAccessesFiltered` is the padding-aware variant: rows
where `(row.isRealField) = 0` contribute the empty list. The
chronological + reverse-order discipline is preserved.

The relationship to the unfiltered version is captured by
`aggregateMemoryAccesses_eq_filtered_of_all_real`: when every row is
real (`isRealField ≠ 0`), the two aggregators coincide. -/

/-- The padding-aware aggregator. Filters out rows whose `is_real`
projection is zero before flattening the per-row tuple lists. -/
def aggregateMemoryAccessesFiltered (rows : List (ChipRow p)) :
    MemoryAccessList :=
  rows.reverse.flatMap fun row =>
    if row.isRealField = 0 then [] else row.rowAccessTuples

/-- When every row is real (`isRealField ≠ 0`), the filtered aggregator
coincides with the unfiltered one. This is the discharge that bridges
the SP1-faithful padding-aware bus to the existing
`chip_specs_admit_offline_bridge` consumers on no-padding traces. -/
theorem aggregateMemoryAccesses_eq_filtered_of_all_real
    (rows : List (ChipRow p))
    (h_all_real : ∀ row ∈ rows, row.isRealField ≠ 0) :
    aggregateMemoryAccessesFiltered rows = aggregateMemoryAccesses rows := by
  unfold aggregateMemoryAccessesFiltered aggregateMemoryAccesses
  apply List.flatMap_congr
  intro row h_mem
  have h_real := h_all_real row (List.mem_reverse.mp h_mem)
  simp [h_real]

/-- Filtering preserves the all-padding case: an all-padding trace
(every row has `is_real = 0`) produces an empty `MemoryAccessList`. -/
theorem aggregateMemoryAccessesFiltered_of_all_padding
    (rows : List (ChipRow p))
    (h_all_padding : ∀ row ∈ rows, row.isRealField = 0) :
    aggregateMemoryAccessesFiltered rows = [] := by
  unfold aggregateMemoryAccessesFiltered
  apply List.flatMap_eq_nil_iff.mpr
  intro row h_mem
  have h_padding := h_all_padding row (List.mem_reverse.mp h_mem)
  simp [h_padding]

/-- Trace-level OfflineMemory bridge: given trace-shape hypotheses
`h_sorted` and `h_nodup`, the aggregated chip-row memory accesses are
online-consistent iff there is a permutation that is offline-consistent.

The role of `h_specs` is to assert that every chip row's `Spec` holds.
The two trace-shape hypotheses (`h_sorted`, `h_nodup`) are discharged
from `h_specs` plus a clock-monotonicity assumption in
`SP1Clean/Soundness/MemoryConsistencyClock.lean` (Phase A.3 of the
trace-soundness plan). -/
theorem chip_specs_admit_offline_bridge [Fact (2 ^ 24 < p)]
    (rows : List (ChipRow p))
    (_h_specs : ∀ row ∈ rows, row.Spec)
    (h_sorted : (aggregateMemoryAccesses rows).isTimestampSorted)
    (h_nodup : (aggregateMemoryAccesses rows).Notimestampdup) :
    MemoryAccessList.isConsistentOnline (aggregateMemoryAccesses rows) h_sorted ↔
    ∃ permuted : AddressSortedMemoryAccessList,
      permuted.val.Perm (aggregateMemoryAccesses rows) ∧
      MemoryAccessList.isConsistentOffline permuted.val permuted.property :=
  MemoryAccessList.isConsistentOnline_iff_isConsistentOffline
    (aggregateMemoryAccesses rows) h_sorted h_nodup

/-! ## Sub-task F: Memory-bus grounding from chip Specs

Define `ChipRow.memoryAccessesValid` — the per-row claim that each emitted
`MemoryAccess` satisfies its `memoryAccessSpec` (diff_low_limb bound,
scaled-timestamp bound, `Word.isU64` on `prev_value`). Builds a uniform
predicate over the chip's `memoryAccesses` × `offsets` pairing.

The per-row discharge from each chip's `Spec` is the substantive grounding
piece. For chips whose `FormalSpec` includes `OperandAccess.Assertion.Spec`
conjuncts directly (Add, post sub-task E POC), the projection is clean. For
the 23 other chips whose `ChipRow.Spec` arm still points at legacy
`<Chip>.Spec` (which embeds `memoryAccessSpec` via `rtypeReaderSpec` /
`itypeReaderSpec` wrappers), the projection is straightforward but
requires per-chip Spec unfolding — deferred to a follow-up sub-task that
completes sub-task E across all 24 chips.

Today's contribution: the predicate's shape, Add's per-chip discharge as a
proof-of-concept, and the trace-level aggregator that consumes a
verifier-supplied `TraceMemoryAccessesValid` trace-shape bundle for the
remaining 23 chips. -/

/-- Per-row claim that every emitted memory access satisfies its
`memoryAccessSpec` (byte-bus consequence triple) under the row's `clk_low`
and the access's per-operand offset. Uniform across all 24 chips —
matches the data flow of `memoryAccesses` + `offsets`. -/
def ChipRow.memoryAccessesValid (row : ChipRow p) : Prop :=
  let (_, clk_low) := row.clockComponents
  let accesses := row.memoryAccesses
  let offs := row.offsets
  ∀ p ∈ accesses.zip offs,
    SP1Clean.memoryAccessSpec clk_low p.2 p.1.1

/-- Trace-level memory-bus validity bundle: every row's
`memoryAccessesValid` holds. -/
def TraceMemoryAccessesValid (rows : List (ChipRow p)) : Prop :=
  ∀ row ∈ rows, row.memoryAccessesValid

/-- Add's per-chip discharge — vacuously true, since AddChip's memory
contributions now flow through the multiplicity-aware lookup bus emitted
inside `RTypeReader.Gated.assertion`. Mirrors `memoryAccessesValid_of_spec_addw`,
`_sub`, `_subw`, `_addi`. -/
theorem memoryAccessesValid_of_spec_add
    (_cols : SP1Clean.Add.AddCols (ZMod p))
    (_h : SP1Clean.Add.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.add _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- UType's per-chip discharge — vacuously true, since UTypeChip's
memory contributions now flow through the multiplicity-aware lookup bus
emitted inside `JTypeReader.Gated.assertion` (Phase 4 + (a)-shape
migration). Mirrors `memoryAccessesValid_of_spec_addi`. -/
theorem memoryAccessesValid_of_spec_uType
    (_cols : SP1Clean.UType.UTypeCols (ZMod p))
    (_h : SP1Clean.UType.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.uType _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- Jal's per-chip discharge — vacuously true, since JalChip's memory
contributions now flow through the multiplicity-aware lookup bus emitted
inside `JTypeReader.Gated.assertion` (canonical-(a) FormalSpec migration).
Mirrors `memoryAccessesValid_of_spec_uType`. -/
theorem memoryAccessesValid_of_spec_jal
    (_cols : SP1Clean.Jal.JalCols (ZMod p))
    (_h : SP1Clean.Jal.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.jal _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- Addi's per-chip discharge — vacuously true, since AddiChip's memory
contributions now flow through the multiplicity-aware lookup bus emitted
inside `ITypeReader.Gated.assertion`. Mirrors `memoryAccessesValid_of_spec_add`. -/
theorem memoryAccessesValid_of_spec_addi
    (_cols : SP1Clean.Addi.AddiCols (ZMod p))
    (_h : SP1Clean.Addi.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.addi _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- Branch's per-chip discharge — projects the two `OperandAccess.Assertion.Spec`
conjuncts. Branch emits 2 register reads (op_a/+4, op_b/+3) — no writes;
Branch updates PC only. -/
theorem memoryAccessesValid_of_spec_branch
    (cols : SP1Clean.Branch.BranchCols (ZMod p))
    (h : SP1Clean.Branch.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.branch cols) := by
  change SP1Clean.Branch.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_prog, _h_beq, _h_bne, _h_blt, _h_bge, _h_bltu, _h_bgeu,
          _h_sum, _h_addr_taken, _h_addr_unt, _h_branching_bool,
          _h_mux0, _h_mux1, _h_mux2, h_oa_a, h_oa_b⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right,
    SP1Clean.Branch.opAMemoryAccess, SP1Clean.Branch.opBMemoryAccess]
  intro entry h_mem
  rcases h_mem with h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b

/-- Jalr's per-chip discharge — projects the two `OperandAccess.Assertion.Spec`
conjuncts. Jalr emits 2 register accesses: op_a/+4 (return-address write)
and op_b/+3 (jump-target base register read). op_c is the I-type
immediate. -/
theorem memoryAccessesValid_of_spec_jalr
    (cols : SP1Clean.Jalr.JalrCols (ZMod p))
    (h : SP1Clean.Jalr.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.jalr cols) := by
  change SP1Clean.Jalr.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_prog, _h_gated, _h_isreal, _h_lowbit, _h_isreal_op_a_0,
          h_oa_a, h_oa_b⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right,
    SP1Clean.Jalr.opAMemoryAccess, SP1Clean.Jalr.opBMemoryAccess]
  intro entry h_mem
  rcases h_mem with h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b

/-- Sub's per-chip discharge — vacuously true, since SubChip's memory
contributions now flow through the multiplicity-aware lookup bus emitted
inside `RTypeReader.Gated.assertion`. Mirrors `memoryAccessesValid_of_spec_add`. -/
theorem memoryAccessesValid_of_spec_sub
    (_cols : SP1Clean.Sub.SubCols (ZMod p))
    (_h : SP1Clean.Sub.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.sub _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- Subw's per-chip discharge — vacuously true, since SubwChip's memory
contributions now flow through the multiplicity-aware lookup bus emitted
inside `RTypeReader.Gated.assertion`. Mirrors `memoryAccessesValid_of_spec_addw`. -/
theorem memoryAccessesValid_of_spec_subw
    (_cols : SP1Clean.Subw.SubwCols (ZMod p))
    (_h : SP1Clean.Subw.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.subw _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- Bitwise's per-chip discharge. -/
-- TODO(Spec-canonical-2026-05-26): `FormalSpec` was rewritten to the
-- canonical (a) shape (CPUState.Gated + ALUTypeReader.Gated). The
-- prior `OperandAccess.Assertion.Spec` triple is now nested inside
-- `ALUTypeReader.Gated.Assertion.Spec` as `RegisterAccess.Assertion.Spec`
-- (which wraps `OperandAccess.AssertionGated.Spec`). Mirrors the
-- `_mul` case immediately below. The right closure is likely
-- `simp [ChipRow.memoryAccessesValid, …]`-vacuous once
-- `ChipRow.memoryAccesses .bitwise` is empty (see
-- `feedback_memoryaccesses_vacuous_for_gated_chips`).
theorem memoryAccessesValid_of_spec_bitwise
    (_cols : SP1Clean.Bitwise.BitwiseCols (ZMod p))
    (_h : SP1Clean.Bitwise.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.bitwise _cols) :=
  sorry

/-- Lt's per-chip discharge. -/
-- TODO(Spec-canonical-2026-05-26): see `_bitwise` above. Same
-- structural shift; reader-gated form nests the operand-access
-- conjuncts inside `ALUTypeReader.Gated.Assertion.Spec`.
theorem memoryAccessesValid_of_spec_lt
    (_cols : SP1Clean.Lt.LtCols (ZMod p))
    (_h : SP1Clean.Lt.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.lt _cols) :=
  sorry

/-- Addw's per-chip discharge — vacuously true, since AddwChip's memory
contributions now flow through the multiplicity-aware lookup bus rather
than the unconditional `memoryAccesses` aggregator (see Phase 4–5 of
`docs/MULTIPLICITY_BUS.md`). The op_c access in particular needs to be
gated by `is_real - imm_c`, which `memoryAccesses` cannot express. -/
theorem memoryAccessesValid_of_spec_addw
    (_cols : SP1Clean.Addw.AddwCols (ZMod p))
    (_h : SP1Clean.Addw.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.addw _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- StoreByte's per-chip discharge — vacuously true, since StoreByteChip's
memory contributions (op_a / op_b register reads + store-side RAM
read-then-write) now flow through the multiplicity-aware lookup bus.
Mirrors `memoryAccessesValid_of_spec_addw`. -/
theorem memoryAccessesValid_of_spec_storeByte
    (_cols : SP1Clean.StoreByte.StoreByteCols (ZMod p))
    (_h : SP1Clean.StoreByte.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.storeByte _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- StoreHalf's per-chip discharge — same shape as `_storeByte`. -/
theorem memoryAccessesValid_of_spec_storeHalf
    (_cols : SP1Clean.StoreHalf.StoreHalfCols (ZMod p))
    (_h : SP1Clean.StoreHalf.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.storeHalf _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- StoreWord's per-chip discharge — same shape as `_storeByte`. -/
theorem memoryAccessesValid_of_spec_storeWord
    (_cols : SP1Clean.StoreWord.StoreWordCols (ZMod p))
    (_h : SP1Clean.StoreWord.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.storeWord _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- StoreDouble's per-chip discharge — same shape as `_storeByte`. -/
theorem memoryAccessesValid_of_spec_storeDouble
    (_cols : SP1Clean.StoreDouble.StoreDoubleCols (ZMod p))
    (_h : SP1Clean.StoreDouble.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.storeDouble _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- LoadByte's per-chip discharge — vacuously true, since LoadByteChip's
memory contributions (op_a register write + op_b register read + load-side
RAM read) now flow through the multiplicity-aware lookup bus. The
disjunctive multiplicity (`is_lb + is_lbu` shared, `is_lb` for MSB) makes
the bus the canonical home. -/
theorem memoryAccessesValid_of_spec_loadByte
    (_cols : SP1Clean.LoadByte.LoadByteCols (ZMod p))
    (_h : SP1Clean.LoadByte.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.loadByte _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- LoadHalf's per-chip discharge — same shape as `_loadByte`, with
multiplicities `is_lh + is_lhu` (shared) and `is_lh` (MSB). -/
theorem memoryAccessesValid_of_spec_loadHalf
    (_cols : SP1Clean.LoadHalf.LoadHalfCols (ZMod p))
    (_h : SP1Clean.LoadHalf.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.loadHalf _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- LoadWord's per-chip discharge — multiplicities `is_lw + is_lwu` (shared)
and `is_lw` (MSB). -/
theorem memoryAccessesValid_of_spec_loadWord
    (_cols : SP1Clean.LoadWord.LoadWordCols (ZMod p))
    (_h : SP1Clean.LoadWord.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.loadWord _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- LoadDouble's per-chip discharge — single multiplicity `is_real` (LD only,
no unsigned variant). -/
theorem memoryAccessesValid_of_spec_loadDouble
    (_cols : SP1Clean.LoadDouble.LoadDoubleCols (ZMod p))
    (_h : SP1Clean.LoadDouble.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.loadDouble _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- LoadX0's per-chip discharge — multiplicity is the 7-way sum
`is_lb + is_lbu + is_lh + is_lhu + is_lw + is_lwu + is_ld` (one variant
active per row). op_a write_value is zero (destination is x0). -/
theorem memoryAccessesValid_of_spec_loadX0
    (_cols : SP1Clean.LoadX0.LoadX0Cols (ZMod p))
    (_h : SP1Clean.LoadX0.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.loadX0 _cols) := by
  simp [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses, ChipRow.offsets]

/-- Mul's per-chip discharge — sorry'd after MulChip's `FormalSpec` was
restructured to compose `MulOp.assertion` + `CPUState.Gated` +
`RTypeReader.Gated` (CLEAN_FUTURE D2/D3 alignment). The OperandAccess
conjuncts that this destructure extracted are now nested inside
`RTypeReader.Gated.Assertion.Spec` as `RegisterAccess.Assertion.Spec`
(which wraps `OperandAccess.AssertionGated.Spec`). Re-deriving the
flat `OperandAccess.Assertion.Spec` from there is a follow-up; the
sorry tracks the structural gap. -/
theorem memoryAccessesValid_of_spec_mul [Fact (2 ^ 24 < p)]
    (cols : SP1Clean.Mul.MulCols (ZMod p))
    (h : SP1Clean.Mul.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.mul cols) := by
  sorry

/-- ShiftLeft's per-chip discharge. -/
-- TODO(Spec-canonical-2026-05-26): see `_bitwise` above. Same shift to
-- the gated reader form; operand accesses now nested in
-- `ALUTypeReader.Gated.Assertion.Spec`.
theorem memoryAccessesValid_of_spec_shiftLeft
    (_cols : SP1Clean.ShiftLeft.ShiftLeftCols (ZMod p))
    (_h : SP1Clean.ShiftLeft.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.shiftLeft _cols) :=
  sorry

/-- ShiftRight's per-chip discharge. -/
-- TODO(Spec-canonical-2026-05-26): see `_bitwise` above.
theorem memoryAccessesValid_of_spec_shiftRight
    (_cols : SP1Clean.ShiftRight.ShiftRightCols (ZMod p))
    (_h : SP1Clean.ShiftRight.assertion.Spec _cols) :
    ChipRow.memoryAccessesValid (.shiftRight _cols) :=
  sorry

/-- DivRem's per-chip discharge — sorry'd after DivRemChip's
`FormalSpec` was restructured to compose 17 sub-circuits + 2 reader
Gated assertions (CLEAN_FUTURE D2/D3 alignment). See the parallel
comment on `memoryAccessesValid_of_spec_mul`. -/
theorem memoryAccessesValid_of_spec_divRem [Fact (2 ^ 24 < p)]
    (cols : SP1Clean.DivRem.DivRemCols (ZMod p))
    (h : SP1Clean.DivRem.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.divRem cols) := by
  sorry

/-- Trace-level memory-bus grounding: from per-row chip Specs + a
verifier-supplied `TraceMemoryAccessesValid` bundle for the 23 chips whose
per-chip discharge is deferred. Add's contribution is fully grounded from
its `FormalSpec` via `memoryAccessesValid_of_spec_add`.

The discharge architecture: at completion of sub-task E (widening 23 more
chips' `FormalSpec`s with `OperandAccess.Assertion.Spec` conjuncts), the
`h_link` hypothesis becomes derivable and can be dropped. -/
theorem traceMemoryAccessesValid_of_chip_specs [Fact (2 ^ 24 < p)]
    (rows : List (ChipRow p))
    (_h_specs : ∀ row ∈ rows, ChipRow.Spec row)
    (h_link : TraceMemoryAccessesValid rows) :
    TraceMemoryAccessesValid rows :=
  h_link

end SP1Clean.Soundness
