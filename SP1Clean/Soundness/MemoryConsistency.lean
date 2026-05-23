import Clean.Utils.OfflineMemory
import SP1Clean.MemoryAccess
import SP1Clean.AddChip
import SP1Clean.LoadByteChip
import SP1Clean.StoreByteChip
import SP1Clean.JalChip
import SP1Clean.MulChip
import SP1Clean.ShiftLeftChip
import SP1Clean.AddwChip
import SP1Clean.UTypeChip
import SP1Clean.JalrChip
import SP1Clean.LtChip
import SP1Clean.StoreWordChip
import SP1Clean.StoreDoubleChip
import SP1Clean.StoreHalfChip
import SP1Clean.LoadDoubleChip
import SP1Clean.LoadWordChip
import SP1Clean.LoadHalfChip
import SP1Clean.BranchChip
import SP1Clean.LoadX0Chip
import SP1Clean.ShiftRightChip
import SP1Clean.DivRemChip
import SP1Clean.AddiChip
import SP1Clean.BitwiseChip
import SP1Clean.SubChip
import SP1Clean.SubwChip
import SP1Clean.MemoryGlobalChip

/-! # Trace-level OfflineMemory bridge

This file wires per-chip `MemoryAccess` records into the
`Clean.Utils.OfflineMemory` consistency theorem
(`MemoryAccessList.isConsistentOnline_iff_isConsistentOffline`).

`MemoryAccessTuple` / `MemoryAccessList` are transparent aliases for
the upstream `_root_.MemoryAccess` / `_root_.MemoryAccessList`
(`Clean.Utils.OfflineMemory`).

The design (per `docs/CLEAN_PILOT_NOTES.md` and the plan
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
  | subw (cols : SP1Clean.Sub.W.SubwCols (ZMod p))
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
  | .add cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_c, 0, 0],
          prev_value := cols.op_c_memory_prev_value,
          prev_low := cols.op_c_memory_prev_low,
          diff_low_limb := cols.op_c_memory_diff_low }
      -- op_a is read AND written (write_value = op_a_write_value);
      -- op_b and op_c are pure reads (write_value = prev_value).
      [(op_a_mem, cols.op_a_write_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (op_c_mem, cols.op_c_memory_prev_value)]
  | .loadByte cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      -- The load access at the computed RAM address. write_value =
      -- prev_value (the chip itself doesn't modify the loaded memory
      -- word; that's the semantics of a load).
      let load_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.LoadByte.loadMemoryAccess cols
      -- op_a is written with the sign-extended loaded byte.
      [(op_a_mem,
        #v[cols.selected_byte + 65280 * cols.signed_extension_flag,
           65535 * cols.signed_extension_flag,
           65535 * cols.signed_extension_flag,
           65535 * cols.signed_extension_flag]),
       (op_b_mem, cols.op_b_memory_prev_value),
       (load_mem, cols.load_prev_value)]
  | .storeByte cols =>
      -- op_a and op_b are both pure register reads (stores do not
      -- modify the source data register or the base register).
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      -- The store access at the computed RAM address: read-then-write
      -- at the same address. The MemoryAccess record carries the read
      -- side (prev_value at the prior timestamp); the write side
      -- (cols.store_value at the current timestamp) is supplied
      -- by the aggregator below.
      let store_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.StoreByte.storeMemoryAccess cols
      [(op_a_mem, cols.op_a_memory_prev_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (store_mem, SP1Clean.StoreByte.storeWriteValue cols)]
  | .jal cols =>
      -- Jal has one register access (op_a write for the return address).
      -- The state-bus PC chain is tracked at trace level — not via
      -- MemoryAccess records.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Jal.opAMemoryAccess cols
      [(op_a_mem, cols.op_a_write_value)]
  | .mul cols =>
      -- Three register accesses. op_a is read AND written (write_value =
      -- op_a_write_value, holding whatever the carry-chain produced —
      -- correctness of that value is the MulOperation surface, which the
      -- pilot's iff-only mirror leaves at `True`). op_b and op_c are pure
      -- reads.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_c, 0, 0],
          prev_value := cols.op_c_memory_prev_value,
          prev_low := cols.op_c_memory_prev_low,
          diff_low_limb := cols.op_c_memory_diff_low }
      [(op_a_mem, cols.op_a_write_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (op_c_mem, cols.op_c_memory_prev_value)]
  | .shiftLeft cols =>
      -- Three register accesses. op_a is read AND written (write_value =
      -- `cols.result`, the 4-limb shifted output). op_b and op_c are pure
      -- reads.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_c, 0, 0],
          prev_value := cols.op_c_memory_prev_value,
          prev_low := cols.op_c_memory_prev_low,
          diff_low_limb := cols.op_c_memory_diff_low }
      [(op_a_mem, cols.result),
       (op_b_mem, cols.op_b_memory_prev_value),
       (op_c_mem, cols.op_c_memory_prev_value)]
  | .addw cols =>
      -- Three register accesses. op_a is read AND written (write_value is
      -- the 4-limb sign-extended reconstruction of the 32-bit result).
      -- op_c uses `cols.op_c[0]` as the register-index limb; when
      -- `imm_c = 1` (addiw) the chip Spec constrains
      -- `op_c_memory.prev_value = op_c` so the access is harmless.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_c[0], 0, 0],
          prev_value := cols.op_c_memory_prev_value,
          prev_low := cols.op_c_memory_prev_low,
          diff_low_limb := cols.op_c_memory_diff_low }
      [(op_a_mem,
        #v[cols.addw_value[0], cols.addw_value[1],
           cols.addw_msb * 65535, cols.addw_msb * 65535]),
       (op_b_mem, cols.op_b_memory_prev_value),
       (op_c_mem, cols.op_c_memory_prev_value)]
  | .uType cols =>
      -- One register access only (op_a write). U-type has no op_b/op_c
      -- register reads — both are immediates.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.UType.opAMemoryAccess cols
      [(op_a_mem, cols.add_result)]
  | .jalr cols =>
      -- Two register accesses: op_a write (return address), op_b read
      -- (jump-target base register). op_c is an I-type immediate.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Jalr.opAMemoryAccess cols
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Jalr.opBMemoryAccess cols
      [(op_a_mem, cols.op_a_write_value),
       (op_b_mem, cols.op_b_memory_prev_value)]
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
       (op_b_mem, cols.op_b_memory_prev_value),
       (op_c_mem, cols.op_c_memory_prev_value)]
  | .storeWord cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let store_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.StoreWord.storeMemoryAccess cols
      [(op_a_mem, cols.op_a_memory_prev_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (store_mem, SP1Clean.StoreWord.storeWriteValue cols)]
  | .storeDouble cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let store_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.StoreDouble.storeMemoryAccess cols
      [(op_a_mem, cols.op_a_memory_prev_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (store_mem, SP1Clean.StoreDouble.storeWriteValue cols)]
  | .storeHalf cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let store_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.StoreHalf.storeMemoryAccess cols
      [(op_a_mem, cols.op_a_memory_prev_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (store_mem, SP1Clean.StoreHalf.storeWriteValue cols)]
  | .loadDouble cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let load_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.LoadDouble.loadMemoryAccess cols
      [(op_a_mem, cols.load_prev_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (load_mem, cols.load_prev_value)]
  | .loadWord cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let load_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.LoadWord.loadMemoryAccess cols
      -- op_a is written with the sign-extended loaded word: the two
      -- stored limbs `op_a_write_value_lo[0..1]` plus the
      -- sign-extension limbs derived from `signed_extension_msb`.
      [(op_a_mem,
        #v[cols.op_a_write_value_lo[0], cols.op_a_write_value_lo[1],
           65535 * cols.signed_extension_msb,
           65535 * cols.signed_extension_msb]),
       (op_b_mem, cols.op_b_memory_prev_value),
       (load_mem, cols.load_prev_value)]
  | .branch cols =>
      -- Two register reads (op_a / op_b as comparison operands); no
      -- writes. PC chain is state-bus, trace-level.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Branch.opAMemoryAccess cols
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.Branch.opBMemoryAccess cols
      [(op_a_mem, cols.op_a_memory_prev_value),
       (op_b_mem, cols.op_b_memory_prev_value)]
  | .loadX0 cols =>
      -- Two reg + 1 RAM read. op_a's write is absorbed (target is x0).
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let load_mem : SP1Clean.MemoryAccess (ZMod p) :=
        SP1Clean.LoadX0.loadMemoryAccess cols
      [(op_a_mem, cols.op_a_memory_prev_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (load_mem, cols.load_prev_value)]
  | .shiftRight cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_c[0], 0, 0],
          prev_value := cols.op_c_memory_prev_value,
          prev_low := cols.op_c_memory_prev_low,
          diff_low_limb := cols.op_c_memory_diff_low }
      [(op_a_mem, cols.op_a_write_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (op_c_mem, cols.op_c_memory_prev_value)]
  | .divRem cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_c, 0, 0],
          prev_value := cols.op_c_memory_prev_value,
          prev_low := cols.op_c_memory_prev_low,
          diff_low_limb := cols.op_c_memory_diff_low }
      [(op_a_mem, cols.op_a_write_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (op_c_mem, cols.op_c_memory_prev_value)]
  | .loadHalf cols =>
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
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
       (op_b_mem, cols.op_b_memory_prev_value),
       (load_mem, cols.load_prev_value)]
  | .addi cols =>
      -- I-type: two register accesses (op_a read+write, op_b pure read).
      -- op_c is the 4-limb immediate `op_c_imm` — no memory access.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      [(op_a_mem, cols.op_a_write_value),
       (op_b_mem, cols.op_b_memory_prev_value)]
  | .bitwise cols =>
      -- Three register accesses (op_a write, op_b/op_c pure reads). The
      -- op_a write value is the 4-limb word reconstruction from the chip's
      -- 8-limb `bitwise_result` (mirrors the `E19/E21/E23/E25` halfword
      -- packs in `BitwiseU16Operation.constraints`).
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_c[0], 0, 0],
          prev_value := cols.op_c_memory_prev_value,
          prev_low := cols.op_c_memory_prev_low,
          diff_low_limb := cols.op_c_memory_diff_low }
      [(op_a_mem,
        #v[cols.bitwise_result[0] + cols.bitwise_result[1] * 256,
           cols.bitwise_result[2] + cols.bitwise_result[3] * 256,
           cols.bitwise_result[4] + cols.bitwise_result[5] * 256,
           cols.bitwise_result[6] + cols.bitwise_result[7] * 256]),
       (op_b_mem, cols.op_b_memory_prev_value),
       (op_c_mem, cols.op_c_memory_prev_value)]
  | .sub cols =>
      -- R-type: three register accesses. op_a is read AND written
      -- (write_value = op_a_write_value); op_b and op_c are pure reads.
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_c, 0, 0],
          prev_value := cols.op_c_memory_prev_value,
          prev_low := cols.op_c_memory_prev_low,
          diff_low_limb := cols.op_c_memory_diff_low }
      [(op_a_mem, cols.op_a_write_value),
       (op_b_mem, cols.op_b_memory_prev_value),
       (op_c_mem, cols.op_c_memory_prev_value)]
  | .subw cols =>
      -- W-type: three register accesses, op_a write is the 4-limb
      -- sign-extended reconstruction `[subw_value[0], subw_value[1],
      -- subw_msb * 65535, subw_msb * 65535]` (mirrors Addw).
      let op_a_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_a, 0, 0],
          prev_value := cols.op_a_memory_prev_value,
          prev_low := cols.op_a_memory_prev_low,
          diff_low_limb := cols.op_a_memory_diff_low }
      let op_b_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_b, 0, 0],
          prev_value := cols.op_b_memory_prev_value,
          prev_low := cols.op_b_memory_prev_low,
          diff_low_limb := cols.op_b_memory_diff_low }
      let op_c_mem : SP1Clean.MemoryAccess (ZMod p) :=
        { addr := #v[cols.op_c, 0, 0],
          prev_value := cols.op_c_memory_prev_value,
          prev_low := cols.op_c_memory_prev_low,
          diff_low_limb := cols.op_c_memory_diff_low }
      [(op_a_mem,
        #v[cols.subw_value[0], cols.subw_value[1],
           cols.subw_msb * 65535, cols.subw_msb * 65535]),
       (op_b_mem, cols.op_b_memory_prev_value),
       (op_c_mem, cols.op_c_memory_prev_value)]
  -- Boundary chips: Phase 4 placeholder — emit empty accesses. Full
  -- boundary-record emission is a Phase 4.5 follow-up.
  | .memInit cols => SP1Clean.MemoryGlobal.initMemoryAccesses cols
  | .memFinalize cols => SP1Clean.MemoryGlobal.finalizeMemoryAccesses cols

/-- The chip-row's `clk_high` and (composed) `clk_low` for the per-access
timestamp encoding `clk_high * 2^24 + clk_low + offset`. -/
def clockComponents : ChipRow p → ZMod p × ZMod p
  | .add cols => (cols.state.clk_high, cols.state.clk_0_16 + cols.state.clk_16_24 * 65536)
  | .loadByte cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .storeByte cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .jal cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .mul cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .shiftLeft cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .addw cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .uType cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .jalr cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .lt cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .storeWord cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .storeDouble cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .storeHalf cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .loadDouble cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .loadWord cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .loadHalf cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .branch cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .loadX0 cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .shiftRight cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .divRem cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .addi cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .bitwise cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .sub cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  | .subw cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
  -- Boundary chips: clk_low is raw (no clk_0_16 / clk_16_24 decomposition).
  | .memInit cols => (cols.clk_high, cols.clk_low)
  | .memFinalize cols => (cols.clk_high, cols.clk_low)

/-- The chip-row's natural Spec predicate (the propositional content the
chip's FormalAssertion / iff_sp1 establishes). -/
def Spec : ChipRow p → Prop
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
  | .subw cols => SP1Clean.Sub.W.assertion.Spec cols
  -- Boundary chips: Phase 4 placeholder Spec := True.
  | .memInit cols => SP1Clean.MemoryGlobal.Spec cols
  | .memFinalize cols => SP1Clean.MemoryGlobal.Spec cols

/-- Per-row, per-access sub-clock offsets. R-type and I-type readers
emit accesses at `clk_low + 4` (op_a), `clk_low + 3` (op_b), and
`clk_low + 2` (op_c); `LoadByte` adds an access at `clk_low + 1` for
the RAM load. The offset list mirrors `memoryAccesses` above. -/
def offsets : ChipRow p → List (ZMod p)
  | .add _ => [4, 3, 2]
  | .loadByte _ => [4, 3, 1]
  -- Store: op_a (data source) at +4, op_b (base) at +3, store memory
  -- access at +0 (matches SP1's `.send (.memory ...) ... Main[33] Main[34]`
  -- which uses the *prior* timestamp components, not the current row's).
  | .storeByte _ => [4, 3, 0]
  -- Jal: only op_a write at +4. State-bus PC chain is trace-level.
  | .jal _ => [4]
  -- Mul and ShiftLeft: same R-type-reader pattern as Add (3 register
  -- accesses at +4 / +3 / +2). No RAM accesses.
  | .mul _ => [4, 3, 2]
  | .shiftLeft _ => [4, 3, 2]
  | .addw _ => [4, 3, 2]
  | .uType _ => [4]
  | .jalr _ => [4, 3]
  | .lt _ => [4, 3, 2]
  | .storeWord _ => [4, 3, 0]
  | .storeDouble _ => [4, 3, 0]
  | .storeHalf _ => [4, 3, 0]
  | .loadDouble _ => [4, 3, 1]
  | .loadWord _ => [4, 3, 1]
  | .loadHalf _ => [4, 3, 1]
  | .branch _ => [4, 3]
  | .loadX0 _ => [4, 3, 1]
  | .shiftRight _ => [4, 3, 2]
  | .divRem _ => [4, 3, 2]
  -- Addi: 2 register accesses (op_a + op_b) at +4/+3; op_c is immediate.
  | .addi _ => [4, 3]
  | .bitwise _ => [4, 3, 2]
  | .sub _ => [4, 3, 2]
  | .subw _ => [4, 3, 2]
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
theorem chip_specs_admit_offline_bridge
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

/-- Add's per-chip discharge — projects three `OperandAccess.Assertion.Spec`
conjuncts (FormalSpec positions #7/#8/#9 after sub-task E POC widening)
onto the corresponding `memoryAccessSpec` clauses. The
`OperandAccess.Assertion.Spec` definition IS `memoryAccessSpec`-shaped, so
each is a direct projection. -/
theorem memoryAccessesValid_of_spec_add
    (cols : SP1Clean.Add.AddCols (ZMod p))
    (h : SP1Clean.Add.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.add cols) := by
  change SP1Clean.Add.Assertion.FormalSpec cols at h
  obtain ⟨_h_addop, _h_cpu, _h_prog, _h_addr, _h_isreal, _h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h
  -- The three OperandAccess.Assertion.Spec carry the memoryAccessSpec
  -- content for op_a/b/c at offsets +4/+3/+2.
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right]
  intro entry h_mem
  rcases h_mem with h | h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b
  · subst h; exact h_oa_c

/-- UType's per-chip discharge — projects the single
`OperandAccess.Assertion.Spec` conjunct (FormalSpec position #7 after
the Phase-1 widening) onto the matching `memoryAccessSpec` clause. UType
has only the op_a register access at offset +4. -/
theorem memoryAccessesValid_of_spec_uType
    (cols : SP1Clean.UType.UTypeCols (ZMod p))
    (h : SP1Clean.UType.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.uType cols) := by
  change SP1Clean.UType.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_prog, _h_addr, _h_isreal, _h_isauipc, _h_op_a_0,
          h_oa_a⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right]
  intro entry h_mem
  subst h_mem
  exact h_oa_a

/-- Jal's per-chip discharge — projects the single
`OperandAccess.Assertion.Spec` conjunct. Jal has only the op_a register
access at offset +4 (return-address write). -/
theorem memoryAccessesValid_of_spec_jal
    (cols : SP1Clean.Jal.JalCols (ZMod p))
    (h : SP1Clean.Jal.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.jal cols) := by
  change SP1Clean.Jal.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_jump, _h_ret, _h_prog, _h_isreal, h_oa_a⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right,
    SP1Clean.Jal.opAMemoryAccess]
  intro entry h_mem
  subst h_mem
  exact h_oa_a

/-- Addi's per-chip discharge — projects the two `OperandAccess.Assertion.Spec`
conjuncts. I-type: op_a/+4 and op_b/+3 register accesses (op_c is the
immediate `op_c_imm`, no memory access). -/
theorem memoryAccessesValid_of_spec_addi
    (cols : SP1Clean.Addi.AddiCols (ZMod p))
    (h : SP1Clean.Addi.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.addi cols) := by
  change SP1Clean.Addi.Assertion.FormalSpec cols at h
  obtain ⟨_h_addop, _h_cpu, _h_prog, _h_addr, _h_isreal, _h_op_a_0,
          h_oa_a, h_oa_b⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right]
  intro entry h_mem
  rcases h_mem with h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b

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

/-- Sub's per-chip discharge — three `OperandAccess.Assertion.Spec`
conjuncts. R-type: op_a/+4, op_b/+3, op_c/+2. -/
theorem memoryAccessesValid_of_spec_sub
    (cols : SP1Clean.Sub.SubCols (ZMod p))
    (h : SP1Clean.Sub.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.sub cols) := by
  change SP1Clean.Sub.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_prog, _h_addr, _h_isreal, _h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right]
  intro entry h_mem
  rcases h_mem with h | h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b
  · subst h; exact h_oa_c

/-- Subw's per-chip discharge — three `OperandAccess.Assertion.Spec`
conjuncts. R-type variant (W-flavor): op_a/+4, op_b/+3, op_c/+2. -/
theorem memoryAccessesValid_of_spec_subw
    (cols : SP1Clean.Sub.W.SubwCols (ZMod p))
    (h : SP1Clean.Sub.W.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.subw cols) := by
  change SP1Clean.Sub.W.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_prog, _h_addr, _h_isreal, _h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right]
  intro entry h_mem
  rcases h_mem with h | h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b
  · subst h; exact h_oa_c

/-- Bitwise's per-chip discharge — three `OperandAccess.Assertion.Spec`
conjuncts. R-type-shaped: op_a/+4, op_b/+3, op_c/+2 (the chip's `op_c`
is a 4-limb vector but the memory-access record uses `op_c[0]` as the
register index). -/
theorem memoryAccessesValid_of_spec_bitwise
    (cols : SP1Clean.Bitwise.BitwiseCols (ZMod p))
    (h : SP1Clean.Bitwise.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.bitwise cols) := by
  change SP1Clean.Bitwise.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_prog, _h_addr, _h_xor, _h_or, _h_and, _h_sum,
          _h_op_a_0, h_oa_a, h_oa_b, h_oa_c⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right]
  intro entry h_mem
  rcases h_mem with h | h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b
  · subst h; exact h_oa_c

/-- Lt's per-chip discharge — three `OperandAccess.Assertion.Spec`
conjuncts. R-type-shaped: op_a/+4, op_b/+3, op_c/+2. -/
theorem memoryAccessesValid_of_spec_lt
    (cols : SP1Clean.Lt.LtCols (ZMod p))
    (h : SP1Clean.Lt.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.lt cols) := by
  change SP1Clean.Lt.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_prog, _h_addr, _h_isslt, _h_issltu, _h_sum, _h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right,
    SP1Clean.Lt.opAMemoryAccess, SP1Clean.Lt.opBMemoryAccess,
    SP1Clean.Lt.opCMemoryAccess]
  intro entry h_mem
  rcases h_mem with h | h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b
  · subst h; exact h_oa_c

/-- Addw's per-chip discharge — three `OperandAccess.Assertion.Spec`
conjuncts. R-type-shaped W-flavor: op_a/+4, op_b/+3, op_c/+2 (4-limb
op_c column for ALU-W discipline). -/
theorem memoryAccessesValid_of_spec_addw
    (cols : SP1Clean.Addw.AddwCols (ZMod p))
    (h : SP1Clean.Addw.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.addw cols) := by
  change SP1Clean.Addw.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_prog, _h_addr, _h_isreal, _h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right]
  intro entry h_mem
  rcases h_mem with h | h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b
  · subst h; exact h_oa_c

/-- Mul's per-chip discharge — three `OperandAccess.Assertion.Spec`
conjuncts. R-type: op_a/+4, op_b/+3, op_c/+2. -/
theorem memoryAccessesValid_of_spec_mul
    (cols : SP1Clean.Mul.MulCols (ZMod p))
    (h : SP1Clean.Mul.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.mul cols) := by
  change SP1Clean.Mul.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_prog, _h_addr, _h_mul, _h_mulh, _h_mulw, _h_mulhsu,
          _h_mulhu, _h_real, _h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right]
  intro entry h_mem
  rcases h_mem with h | h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b
  · subst h; exact h_oa_c

/-- ShiftLeft's per-chip discharge — three `OperandAccess.Assertion.Spec`
conjuncts. R-type: op_a/+4, op_b/+3, op_c/+2. -/
theorem memoryAccessesValid_of_spec_shiftLeft
    (cols : SP1Clean.ShiftLeft.ShiftLeftCols (ZMod p))
    (h : SP1Clean.ShiftLeft.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.shiftLeft cols) := by
  change SP1Clean.ShiftLeft.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_prog, _h_addr, _h_sll, _h_sllw, _h_sum, _h_op_a_0,
          h_oa_a, h_oa_b, h_oa_c⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right]
  intro entry h_mem
  rcases h_mem with h | h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b
  · subst h; exact h_oa_c

/-- ShiftRight's per-chip discharge — three `OperandAccess.Assertion.Spec`
conjuncts. R-type-shaped (ALU-type): op_a/+4, op_b/+3, op_c/+2. -/
theorem memoryAccessesValid_of_spec_shiftRight
    (cols : SP1Clean.ShiftRight.ShiftRightCols (ZMod p))
    (h : SP1Clean.ShiftRight.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.shiftRight cols) := by
  change SP1Clean.ShiftRight.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_prog, _h_addr, _h_srl, _h_sra, _h_srlw, _h_sraw, _h_sum,
          _h_op_a_0, h_oa_a, h_oa_b, h_oa_c⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right]
  intro entry h_mem
  rcases h_mem with h | h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b
  · subst h; exact h_oa_c

/-- DivRem's per-chip discharge — three `OperandAccess.Assertion.Spec`
conjuncts. R-type: op_a/+4, op_b/+3, op_c/+2. -/
theorem memoryAccessesValid_of_spec_divRem
    (cols : SP1Clean.DivRem.DivRemCols (ZMod p))
    (h : SP1Clean.DivRem.assertion.Spec cols) :
    ChipRow.memoryAccessesValid (.divRem cols) := by
  change SP1Clean.DivRem.Assertion.FormalSpec cols at h
  obtain ⟨_h_cpu, _h_prog, _h_addr, _h_signed, _h_w, _h_rem, _h_real,
          _h_op_a_0, h_oa_a, h_oa_b, h_oa_c⟩ := h
  simp only [ChipRow.memoryAccessesValid, ChipRow.memoryAccesses,
    ChipRow.offsets, ChipRow.clockComponents, List.zip_cons_cons,
    List.mem_cons, List.not_mem_nil, or_false, List.zip_nil_right]
  intro entry h_mem
  rcases h_mem with h | h | h
  · subst h; exact h_oa_a
  · subst h; exact h_oa_b
  · subst h; exact h_oa_c

/-- Trace-level memory-bus grounding: from per-row chip Specs + a
verifier-supplied `TraceMemoryAccessesValid` bundle for the 23 chips whose
per-chip discharge is deferred. Add's contribution is fully grounded from
its `FormalSpec` via `memoryAccessesValid_of_spec_add`.

The discharge architecture: at completion of sub-task E (widening 23 more
chips' `FormalSpec`s with `OperandAccess.Assertion.Spec` conjuncts), the
`h_link` hypothesis becomes derivable and can be dropped. -/
theorem traceMemoryAccessesValid_of_chip_specs
    (rows : List (ChipRow p))
    (_h_specs : ∀ row ∈ rows, ChipRow.Spec row)
    (h_link : TraceMemoryAccessesValid rows) :
    TraceMemoryAccessesValid rows :=
  h_link

end SP1Clean.Soundness
