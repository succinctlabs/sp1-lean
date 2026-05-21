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
        #v[cols.result_byte + 65280 * cols.signed_extension_flag,
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
      -- (cols.store_write_value at the current timestamp) is supplied
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
      [(op_a_mem, #v[cols.compare_bit, 0, 0, 0]),
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

/-- The chip-row's `clk_high` and (composed) `clk_low` for the per-access
timestamp encoding `clk_high * 2^24 + clk_low + offset`. -/
def clockComponents : ChipRow p → ZMod p × ZMod p
  | .add cols => (cols.clk_high, cols.clk_0_16 + cols.clk_16_24 * 65536)
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

/-- The chip-row's natural Spec predicate (the propositional content the
chip's FormalAssertion / iff_sp1 establishes). -/
def Spec : ChipRow p → Prop
  | .add cols => SP1Clean.Add.assertion.Spec cols
  | .loadByte cols => SP1Clean.LoadByte.Spec cols
  | .storeByte cols => SP1Clean.StoreByte.Spec cols
  | .jal cols => SP1Clean.Jal.Spec cols
  | .mul cols => SP1Clean.Mul.Spec cols
  | .shiftLeft cols => SP1Clean.ShiftLeft.Spec cols
  | .addw cols => SP1Clean.Addw.Spec cols
  | .uType cols => SP1Clean.UType.Spec cols
  | .jalr cols => SP1Clean.Jalr.Spec cols
  | .lt cols => SP1Clean.Lt.Spec cols
  | .storeWord cols => SP1Clean.StoreWord.Spec cols
  | .storeDouble cols => SP1Clean.StoreDouble.Spec cols
  | .storeHalf cols => SP1Clean.StoreHalf.Spec cols
  | .loadDouble cols => SP1Clean.LoadDouble.Spec cols
  | .loadWord cols => SP1Clean.LoadWord.Spec cols
  | .loadHalf cols => SP1Clean.LoadHalf.Spec cols
  | .branch cols => SP1Clean.Branch.Spec cols
  | .loadX0 cols => SP1Clean.LoadX0.Spec cols
  | .shiftRight cols => SP1Clean.ShiftRight.Spec cols
  | .divRem cols => SP1Clean.DivRem.Spec cols

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

end SP1Clean.Soundness
