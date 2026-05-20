import SP1Foundations.Constraint
import SP1Foundations.Field
import SP1Foundations.Word
import SP1Foundations.MemoryConsistency

/-! # Clean-side mirror of SP1's memory-bus interactions

This file defines the per-row record `MemoryAccess` plus the per-row
predicate `memoryAccessSpec` that mirrors the timestamp / U64 clauses
surfaced by SP1's reader-level `_poly` iff lemmas (R-type, I-type,
ALU-type) for each memory bus interaction.

The clauses come from `_root_.RTypeReader.allHold_constraints_iff_is_real_poly`'s
RHS in `SP1Operations/Reader/RTypeReader.lean` and the parallel
`AirInteraction.memory` semantics in `SP1Foundations/Constraint.lean:44-45`
(per-row: `Word.isU64_poly` on the 4-limb value).

`MemoryAccess` carries only the **read side** of an access — `prev_value`
plus the prior-access timestamp components. The write side (when present,
e.g. for `op_a` register writes or store instructions) is held by the
chip's own column struct and combined with this record at OfflineMemory
aggregation time (see `SP1Clean/Soundness/MemoryConsistency.lean`).

Per the pilot's stateless-table convention, SP1's send/receive
multiplicities are dropped — `is_real = 1` and `is_trusted = 1` discharge
the `mult ≠ 0` guards at the reader level. Cross-row consistency lives in
the trace-level OfflineMemory bridge, not here.
-/

namespace SP1Clean

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Per-row memory access record. Read-side only: the 3-limb address plus
the prior `(prev_value, prev_low, diff_low_limb)` triple SP1 carries on
each memory bus send.

For register reads, `addr = #v[reg_index, 0, 0]` and `prev_value` is the
4-limb encoding of the register's 64-bit value. For RAM accesses, the
3-limb address decodes the byte address and `prev_value` is the 4-limb
encoding of the 64-bit memory word at that address. -/
structure MemoryAccess (T : Type) where
  addr : Vector T 3
  prev_value : Word T
  prev_low : T
  diff_low_limb : T

/-- Per-row spec for a memory access. Matches the clauses surfaced by
`_root_.RTypeReader.allHold_constraints_iff_is_real_poly` for each
operand:

- `diff_low_limb.val < 65536` (Nat-level limb bound)
- `(clk_low + offset - prev_low - 1 - diff_low_limb) * 65536⁻¹ < 256`
  (field-level scaled timestamp bound)
- `Word.isU64_poly prev_value` (the 4 limbs each fit in 16 bits)

The `offset` parameter is the per-operand sub-clock offset SP1's constraint
compiler emits (e.g., `+2` for `op_c`, `+3` for `op_b`, `+4` for `op_a` on
R-type reads). -/
def memoryAccessSpec (clk_low offset : ZMod p) (acc : MemoryAccess (ZMod p)) : Prop :=
  acc.diff_low_limb.val < 65536 ∧
  (clk_low + offset - acc.prev_low - 1 - acc.diff_low_limb)
      * (65536 : ZMod p)⁻¹ < (256 : ZMod p) ∧
  Word.isU64_poly acc.prev_value

/-- Construct a `MemoryAccess` from an existing
`MemoryAccessInSharedCols`-shaped record and an explicit address. Bridges
the SP1 reader struct (no `addr` field — addresses are contextual at the
chip level) to the Clean-side record (`addr` is explicit so OfflineMemory
aggregation can read it directly). -/
@[reducible]
def MemoryAccess.ofShared (addr : Vector (ZMod p) 3)
    (m : MemoryAccessInSharedCols (ZMod p)) : MemoryAccess (ZMod p) :=
  ⟨addr, m.prev_value, m.access_timestamp.prev_low,
   m.access_timestamp.diff_low_limb⟩

/-- Construct a `MemoryAccess` for a register read: the 3-limb address is
`#v[reg_index, 0, 0]` per `SP1Constraint.toStateProp_poly`'s
`addr0.val < 32 ∧ addr1 = 0 ∧ addr2 = 0` register-special-case branch
(`SP1Foundations/Constraint.lean:89-92`). -/
@[reducible]
def MemoryAccess.ofRegisterShared (reg_index : ZMod p)
    (m : MemoryAccessInSharedCols (ZMod p)) : MemoryAccess (ZMod p) :=
  MemoryAccess.ofShared #v[reg_index, 0, 0] m

/-- Flatten a `MemoryAccess` plus an explicit `write_value` into the
4-tuple shape `(timestamp, address, readValue, writeValue) : ℕ × ℕ × ℕ × ℕ`
that `Clean.Utils.OfflineMemory`'s `MemoryAccessList` expects.

The `timestamp` is `clk_high * 2^24 + clk_low + offset` (SP1's 24-bit clock
encoding); `address` is the 3-limb little-endian decoding; `readValue`
and `writeValue` are 4-limb little-endian U64 decodings.

For pure register reads the caller passes `write_value = acc.prev_value`
(the receive side carries the same value back). For writes (e.g. `op_a`,
Store) the caller passes the chip's `op_*_write_value` column. -/
def MemoryAccess.toAccessTuple
    (clk_high clk_low offset : ZMod p)
    (acc : MemoryAccess (ZMod p)) (write_value : Word (ZMod p)) :
    ℕ × ℕ × ℕ × ℕ :=
  let ts := clk_high.val * (2 ^ 24) + (clk_low + offset).val
  let address :=
    acc.addr[0].val + acc.addr[1].val * 65536 + acc.addr[2].val * (65536 ^ 2)
  let readValue :=
    acc.prev_value[0].val + acc.prev_value[1].val * 65536 +
      acc.prev_value[2].val * (65536 ^ 2) + acc.prev_value[3].val * (65536 ^ 3)
  let writeValue :=
    write_value[0].val + write_value[1].val * 65536 +
      write_value[2].val * (65536 ^ 2) + write_value[3].val * (65536 ^ 3)
  (ts, address, readValue, writeValue)

end SP1Clean
