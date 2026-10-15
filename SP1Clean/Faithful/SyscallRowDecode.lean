import SP1Clean.Extracted.SystemOracle.SyscallInstrs
import SP1Clean.Model.Machine.Syscall

/-! # Audited syscall-row view

The total decoder from one physical `SyscallInstrs` row (the extracted Rust column vector) to a
`Machine.CoreSyscallEvent`.  It is the one syscall-row decoder in the tree: the exact Core AIR's
event decoder (`Faithful/CoreAIR.lean`) and the native bridge (`Soundness/SyscallRowSemantics.lean`)
both apply it, so the events the native theorem grounds are the events the exact relation's commit
obligations quantify over.

It lives here, below `Faithful/CoreAIR.lean`, because it needs only the `SyscallInstrs` column
vector and the event type — not the other system tables the exact relation assembles. -/

namespace SP1Clean.CoreAIR.Current

open SP1Clean.Extracted
open SP1Clean.Circuits.Types

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Reassemble four little-endian 16-bit row limbs as the 64-bit word used by SP1. -/
def word64 (values : Vector (ZMod p) 65) (i0 i1 i2 i3 : Fin 65) : BitVec 64 :=
  BitVec.ofNat 64 (values[i0].val + values[i1].val * 2 ^ 16 +
    values[i2].val * 2 ^ 32 + values[i3].val * 2 ^ 48)

/-- Reassemble a three-limb pc in the same little-endian layout. -/
def pc64 (values : Vector (ZMod p) 65) (i0 i1 i2 : Fin 65) : BitVec 64 :=
  BitVec.ofNat 64
    (values[i0].val + values[i1].val * 2 ^ 16 + values[i2].val * 2 ^ 32)

/-- Read the timestamp represented by `CPUState`'s `(high, 8, 16)` columns. -/
def clock (values : Vector (ZMod p) 65) : ℕ :=
  values[0].val * 2 ^ 24 + values[1].val * 2 ^ 16 + values[2].val

/-- Total decoder of one physical `SyscallInstrs` row.  The indices are the flattened field order of
`SyscallInstrColumns<T, SupervisorMode>` at the pinned Rust revision:
`state = 0..5`, `RTypeReader = 6..27`, `next_pc = 28..30`, `op_a_value = 32..35`, and
`is_real = 64`. -/
def decodeSyscallRow (row : SyscallInstrsCols (ZMod p)) : Machine.CoreSyscallEvent where
  clock := clock row.values
  pc := pc64 row.values 3 4 5
  nextPc := pc64 row.values 28 29 30
  rawCode := word64 row.values 7 8 9 10
  arg1 := word64 row.values 15 16 17 18
  arg2 := word64 row.values 22 23 24 25
  result := word64 row.values 32 33 34 35

end SP1Clean.CoreAIR.Current
