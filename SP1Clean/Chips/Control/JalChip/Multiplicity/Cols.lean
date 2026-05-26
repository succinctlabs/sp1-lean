import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.JTypeReader.JTypeReader
import SP1Clean.Reader.CPUState
import SP1Clean.TrustMode

/-! # `Jal` cols-level surface (multiplicity-aware redesign)

Sibling of `SP1Clean.JalChip` (iter-9 Approach A baseline). The struct
shape is identical (mirrors Rust `JalCols<T, M : TrustMode>` under
`M = UserMode`) but the chip-level `main` / `Spec` / `FormalAssertion`
in `SP1Clean.Jal.Circuit` is rebuilt on top of the multiplicity-aware
lookup bus (`GatedAddOp`, `byteOpcodeGated`, `JTypeReader.Gated`,
`CPUState.assertion`) so every Rust `air.rs` emission corresponds
1-to-1 to a sub-`FormalAssertion` with an explicit multiplicity. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Jal

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `JalCols<T, M : TrustMode>`
(`sp1/crates/core/machine/src/control_flow/jal/columns.rs`). Field order
matches the `Main[k]` indexing in `SP1Chips/Jal/Constraints.lean` (31
columns). -/
@[ext]
structure JalCols (T : Type) where
  state : CPUState T
  adapter : JTypeReader T
  next_pc : Vector T 4                      -- Main[22..25] (jump target; Main[25] is high limb)
  op_a_write_value : Vector T 4             -- Main[26..29] (return address = pc + 4)
  is_real : T                               -- Main[30]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

end SP1Clean.Jal
