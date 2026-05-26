import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ITypeReader.ITypeReader
import SP1Clean.Reader.CPUState
import SP1Clean.TrustMode

/-! # `Jalr` cols-level surface (multiplicity-aware redesign)

Sibling of `SP1Clean.JalrChip` (iter-9 Approach A baseline). The struct
shape is identical (mirrors Rust `JalrCols<T, M : TrustMode>` under
`M = UserMode`) but the chip-level `main` / `Spec` / `FormalAssertion`
in `SP1Clean.Jalr.Circuit` is rebuilt on top of the multiplicity-aware
lookup bus (`GatedAddOp`, `byteOpcodeGated`, `ITypeReader.Gated`,
`CPUState.assertion`) so every Rust `air.rs` emission corresponds
1-to-1 to a sub-`FormalAssertion` with an explicit multiplicity. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Jalr

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `JalrCols<T, M : TrustMode>`
(`sp1/crates/core/machine/src/control_flow/jalr/columns.rs`). Field order
matches the `Main[k]` indexing in `SP1Chips/Jalr/Constraints.lean` (35
columns). The `lsb` column holds the bit-0 of the unmasked sum
`op_b + sign_ext(op_c_imm)` — the actual next-PC is the sum with that
bit cleared (`next_pc[0] = jump_target[0] - lsb`). -/
@[ext]
structure JalrCols (T : Type) where
  state : CPUState T
  adapter : ITypeReader T
  is_real : T
  jump_target : Vector T 4
  op_a_write_value : Vector T 4
  lsb : T
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

end SP1Clean.Jalr
