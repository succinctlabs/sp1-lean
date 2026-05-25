import Clean.Circuit.Basic
import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Foundations
import SP1Foundations.Field
import SP1Operations.Reader.CPUState.CPUState
import SP1Operations.Reader.ITypeReaderImmutable.ITypeReaderImmutable
import SP1Operations.Compare.LtOperationSigned.LtOperationSigned
import SP1Clean.Reader.CPUState
import SP1Clean.Compare.LtOperationSigned
import SP1Clean.TrustMode

/-! # `Branch` cols-level surface (multiplicity-aware redesign)

Sibling of `SP1Clean.BranchChip` (iter-9 Approach A baseline). The struct
shape is identical (mirrors Rust `BranchCols<T, M : TrustMode>` under
`M = UserMode`) but the chip-level `main` / `Spec` / `FormalAssertion`
in `SP1Clean.Branch.Circuit` is rebuilt on top of the multiplicity-aware
lookup bus (`GatedAddOp`, `byteOpcodeGated`, `CPUState.assertion`,
`ITypeReaderImmutable.assertion`) so every Rust `air.rs` emission
corresponds 1-to-1 to a sub-`FormalAssertion` with an explicit
multiplicity. Sail bridging is deferred; the iter-9 baseline lives in
`SP1Clean/BranchChip.lean` and is unaffected by this file. -/

set_option linter.style.setOption false
set_option linter.style.longLine false

namespace SP1Clean.Branch

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The chip's column struct, mirroring SP1's Rust `BranchCols<T, M : TrustMode>`
(`sp1/crates/core/machine/src/control_flow/branch/columns.rs`). Field order
matches the `Main[k]` indexing in `SP1Chips/Branch/Constraints.lean` (45
columns). Six opcode selectors (`is_beq`/`is_bne`/`is_blt`/`is_bge`/
`is_bltu`/`is_bgeu`) gate the variant; their sum is the aggregate
`is_real`. `is_branching` (Main[34]) is the branch-taken predicate,
forced by the bridge to equal the appropriate comparison output. The
`compare_operation` field packs Main[35..44] (the LtOperationSigned
witness columns: u16-compare bit, four u16 flags, not-eq inverse, two
comparison limbs, two MSBs). -/
@[ext]
structure BranchCols (T : Type) where
  state : CPUState T                          -- Main[0..5]
  adapter : ITypeReader T                     -- Main[6..24] (Imm reader reuses ITypeReader struct)
  next_pc : Vector T 3                        -- Main[25..27]
  is_beq : T                                  -- Main[28]
  is_bne : T                                  -- Main[29]
  is_blt : T                                  -- Main[30]
  is_bge : T                                  -- Main[31]
  is_bltu : T                                 -- Main[32]
  is_bgeu : T                                 -- Main[33]
  is_branching : T                            -- Main[34]
  compare_operation : LtOperationSigned T     -- Main[35..44]
  adapter_cols : SP1Clean.UserModeReaderCols T
deriving ProvableStruct

end SP1Clean.Branch
