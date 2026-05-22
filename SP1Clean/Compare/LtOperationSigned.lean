import Clean.Circuit.Provable
import Clean.Utils.Tactics.ProvableStructDeriving
import SP1Operations.Compare.U16CompareOperation.Operation
import SP1Operations.Compare.LtOperationUnsigned.Operation
import SP1Operations.Compare.LtOperationSigned.Operation
import SP1Operations.Operation.U16MSBOperation.Operation

/-! # `ProvableStruct` derivations for the `LtOperationSigned` chain

Sidecar-style: derives `ProvableStruct` instances for the four
SP1Operations structs that compose `LtOperationSigned`, without
modifying SP1Operations (which has no Clean dependency). Importing
this file lets a Clean-side `Cols` struct nest `LtOperationSigned`
as a single field instead of inlining six flat columns.

Cell layout (left-to-right `toComponents` flatten) matches the order
expected by the auto-generated `Main[k]` indexing on the chip side:
`result.u16_compare_operation.bit, result.u16_flags(4),
result.not_eq_inv, result.comparison_limbs(2), b_msb.msb, c_msb.msb`
— ten cells total. -/

deriving instance ProvableStruct for U16MSBOperation
deriving instance ProvableStruct for U16CompareOperation
deriving instance ProvableStruct for LtOperationUnsigned
deriving instance ProvableStruct for LtOperationSigned
