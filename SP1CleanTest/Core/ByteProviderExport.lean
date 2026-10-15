import SP1CleanTest.Core.ComponentExport
import SP1Clean.Proofs.Chips.ByteChip.ByteChip

/-! # Built-in export of all six native byte providers

SP1 authenticates a preprocessed byte table. These native providers instead prove membership
with polynomial constraints. Rust comparisons check the emitted messages against SP1's actual
preprocessed table and AIR; the physical row layouts intentionally differ.
-/

namespace SP1CleanTest.Core.ByteProviderExport

open SP1Clean ComponentExport

/-- Byte providers in SP1's opcode order. The multiplicity stays a caller-supplied input. -/
def rustExports : List (String × Except String String) := [
  ("and_byte_provider.rs", exportRust "AndByteProvider" ByteChip.AndByte.circuit),
  ("or_byte_provider.rs", exportRust "OrByteProvider" ByteChip.OrByte.circuit),
  ("xor_byte_provider.rs", exportRust "XorByteProvider" ByteChip.XorByte.circuit),
  ("u8_range_byte_provider.rs", exportRust "U8RangeByteProvider" ByteChip.U8Range.circuit),
  ("ltu_byte_provider.rs", exportRust "LtuByteProvider" ByteChip.Ltu.circuit),
  ("msb_byte_provider.rs", exportRust "MsbByteProvider" ByteChip.MSB.circuit)]

end SP1CleanTest.Core.ByteProviderExport
