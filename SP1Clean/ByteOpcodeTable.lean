import Clean.Circuit.Basic
import Clean.Circuit.Lookup
import Clean.Utils.Field
import SP1Foundations.ByteOpcode

/-! # Clean-side mirror of SP1's byte-opcode interactions

This file defines the lookup table that mirrors SP1's
`send (.byte op a b c) mult` / `receive (.byte op a b c) mult` interactions.

Per `docs/CLEAN_FUTURE.md` "Open risks — multiplicity tracking", the encoding
chosen is a **stateless** `Table` rather than a multiplicity-aware `Channel`.
SP1's `mult` is dropped here; per-row this is sound because every SP1 chip
carries an `is_real ≠ 0` discharger on every send. The cost is that this
encoding can't witness the global "balanced multiplicities" property — a
known limitation; see also `docs/MULTIPLICITY_BUS.md` for the parallel
hint-witness `lookupGated` primitive that closes part of this gap.

The row layout is `#v[op, a, b, c]` to match `AirInteraction.byte op a b c`
from `SP1Foundations/Constraint.lean:9-22`, with `op` encoded as a field
element via `ByteOpcode.toNat`.
-/

namespace SP1Clean

variable {p : ℕ} [Fact p.Prime] [Fact (p > 512)]

/-- Spec of `ByteOpcodeTable`. A 4-tuple `#v[op, a, b, c]` is in the table iff
there exists a concrete `ByteOpcode` whose `toNat` matches `op` (as a field
element) and whose `constrain` holds on `(a, b, c)`. -/
def ByteOpcodeSpec (row : fields 4 (ZMod p)) : Prop :=
  ∃ bop : ByteOpcode,
    (bop.toNat : ZMod p) = row[0] ∧ bop.constrain row[1] row[2] row[3]

/-- The polymorphic byte-opcode table.

`Contains := Soundness := Completeness := ByteOpcodeSpec`, sidestepping the
`StaticTable` enumeration (it would require explicitly listing every
AND/OR/XOR/Range/… row — overkill for the pilot, whose only goal is the
equivalence to SP1's `toProp`). -/
def ByteOpcodeTable : Table (ZMod p) (fields 4) where
  name := "SP1ByteOpcode"
  Contains _ row := ByteOpcodeSpec row
  Soundness _ row := ByteOpcodeSpec row
  Completeness _ row := ByteOpcodeSpec row

end SP1Clean
