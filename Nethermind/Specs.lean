import Nethermind.Basic

namespace Sp1

def spec_32_bit_wrap_add (A1 A2 A3 A4 B1 B2 B3 B4 C1 C2 C3 C4 : BabyBear) : Prop :=
  ( A1.val < 256 ) ∧ ( A2.val < 256 ) ∧ ( A3.val < 256 ) ∧ ( A4.val < 256 ) ∧
  ( B1.val < 256 ) ∧ ( B2.val < 256 ) ∧ ( B3.val < 256 ) ∧ ( B4.val < 256 ) ∧
  ( C1.val < 256 ) ∧ ( C2.val < 256 ) ∧ ( C3.val < 256 ) ∧ ( C4.val < 256 ) ∧
  ( ( B1.val + 256 * B2.val + 65536 * B3.val + 16777216 * B4.val ) +
    ( C1.val + 256 * C2.val + 65536 * C3.val + 16777216 * C4.val ) ) % 4294967296 =
  ( A1.val + 256 * A2.val + 65536 * A3.val + 16777216 * A4.val )

end Sp1
