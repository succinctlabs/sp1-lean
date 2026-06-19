import SP1Clean.Native.Operations.LtOperationUnsigned.Populate
import SP1Clean.Native.Operations.U16MSBOperation.Populate
import SP1Clean.Extracted.LtOperationSigned

/-! # `LtOperationSigned` — native witness generation

SP1's `LtOperationSigned::populate` ported to Lean: the two `is_signed`-gated sign bits (`b_msb`,
`c_msb`, each `is_signed · populate_msb`) and the `LtOperationUnsigned.populate` on the sign-adjusted
words. The op witnesses nothing itself (it is a `FormalAssertion`); a composing chip
(`LtChip`/`BranchChip`) witnesses the whole `LtOperationSigned` column block with `populate`.

The unsigned compare columns are gated on `is_real`: the auto-generated `main` threads the row's
`is_real` to the composed `LtOperationUnsigned.circuit` (faithful to SP1), and the unsigned selectors
`(is_real − Σflags≥i)·(bᵢ − ccᵢ)` are `is_real`-dependent — so on a padding row (`is_real = 0`) the
satisfying witness is the **all-zero** unsigned block (`Σflags = 0` makes every selector vanish), not
the real one-hot. `spec_populate` (that the witness satisfies the gadget `Spec`) lives in `Formal.lean`. -/

namespace SP1Clean.LtOperationSigned

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Fully witnessed `LtOperationSigned` column struct (SP1's `populate`): the two `is_signed`-gated
sign bits and the `LtOperationUnsigned` compare columns on the sign-adjusted words — the latter zeroed
on a padding row (`is_real = 0`), where the threaded unsigned compare contributes nothing. -/
def populate (b cc : Word (ZMod p)) (is_signed is_real : ZMod p) :
    Extracted.LtOperationSigned (ZMod p) :=
  let bm := is_signed * U16MSBOperation.populate_msb b[3]
  let cm := is_signed * U16MSBOperation.populate_msb cc[3]
  let bAdj : Word (ZMod p) := #v[b[0], b[1], b[2], b[3] + is_signed * 32768 - 65536 * bm]
  let cAdj : Word (ZMod p) := #v[cc[0], cc[1], cc[2], cc[3] + is_signed * 32768 - 65536 * cm]
  let result : Extracted.LtOperationUnsigned (ZMod p) :=
    if is_real = 1 then LtOperationUnsigned.populate bAdj cAdj
    else ⟨⟨0⟩, #v[0, 0, 0, 0], 0, #v[0, 0]⟩
  ⟨result, ⟨bm⟩, ⟨cm⟩⟩

end SP1Clean.LtOperationSigned
