import SP1Clean.Soundness.ChipRegistry

/-! # The all-chips trace — one row of every wired chip

A concrete heterogeneous `List (ChipRow p)` interleaving one row of every capstone-wired chip (the 24 in
`allChipsTrace`). ALU / R-type / I-type / J-type / memory rows — with different `Inputs`/`Cols` types and
different readers — all coexist in one `List (ChipRow p)` and ride the shared bus layer.

(The demo instantiation of the gated whole-program capstone on this trace — the former
`Soundness/GatedVm/Bridge.lean`'s `gatedExecution_allChips` — was deleted as an orphaned dead leaf during the
consolidation; the capstone core lives in `Soundness/GatedVm/Capstone.lean`.) -/

namespace SP1Clean.Soundness

open SP1Clean

-- `Mul` (last row) carries `Fact (2 ^ 24 < p)`; the trace is stated under the stronger bound with the
-- project-standard `Fact (2 ^ 17 < p)` derived locally.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


/-- A concrete **all-chips** trace — one row of every wired chip, in one `List (ChipRow p)`. The order
mirrors `allChipKinds`: the ALU/R-type chips, the three control-flow chips, the nine memory chips, then
the multiply chip, then the ALU-into-`x0` chip.
Each `⟨Chip.kind, inp, cols⟩` carries its chip's reader/`Inputs`/`Cols` by value, so the whole list is one
homogeneous `List (ChipRow p)` despite the per-chip type heterogeneity. -/
def allChipsTrace
    (addI : AddChip.Inputs (ZMod p)) (addC : Extracted.AddCols (ZMod p))
    (addiI : AddiChip.Inputs (ZMod p)) (addiC : Extracted.AddiCols (ZMod p))
    (addwI : AddwChip.Inputs (ZMod p)) (addwC : Extracted.AddwCols (ZMod p))
    (subI : SubChip.Inputs (ZMod p)) (subC : Extracted.SubCols (ZMod p))
    (subwI : SubwChip.Inputs (ZMod p)) (subwC : Extracted.SubwCols (ZMod p))
    (bitI : BitwiseChip.Inputs (ZMod p)) (bitC : Extracted.BitwiseCols (ZMod p))
    (ltI : LtChip.Inputs (ZMod p)) (ltC : Extracted.LtCols (ZMod p))
    (sllI : ShiftLeftChip.Inputs (ZMod p)) (sllC : Extracted.ShiftLeftCols (ZMod p))
    (srlI : ShiftRightChip.Inputs (ZMod p)) (srlC : Extracted.ShiftRightCols (ZMod p))
    (jalI : JalChip.Inputs (ZMod p)) (jalC : Extracted.JalColumns (ZMod p))
    (jalrI : JalrChip.Inputs (ZMod p)) (jalrC : Extracted.JalrColumns (ZMod p))
    (brI : BranchChip.Inputs (ZMod p)) (brC : Extracted.BranchColumns (ZMod p))
    (utI : UTypeChip.Inputs (ZMod p)) (utC : Extracted.UTypeColumns (ZMod p))
    (lbI : LoadByteChip.Inputs (ZMod p)) (lbC : Extracted.LoadByteColumns (ZMod p))
    (lhI : LoadHalfChip.Inputs (ZMod p)) (lhC : Extracted.LoadHalfColumns (ZMod p))
    (lwI : LoadWordChip.Inputs (ZMod p)) (lwC : Extracted.LoadWordColumns (ZMod p))
    (ldI : LoadDoubleChip.Inputs (ZMod p)) (ldC : Extracted.LoadDoubleColumns (ZMod p))
    (lx0I : LoadX0Chip.Inputs (ZMod p)) (lx0C : Extracted.LoadX0Columns (ZMod p))
    (sbI : StoreByteChip.Inputs (ZMod p)) (sbC : Extracted.StoreByteColumns (ZMod p))
    (shI : StoreHalfChip.Inputs (ZMod p)) (shC : Extracted.StoreHalfColumns (ZMod p))
    (swI : StoreWordChip.Inputs (ZMod p)) (swC : Extracted.StoreWordColumns (ZMod p))
    (sdI : StoreDoubleChip.Inputs (ZMod p)) (sdC : Extracted.StoreDoubleColumns (ZMod p))
    (mulI : MulChip.Inputs (ZMod p)) (mulC : Extracted.MulCols (ZMod p))
    (alux0I : AluX0Chip.Inputs (ZMod p)) (alux0C : Extracted.AluX0Cols (ZMod p)) :
    List (ChipRow p) :=
  [⟨AddChip.kind, addI, addC⟩, ⟨AddiChip.kind, addiI, addiC⟩, ⟨AddwChip.kind, addwI, addwC⟩,
   ⟨SubChip.kind, subI, subC⟩, ⟨SubwChip.kind, subwI, subwC⟩, ⟨BitwiseChip.kind, bitI, bitC⟩,
   ⟨LtChip.kind, ltI, ltC⟩, ⟨ShiftLeftChip.kind, sllI, sllC⟩, ⟨ShiftRightChip.kind, srlI, srlC⟩,
   ⟨JalChip.kind, jalI, jalC⟩, ⟨JalrChip.kind, jalrI, jalrC⟩, ⟨BranchChip.kind, brI, brC⟩,
   ⟨UTypeChip.kind, utI, utC⟩,
   ⟨LoadByteChip.kind, lbI, lbC⟩, ⟨LoadHalfChip.kind, lhI, lhC⟩, ⟨LoadWordChip.kind, lwI, lwC⟩,
   ⟨LoadDoubleChip.kind, ldI, ldC⟩, ⟨LoadX0Chip.kind, lx0I, lx0C⟩,
   ⟨StoreByteChip.kind, sbI, sbC⟩, ⟨StoreHalfChip.kind, shI, shC⟩, ⟨StoreWordChip.kind, swI, swC⟩,
   ⟨StoreDoubleChip.kind, sdI, sdC⟩, ⟨MulChip.kind, mulI, mulC⟩,
   ⟨AluX0Chip.kind, alux0I, alux0C⟩]

end SP1Clean.Soundness
