import SP1Clean.Soundness.GatedVm.Capstone
import SP1Clean.Soundness.AllChips

/-! # The gated capstone on the 24-chip machine

> **FROZEN (consolidation step 0, 2026-07-09).** Legacy soundness path — scheduled for deletion at the cutover (proposal §5.6). Do NOT add new lemmas against this module; new soundness work targets the timed-grounding engine (proposal §3.2).

`gatedExecution_allChips` — the gated capstone (`GatedVm/Capstone.lean`) instantiated on
`allChipsTrace`, the heterogeneous trace carrying one row of every chip in `allChipsTrace`. Demonstrates
the gated whole-program execution result holds for the full SP1 chip set on one shared trace. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.LookupAccessList
open Sail LeanRV64D LeanRV64D.Functions

-- `Mul` (in `allChipsTrace`) carries `Fact (2 ^ 24 < p)`; stated under the stronger bound with the
-- project-standard `Fact (2 ^ 17 < p)` derived locally.
variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]


/-- **The gated capstone on the full 24-chip machine.** `gatedExecution_of_specs_and_balance`
instantiated on `allChipsTrace` (one row of every wired chip). Same hypotheses — per-row chip `Spec`s,
binary gating, and the gated State-bus balance with the genesis/finalization boundary — now witnessing a
valid whole-program execution from `pc_start` to `next_pc` across the entire chip set. -/
theorem gatedExecution_allChips
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
    (alux0I : AluX0Chip.Inputs (ZMod p)) (alux0C : Extracted.AluX0Cols (ZMod p))
    (data : ProverData (ZMod p)) (initEntry finalEntry : List ℕ)
    (rows : List (ChipRow p))
    (hrows : rows = allChipsTrace addI addC addiI addiC addwI addwC subI subC subwI subwC bitI bitC
      ltI ltC sllI sllC srlI srlC jalI jalC jalrI jalrC brI brC utI utC lbI lbC lhI lhC lwI lwC
      ldI ldC lx0I lx0C sbI sbC shI shC swI swC sdI sdC mulI mulC alux0I alux0C)
    (h_spec : ∀ r ∈ rows, r.chipSpec data)
    (hbin : ∀ r ∈ rows.map ChipRow.view, r.is_real = 0 ∨ r.is_real = 1)
    (h_bal : isConsistentBalanced (aggregateChipRows (rows.map ChipRow.view) stateLookups
        ++ [(InteractionKind.State, "SP1State", initEntry, (1 : ℤ)),
            (InteractionKind.State, "SP1State", finalEntry, (-1 : ℤ))])) :
    GatedExecution rows initEntry finalEntry := by
  subst hrows
  exact gatedExecution_of_specs_and_balance _ data initEntry finalEntry h_spec hbin h_bal

end SP1Clean.Soundness
