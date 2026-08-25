import SP1Clean

/-! # Non-vacuity anchors for the chip soundness `Assumptions` (V3)

Every chip soundness theorem is conditional on its `Assumptions`; a contradictory `Assumptions`
would make the soundness statement vacuously true. This module witnesses, at SP1's concrete
KoalaBear prime, one concrete satisfying input row for **every** registered chip whose
`Assumptions` is not literally `True` (the remaining chips — Add / Sub / Subw / AluX0 / Mul —
assume `True` and are non-vacuous by construction).

The all-zero input row satisfies every operand `Word.isU64` bound (each limb is `0 < 2^16`), and
`UTypeChip`'s semantic decode conjunct `toBitVec64 op_b_imm = RV64.lui (immOf adapter)` is also
satisfied by the zero row (a genuine decoded LUI-of-zero: `immOf 0 = 0` and `RV64.lui 0 = 0`, so
no vector-file row is needed). The three sub-word store chips are additionally witnessed with
`is_real = 1`, so their gated `isU64 store_value` conjunct is exercised non-vacuously rather than
discharged by a false antecedent. Each anchor `unfold`s the chip's `Assumptions` (a plain def, so
`Decidable` synthesis cannot see through it) and lets `native_decide` evaluate the decidable
bounds at the concrete prime — confined to this test library per the project rule (never in
`SP1Clean/`). -/

namespace SP1Clean.NonVacuityTests

open SP1Clean

/-- `Word.isU64` is definitionally the decidable limb-wise bound `∀ i : Fin 4, w[i].val < 2^16`;
registered as a `Decidable` instance so the anchors below can be discharged by `native_decide`. -/
instance {n : ℕ} [NeZero n] (w : Word (ZMod n)) : Decidable (Word.isU64 w) :=
  decidable_of_iff (∀ i : Fin 4, w[i].val < 2 ^ 16) Iff.rfl

/-- The all-zero valuation of a provable input struct at SP1's prime — every cell `0`, so every
`isU64` operand bound holds limb-wise. -/
def zeroed (α : TypeMap) [ProvableType α] : α (ZMod SP1Prime) :=
  ProvableType.fromElements (.replicate _ 0)

/-- Empty committed prover data (every chip `Assumptions` ignores it). -/
def emptyData : ProverData (ZMod SP1Prime) := fun _ _ => #[]

/-! ## ALU chips (audit-surface `Assumptions`, `Contracts/ChipAssumptions.lean`) -/

example : AddiChip.Assumptions (p := SP1Prime) (zeroed AddiChip.Inputs) emptyData := by
  unfold AddiChip.Assumptions
  native_decide

example : AddwChip.Assumptions (p := SP1Prime) (zeroed AddwChip.Inputs) emptyData := by
  unfold AddwChip.Assumptions
  native_decide

/-! ## ALU / mul-div / shift / comparison chips (proof-file `Assumptions`) -/

example : BitwiseChip.Assumptions (p := SP1Prime) (zeroed BitwiseChip.Inputs) emptyData := by
  unfold BitwiseChip.Assumptions
  native_decide

example : DivRemChip.Assumptions (p := SP1Prime) (zeroed DivRemChip.Inputs) emptyData := by
  unfold DivRemChip.Assumptions
  native_decide

example : LtChip.Assumptions (p := SP1Prime) (zeroed LtChip.Inputs) emptyData := by
  unfold LtChip.Assumptions
  native_decide

example : ShiftLeftChip.Assumptions (p := SP1Prime) (zeroed ShiftLeftChip.Inputs) emptyData := by
  unfold ShiftLeftChip.Assumptions
  native_decide

example : ShiftRightChip.Assumptions (p := SP1Prime) (zeroed ShiftRightChip.Inputs) emptyData := by
  unfold ShiftRightChip.Assumptions
  native_decide

/-! ## Control-flow chips -/

example : BranchChip.Assumptions (p := SP1Prime) (zeroed BranchChip.Inputs) emptyData := by
  unfold BranchChip.Assumptions
  native_decide

example : JalChip.Assumptions (p := SP1Prime) (zeroed JalChip.Inputs) emptyData := by
  unfold JalChip.Assumptions
  native_decide

example : JalrChip.Assumptions (p := SP1Prime) (zeroed JalrChip.Inputs) emptyData := by
  unfold JalrChip.Assumptions
  native_decide

/-- The U-type decode conjunct holds at the zero row: `immOf 0 = 0` and `RV64.lui 0 = 0`. -/
example : UTypeChip.Assumptions (p := SP1Prime) (zeroed UTypeChip.Inputs) emptyData := by
  unfold UTypeChip.Assumptions
  native_decide

/-! ## Load chips -/

example : LoadByteChip.Assumptions (p := SP1Prime) (zeroed LoadByteChip.Inputs) emptyData := by
  unfold LoadByteChip.Assumptions
  native_decide

example : LoadHalfChip.Assumptions (p := SP1Prime) (zeroed LoadHalfChip.Inputs) emptyData := by
  unfold LoadHalfChip.Assumptions
  native_decide

example : LoadWordChip.Assumptions (p := SP1Prime) (zeroed LoadWordChip.Inputs) emptyData := by
  unfold LoadWordChip.Assumptions
  native_decide

example : LoadDoubleChip.Assumptions (p := SP1Prime) (zeroed LoadDoubleChip.Inputs) emptyData := by
  unfold LoadDoubleChip.Assumptions
  native_decide

example : LoadX0Chip.Assumptions (p := SP1Prime) (zeroed LoadX0Chip.Inputs) emptyData := by
  unfold LoadX0Chip.Assumptions
  native_decide

/-! ## Store chips (the sub-word stores on an active row, exercising the gated
`isU64 store_value` conjunct) -/

example : StoreByteChip.Assumptions (p := SP1Prime)
    { zeroed StoreByteChip.Inputs with is_real := 1 } emptyData := by
  unfold StoreByteChip.Assumptions
  native_decide

example : StoreHalfChip.Assumptions (p := SP1Prime)
    { zeroed StoreHalfChip.Inputs with is_real := 1 } emptyData := by
  unfold StoreHalfChip.Assumptions
  native_decide

example : StoreWordChip.Assumptions (p := SP1Prime)
    { zeroed StoreWordChip.Inputs with is_real := 1 } emptyData := by
  unfold StoreWordChip.Assumptions
  native_decide

example : StoreDoubleChip.Assumptions (p := SP1Prime) (zeroed StoreDoubleChip.Inputs)
    emptyData := by
  unfold StoreDoubleChip.Assumptions
  native_decide

end SP1Clean.NonVacuityTests
