import SP1Clean.Soundness.CoreRowBalance
import SP1Clean.Model.SP1Field

/-! # Mixed read-time regression

The Memory transport must accept syscall rows without imposing the ordinary carrier's
all-reads-at-start restriction. This kernel-checked regression distinguishes those two interfaces.
-/

namespace SP1Clean.Audit.MixedMemoryRows

open SP1Clean.Soundness SP1Clean.Semantics SP1Clean.Soundness.NativeCore

variable {p : ℕ} [Fact p.Prime]

/-- The ledger interface admits the syscall carrier, whereas the ordinary alignment interface
cannot accept its later register reads as the original carrier. -/
theorem syscallKeepsMixedReadTimes (row : SyscallInstrsChip.Inputs (ZMod p)) :
    RowMemoryPermutation (syscallRowFacts row) (syscallRowFacts row) ∧
      ¬ ∃ aligned, TimedGrounding.AlignsWith aligned (syscallRowFacts row) := by
  refine ⟨RowMemoryPermutation.refl _, ?_⟩
  rintro ⟨aligned, agreement⟩
  have late := agreement.ordTime
    (SyscallInstrsChip.memPulledMessage row row.op_b_memory row.op_b,
      StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) + 3)
    (by simp [syscallRowFacts])
  change StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) + 3 =
    StateMsg.timeNat (SyscallInstrsChip.statePulledMessage row) at late
  omega

/-- The actual non-HALT PC arm permits a raw low limb of `65536`: recombination advances four
bytes, while the old context's no-carry premise fails. This checks the arm, not a whole AIR witness. -/
theorem syscallPcArmCrossesLimb :
    let row : SyscallInstrsChip.PcArm.Inputs (ZMod SP1Prime) :=
      ⟨#v[65532, 1, 0], #v[65536, 1, 0], 1, 0⟩
    SyscallInstrsChip.PcArm.Assumptions row ∧ SyscallInstrsChip.PcArm.Spec row ∧
      ¬ (row.pc[0].val + 4 < 2 ^ 16) ∧
      pcBits row.next_pc[0] row.next_pc[1] row.next_pc[2] =
        pcBits row.pc[0] row.pc[1] row.pc[2] + 4 := by
  have low : (65532 : ZMod SP1Prime).val = 65532 :=
    ZMod.val_natCast_of_lt (by norm_num [SP1Prime])
  norm_num [SyscallInstrsChip.PcArm.Assumptions, SyscallInstrsChip.PcArm.Spec,
    pcBits, low, ZMod.val_one, SP1Prime]
  decide

end SP1Clean.Audit.MixedMemoryRows
