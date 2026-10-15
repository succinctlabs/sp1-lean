import SP1Clean.Proofs.Chips.HostHaltChip.Formal
import SP1Clean.Model.SP1Field

/-! # The native HALT range agrees with the pinned instruction range

The faithful instruction's structural bound names KoalaBear, even when its arithmetic is
interpreted over another field. The native handler instead matches its host policy to that
field's characteristic. These ranges agree at `SP1Prime`, the intended full-core specialization;
generic component proofs alone do not establish whole-core completeness for arbitrary fields.
-/

namespace SP1Clean.SyscallInstrsChip

variable {p : ℕ} [Fact p.Prime]

/-- The instruction's structural predicate means a canonical KoalaBear integer. -/
theorem exitCodeValid_iff_below_sp1 (word : Word (ZMod p)) (bounded : Word.isU64 word) :
    ExitCodeValid word ↔ Word.toNat word < SP1Prime := by
  have low : word[0].val < 2 ^ 16 := bounded 0
  simp only [ExitCodeValid, ← ZMod.val_eq_zero, Word.toNat, fieldLimbBound, SP1Prime]
  omega

end SP1Clean.SyscallInstrsChip

namespace SP1Clean.HostHaltChip

/-- At the native core's field, neither handler nor instruction narrows the other's exit range. -/
theorem exit_bound_iff (word : Word (ZMod SP1Prime)) (bounded : Word.isU64 word) :
    Word.toNat word < bound SP1Prime ↔ SyscallInstrsChip.ExitCodeValid word := by
  have limit : bound SP1Prime = SP1Prime := by decide
  rw [limit, SyscallInstrsChip.exitCodeValid_iff_below_sp1 word bounded]

theorem instruction_exit_of_spec (input : Inputs (ZMod SP1Prime)) (valid : Spec input) :
    SyscallInstrsChip.ExitCodeValid input.call.arg1 := by
  obtain ⟨_, _, _, word, below⟩ := valid
  exact (exit_bound_iff input.call.arg1 word).mp below

end SP1Clean.HostHaltChip
