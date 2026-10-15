import SP1Clean.Proofs.Chips.HostCallChip.Formal
import SP1Clean.Native.Readers.RegisterReadPopulate

/-! # Completing a syscall row with its host-call handoff

The original instruction row keeps its own completeness contract. The extra semantic input is
WRITE's bounded prior x12 word and strict prior/access order. The CPU contract supplies the target
clock bound; the constructor computes the extra timestamp column, and Clean computes the selector.
-/

namespace SP1Clean.HostCallChip

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def populate (instruction : SyscallInstrsChip.Inputs (ZMod p))
    (length : Word (ZMod p)) (previous : ZMod p) : Inputs (ZMod p) :=
  ⟨instruction, (Readers.RegisterRead.populate length previous instruction.state.clk_high
    (SyscallInstrsChip.clkLow instruction + 1) 12
    (instruction.is_real * writeFlag instruction.op_a_memory.prev_value)).cols⟩

def Domain (instruction : SyscallInstrsChip.Inputs (ZMod p))
    (length : Word (ZMod p)) (previous : ZMod p) : Prop :=
  SyscallInstrsChip.RowContract instruction ∧
    SyscallCodeGuard.Spec ⟨instruction.op_a_memory.prev_value, instruction.is_real⟩ ∧
    (instruction.is_real = 1 → instruction.op_a_memory.prev_value = writeWord →
      Word.isU64 length ∧ previous.val < (SyscallInstrsChip.clkLow instruction + 1).val)

theorem populate_assumptions (instruction : SyscallInstrsChip.Inputs (ZMod p))
    (length : Word (ZMod p)) (previous : ZMod p) (valid : Domain instruction length previous) :
    ProverAssumptions (populate instruction length previous) := by
  refine ⟨valid.1, valid.2.1, ?_⟩
  apply Readers.RegisterRead.populate_assumptions
  change Readers.RegisterRead.Domain length previous (SyscallInstrsChip.clkLow instruction + 1)
    (instruction.is_real * writeFlag instruction.op_a_memory.prev_value)
  have binary : instruction.is_real = 0 ∨ instruction.is_real = 1 := valid.2.1.1
  refine ⟨?_, ?_⟩
  · rcases binary with zero | one
    · exact Or.inl (by rw [zero, zero_mul])
    · simpa only [one, one_mul] using writeFlag_binary instruction.op_a_memory.prev_value
  · intro active
    have real : instruction.is_real = 1 := by
      rcases binary with zero | one
      · simp only [zero, zero_mul] at active
        exact False.elim (zero_ne_one active)
      · exact one
    have code : instruction.op_a_memory.prev_value = writeWord := by
      by_contra different
      simp only [writeFlag, if_neg different, mul_zero] at active
      exact zero_ne_one active
    have clock := (Readers.ClkDiscipline.of_cpuState_spec valid.1.2.1).at_one real
    exact ⟨(valid.2.2 real code).1, (valid.2.2 real code).2, clock⟩

end SP1Clean.HostCallChip
