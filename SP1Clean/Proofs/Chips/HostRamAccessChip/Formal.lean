import SP1Clean.Native.Chips.HostRamAccessChip.Defs

/-! # Soundness and completeness of a host RAM access

The bounded timestamp proof rules out field underflow locally, including a change of high
clock component. No caller supplies a previous-record high-clock bound to soundness.
-/

namespace SP1Clean.HostRamAccessChip

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem bounded_gap (current previous low high : ZMod p)
    (previousBound : previous.val < 2 ^ 24) (lowBound : low.val < 2 ^ 16)
    (highBound : high.val < 2 ^ 8)
    (gap : current - previous - 1 = low + high * 65536) :
    previous.val < current.val := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  have sumBound : previous.val + 1 + low.val + high.val * 65536 < p := by omega
  have equality : current = ((previous.val + 1 + low.val + high.val * 65536 : ℕ) : ZMod p) := by
    push_cast
    simp only [ZMod.natCast_zmod_val]
    linear_combination gap
  rw [equality, ZMod.val_natCast_of_lt sumBound]
  omega

private theorem reader_order (input : Inputs (ZMod p))
    (previousHigh : input.access.access_timestamp.prev_high.val < 2 ^ 24)
    (checked : Readers.MemoryAccess.Spec input.reader) :
    Semantics.MemoryMsg.timeNat input.prior < Semantics.MemoryMsg.timeNat input.pushed := by
  obtain ⟨binary, equalHigh, gap, lowBound, highBound, _, previousLow⟩ := checked rfl
  simp only [Inputs.reader, Readers.MemoryAccess.selCur, Readers.MemoryAccess.selPrev] at gap equalHigh
  simp only [Inputs.reader] at binary previousLow lowBound highBound
  rcases binary with zero | one
  · simp only [zero, zero_mul, sub_zero, one_mul, zero_add] at gap
    have increases := bounded_gap _ _ _ _ previousHigh lowBound highBound gap
    simp only [Semantics.MemoryMsg.timeNat, Semantics.clkNat, Inputs.prior, Inputs.pushed]
    omega
  · simp only [one, one_mul, sub_self, zero_mul, add_zero] at gap equalHigh
    have increases := bounded_gap _ _ _ _ previousLow lowBound highBound gap
    have equal := sub_eq_zero.mp equalHigh
    simp only [Semantics.MemoryMsg.timeNat, Semantics.clkNat, Inputs.prior, Inputs.pushed, equal]
    omega

private theorem reader_assumptions (input : Inputs (ZMod p))
    (word : Word.isU64 input.new_value)
    (low : ((input.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13)
    (high : input.clk_16_24.val < 2 ^ 8) : Readers.MemoryAccess.Assumptions input.reader :=
  ⟨Or.inr rfl, fun _ => word, Readers.ClkDiscipline.of_cpuState_spec (fun _ => ⟨low, high⟩)⟩

/-- The locally checked low-clock discipline places the host write at the call clock plus one. -/
theorem pushed_time (input : Inputs (ZMod p))
    (discipline : Readers.ClkDiscipline input.clockLow (1 : ZMod p)) :
    Semantics.MemoryMsg.timeNat input.pushed = Semantics.clkNat input.clk_high input.clockLow + 1 := by
  have low := discipline 0 0 (ZMod.val_zero) (by omega) rfl
  simp only [add_zero] at low
  have hp := Fact.out (p := 2 ^ 25 < p)
  have increment : (input.clockLow + 1).val = input.clockLow.val + 1 := by
    rw [ZMod.val_add_of_lt (by rw [ZMod.val_one]; omega), ZMod.val_one]
  simp only [Semantics.MemoryMsg.timeNat, Semantics.clkNat, Inputs.pushed, increment]
  omega

omit [Fact (2 ^ 25 < p)] in
private theorem zero_word : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) := by
  apply Word.isU64_of_cases <;> norm_num

omit [Fact (2 ^ 25 < p)] in
/-- The existing address gadget and canonical limbs establish an aligned native RAM key. -/
theorem ram_key (record : MemoryMsg (ZMod p))
    (bound : Word.isU64 (MemoryBoundary.address record))
    (output : Circuits.Types.AddressOperation (ZMod p))
    (checked : AddressOperation.Spec (FinalRamProvider.addressInput record) output) : RamKey record := by
  have fits : Word.toNat (MemoryBoundary.address record) < 2 ^ 64 := by
    rw [← Word.toBitVec64_toNat bound]
    exact BitVec.isLt _
  have zeroNat : Word.toNat (#v[0, 0, 0, 0] : Word (ZMod p)) = 0 := by simp [Word.toNat]
  have valid := AddressOperation.validAddress_of_spec checked
  simp only [AddressOperation.ValidAddress, FinalRamProvider.addressInput, zeroNat, add_zero,
    Nat.mod_eq_of_lt fits, ZMod.val_zero, mul_zero] at valid
  exact ⟨by simpa only [Nat.mod_eq_of_lt valid.1] using valid.2.1,
    valid.1, by simpa only [Nat.mod_eq_of_lt valid.1] using valid.2.2.symm⟩

theorem soundness : GeneralFormalCircuit.Soundness (Output := unit) (ZMod p) main
    (fun _ _ => True) (fun input _ _ => Spec input) := by
  circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec,
    AddressOperation.circuit, Gadgets.ToBits.rangeCheck, Readers.MemoryAccess.circuit,
    Readers.MemoryAccess.AssumptionsD, Readers.MemoryAccess.SpecD, channel,
    Inputs.reader, Inputs.pushed, Inputs.message, Inputs.clockLow, MemoryBoundary.address,
    FinalRamProvider.addressInput]
  obtain ⟨address, addressChecked, word, low, high, clockHigh, previousHigh, read⟩ := h_holds
  let input : Inputs (ZMod p) :=
    ⟨⟨input_access_prev_value,
      ⟨input_access_access_timestamp_prev_high, input_access_access_timestamp_prev_low,
       input_access_access_timestamp_compare_low, input_access_access_timestamp_diff_low_limb,
       input_access_access_timestamp_diff_high_limb⟩⟩,
     input_clk_high, input_clk_0_16, input_clk_16_24, input_addr0, input_addr1, input_addr2, input_new_value⟩
  have assumptions := reader_assumptions input word low high
  have checked : Readers.MemoryAccess.Spec input.reader := read assumptions
  have addressSpec := (addressChecked ⟨address, zero_word, Or.inr rfl⟩).2.2.2 rfl
  refine ⟨?_, assumptions⟩
  exact ⟨FinalRamProvider.canonical input.pushed address _ addressSpec,
    ram_key input.pushed address _ addressSpec,
    (checked rfl).2.2.2.2.2.1, word, previousHigh, (checked rfl).2.2.2.2.2.2,
    clockHigh, assumptions.2.2.at_one rfl, reader_order input previousHigh checked,
    pushed_time input assumptions.2.2⟩

theorem completeness : GeneralFormalCircuit.Completeness (Output := unit) (ZMod p) main
    (fun input _ _ => ProverAssumptions input) (fun _ _ _ => True) := by
  circuit_proof_start [WordRangeCheck.circuit, WordRangeCheck.Assumptions, WordRangeCheck.Spec,
    AddressOperation.circuit, Gadgets.ToBits.rangeCheck, Readers.MemoryAccess.circuit,
    Readers.MemoryAccess.ProverAssumptionsD, channel,
    Inputs.reader, Inputs.pushed, Inputs.message, Inputs.clockLow, MemoryBoundary.address,
    FinalRamProvider.addressInput]
  obtain ⟨domain, word, low, high, clockHigh, previousHigh, read⟩ := h_assumptions
  have address := (FinalRamProvider.proverAssumptions_iff _ env.data env.hint).mpr domain
  exact ⟨address.1, address.2, word, low, high, clockHigh, previousHigh,
    ⟨Or.inr rfl, fun _ => word, Readers.ClkDiscipline.of_cpuState_spec (fun _ => ⟨low, high⟩)⟩, read⟩

def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  elaborated
  Spec input _ _ := Spec input
  ProverAssumptions input _ _ := ProverAssumptions input
  soundness
  completeness
  channelsWithRequirements := [memoryChannel.toRaw, channel.toRaw]

end SP1Clean.HostRamAccessChip
