import SP1Clean.Proofs.Chips.HostRamAccessChip.Formal
import SP1Clean.Soundness.TypedTime
import SP1Clean.Soundness.TypedInteractions
import SP1Clean.Soundness.TouchChains

/-! # Host RAM touches before value grounding

The host access circuit fixes one aligned RAM key and a write at the call clock plus one.
Its Byte checks and timestamp assertions establish the local access discipline without using
prior Memory values. Prior low-clock bounds remain conditional until the complete ledger
transfers them from produced records. These are the facts needed to include host writes in
mixed grounding; their value truth is a later conclusion of that walk.
-/

namespace SP1Clean.Soundness.HostRamTouches

open Circuit Air.Flat Channels HostRamAccessChip Semantics TimedGrounding

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem byte_children (ops : Operations (ZMod p)) (env : Environment (ZMod p))
    (lawful : ops.SubcircuitChannelsLawful) (constraints : ops.ConstraintsHold env)
    (bytes : ops.ChannelGuarantees byteChannel.toRaw env) :
    ∀ child ∈ ops.subcircuits,
      child.2.channelsWithGuarantees ⊆ [byteChannel.toRaw] →
      child.2.Assumptions env → child.2.Spec env := by
  intro child member channels assumptions
  apply (child.2.soundness env assumptions
    (constraintsHoldFlat_subcircuit_of_mem env ops child.2 member constraints) ?_).1
  rw [FlatOperation.guarantees_iff_forall_mem]
  have allowed := (lawful child member).1 env
  rw [FlatOperation.inChannelsOrGuarantees_iff_forall_mem] at allowed
  have inherited := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env ops child.2 member bytes
  rw [FlatOperation.channelGuarantees_iff_forall_mem] at inherited
  intro interaction present
  rcases allowed interaction present with channel | valid
  · exact inherited interaction present (List.mem_singleton.mp (channels channel))
  · exact valid

omit [Fact (2 ^ 25 < p)] in
private theorem range_bound (n : ℕ) (bound : 2 ^ n < p) (input : Expression (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p))
    (checked :
      ((Gadgets.ToBits.rangeCheck n bound).toSubcircuit offset input).channelsWithGuarantees ⊆
        [byteChannel.toRaw] →
      ((Gadgets.ToBits.rangeCheck n bound).toSubcircuit offset input).Assumptions env →
      ((Gadgets.ToBits.rangeCheck n bound).toSubcircuit offset input).Spec env) :
    (eval env input).val < 2 ^ n := by
  exact checked (by change [] ⊆ _; exact List.nil_subset _) (by trivial)

private theorem local_bounds (input : Var Inputs (ZMod p))
    (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((HostRamAccessChip.main input).operations offset).ConstraintsHold env)
    (bytes : ((HostRamAccessChip.main input).operations offset).ChannelGuarantees byteChannel.toRaw env) :
    let row := eval env input
    MemoryBoundary.CanonicalSpec row.pushed ∧ RamKey row.pushed ∧ Word.isU64 row.new_value ∧
    Readers.ClkDiscipline row.clockLow (1 : ZMod p) ∧
    row.clk_high.val < 2 ^ 24 ∧ row.access.access_timestamp.prev_high.val < 2 ^ 24 := by
  have children := byte_children _ env (circuit.subcircuitChannelsLawful input offset) constraints bytes
  change ∀ child ∈ ((HostRamAccessChip.main input).operations offset).subcircuits,
    child.2.channelsWithGuarantees ⊆ [byteChannel.toRaw] →
    child.2.Assumptions env → child.2.Spec env at children
  simp only [HostRamAccessChip.main, circuit_norm, Operations.subcircuits] at children
  have address := children _ (Or.inl rfl)
  have addressChecked := children _ (Or.inr (Or.inl rfl))
  have word := children _ (Or.inr (Or.inr (Or.inl rfl)))
  have low := children _ (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have high := children _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have clockHigh := children _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have previousHigh := children _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
  clear children
  simp only [WordRangeCheck.circuit, circuit_norm, WordRangeCheck.Assumptions,
    WordRangeCheck.Spec, List.nil_subset, true_implies] at word address
  have lowBound := range_bound 13 _ _ _ env low
  have highBound := range_bound 8 _ _ _ env high
  have clockHighBound := range_bound 24 _ _ _ env clockHigh
  have previousHighBound := range_bound 24 _ _ _ env previousHigh
  clear low high clockHigh previousHigh
  have checked := addressChecked (by change [byteChannel.toRaw] ⊆ _; exact List.Subset.refl _)
  clear addressChecked
  simp only [circuit_norm, AddressOperation.circuit] at checked
  have evaluated : ProvableStruct.eval env (FinalRamProvider.addressInput input.pushed) =
      FinalRamProvider.addressInput (eval env input).pushed := by
    rcases input with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
    simp only [FinalRamProvider.addressInput, Inputs.pushed, MemoryBoundary.address, circuit_norm]
  rw [evaluated] at checked
  have addressEq : Vector.map (Expression.eval env) (MemoryBoundary.address input.pushed) =
      MemoryBoundary.address (eval env input).pushed := by
    rcases input with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
    simp only [Inputs.pushed, MemoryBoundary.address, circuit_norm]
  rw [addressEq] at address
  have zero : Word.isU64 (#v[0, 0, 0, 0] : Word (ZMod p)) := by
    apply Word.isU64_of_cases <;> norm_num
  have addressSpec := (checked ⟨address, zero, Or.inr rfl⟩).2.2.2 rfl
  refine ⟨FinalRamProvider.canonical _ address _ addressSpec,
    HostRamAccessChip.ram_key _ address _ addressSpec, ?_⟩
  clear constraints bytes checked addressSpec address evaluated addressEq zero
  rcases input with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
  rcases access with ⟨prior, timestamp⟩
  rcases timestamp with ⟨prevHigh, prevLow, compare, diffLow, diffHigh⟩
  simp only [circuit_norm] at lowBound highBound clockHighBound previousHighBound ⊢
  exact ⟨word, Readers.ClkDiscipline.of_cpuState_spec (fun _ => ⟨lowBound, highBound⟩),
    clockHighBound, previousHighBound⟩

omit [Fact (2 ^ 25 < p)] in
@[local circuit_norm] private theorem range_length (n : ℕ) (bound : 2 ^ n < p)
    (input : Expression (ZMod p)) :
    (Gadgets.ToBits.rangeCheck n bound).localLength input = n := rfl

private theorem timestamp_facts (input : Var Inputs (ZMod p)) (offset : ℕ)
    (env : Environment (ZMod p))
    (constraints : ((HostRamAccessChip.main input).operations offset).ConstraintsHold env)
    (bytes : ((HostRamAccessChip.main input).operations offset).ChannelGuarantees byteChannel.toRaw env) :
    let row := eval env input
    ActiveMemoryTimestampFacts row.access.access_timestamp.compare_low
      row.access.access_timestamp.prev_high row.access.access_timestamp.prev_low
      row.access.access_timestamp.diff_low_limb row.access.access_timestamp.diff_high_limb
      row.clk_high row.clockLow := by
  have retained : ⟨offset + 201, Readers.MemoryAccess.circuit.toSubcircuit (offset + 201) input.reader⟩ ∈
      ((HostRamAccessChip.main input).operations offset).subcircuits := by
    simp only [HostRamAccessChip.main, circuit_norm, Operations.subcircuits]
  have checked := constraintsHold_generalSubcircuit_of_mem env _ Readers.MemoryAccess.circuit
    input.reader (offset + 201) retained constraints
  have guarantees := channelGuarantees_subcircuit_of_mem byteChannel.toRaw env _ _ retained bytes
  have facts := Readers.MemoryAccess.timestampFacts_of_constraintsAndByteGuarantees input.reader
    (offset + 201) env checked guarantees rfl
  rcases input with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
  rcases access with ⟨prior, timestamp⟩
  rcases timestamp with ⟨prevHigh, prevLow, compare, diffLow, diffHigh⟩
  simpa only [Inputs.reader, Inputs.clockLow, circuit_norm] using facts

/-- Structural RAM access facts derived before the walk establishes previous-value truth.
Only strict predecessor order needs the prior record's low-clock bound, supplied later by balance. -/
structure AccessFacts (input : Inputs (ZMod p)) : Prop where
  canonical : MemoryBoundary.CanonicalSpec input.pushed
  ram : RamKey input.pushed
  value : MemoryMsg.isU64 input.pushed
  priorHigh : input.prior.clk_high.val < 2 ^ 24
  pushHigh : input.pushed.clk_high.val < 2 ^ 24
  pushLow : MemoryMsg.ClkBound input.pushed
  time : MemoryMsg.timeNat input.pushed = clkNat input.clk_high input.clockLow + 1
  touch : TouchOK (clkNat input.clk_high input.clockLow)
    (input.prior, clkNat input.clk_high input.clockLow) input.pushed
  order : MemoryMsg.ClkBound input.prior → MemoryMsg.timeNat input.prior < MemoryMsg.timeNat input.pushed

omit [Fact (2 ^ 25 < p)] in
private theorem touch_of_time (input : Inputs (ZMod p)) (ram : RamKey input.pushed)
    (time : MemoryMsg.timeNat input.pushed = clkNat input.clk_high input.clockLow + 1) :
    TouchOK (clkNat input.clk_high input.clockLow)
      (input.prior, clkNat input.clk_high input.clockLow) input.pushed := by
  have notRegister : ¬(input.addr0.val < 32 ∧ input.addr1 = 0 ∧ input.addr2 = 0) := by
    rintro ⟨small, zero1, zero2⟩
    have lower := ram.1
    simp [Inputs.pushed, MemoryBoundary.address, Word.toNat, zero1, zero2] at lower
    omega
  have hloc : MemoryMsg.locOf input.pushed = .ram (BitVec.ofNat 61
      ((input.addr0.val + input.addr1.val * 2 ^ 16 + input.addr2.val * 2 ^ 32) / 8)) := by
    unfold MemoryMsg.locOf
    simp only [Inputs.pushed]
    exact if_neg notRegister
  refine ⟨rfl, Nat.le_refl _, Nat.le_add_right _ _, Or.inr ?_⟩
  rw [hloc, writeOffset_ram]
  exact time

/-- The actual host RAM circuit proves the touch used by mixed grounding from constraints and
Byte guarantees alone. This theorem neither assumes nor concludes prior Memory-value truth. -/
theorem of_constraints (input : Var Inputs (ZMod p)) (offset : ℕ) (env : Environment (ZMod p))
    (constraints : ((HostRamAccessChip.main input).operations offset).ConstraintsHold env)
    (bytes : ((HostRamAccessChip.main input).operations offset).ChannelGuarantees byteChannel.toRaw env) :
    AccessFacts (eval env input) := by
  obtain ⟨canonical, ram, word, discipline, high, previousHigh⟩ := local_bounds input offset env constraints bytes
  have timestamp := timestamp_facts input offset env constraints bytes
  have time := HostRamAccessChip.pushed_time (eval env input) discipline
  refine ⟨canonical, ram, word, previousHigh, high, discipline.at_one rfl,
    time, touch_of_time _ ram time, ?_⟩
  intro previousLow
  exact memoryTimeNat_lt_of_memoryAccessFacts _ _ _ _ _ _ _ _ _ previousLow previousHigh timestamp rfl rfl rfl rfl

end SP1Clean.Soundness.HostRamTouches
