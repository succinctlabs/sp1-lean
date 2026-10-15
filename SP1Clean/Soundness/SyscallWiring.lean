import SP1Clean.Soundness.ChipContracts
import SP1Clean.Soundness.SyscallGrounding
import SP1Clean.Soundness.SyscallInputs

/-! # Wiring a syscall row into the walk

`syscallStepFact_of_advance` needs the row's `Spec`, its `SelectorsValid`, its `PulledFacts` and its
`SyscallRowContext` *before* the walk runs. All four are reachable from the ensemble — but the route
to `Spec` runs through `Component.weakSoundness`, which consumes the row's **Memory** channel
guarantees, and those are a conclusion of grounding rather than an input to it.

That is the same currency circularity the ordinary rows hit, and it has the same resolution: the
walk's own step antecedent already hands each row `isU64 ∧ ClkBound` for its pulls before asking for
the step fact, so the guarantee can be rebuilt from the antecedent rather than from the walk's
output. `DecodedInstructionRow.memoryChannelGuarantees_of_pullCurrency` is the instruction-row
version. `SyscallInputs` provides the component-local syscall implementation; this file keeps
the legacy assembly specializations. The mixed native carrier derives HALT separately through
`HaltGrounding`. -/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open SP1Clean.Machine
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg memoryChannel byteChannel programChannel)
open Air.Flat
open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

-- Named rather than anonymous: `SyscallTrail` already declares an anonymous `Fact (2 ^ 17 < p)`
-- instance in this namespace, and `local` scopes the *use* but not the generated declaration name.
local instance syscallWiring_fact_24 : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance syscallWiring_fact_17 : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- **The circularity break at a syscall row.** The row's three pulled priors carry `isU64 ∧
ClkBound` in the walk's currency antecedent; that is exactly the memory channel's `Guarantees`, so
the row's own Memory `ChannelGuarantees` follows without any appeal to the walk's output.

The three *pushes* need nothing: `consumedMessages` keeps only the pull-polarity interactions, and a
boolean gate can never make a push's `signedVal` negative. -/
theorem syscallInstrsRow_memoryGuarantees_of_pullCurrency
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    {row : Array (ZMod p)} (rowMem : row ∈ (syscallInstrsTable witness).table)
    (currency : ∀ mp ∈
        (syscallRowFacts (syscallInstrsRow witness.data row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1) :
    (syscallInstrsTable witness).component.operations.ChannelGuarantees memoryChannel.toRaw
      (Environment.fromArray row witness.data) :=
  syscallInstrsRow_memoryGuarantees_of_component _ witness.data (syscallInstrsTable_component witness)
    (constraints _ (List.getElem_mem (syscallInstrsIndex_lt_tablesLength witness))) rowMem currency

/-- **A syscall row's `Spec`, from the walk's currency rather than from grounding.** This is the
statement `SyscallRowWiring` is built on: everything the row's meaning needs is either a finished
channel (Byte, Program) or the antecedent the walk supplies anyway. -/
theorem syscallInstrsRow_spec_of_pullCurrency
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels)
    {row : Array (ZMod p)} (rowMem : row ∈ (syscallInstrsTable witness).table)
    (currency : ∀ mp ∈
        (syscallRowFacts (syscallInstrsRow witness.data row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1) :
    SyscallInstrsChip.Spec (syscallInstrsRow witness.data row) := by
  have member := List.getElem_mem (syscallInstrsIndex_lt_tablesLength witness)
  have finished := (sp1_finishedChannel_guarantees witness constraints balanced).2 _ member
  exact (syscallInstrsRow_contract_of_component _ witness.data (syscallInstrsTable_component witness)
    (constraints _ member) finished.1 finished.2 rowMem currency).1

/-- **The row's committed `ECALL` fetch satisfies the Program bus's `RowSpec`.** The Program channel
is finished, so the row's single gated pull carries its guarantee outright — the same route
`decodedInstructionRow_programRowSpec` takes for an instruction row. -/
theorem syscallInstrsRow_programRowSpec
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels)
    {row : Array (ZMod p)} (rowMem : row ∈ (syscallInstrsTable witness).table)
    (real : (syscallInstrsRow witness.data row).is_real = 1) :
    Channels.ProgramMsg.RowSpec (SyscallInstrsChip.programMessage (syscallInstrsRow witness.data row)) :=
  syscallInstrsRow_programRowSpec_of_component _ witness.data (syscallInstrsTable_component witness)
    ((sp1_finishedChannel_guarantees witness constraints balanced).2 _
      (List.getElem_mem (syscallInstrsIndex_lt_tablesLength witness))).2 rowMem real

/-- **The row's `PulledFacts`, assembled from the three buses.** Nothing here is row-local: the
first five conjuncts are the Program bus's `RowSpec` at the committed `ECALL`, the next six are the
walk's own currency at the three register pulls, and the last — the written `t0` word's
`Word.isU64` — is the byte bus's four `Range 16` checks, because no arm of the `Spec` constrains it
(`HINT_LEN` deliberately leaves the result free). -/
theorem syscallInstrsRow_pulledFacts
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels)
    {row : Array (ZMod p)} (rowMem : row ∈ (syscallInstrsTable witness).table)
    (currency : ∀ mp ∈ (syscallRowFacts (syscallInstrsRow witness.data row)).memPulls,
      MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1) :
    SyscallInstrsChip.PulledFacts (syscallInstrsRow witness.data row) := by
  have member := List.getElem_mem (syscallInstrsIndex_lt_tablesLength witness)
  have finished := (sp1_finishedChannel_guarantees witness constraints balanced).2 _ member
  exact (syscallInstrsRow_contract_of_component _ witness.data (syscallInstrsTable_component witness)
    (constraints _ member) finished.1 finished.2 rowMem currency).2

/-- **The row's three operand columns are `x5`/`x10`/`x11`.** Nothing row-local says so — the chip
passes its own columns where `HaltChip` hardcodes the constants — so it is read off the committed
`ECALL` row on the Program bus, whose operand fields *are* those constants
(`Target.ecallProgramRow`). This is what lets `MemoryMsg.locOf` decode each of the row's touches to
`.reg`, and hence what makes `TouchOK` satisfiable at offsets 3 and 4 at all.

Stated in the `((n : ℕ) : ZMod p) = column` direction because that is the form
`Semantics.MemoryMsg.locOf_register` consumes. -/
theorem syscallInstrsRow_operands {program : Target.GuestProgram}
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) (providerBound : ProgramProviderBound program witness)
    {row : Array (ZMod p)} (rowMem : row ∈ realSyscallInstrsRows witness) :
    ((5 : ℕ) : ZMod p) = (syscallInstrsRow witness.data row).op_a ∧
      ((10 : ℕ) : ZMod p) = (syscallInstrsRow witness.data row).op_b ∧
      ((11 : ℕ) : ZMod p) = (syscallInstrsRow witness.data row).op_c := by
  have shape :=
    (witness_syscallRow_ecallTruth witness constraints balanced providerBound rowMem).2
  refine ⟨?_, ?_, ?_⟩
  · have h := congrArg (fun r : SP1Clean.ProgramChip.ProgramRow (ZMod p) => r.op_a) shape
    simpa [Target.ecallProgramRow, Semantics.rowOfMsg,
      SyscallInstrsChip.programMessage] using h.symm
  · have h := congrArg
      (fun r : SP1Clean.ProgramChip.ProgramRow (ZMod p) => r.op_b[0]) shape
    simpa [Target.ecallProgramRow, Semantics.rowOfMsg,
      SyscallInstrsChip.programMessage] using h.symm
  · have h := congrArg
      (fun r : SP1Clean.ProgramChip.ProgramRow (ZMod p) => r.op_c[0]) shape
    simpa [Target.ecallProgramRow, Semantics.rowOfMsg,
      SyscallInstrsChip.programMessage] using h.symm

/-! ## Absorbing the syscall table's Memory summand

`memoryBalance_of_alignsWith` carries the `SyscallInstrs` table's produced and consumed Memory
messages as a *side term* on both sides, exactly as it carries the Halt table's. That is the right
shape for a table whose rows are extracted after the walk. It is the wrong shape for a table whose
rows are *walked*: the walk already accounts for a row's touches through `pushesAt`/`pullsAt`, so
carrying them again would double-count.

The two lemmas below are the absorption. They say the side term *is* the walked term, so the summand
can be dropped from the balance's conclusion rather than tracked. Note that
`memoryFrontierBalance` keeps its syscall summand — it is the raw ledger form and correct there;
what loses the term is this balance's conclusion. -/

/-- The syscall table's produced Memory messages at a location are exactly its rows' walked pushes. -/
theorem syscall_pushesAt_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (syscallRows : List (Array (ZMod p)))
    (exhaustive : syscallRows.Perm (realSyscallInstrsRows witness))
    (loc : Semantics.MemLoc) :
    TimedGrounding.pushesAt
        (syscallRows.map fun row => syscallRowFacts (syscallInstrsRow witness.data row)) loc
      = Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(producedMessages (typedTableInteractionsWith (syscallInstrsTable witness) witness.data
            memoryChannel)) : Multiset (MemoryMsg (ZMod p))) := by
  rw [show (syscallRows.map fun row => syscallRowFacts (syscallInstrsRow witness.data row))
      = (syscallRows.map (syscallInstrsRow witness.data)).map syscallRowFacts from
        by rw [List.map_map]; rfl,
    syscallRows_pushesAt, syscallInstrs_producedMessages_eq witness constraints,
    List.flatMap_map]
  refine congrArg (Multiset.filter _) ?_
  rw [Multiset.coe_eq_coe]
  exact List.Perm.flatMap_right _ exhaustive

/-- The consumed twin of `syscall_pushesAt_eq`. -/
theorem syscall_pullsAt_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (syscallRows : List (Array (ZMod p)))
    (exhaustive : syscallRows.Perm (realSyscallInstrsRows witness))
    (loc : Semantics.MemLoc) :
    TimedGrounding.pullsAt
        (syscallRows.map fun row => syscallRowFacts (syscallInstrsRow witness.data row)) loc
      = Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(consumedMessages (typedTableInteractionsWith (syscallInstrsTable witness) witness.data
            memoryChannel)) : Multiset (MemoryMsg (ZMod p))) := by
  rw [show (syscallRows.map fun row => syscallRowFacts (syscallInstrsRow witness.data row))
      = (syscallRows.map (syscallInstrsRow witness.data)).map syscallRowFacts from
        by rw [List.map_map]; rfl,
    syscallRows_pullsAt, syscallInstrs_consumedMessages_eq witness constraints,
    List.flatMap_map]
  refine congrArg (Multiset.filter _) ?_
  rw [Multiset.coe_eq_coe]
  exact List.Perm.flatMap_right _ exhaustive

/-- **The walked per-location Memory balance.** `memoryBalance_of_alignsWith`'s conclusion carries
four summands beside the instruction rows' touches: the two boundary frontiers, the MemoryBump
refresh pairs, the Halt table's records, and the `SyscallInstrs` table's. Once the syscall rows are
*walked*, the last of those is no longer a side term — it is part of the walk — so the balance is
restated over the combined carrier with that summand gone.

`splitPerm` is the only new obligation, and it is the honest statement of what "the trail is an
arbitrary interleaving" means: the walked carrier's facts are, up to order, the instruction rows'
aligned facts together with the syscall rows' facts. `pushesAt`/`pullsAt` are multiset sums, so the
interleaving itself never has to be reconstructed. -/
theorem walkedMemoryBalance
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (memBinary : ∀ interaction ∈ typedEnsembleInteractionsWith witness memoryChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1)
    (initPure : consumedMessages (typedTableInteractionsWith (memoryInitProviderTable witness) witness.data
      memoryChannel) = [])
    (finPure : producedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness) witness.data
      memoryChannel) = [])
    (initUnique : MemoryInitProviderUnique witness)
    (finalizeUnique : MemoryFinalizeProviderUnique witness)
    (paddingEmpty : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real ≠ 1 →
        decoded.producedMemoryMessages witness.data = [] ∧
          decoded.consumedMemoryMessages witness.data = [])
    (orderedRows : List (DecodedInstructionRow p))
    (exhaustive : orderedRows.Perm (realDecodedInstructionRows witness.data witness.tables))
    (g : DecodedInstructionRow p → Semantics.RowFacts p)
    (aligns : ∀ d ∈ orderedRows, TimedGrounding.AlignsWith (g d)
      (d.ordinaryRowFacts witness.data))
    (syscallRows : List (Array (ZMod p)))
    (syscallExhaustive : syscallRows.Perm (realSyscallInstrsRows witness))
    (walkedRows : List (WalkedRow p))
    (splitPerm : (walkedRows.map (WalkedRow.facts g)).Perm
      (orderedRows.map g ++ syscallRows.map fun row => syscallRowFacts (syscallInstrsRow witness.data row)))
    (loc : Semantics.MemLoc) :
    TimedGrounding.optMS (memoryInitFrontier witness loc)
        + TimedGrounding.pushesAt (walkedRows.map (WalkedRow.facts g)) loc
        + Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(producedMessages (typedTableInteractionsWith (memoryBumpTable witness) witness.data
            memoryChannel)) : Multiset (MemoryMsg (ZMod p)))
        + Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(producedMessages (typedTableInteractionsWith (haltTable witness) witness.data
            memoryChannel)) : Multiset (MemoryMsg (ZMod p))) =
      TimedGrounding.optMS (memoryFinalizeFrontier witness loc)
        + TimedGrounding.pullsAt (walkedRows.map (WalkedRow.facts g)) loc
        + Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(consumedMessages (typedTableInteractionsWith (memoryBumpTable witness) witness.data
            memoryChannel)) : Multiset (MemoryMsg (ZMod p)))
        + Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(consumedMessages (typedTableInteractionsWith (haltTable witness) witness.data
            memoryChannel)) : Multiset (MemoryMsg (ZMod p))) := by
  have base := memoryBalance_of_alignsWith witness balanced memBinary initPure finPure
    initUnique finalizeUnique paddingEmpty orderedRows exhaustive g aligns loc
  have hpush : TimedGrounding.pushesAt (walkedRows.map (WalkedRow.facts g)) loc
      = TimedGrounding.pushesAt (orderedRows.map g) loc
        + Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(producedMessages (typedTableInteractionsWith (syscallInstrsTable witness) witness.data
            memoryChannel)) : Multiset (MemoryMsg (ZMod p))) := by
    rw [pushesAt_perm splitPerm loc, TimedGrounding.pushesAt_append,
      syscall_pushesAt_eq witness constraints syscallRows syscallExhaustive loc]
  have hpull : TimedGrounding.pullsAt (walkedRows.map (WalkedRow.facts g)) loc
      = TimedGrounding.pullsAt (orderedRows.map g) loc
        + Multiset.filter (fun m => Semantics.MemoryMsg.locOf m = loc)
          (↑(consumedMessages (typedTableInteractionsWith (syscallInstrsTable witness) witness.data
            memoryChannel)) : Multiset (MemoryMsg (ZMod p))) := by
    rw [pullsAt_perm splitPerm loc, TimedGrounding.pullsAt_append,
      syscall_pullsAt_eq witness constraints syscallRows syscallExhaustive loc]
  rw [hpush, hpull]
  -- Both sides are now the base balance's terms in a different order; Memory multisets form an
  -- additive commutative monoid, so AC-normalizing both settles it.
  simp only [add_assoc, add_left_comm, add_comm] at base ⊢
  exact base

/-! ## The dynamic row consumer, at the event trajectory

`DecodedInstructionRow.dynamicGrounded_of_weakCurrency` takes a `SailChain steps initial state` and
uses it in exactly three places, all of them `localValueAt_stepStart_iff` — the same single appeal
that `RowWiring.advance_at` made. Replacing it with `localValueAtG_stepStart_iff` re-indexes the
whole consumer off the trajectory, which is what lets the engine's conclusion stop being
`SailChain`-shaped. `DynamicGroundedRow` itself never mentioned a chain; only the quantifier in
front of it did. -/

theorem RowWiring.valueOperandsBound_of_pullCurrencyG
    {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring view rf) {traj : Semantics.Trajectory} {initial state : SailState}
    {tl : Semantics.Timeline} {n : ℕ}
    (curr : ∀ mp ∈ rf.memPulls,
      Semantics.LocalValueAtG traj initial tl (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    (htraj : traj n = some state)
    (rowTime : StateMsg.timeNat rf.statePull = tl.start n) :
    Target.ValueOperandsBound view state := by
  constructor
  · intro index immediate indexEq
    obtain ⟨mp, hmp, location, value⟩ := wiring.opB_pull index immediate indexEq
    have current := curr mp hmp
    rw [location, value, wiring.readTime mp hmp, rowTime] at current
    exact (TimedGrounding.localValueAtG_stepStart_iff htraj).mp current
  · intro index immediate indexEq
    obtain ⟨mp, hmp, location, value⟩ := wiring.opC_pull index immediate indexEq
    have current := curr mp hmp
    rw [location, value, wiring.readTime mp hmp, rowTime] at current
    exact (TimedGrounding.localValueAtG_stepStart_iff htraj).mp current

theorem RowWiring.sourceAValueBound_of_pullCurrencyG
    {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring view rf) {traj : Semantics.Trajectory} {initial state : SailState}
    {tl : Semantics.Timeline} {n : ℕ}
    (curr : ∀ mp ∈ rf.memPulls,
      Semantics.LocalValueAtG traj initial tl (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    (htraj : traj n = some state)
    (rowTime : StateMsg.timeNat rf.statePull = tl.start n) :
    Target.SourceAValueBound view state := by
  intro index indexEq
  obtain ⟨mp, hmp, location, value⟩ := wiring.opA_pull index indexEq
  have current := curr mp hmp
  rw [location, value, wiring.readTime mp hmp, rowTime] at current
  exact (TimedGrounding.localValueAtG_stepStart_iff htraj).mp current

theorem RowWiring.memoryPullsBound_of_pullCurrencyG
    {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring view rf) {traj : Semantics.Trajectory} {initial state : SailState}
    {tl : Semantics.Timeline} {n : ℕ}
    (curr : ∀ mp ∈ rf.memPulls,
      Semantics.LocalValueAtG traj initial tl (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    (htraj : traj n = some state)
    (rowTime : StateMsg.timeNat rf.statePull = tl.start n) :
    MemoryPullsBound rf state := by
  intro mp hmp
  have current := curr mp hmp
  rw [wiring.readTime mp hmp, rowTime] at current
  exact (TimedGrounding.localValueAtG_stepStart_iff htraj).mp current

/-- **The weak dynamic-row consumer, event-indexed.** `dynamicGrounded_of_weakCurrency` with its
`SailChain` replaced by `traj n = some state` and its `initialClock + 8 * steps` by `tl.start n` —
the two places a 264-tick row makes the Sail form unusable. -/
theorem DecodedInstructionRow.dynamicGroundedG_of_weakCurrency
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (contracts : ChipGroundingContracts decoded.chip)
    (program : Target.GuestProgram) {traj : Semantics.Trajectory}
    (initial state : SailState) {tl : Semantics.Timeline} {n : ℕ}
    (decode : Target.decodedInROM program
      (programAccess (decoded.toChipRow witness.data).view).toRow)
    (hcurr : ∀ mp ∈ (decoded.ordinaryRowFacts witness.data).memPulls,
      (MemoryMsg.isU64 (mp : MemoryMsg (ZMod p) × ℕ).1 ∧ MemoryMsg.ClkBound mp.1) ∧
        Semantics.LocalValueAtG traj initial tl (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value)
    (htraj : traj n = some state)
    (real : (decoded.toChipRow witness.data).is_real = 1)
    (rowTime : StateMsg.timeNat
      (statePullMessage (decoded.toChipRow witness.data)) = tl.start n) :
    DynamicGroundedRow witness.data program (decoded.toChipRow witness.data) state := by
  have guard := contracts.routing witness constraints decoded rfl decodedMem real program decode
  have memory := decoded.memoryChannelGuarantees_of_pullCurrency witness.data
    (fun mp hmp => ⟨(hcurr mp hmp).1.1, (hcurr mp hmp).1.2⟩)
  have assumptions := contracts.assumptions witness constraints balanced decoded rfl decodedMem
    real program decode memory
  let openInputs : DecodedRowOpenSoundnessInputs decoded witness.data := ⟨assumptions, memory⟩
  have wiring := contracts.wiring witness constraints balanced decoded rfl decodedMem real
    program decode openInputs
  have rowTime' : StateMsg.timeNat
      (decoded.ordinaryRowFacts witness.data).statePull = tl.start n := by
    simpa only [DecodedInstructionRow.ordinaryRowFacts_statePull] using rowTime
  have curr' : ∀ mp ∈ (decoded.ordinaryRowFacts witness.data).memPulls,
      Semantics.LocalValueAtG traj initial tl (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value :=
    fun mp hmp => (hcurr mp hmp).2
  have operands := wiring.valueOperandsBound_of_pullCurrencyG curr' htraj rowTime'
  have sourceA := wiring.sourceAValueBound_of_pullCurrencyG curr' htraj rowTime'
  have pulls := wiring.memoryPullsBound_of_pullCurrencyG curr' htraj rowTime'
  have ready := contracts.readiness witness constraints balanced decoded rfl decodedMem real guard
    program decode openInputs state operands sourceA pulls
  exact decoded.dynamicGrounded_of_inputs witness constraints balanced decodedMem program state
    { circuit := openInputs, ready, operands }

/-- Component-local ordinary execution facts on any trajectory whose successor at this row is
Sail's `stepOnce`. Wiring, chip semantics, and readiness are derived inside incoming Memory
currency; the enclosing assembly supplies only physical evidence, decode, and timeline position. -/
theorem ChipGroundingContracts.engineFactsLocalG_of_rowEffect
    {chip : SupportedChip p} (contracts : ChipGroundingContracts chip)
    (proverData : ProverData (ZMod p))
    (decoded : DecodedInstructionRow p) (hchip : decoded.chip = chip)
    (staticInputs : DecodedRowStaticInputs decoded proverData)
    (real : (decoded.toChipRow proverData).is_real = 1)
    (program : Target.GuestProgram)
    (decode : Target.decodedInROM program
      (programAccess (decoded.toChipRow proverData).view).toRow)
    (trajectory : Semantics.Trajectory) (initial : SailState) (tl : Semantics.Timeline)
    (codeMemoryCompatible : ∀ {m : ℕ} {st nx : SailState},
      trajectory m = some st →
        Target.RowEffect program (decoded.toChipRow proverData).view st nx →
          Target.RomLoaded program st → Target.RomLoaded program nx)
    (timeStep : ∀ n, StateMsg.timeNat (decoded.ordinaryRowFacts proverData).statePull = tl.start n →
      tl.start (n + 1) = tl.start n + 8)
    (step : Semantics.LocalStateTruthG program trajectory tl
        (decoded.ordinaryRowFacts proverData).statePull →
      ∀ n, StateMsg.timeNat (decoded.ordinaryRowFacts proverData).statePull = tl.start n →
      trajectory (n + 1) = (trajectory n).bind Machine.stepOnce) :
    Semantics.LocalStepFactG program
        trajectory initial
        tl (decoded.ordinaryRowFacts proverData) ∧
      Semantics.FrameFactG program
        trajectory initial
        tl (decoded.ordinaryRowFacts proverData) := by
  have guard := contracts.routingLocal proverData decoded hchip staticInputs.constraints real program decode
  have migrated : (decoded.toChipRow proverData).kind.advance.isSome = true := by
    show decoded.chip.kind.advance.isSome = true
    rw [hchip]
    exact contracts.migrated
  -- The D0 circularity break, unchanged: the row's open Memory inputs come from the *assumed* pull
  -- currency, never from the walk's own `Grounded` output.
  have mkOpenInputs : (∀ mp ∈ (decoded.ordinaryRowFacts proverData).memPulls,
        MemoryMsg.isU64 mp.1 ∧ MemoryMsg.ClkBound mp.1 ∧
        Semantics.LocalValueAtG trajectory initial
          tl
          (Semantics.MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
      DecodedRowOpenSoundnessInputs decoded proverData := fun hcurr => by
    let memory := decoded.memoryChannelGuarantees_of_pullCurrency proverData
      (fun mp hmp => ⟨(hcurr mp hmp).1, (hcurr mp hmp).2.1⟩)
    exact
      { assumptions := contracts.assumptionsLocal proverData decoded hchip staticInputs
          real program decode memory
        memory }
  have advance := ChipKind.advancePayload_of_migrated migrated
  refine ⟨?_, ?_⟩
  · intro hpull hcurr
    have inputs := mkOpenInputs hcurr
    exact ordinaryStepFactG_of_rowEffect
      (contracts.wiringLocal proverData decoded hchip staticInputs real program decode inputs)
      advance real (staticInputs.chipSpec inputs) decode
      (contracts.readinessLocal proverData decoded hchip staticInputs real guard program decode inputs)
      trajectory initial tl codeMemoryCompatible timeStep (step hpull) hpull hcurr
  · intro hpull hcurr loc value pushes current
    have inputs := mkOpenInputs hcurr
    exact ordinaryFrameFactG_of_advanceOnTrajectory
      (contracts.wiringLocal proverData decoded hchip staticInputs real program decode inputs)
      advance real (staticInputs.chipSpec inputs) decode
      (contracts.readinessLocal proverData decoded hchip staticInputs real guard program decode inputs)
      trajectory initial tl timeStep (step hpull) hpull hcurr loc value pushes current

/-- Preserve the public trajectory-wide contract as a specialization of the row-effect interface. -/
theorem ChipGroundingContracts.engineFactsLocalG_of_stateStep
    {chip : SupportedChip p} (contracts : ChipGroundingContracts chip)
    (proverData : ProverData (ZMod p))
    (decoded : DecodedInstructionRow p) (hchip : decoded.chip = chip)
    (staticInputs : DecodedRowStaticInputs decoded proverData)
    (real : (decoded.toChipRow proverData).is_real = 1)
    (program : Target.GuestProgram)
    (decode : Target.decodedInROM program
      (programAccess (decoded.toChipRow proverData).view).toRow)
    (trajectory : Semantics.Trajectory) (initial : SailState) (tl : Semantics.Timeline)
    (codeMemoryCompatible : ∀ {m : ℕ} {st nx : SailState},
      trajectory m = some st →
        Target.SailStep st nx → Target.RomLoaded program st → Target.RomLoaded program nx)
    (timeStep : ∀ n, StateMsg.timeNat (decoded.ordinaryRowFacts proverData).statePull = tl.start n →
      tl.start (n + 1) = tl.start n + 8)
    (step : Semantics.LocalStateTruthG program trajectory tl
        (decoded.ordinaryRowFacts proverData).statePull →
      ∀ n, StateMsg.timeNat (decoded.ordinaryRowFacts proverData).statePull = tl.start n →
      trajectory (n + 1) = (trajectory n).bind Machine.stepOnce) :
    Semantics.LocalStepFactG program
        trajectory initial
        tl (decoded.ordinaryRowFacts proverData) ∧
      Semantics.FrameFactG program
        trajectory initial
        tl (decoded.ordinaryRowFacts proverData) := by
  exact contracts.engineFactsLocalG_of_rowEffect proverData decoded hchip staticInputs real program decode
    trajectory initial tl (fun present effect => codeMemoryCompatible present effect.normal.sailStep)
    timeStep step

/-- The unguarded successor interface remains a specialization of incoming-state replay. -/
theorem ChipGroundingContracts.engineFactsLocalG
    {chip : SupportedChip p} (contracts : ChipGroundingContracts chip)
    (proverData : ProverData (ZMod p))
    (decoded : DecodedInstructionRow p) (hchip : decoded.chip = chip)
    (staticInputs : DecodedRowStaticInputs decoded proverData)
    (real : (decoded.toChipRow proverData).is_real = 1)
    (program : Target.GuestProgram)
    (decode : Target.decodedInROM program
      (programAccess (decoded.toChipRow proverData).view).toRow)
    (trajectory : Semantics.Trajectory) (initial : SailState) (tl : Semantics.Timeline)
    (codeMemoryCompatible : ∀ {m : ℕ} {st nx : SailState},
      trajectory m = some st →
        Target.SailStep st nx → Target.RomLoaded program st → Target.RomLoaded program nx)
    (timeStep : ∀ n, StateMsg.timeNat (decoded.ordinaryRowFacts proverData).statePull = tl.start n →
      tl.start (n + 1) = tl.start n + 8)
    (step : ∀ n, StateMsg.timeNat (decoded.ordinaryRowFacts proverData).statePull = tl.start n →
      trajectory (n + 1) = (trajectory n).bind Machine.stepOnce) :
    Semantics.LocalStepFactG program
        trajectory initial
        tl (decoded.ordinaryRowFacts proverData) ∧
      Semantics.FrameFactG program
        trajectory initial
        tl (decoded.ordinaryRowFacts proverData) := by
  exact contracts.engineFactsLocalG_of_stateStep proverData decoded hchip staticInputs real program decode
    trajectory initial tl codeMemoryCompatible timeStep (fun _ => step)

/-- The legacy ensemble and event transcript specialize the component-local engine facts. -/
theorem ChipGroundingContracts.engineFactsG
    {chip : SupportedChip p} (contracts : ChipGroundingContracts chip)
    (handler : Machine.ExecutableSyscallHandler) (events : List Machine.ExecutionEvent)
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p) (hchip : decoded.chip = chip)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (real : (decoded.toChipRow witness.data).is_real = 1)
    (program : Target.GuestProgram)
    (decode : Target.decodedInROM program
      (programAccess (decoded.toChipRow witness.data).view).toRow)
    (initial : SailState) (initialClock : ℕ)
    (codeMemoryCompatible : ∀ {m : ℕ} {st nx : SailState},
      Semantics.eventTrajectory handler program events initial m = some st →
        Target.SailStep st nx → Target.RomLoaded program st → Target.RomLoaded program nx)
    (positioned : ∀ n : ℕ,
      StateMsg.timeNat (decoded.ordinaryRowFacts witness.data).statePull
        = (Semantics.eventTimeline events initialClock).start n →
      events[n]? = some Machine.ExecutionEvent.ordinary) :
    Semantics.LocalStepFactG program
        (Semantics.eventTrajectory handler program events initial) initial
        (Semantics.eventTimeline events initialClock) (decoded.ordinaryRowFacts witness.data) ∧
      Semantics.FrameFactG program
        (Semantics.eventTrajectory handler program events initial) initial
        (Semantics.eventTimeline events initialClock) (decoded.ordinaryRowFacts witness.data) := by
  apply contracts.engineFactsLocalG witness.data decoded hchip
    (decodedRowStaticInputs_of_witness witness constraints balanced decoded decodedMem)
    real program decode (Semantics.eventTrajectory handler program events initial) initial
    (Semantics.eventTimeline events initialClock) codeMemoryCompatible
  · intro n time
    have event := positioned n time
    simp only [Semantics.eventTimeline_start, List.range_succ, List.map_append,
      List.sum_append, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    simp only [Semantics.durationAt, event, Machine.ExecutionEvent.duration_ordinary]
    omega
  · intro n time
    rw [Semantics.eventTrajectory_succ, positioned n time]
    rfl

/-! ## The row's semantic context, from the walk

`SyscallRowContext` names the five things a syscall row's meaning needs that the row itself does not
carry. `syscallInstrsRow_operands` supplied the first from the Program bus. The three below come
from the walk — the pulled state's pc and the three register reads. The released `pcCarry` premise
remains for source compatibility; `rowLaw_of_spec_and_pulledFacts` proves the row law without it. -/

/-- **`SyscallRowContext`, assembled at the walk's own state.** The three register reads all speak
about the *same* state, and that is the content of the `+0`/`+3`/`+2` read times being below
`regEffectOffset`: every one of them is still in the pre-write half of the row's window, so
`localValueAtG_regRead_of_traj` sends all three to `traj n`.

`ecall` then follows from `pcValue` and the committed `ECALL` fetch, which is where
`witness_syscallRow_ecallTruth` is spent a second time — once for the operand indices, once for the
fetch itself. -/
theorem syscallRowContext_of_currency {program : Target.GuestProgram}
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (constraints : witness.Constraints)
    (balanced : witness.BalancedChannels) (providerBound : ProgramProviderBound program witness)
    {row : Array (ZMod p)} (rowMem : row ∈ realSyscallInstrsRows witness)
    (pcCarry : ((syscallInstrsRow witness.data row).state.pc[0]).val + 4 < 2 ^ 16)
    {traj : Semantics.Trajectory} {initial source : SailState} {tl : Semantics.Timeline}
    {n : ℕ}
    (htraj : traj n = some source)
    (hpc : source.regs.get? Register.PC
      = some (Semantics.pcBits (SyscallInstrsChip.statePulledMessage (syscallInstrsRow witness.data row)).pc0
          (SyscallInstrsChip.statePulledMessage (syscallInstrsRow witness.data row)).pc1
          (SyscallInstrsChip.statePulledMessage (syscallInstrsRow witness.data row)).pc2))
    (htime : StateMsg.timeNat (SyscallInstrsChip.statePulledMessage (syscallInstrsRow witness.data row)) = tl.start n)
    (hcurr : ∀ mp ∈ (syscallRowFacts (syscallInstrsRow witness.data row)).memPulls,
      Semantics.LocalValueAtG traj initial tl
        (Semantics.MemoryMsg.locOf (mp : MemoryMsg (ZMod p) × ℕ).1) mp.2 mp.1.value) :
    SyscallRowContext (syscallInstrsRow witness.data row) program source := by
  obtain ⟨opA, opB, opC⟩ :=
    syscallInstrsRow_operands witness constraints balanced providerBound rowMem
  obtain ⟨locPullA, -⟩ := syscallRow_locOf_reg (syscallInstrsRow witness.data row) (i := 5#5) opA
    (syscallInstrsRow witness.data row).op_a_memory (syscallInstrsRow witness.data row).op_a_value 4
  obtain ⟨locPullB, -⟩ := syscallRow_locOf_reg (syscallInstrsRow witness.data row) (i := 10#5) opB
    (syscallInstrsRow witness.data row).op_b_memory (syscallInstrsRow witness.data row).op_b_memory.prev_value 3
  obtain ⟨locPullC, -⟩ := syscallRow_locOf_reg (syscallInstrsRow witness.data row) (i := 11#5) opC
    (syscallInstrsRow witness.data row).op_c_memory (syscallInstrsRow witness.data row).op_c_memory.prev_value 2
  obtain ⟨curA, curB, curC⟩ := syscallRowFacts_currency_split_values _ hcurr
  rw [locPullA, htime] at curA
  rw [locPullB, htime] at curB
  rw [locPullC, htime] at curC
  exact SyscallRowContext.of_pieces (syscallInstrsRow witness.data row) _ source opA opB opC pcCarry
    (witness_syscallRow_ecallTruth witness constraints balanced providerBound rowMem).1 hpc
    ((TimedGrounding.localValueAtG_stepStart_iff htraj).mp curA)
    (TimedGrounding.localValueAtG_regRead_of_traj (k := 3) htraj (by norm_num) curB)
    (TimedGrounding.localValueAtG_regRead_of_traj (k := 2) htraj (by norm_num) curC)

/-! ## The canonicity premise, at the native witness

D9's condition lives on the supported profile (`Model.Core.Profile.CanonicalSyscallCodes`) because it is a
fact about SP1's *executor*, not about its AIR: the AIR reads bytes 0 and 1 of `x5`, while
`SyscallCode::from_u32` dispatches on the full word and panics on a non-enumerated value. An
AIR-valid `HALT` row may therefore carry `x5 = 0x00010000`, which no execution produces.

The native side's projection into that predicate is below. It is what a caller must supply for a
syscall row's step fact, which takes `IsInlineCanonical` and cannot derive it — and the reason
`SyscallTableInactive.noActiveRows` cannot simply be dropped: without active syscall rows the
condition is vacuous, and with them it is a genuine, disclosed obligation. -/

/-- The decoded events of a witness's active syscall rows — the native side's projection into
`Model.Core.Profile.CanonicalSyscallCodes`. -/
noncomputable def syscallEventsOf (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    List Machine.CoreSyscallEvent :=
  (realSyscallInstrsRows witness).map fun row => syscallEventOfRow (syscallInstrsRow witness.data row)

/-- Reading the profile condition back at one active row — the form
`syscallStepFact_of_advance` consumes. -/
theorem isInlineCanonical_of_profile
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (canonical : SP1Clean.Model.Core.Profile.CanonicalSyscallCodes (syscallEventsOf witness))
    {row : Array (ZMod p)} (rowMem : row ∈ realSyscallInstrsRows witness) :
    (syscallEventOfRow (syscallInstrsRow witness.data row)).IsInlineCanonical :=
  canonical _ (List.mem_map_of_mem rowMem)

end SP1Clean.Soundness
