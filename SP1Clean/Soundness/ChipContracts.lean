import SP1Clean.Soundness.GroundingAdapter
import SP1Clean.Soundness.Grounding.RTypeChips
import SP1Clean.Soundness.Grounding.ITypeChips
import SP1Clean.Soundness.Grounding.ALUTypeChips
import SP1Clean.Soundness.Grounding.JTypeChips
import SP1Clean.Soundness.Grounding.ControlFlowChips
import SP1Clean.Soundness.Grounding.MemoryChips
import SP1Clean.Soundness.Decode
import SP1Clean.Soundness.MemoryFrontier
import SP1Clean.Proofs.Chips.LoadByteChip.Contracts
import SP1Clean.Proofs.Chips.LoadHalfChip.Contracts
import SP1Clean.Proofs.Chips.LoadWordChip.Contracts
import SP1Clean.Proofs.Chips.LoadDoubleChip.Contracts
import SP1Clean.Proofs.Chips.LoadX0Chip.Contracts
import SP1Clean.Proofs.Chips.SubChip.Contracts
import SP1Clean.Proofs.Chips.MulChip.Contracts

/-! # Per-chip grounding contracts — the `ChipGroundingContracts` bundle

The registry-wide per-chip obligation surface for the capstone seam
`supportedCore_orderedRows_dynamic` (`Soundness/AIR.lean`).  One `ChipGroundingContracts chip`
bundle collects everything the timed grounding assembly needs from one `SupportedChip` descriptor,
so the 25-chip rollout is a list of bundle instances rather than 25 bespoke capstone arguments.

The bundle serves the two seam consumers:

* **the engine feed** — `TimedGrounding.walk` consumes per row a `LocalStepFact`, a `FrameFact`
  (both produced by `GroundingAdapter` from the `wiring` field and the chip's registered
  `advance` payload; see `ChipGroundingContracts.engineFacts`), and a `RowOK` record;
* **the dynamic-row assembly** — `DecodedInstructionRow.dynamicGrounded_of_timedInputs`
  consumes the chip `Assumptions`, the walk's `Grounded` output, `advanceReady`, and the
  register-operand pull shape (see `DecodedInstructionRow.dynamicGrounded_of_contracts`).

**What is deliberately per-position, not per-chip.**  `RowOK.align8` (every state pull ≡ the public
initial clock mod 8) is a state-trail fact; `decodedInROM` is Program-bus grounding
(`supportedCore_orderedRows_programDecoded`); the row's clock position (`rowTime`) comes from
`statePullTime_of_decodedStateWalk`.  The `op_a = x0` dispatch bit is different: each chip's
`routing` field derives its declared `RdGuardFact` from that chip's physical constraints plus the
grounded Program decode.  It is never an independent assembly hypothesis.

`RowOK.touches`/`RowOK.chain_mono` are not duplicated as a second contract surface here:

* the positional pull/push pairing of `DecodedInstructionRow.ordinaryRowFacts` (pulls in
  consumed order, all read micro-times at the window start) is not the touch-aligned pairing
  `TouchOK` expects — e.g. Add's pulls `[op_a, op_b, op_c]` zip against pushes
  `[rb_b@+3, rb_c@+2, write@+4]`, so `loc_eq` fails positionally and the read-back `push_kind`
  disjunct needs per-access micro-times (`+3`/`+2`), not the uniform window start.  Choosing the
  aligned `RowFacts` carrier (and transporting `Grounded` across it) is arc-B assembly work; the
  `TypedMemory` module doc already anticipates replacing the ordinary carrier.
* `TouchOK.pull_lt_push` (the SP1 `prev_clk < access_clk` bound) is **not a purely local
  fact**: the in-circuit `RegisterAccessTimestamp` diff decomposition proves it only given a
  range bound on the pulled record's own time, which is supplied by the balance chain forcing
  (the matched frontier push was range-checked by its writer), not by this row's constraints.

The consumed surface is `rowAligned`, which directly supplies the aligned touches, `TouchOK`, and
per-location `IsChain` facts used by `rowOK_alignedOf`.  The generic `RowWiring.push_window` lemma
remains available for local reasoning, but no unused weaker duplicate is retained in the bundle.

Add is the validation anchor: `addChip_groundingContracts` discharges the whole bundle from the
existing `GroundingAdapter`/`AddChip.Contracts` lemmas. -/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open Sail LeanRV64D LeanRV64D.Functions
open Air.Flat Circuit
open SP1Clean.Soundness.Target
open SP1Clean.Soundness.TimedGrounding
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The `rd == x0` routing conclusion for one decoded row, phrased against the descriptor's declared
`RdGuard`.  A chip contract proves it from the chip's own routing constraint and canonical Program
decode; `readiness` may then consume it (notably `.nonX0` chips' `op_a ≠ 0` invariant). -/
def RdGuardFact (chip : SupportedChip p) (view : Trace.RowView (ZMod p)) : Prop :=
  match chip.rdGuard with
  | .any => True
  | .nonX0 => view.adapter.op_a ≠ 0
  | .onlyX0 => view.adapter.op_a = 0

/-- Every push of a wired row lands inside the row's effect window `[t, t+4]` — the generic
`TouchOK.push_lo`/`push_hi` half of the touch discipline, already forced by
`RowWiring.push_classified` for every chip. -/
theorem RowWiring.push_window {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring view rf) :
    ∀ m ∈ rf.memPushes, StateMsg.timeNat rf.statePull ≤ MemoryMsg.timeNat m ∧
      MemoryMsg.timeNat m ≤ StateMsg.timeNat rf.statePull + 4 := by
  intro m hm
  rcases wiring.push_classified m hm with ⟨mp, -, -, -, hlo, hhi, -⟩ | ⟨-, -, -, -, ht⟩ |
    ⟨-, mp, -, -, -, -, ht⟩ | ⟨-, -, -, -, ht⟩ | ⟨-, -, -, ht, -⟩
  · exact ⟨hlo, by omega⟩
  · omega
  · omega
  · omega
  · omega

section Contracts

variable [Fact (2 ^ 25 < p)]

/-- The state-dependent readiness boundary shared by every chip-family constructor.  It is asked
only after the row's open circuit inputs and all three live register-source bindings have been
derived from the exact grounded Memory interactions. -/
def ChipReadinessContract (chip : SupportedChip p) : Prop :=
  ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints → witness.BalancedChannels →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      RdGuardFact chip (decoded.toChipRow witness.data).view →
      ∀ (program : GuestProgram),
      decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
      DecodedRowOpenSoundnessInputs decoded witness.data →
      ∀ (state : SailState),
      Target.ValueOperandsBound (decoded.toChipRow witness.data).view state →
      Target.SourceAValueBound (decoded.toChipRow witness.data).view state →
      MemoryPullsBound (decoded.ordinaryRowFacts witness.data) state →
        (decoded.toChipRow witness.data).kind.advanceReady
          (decoded.toChipRow witness.data).inputs (decoded.toChipRow witness.data).cols
          program state

/-- The dynamic circuit-input contract shared by every chip-family constructor.  Naming this
dependent proposition keeps the selected chip descriptor folded while individual bundle instances
are elaborated; unfolding a full `GeneralFormalCircuit` merely to discover its `Assumptions`
projection is both semantically irrelevant and prohibitively expensive. -/
def ChipAssumptionsContract (chip : SupportedChip p) : Prop :=
  ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints → witness.BalancedChannels →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ (program : GuestProgram),
      decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
      decoded.chip.table.operations.ChannelGuarantees Channels.memoryChannel.toRaw
        (decoded.environment witness.data) →
      decoded.chip.table.Assumptions (decoded.environment witness.data)

/-- **The per-chip grounding-contract bundle.**  Everything the dynamic capstone seam needs from
one registered chip, quantified over the per-row residuals the assembly supplies (the canonical
witness with its constraints and balance, the decoded row with its registry membership and active
selector, and the open circuit inputs).  See the module doc for the field rationale and the
deliberately absent assembly-level facts. -/
structure ChipGroundingContracts (chip : SupportedChip p) : Prop where
  /-- The chip has migrated to the uniform `ChipKind.advance` payload. -/
  migrated : chip.kind.advance.isSome = true
  /-- The per-row `RowWiring` producer: the message ↔ view correspondences the grounding adapter
  consumes, from the finished Byte channel (clock decode), independently grounded Program decode
  (register-index bounds), and the row's own push `Requirements`. -/
  wiring : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints → witness.BalancedChannels →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ (program : GuestProgram),
      decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
      DecodedRowOpenSoundnessInputs decoded witness.data →
      RowWiring (decoded.toChipRow witness.data).view (decoded.ordinaryRowFacts witness.data)
  /-- The chip circuit's soundness-side `Assumptions` follow once the row's actual Memory pulls
  satisfy the Memory-channel guarantee.  This dependency is intentional: operand range facts belong
  to grounded Memory currency, while decode/address facts may additionally use constraints and the
  finished Byte/Program channels.  Requiring the whole assumption bundle before Memory grounding
  would reverse that dependency for load/store/shift chips. -/
  assumptions : ChipAssumptionsContract chip
  /-- The descriptor's `rd` guard follows from its physical assertion system and the canonical
  committed Program decode.  In particular, this field must not appeal to trace-generator routing
  or infer row existence from an unrelated selector. -/
  routing : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ (program : GuestProgram),
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
          RdGuardFact chip (decoded.toChipRow witness.data).view
  /-- The `advanceReady` producer: the reader passthrough (`cols = main inp`), committed Program
  decode facts (for example an immediate selector or decoded-PC bound), and whatever the routing
  guard supplies (`op_a ≠ 0` for the `.nonX0` write-routing chips).  The conclusion remains
  state-independent, but it is intentionally relative to the canonical ROM decode. -/
  readiness : ChipReadinessContract chip
  /-- The aligned-carrier `RowOK` producer (arc B): the row's memory touches admit an aligned
  ordering (`AlignsWith`) whose `TouchOK`/per-key `IsChain`/push-`ClkBound`/conditional-slot facts
  feed `rowOK_alignedOf`.  Register-index bounds come from Program decoding; timestamp bounds come
  from the finished Byte guarantees.  This field deliberately has no
  `DecodedRowOpenSoundnessInputs`: `RowOK` is an input to the grounding walk, so it cannot depend on
  the Memory truth that the walk itself produces. -/
  rowAligned : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints → witness.BalancedChannels →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ (program : GuestProgram),
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
        MemoryPullTimestampHighBound (decoded.ordinaryRowFacts witness.data) →
        ∃ touches : List (Touch p),
          AlignsWith (alignedOf (decoded.ordinaryRowFacts witness.data) touches)
              (decoded.ordinaryRowFacts witness.data) ∧
            (∀ tc ∈ touches,
              TouchOK (StateMsg.timeNat (decoded.ordinaryRowFacts witness.data).statePull)
                tc.1 tc.2) ∧
            (∀ loc : MemLoc, List.IsChain
              (fun a b : Touch p => MemoryMsg.timeNat a.2 < MemoryMsg.timeNat b.2)
              (touches.filter (fun pq => MemoryMsg.locOf pq.2 = loc))) ∧
            (∀ tc ∈ touches, SP1Clean.Channels.MemoryMsg.ClkBound tc.2) ∧
            (∀ tc ∈ touches, SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
              MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2)

/-- **The engine-feed consumer**: any decoded row of a contracted chip produces both timed-engine
records — the chip-generic form of `addRow_engineFacts`.  `decode` remains the Program-grounding
residual; the bundle derives the routing guard from it and the physical row constraints. -/
theorem ChipGroundingContracts.engineFacts
    {chip : SupportedChip p} (contracts : ChipGroundingContracts chip)
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p) (hchip : decoded.chip = chip)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (real : (decoded.toChipRow witness.data).is_real = 1)
    (program : GuestProgram)
    (decode : Target.decodedInROM program
      (programAccess (decoded.toChipRow witness.data).view).toRow)
    (initial : SailState) (initialClock : ℕ)
    (codeMemoryCompatible : SailCodeMemoryCompatible program initial) :
    LocalStepFact program initial initialClock (decoded.ordinaryRowFacts witness.data) ∧
      FrameFact program initial initialClock (decoded.ordinaryRowFacts witness.data) := by
  have guard := contracts.routing witness constraints decoded hchip decodedMem real program decode
  have migrated : (decoded.toChipRow witness.data).kind.advance.isSome = true := by
    show decoded.chip.kind.advance.isSome = true
    rw [hchip]
    exact contracts.migrated
  -- Build the row's open Memory inputs from the ASSUMED pull currency (`isU64 ∧ ClkBound`), not from
  -- the walk's own `Grounded` — the D0 circularity break.  The chip `Assumptions` are constraint-
  -- derivable (the bundle's `assumptions` field), so `openInputs` is available inside the step/frame
  -- currency antecedent without the grounded output.
  have mkOpenInputs : (∀ mp ∈ (decoded.ordinaryRowFacts witness.data).memPulls,
        SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧ SP1Clean.Channels.MemoryMsg.ClkBound mp.1 ∧
        LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
      DecodedRowOpenSoundnessInputs decoded witness.data := fun hcurr => by
    let memory := decoded.memoryChannelGuarantees_of_pullCurrency witness.data
      (fun mp hmp => ⟨(hcurr mp hmp).1, (hcurr mp hmp).2.1⟩)
    exact
      { assumptions := contracts.assumptions witness constraints balanced decoded hchip decodedMem
          real program decode memory
        memory }
  refine engineFacts_of_kind migrated real decode initial initialClock
    (fun hcurr => contracts.wiring witness constraints balanced decoded hchip decodedMem real
      program decode (mkOpenInputs hcurr))
    (fun hcurr => decoded.chipSpec_of_openSoundnessInputs witness constraints balanced decodedMem
      (mkOpenInputs hcurr))
    (fun hcurr state operands sourceA pulls =>
      contracts.readiness witness constraints balanced decoded hchip decodedMem real guard
        program decode (mkOpenInputs hcurr) state operands sourceA pulls)
    codeMemoryCompatible

/-- **The dynamic-row consumer**: bundle + the walk's `Grounded` output + the row's positional
facts assemble the `DynamicGroundedRow` demanded by `supportedCore_orderedRows_dynamic` — through
the one proved circuit path (`dynamicGrounded_of_timedInputs`), with readiness, assumptions, and
operand pulls all supplied by the bundle. -/
theorem DecodedInstructionRow.dynamicGrounded_of_contracts
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (contracts : ChipGroundingContracts decoded.chip)
    (program : GuestProgram) (initial state : SailState) (initialClock steps : ℕ)
    (decode : Target.decodedInROM program
      (programAccess (decoded.toChipRow witness.data).view).toRow)
    (grounded : TimedGrounding.Grounded program initial initialClock
      (decoded.ordinaryRowFacts witness.data))
    (chain : Target.SailChain steps initial state)
    (real : (decoded.toChipRow witness.data).is_real = 1)
    (rowTime : Semantics.StateMsg.timeNat
      (statePullMessage (decoded.toChipRow witness.data)) = initialClock + 8 * steps) :
    DynamicGroundedRow witness.data program (decoded.toChipRow witness.data) state := by
  have guard := contracts.routing witness constraints decoded rfl decodedMem real program decode
  have memory := decoded.memoryChannelGuarantees_of_grounded witness.data program initial
    initialClock grounded
  have assumptions := contracts.assumptions witness constraints balanced decoded rfl decodedMem
    real program decode memory
  let openInputs : DecodedRowOpenSoundnessInputs decoded witness.data := ⟨assumptions, memory⟩
  have wiring := contracts.wiring witness constraints balanced decoded rfl decodedMem real
    program decode openInputs
  have rowTime' : Semantics.StateMsg.timeNat
      (decoded.ordinaryRowFacts witness.data).statePull = initialClock + 8 * steps := by
    simpa only [ordinaryRowFacts_statePull] using rowTime
  have operands := wiring.valueOperandsBound_of_grounded grounded chain rowTime'
  have sourceA := wiring.sourceAValueBound_of_grounded grounded chain rowTime'
  have pulls := wiring.memoryPullsBound_of_grounded grounded chain rowTime'
  have ready := contracts.readiness witness constraints balanced decoded rfl decodedMem real guard
    program decode openInputs state operands sourceA pulls
  exact decoded.dynamicGrounded_of_grounded witness constraints balanced decodedMem program
    initial state initialClock assumptions grounded ready operands

end Contracts

/-! ## Registry assembly

`Soundness/AIR.lean` proves the generic assembly theorem
`supportedCore_orderedRows_dynamic_of_obligations`.  It chooses every bundle's aligned carrier,
feeds the seven inputs of `TimedGrounding.walk`, transports the result back to the ordinary physical
row, and invokes `DecodedInstructionRow.dynamicGrounded_of_contracts`.  The remaining rollout is
therefore finite: provide this bundle for every registered chip and prove the two structural Memory
selector facts collected by `SupportedCoreGroundingObligations`. -/

/-! ## Arc-B memory-balance reconciliation (walk input ⑦)

The `TimedGrounding.walk` per-location Memory balance is stated over the *aligned* carrier of the
*ordered* real rows, while `memoryFrontierBalance` (`Soundness/MemoryFrontier.lean`) proves it over
`memoryFrontierRows` — the *ordinary* carrier in `realDecodedInstructionRows` order.  These three
lemmas bridge the gap: `pushesAt`/`pullsAt` are invariant under (a) a permutation of the row batch
(the exhaustive `Perm`) and (b) the per-row `AlignsWith` push/pull permutations. -/

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- Per-row: an aligned carrier and its ordinary row contribute the *same* per-location push multiset
(the aligned pushes are a `Perm` of the ordinary ones). -/
theorem rowPushesAt_coe_eq_of_alignsWith {r_align r_ord : RowFacts p}
    (h : AlignsWith r_align r_ord) (loc : MemLoc) :
    (↑(rowPushesAt r_align loc) : Multiset (Channels.MemoryMsg (ZMod p))) =
      ↑(rowPushesAt r_ord loc) :=
  Multiset.coe_eq_coe.mpr (h.pushes.filter fun m => Semantics.MemoryMsg.locOf m = loc)

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- Per-row pull twin of `rowPushesAt_coe_eq_of_alignsWith` (the aligned pull *messages* are a `Perm`
of the ordinary ones). -/
theorem rowPullsAt_coe_eq_of_alignsWith {r_align r_ord : RowFacts p}
    (h : AlignsWith r_align r_ord) (loc : MemLoc) :
    (↑(rowPullsAt r_align loc) : Multiset (Channels.MemoryMsg (ZMod p))) =
      ↑(rowPullsAt r_ord loc) :=
  Multiset.coe_eq_coe.mpr (h.pulls.filter fun m => Semantics.MemoryMsg.locOf m = loc)

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
/-- `pushesAt`/`pullsAt` are permutation-invariant in the row batch (a `List.sum` of per-row
multisets). -/
theorem pushesAt_perm {rows rows' : List (RowFacts p)} (h : rows.Perm rows') (loc : MemLoc) :
    pushesAt rows loc = pushesAt rows' loc :=
  (h.map _).sum_eq

omit [Fact (Nat.Prime p)] [Fact (2 ^ 17 < p)] in
theorem pullsAt_perm {rows rows' : List (RowFacts p)} (h : rows.Perm rows') (loc : MemLoc) :
    pullsAt rows loc = pullsAt rows' loc :=
  (h.map _).sum_eq

omit [Fact (2 ^ 17 < p)] in
/-- **Walk input ⑦ over the aligned ordered rows.**  Any row-indexed aligned carrier `g` (each `g d`
aligning with `d`'s ordinary facts), taken over the exhaustive ordered rows, satisfies the same
per-location Memory balance `memoryFrontierBalance` proves over `memoryFrontierRows` — transported
across the `AlignsWith` per-row permutations (`rowPushesAt/PullsAt_coe_eq_of_alignsWith`) and the
exhaustive batch `Perm` (`pushesAt/pullsAt_perm`). -/
theorem memoryBalance_of_alignsWith [Fact (2 ^ 24 < p)]
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (balanced : witness.BalancedChannels)
    (memBinary : ∀ interaction ∈ typedEnsembleInteractionsWith witness Channels.memoryChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1)
    (initPure : consumedMessages (typedTableInteractionsWith (memoryInitProviderTable witness)
      Channels.memoryChannel) = [])
    (finPure : producedMessages (typedTableInteractionsWith (memoryFinalizeProviderTable witness)
      Channels.memoryChannel) = [])
    (initUnique : MemoryInitProviderUnique witness)
    (finalizeUnique : MemoryFinalizeProviderUnique witness)
    (paddingEmpty : ∀ decoded ∈ decodedInstructionRows (p := p) witness.tables,
      (decoded.toChipRow witness.data).is_real ≠ 1 →
        decoded.producedMemoryMessages witness.data = [] ∧
          decoded.consumedMemoryMessages witness.data = [])
    (orderedRows : List (DecodedInstructionRow p))
    (exhaustive : orderedRows.Perm (realDecodedInstructionRows witness.data witness.tables))
    (g : DecodedInstructionRow p → RowFacts p)
    (aligns : ∀ d ∈ orderedRows, AlignsWith (g d) (d.ordinaryRowFacts witness.data))
    (loc : MemLoc) :
    optMS (memoryInitFrontier witness loc) + pushesAt (orderedRows.map g) loc =
      optMS (memoryFinalizeFrontier witness loc) + pullsAt (orderedRows.map g) loc := by
  have hordinary : memoryFrontierRows witness =
      (realDecodedInstructionRows witness.data witness.tables).map
        (fun d => d.ordinaryRowFacts witness.data) := rfl
  have hpush : pushesAt (orderedRows.map g) loc = pushesAt (memoryFrontierRows witness) loc := by
    have step1 : pushesAt (orderedRows.map g) loc =
        pushesAt (orderedRows.map (fun d => d.ordinaryRowFacts witness.data)) loc := by
      simp only [pushesAt, List.map_map]
      refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
      exact rowPushesAt_coe_eq_of_alignsWith (aligns d hd) loc
    rw [step1, hordinary]
    exact pushesAt_perm (exhaustive.map _) loc
  have hpull : pullsAt (orderedRows.map g) loc = pullsAt (memoryFrontierRows witness) loc := by
    have step1 : pullsAt (orderedRows.map g) loc =
        pullsAt (orderedRows.map (fun d => d.ordinaryRowFacts witness.data)) loc := by
      simp only [pullsAt, List.map_map]
      refine congrArg List.sum (List.map_congr_left fun d hd => ?_)
      exact rowPullsAt_coe_eq_of_alignsWith (aligns d hd) loc
    rw [step1, hordinary]
    exact pullsAt_perm (exhaustive.map _) loc
  rw [hpush, hpull]
  exact memoryFrontierBalance witness balanced memBinary initPure finPure initUnique finalizeUnique
    paddingEmpty loc

/-! ## R-type family constructor -/

section RTypeContracts

variable [Fact (2 ^ 25 < p)]

/-- The genuinely chip-specific residue for a canonical register-register six-pack.  The constructor
below owns all shared Memory extraction, range, decode-bound, wiring, and aligned-carrier reasoning. -/
structure RTypeChipGroundingData (chip : SupportedChip p) : Prop where
  migrated : chip.kind.advance.isSome = true
  memoryShape : RTypeMemoryInteractionShape chip
  viewClockBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ViewClockBounds (decoded.toChipRow data).view
  timestampBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      RTypeTimestampBounds (decoded.toChipRow data).view
  commit_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).view.commit = Trace.CommitEffect.regWrite
  imm_b_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (programAccess (decoded.toChipRow data).view).toRow.imm_b = 0
  imm_c_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (programAccess (decoded.toChipRow data).view).toRow.imm_c = 0
  assumptions : ChipAssumptionsContract chip
  routing : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ (program : GuestProgram),
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
          RdGuardFact chip (decoded.toChipRow witness.data).view
  readiness : ChipReadinessContract chip

/-- Turn one R-type residue bundle into the full grounding contract. -/
theorem RTypeChipGroundingData.toContracts {chip : SupportedChip p}
    (data : RTypeChipGroundingData chip) : ChipGroundingContracts chip where
  migrated := data.migrated
  wiring := by
    intro witness constraints balanced decoded hchip decodedMem real program decode openInputs
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have requirements := fullRequirements_of_openSoundnessInputs witness constraints balanced
      decoded decodedMem openInputs
    have consumed_eq := consumedMemoryMessages_eq_of_rtypeShape data.memoryShape decoded
      witness.data hchip real
    have produced_eq := producedMemoryMessages_eq_of_rtypeShape data.memoryShape decoded
      witness.data hchip real
    have writeU64 : Word.isU64 (decoded.toChipRow witness.data).view.rdWrite := by
      have hmem : rtypeWriteMessage (decoded.toChipRow witness.data).view ∈
          decoded.producedMemoryMessages witness.data := by
        rw [produced_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      exact producedMemoryMessages_isU64_of_fullRequirements decoded witness.data requirements _ hmem
    have registerBounds := decode.register_bounds
    have operandBounds :
        (decoded.toChipRow witness.data).view.adapter.op_a.val < 32 ∧
          ((decoded.toChipRow witness.data).view.adapter.op_b[0]).val < 32 ∧
          ((decoded.toChipRow witness.data).view.adapter.op_c[0]).val < 32 :=
      ⟨registerBounds.1,
        registerBounds.2.1 (data.imm_b_eq decoded witness.data hchip),
        registerBounds.2.2 (data.imm_c_eq decoded witness.data hchip)⟩
    exact rowWiring_rtype_of_decoded decoded witness.data bounds
      (data.commit_eq decoded witness.data hchip) operandBounds.1 writeU64 consumed_eq produced_eq
  assumptions := data.assumptions
  routing := data.routing
  readiness := data.readiness
  rowAligned := by
    intro witness constraints balanced decoded hchip decodedMem real program decode _timestampHigh
    refine ⟨rtypeTouches (decoded.toChipRow witness.data).view
      (decoded.ordinaryRowFacts witness.data), ?_⟩
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have timestamps := data.timestampBounds decoded witness.data hchip byteG real
    have registerBounds := decode.register_bounds
    have opa_lt := registerBounds.1
    have opb_lt := registerBounds.2.1 (data.imm_b_eq decoded witness.data hchip)
    have opc_lt := registerBounds.2.2 (data.imm_c_eq decoded witness.data hchip)
    exact rowAligned_rtype_of_shape data.memoryShape decoded witness.data hchip real bounds timestamps
      opa_lt opb_lt opc_lt

end RTypeContracts

/-! ## I-type family constructor -/

section ITypeContracts

variable [Fact (2 ^ 25 < p)]

/-- Chip-specific residue for a canonical register-plus-immediate four-pack. -/
structure ITypeChipGroundingData (chip : SupportedChip p) : Prop where
  migrated : chip.kind.advance.isSome = true
  memoryShape : ITypeMemoryInteractionShape chip
  viewClockBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ViewClockBounds (decoded.toChipRow data).view
  timestampBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ITypeTimestampBounds (decoded.toChipRow data).view
  commit_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).view.commit = Trace.CommitEffect.regWrite
  imm_b_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (programAccess (decoded.toChipRow data).view).toRow.imm_b = 0
  assumptions : ChipAssumptionsContract chip
  routing : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ (program : GuestProgram),
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
          RdGuardFact chip (decoded.toChipRow witness.data).view
  readiness : ChipReadinessContract chip

/-- Turn one I-type residue bundle into the full grounding contract. -/
theorem ITypeChipGroundingData.toContracts {chip : SupportedChip p}
    (data : ITypeChipGroundingData chip) : ChipGroundingContracts chip where
  migrated := data.migrated
  wiring := by
    intro witness constraints balanced decoded hchip decodedMem real program decode openInputs
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have requirements := fullRequirements_of_openSoundnessInputs witness constraints balanced
      decoded decodedMem openInputs
    have consumedEq := consumedMemoryMessages_eq_of_itypeShape data.memoryShape decoded
      witness.data hchip real
    have producedEq := producedMemoryMessages_eq_of_itypeShape data.memoryShape decoded
      witness.data hchip real
    have writeU64 : Word.isU64 (decoded.toChipRow witness.data).view.rdWrite := by
      have writeMem : rtypeWriteMessage (decoded.toChipRow witness.data).view ∈
          decoded.producedMemoryMessages witness.data := by
        rw [producedEq]
        exact List.mem_cons_of_mem _ List.mem_cons_self
      exact producedMemoryMessages_isU64_of_fullRequirements decoded witness.data requirements _
        writeMem
    have registerBounds := decode.register_bounds
    exact rowWiring_itype_of_decoded decoded witness.data bounds
      (data.commit_eq decoded witness.data hchip)
      (data.memoryShape.imm_c_eq_one decoded witness.data hchip) registerBounds.1 writeU64
      consumedEq producedEq
  assumptions := data.assumptions
  routing := data.routing
  readiness := data.readiness
  rowAligned := by
    intro witness constraints balanced decoded hchip decodedMem real program decode _timestampHigh
    refine ⟨itypeTouches (decoded.toChipRow witness.data).view
      (decoded.ordinaryRowFacts witness.data), ?_⟩
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have timestamps := data.timestampBounds decoded witness.data hchip byteG real
    have registerBounds := decode.register_bounds
    have opbLt := registerBounds.2.1 (data.imm_b_eq decoded witness.data hchip)
    exact rowAligned_itype_of_shape data.memoryShape decoded witness.data hchip real bounds
      timestamps registerBounds.1 opbLt

end ITypeContracts

/-! ## Immediate-capable ALU family constructor -/

section ALUTypeContracts

variable [Fact (2 ^ 25 < p)]

/-- Chip-specific residue for the conditional six-pack shared by Addw, Bitwise, Lt, and the two
shift chips.  Decode chooses the register/immediate form; the constructor owns both physical Memory
layouts and all timed wiring. -/
structure ALUTypeChipGroundingData (chip : SupportedChip p) : Prop where
  migrated : chip.kind.advance.isSome = true
  memoryShape : ConstrainedALUTypeMemoryInteractionShape chip
  viewClockBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ViewClockBounds (decoded.toChipRow data).view
  timestampBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ConstraintsHold (decoded.environment data) →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ALUTypeTimestampBounds (decoded.toChipRow data).view
  commit_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).view.commit = Trace.CommitEffect.regWrite
  imm_b_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (programAccess (decoded.toChipRow data).view).toRow.imm_b = 0
  assumptions : ChipAssumptionsContract chip
  routing : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ (program : GuestProgram),
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
          RdGuardFact chip (decoded.toChipRow witness.data).view
  readiness : ChipReadinessContract chip

/-- Turn one immediate-capable ALU residue bundle into the complete grounding contract. -/
theorem ALUTypeChipGroundingData.toContracts {chip : SupportedChip p}
    (data : ALUTypeChipGroundingData chip) : ChipGroundingContracts chip where
  migrated := data.migrated
  wiring := by
    intro witness constraints balanced decoded hchip decodedMem real program decode openInputs
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have requirements := fullRequirements_of_openSoundnessInputs witness constraints balanced
      decoded decodedMem openInputs
    have immBinary : (decoded.toChipRow witness.data).view.adapter.imm_c = 0 ∨
        (decoded.toChipRow witness.data).view.adapter.imm_c = 1 := by
      simpa only [programAccess, ProgramAccess.toRow] using decode.immediate_flags_binary.2
    have writeMem : rtypeWriteMessage (decoded.toChipRow witness.data).view ∈
        decoded.producedMemoryMessages witness.data := by
      rcases immBinary with register | immediate
      · rw [producedMemoryMessages_eq_of_aluType_register data.memoryShape decoded witness.data
          hchip rowConstraints real register]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · rw [producedMemoryMessages_eq_of_aluType_immediate data.memoryShape decoded witness.data
          hchip rowConstraints real immediate]
        exact List.mem_cons_of_mem _ List.mem_cons_self
    have writeU64 : Word.isU64 (decoded.toChipRow witness.data).view.rdWrite :=
      producedMemoryMessages_isU64_of_fullRequirements decoded witness.data requirements _ writeMem
    exact rowWiring_aluType_of_shape data.memoryShape decoded witness.data hchip rowConstraints
      real bounds
      (data.commit_eq decoded witness.data hchip)
      (by simpa only [programAccess, ProgramAccess.toRow] using decode.immediate_flags_binary.2)
      decode.register_bounds.1 writeU64
  assumptions := data.assumptions
  routing := data.routing
  readiness := data.readiness
  rowAligned := by
    intro witness constraints balanced decoded hchip decodedMem real program decode _timestampHigh
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have timestamps := data.timestampBounds decoded witness.data hchip rowConstraints byteG real
    have registerBounds := decode.register_bounds
    have immBinary : (decoded.toChipRow witness.data).view.adapter.imm_c = 0 ∨
        (decoded.toChipRow witness.data).view.adapter.imm_c = 1 := by
      simpa only [programAccess, ProgramAccess.toRow] using decode.immediate_flags_binary.2
    exact rowAligned_aluType_of_shape data.memoryShape decoded witness.data hchip rowConstraints
      real bounds timestamps immBinary registerBounds.1
      (registerBounds.2.1 (data.imm_b_eq decoded witness.data hchip)) registerBounds.2.2

end ALUTypeContracts

/-! ## Immutable immediate-capable ALU constructor -/

section ImmutableALUTypeContracts

variable [Fact (2 ^ 25 < p)]

/-- Chip-specific residue for an immediate-capable ALU row that discards its result. The register
form reads back A/B/C; the immediate form reads back only A/B. -/
structure ImmutableALUTypeChipGroundingData (chip : SupportedChip p) : Prop where
  migrated : chip.kind.advance.isSome = true
  memoryShape : ImmutableALUTypeMemoryInteractionShape chip
  viewClockBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ViewClockBounds (decoded.toChipRow data).view
  timestampBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ALUTypeTimestampBounds (decoded.toChipRow data).view
  commit_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).view.commit = Trace.CommitEffect.noWrite
  assumptions : ChipAssumptionsContract chip
  routing : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ (program : GuestProgram),
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
          RdGuardFact chip (decoded.toChipRow witness.data).view
  readiness : ChipReadinessContract chip

/-- Turn an immutable ALU residue bundle into the complete per-chip grounding contract. -/
theorem ImmutableALUTypeChipGroundingData.toContracts {chip : SupportedChip p}
    (data : ImmutableALUTypeChipGroundingData chip) : ChipGroundingContracts chip where
  migrated := data.migrated
  wiring := by
    intro witness constraints balanced decoded hchip decodedMem real program decode _openInputs
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have immBinary : (decoded.toChipRow witness.data).view.adapter.imm_c = 0 ∨
        (decoded.toChipRow witness.data).view.adapter.imm_c = 1 := by
      simpa only [programAccess, ProgramAccess.toRow] using
        decode.immediate_flags_binary.2
    rcases immBinary with register | immediate
    · have consumed := consumedMemoryMessages_eq_of_immutableAlu_register
        data.memoryShape decoded witness.data hchip real register
      have produced := producedMemoryMessages_eq_of_immutableAlu_register
        data.memoryShape decoded witness.data hchip real register
      refine rowWiring_immutableRtype bounds
        (data.commit_eq decoded witness.data hchip) decode.register_bounds.1 rfl rfl ?_ ?_
      · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
        rfl
      · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes]
        exact produced
    · have consumed := consumedMemoryMessages_eq_of_immutableAlu_immediate
        data.memoryShape decoded witness.data hchip real immediate
      have produced := producedMemoryMessages_eq_of_immutableAlu_immediate
        data.memoryShape decoded witness.data hchip real immediate
      refine rowWiring_immutableItype bounds
        (data.commit_eq decoded witness.data hchip) immediate decode.register_bounds.1
        rfl rfl ?_ ?_
      · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
        rfl
      · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes]
        exact produced
  assumptions := data.assumptions
  routing := data.routing
  readiness := data.readiness
  rowAligned := by
    intro witness constraints balanced decoded hchip decodedMem real program decode _timestampHigh
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have timestamps := data.timestampBounds decoded witness.data hchip byteG real
    have registerBounds := decode.register_bounds
    have immBinary : (decoded.toChipRow witness.data).view.adapter.imm_c = 0 ∨
        (decoded.toChipRow witness.data).view.adapter.imm_c = 1 := by
      simpa only [programAccess, ProgramAccess.toRow] using
        decode.immediate_flags_binary.2
    rcases immBinary with register | immediate
    · refine ⟨immutableRtypeTouches (decoded.toChipRow witness.data).view
        (decoded.ordinaryRowFacts witness.data), ?_⟩
      have consumed := consumedMemoryMessages_eq_of_immutableAlu_register
        data.memoryShape decoded witness.data hchip real register
      have produced := producedMemoryMessages_eq_of_immutableAlu_register
        data.memoryShape decoded witness.data hchip real register
      obtain ⟨timestampA, timestampB, timestampCOf⟩ := timestamps
      have timestampC := timestampCOf register
      have slots : ∀ tc ∈ immutableRtypeTouches
          (decoded.toChipRow witness.data).view
          (decoded.ordinaryRowFacts witness.data),
          SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
            MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2 := by
        intro tc htc hclk
        simp only [immutableRtypeTouches, List.mem_cons, List.not_mem_nil,
          or_false] at htc
        rcases htc with rfl | rfl | rfl
        · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
            _ _ _ _ _ hclk timestampC rfl rfl rfl
        · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
            _ _ _ _ _ hclk timestampB rfl rfl rfl
        · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
            _ _ _ _ _ hclk timestampA rfl rfl rfl
      refine rowAligned_immutableRtype bounds real registerBounds.1
        (registerBounds.2.1
          (by simpa only [programAccess, ProgramAccess.toRow] using
            data.memoryShape.imm_b_eq_zero decoded witness.data hchip))
        (registerBounds.2.2 register) rfl ?_ ?_ slots
      · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
        rfl
      · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes]
        exact produced
    · refine ⟨immutableItypeTouches (decoded.toChipRow witness.data).view
        (decoded.ordinaryRowFacts witness.data), ?_⟩
      have consumed := consumedMemoryMessages_eq_of_immutableAlu_immediate
        data.memoryShape decoded witness.data hchip real immediate
      have produced := producedMemoryMessages_eq_of_immutableAlu_immediate
        data.memoryShape decoded witness.data hchip real immediate
      obtain ⟨timestampA, timestampB, -⟩ := timestamps
      have slots : ∀ tc ∈ immutableItypeTouches
          (decoded.toChipRow witness.data).view
          (decoded.ordinaryRowFacts witness.data),
          SP1Clean.Channels.MemoryMsg.ClkBound (tc : Touch p).1.1 →
            MemoryMsg.timeNat (tc : Touch p).1.1 < MemoryMsg.timeNat tc.2 := by
        intro tc htc hclk
        simp only [immutableItypeTouches, List.mem_cons, List.not_mem_nil,
          or_false] at htc
        rcases htc with rfl | rfl
        · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
            _ _ _ _ _ hclk timestampB rfl rfl rfl
        · exact TimeExtraction.memoryTimeNat_lt_of_activeTimestampBounds
            _ _ _ _ _ hclk timestampA rfl rfl rfl
      refine rowAligned_immutableItype bounds real registerBounds.1
        (registerBounds.2.1
          (by simpa only [programAccess, ProgramAccess.toRow] using
            data.memoryShape.imm_b_eq_zero decoded witness.data hchip))
        rfl ?_ ?_ slots
      · rw [DecodedInstructionRow.ordinaryRowFacts_memPulls, consumed]
        rfl
      · rw [DecodedInstructionRow.ordinaryRowFacts_memPushes]
        exact produced

end ImmutableALUTypeContracts

/-! ## Destination-only J-type family constructor -/

section JTypeContracts

variable [Fact (2 ^ 25 < p)]

/-- Chip-specific residue for the destination-only J-type pair shared by JAL and U-type.  Unlike
the nonzero-destination ALU families, these chips genuinely admit `rd = x0`: the circuit still emits
the factored destination push, while the retained `JTypeReader` zeroing gates force its value to
zero. `specFacts` exposes exactly those two reader facts from the folded whole-chip `Spec` on an
active row, where the Program interaction makes the reader's destination selector trusted. -/
structure JTypeChipGroundingData (chip : SupportedChip p) : Prop where
  migrated : chip.kind.advance.isSome = true
  memoryShape : JTypeMemoryInteractionShape chip
  viewClockBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ViewClockBounds (decoded.toChipRow data).view
  timestampBound : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      JTypeTimestampBound (decoded.toChipRow data).view
  commit_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).view.commit =
        Trace.CommitEffect.destination (decoded.toChipRow data).view.adapter.op_a_0
  specFacts : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    (decoded.toChipRow data).view.is_real = 1 →
    (decoded.toChipRow data).chipSpec data →
      ((decoded.toChipRow data).view.adapter.op_a_0 = 0 ∨
        (decoded.toChipRow data).view.adapter.op_a_0 = 1) ∧
      ((decoded.toChipRow data).view.adapter.op_a_0 = 1 →
        Word.toBitVec64 (decoded.toChipRow data).view.rdWrite = 0)
  assumptions : ChipAssumptionsContract chip
  routing : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ (program : GuestProgram),
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
          RdGuardFact chip (decoded.toChipRow witness.data).view
  readiness : ChipReadinessContract chip

/-- Turn one destination-only J-type residue bundle into the complete grounding contract. -/
theorem JTypeChipGroundingData.toContracts {chip : SupportedChip p}
    (data : JTypeChipGroundingData chip) : ChipGroundingContracts chip where
  migrated := data.migrated
  wiring := by
    intro witness constraints balanced decoded hchip decodedMem real program decode openInputs
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have spec := decoded.chipSpec_of_openSoundnessInputs witness constraints balanced decodedMem
      openInputs
    have specFacts := data.specFacts decoded witness.data hchip real spec
    have requirements := fullRequirements_of_openSoundnessInputs witness constraints balanced
      decoded decodedMem openInputs
    have producedEq := producedMemoryMessages_eq_of_jtypeShape data.memoryShape decoded
      witness.data hchip real
    have writeMem : rtypeWriteMessage (decoded.toChipRow witness.data).view ∈
        decoded.producedMemoryMessages witness.data := by
      rw [producedEq]
      exact List.mem_cons_self
    have writeU64 : Word.isU64 (decoded.toChipRow witness.data).view.rdWrite :=
      producedMemoryMessages_isU64_of_fullRequirements decoded witness.data requirements _ writeMem
    have zeroIndex : (decoded.toChipRow witness.data).view.adapter.op_a_0 = 1 →
        (decoded.toChipRow witness.data).view.adapter.op_a = 0 := by
      intro flag
      apply decode.op_a_eq_zero_of_op_a_0_eq_one
      simpa only [programAccess, ProgramAccess.toRow] using flag
    exact rowWiring_jtype_of_shape data.memoryShape decoded witness.data hchip real bounds
      (data.commit_eq decoded witness.data hchip) specFacts.1 decode.register_bounds.1 writeU64
      zeroIndex specFacts.2
  assumptions := data.assumptions
  routing := data.routing
  readiness := data.readiness
  rowAligned := by
    intro witness constraints balanced decoded hchip decodedMem real program decode _timestampHigh
    refine ⟨jtypeTouches (decoded.toChipRow witness.data).view
      (decoded.ordinaryRowFacts witness.data), ?_⟩
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have timestamp := data.timestampBound decoded witness.data hchip byteG real
    exact rowAligned_jtype_of_shape data.memoryShape decoded witness.data hchip real bounds timestamp
      decode.register_bounds.1

end JTypeContracts

/-! ## Conditional-destination I-type constructor -/

section ConditionalITypeContracts

variable [Fact (2 ^ 25 < p)]

/-- Chip-specific residue for an I-type row whose destination may be x0.  JALR is the upstream
instance: its physical four-message layout is the ordinary I-type layout, while its architectural
commit is selected by `op_a_0`. -/
structure ConditionalITypeChipGroundingData (chip : SupportedChip p) : Prop where
  migrated : chip.kind.advance.isSome = true
  memoryShape : ITypeMemoryInteractionShape chip
  viewClockBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ViewClockBounds (decoded.toChipRow data).view
  timestampBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ITypeTimestampBounds (decoded.toChipRow data).view
  commit_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).view.commit =
        Trace.CommitEffect.destination (decoded.toChipRow data).view.adapter.op_a_0
  imm_b_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (programAccess (decoded.toChipRow data).view).toRow.imm_b = 0
  specFacts : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    (decoded.toChipRow data).view.is_real = 1 →
    (decoded.toChipRow data).chipSpec data →
      ((decoded.toChipRow data).view.adapter.op_a_0 = 0 ∨
        (decoded.toChipRow data).view.adapter.op_a_0 = 1) ∧
      ((decoded.toChipRow data).view.adapter.op_a_0 = 1 →
        Word.toBitVec64 (decoded.toChipRow data).view.rdWrite = 0)
  assumptions : ChipAssumptionsContract chip
  routing : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ (program : GuestProgram),
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
          RdGuardFact chip (decoded.toChipRow witness.data).view
  readiness : ChipReadinessContract chip

/-- Assemble the complete grounding contract for a conditional-destination I-type chip. -/
theorem ConditionalITypeChipGroundingData.toContracts {chip : SupportedChip p}
    (data : ConditionalITypeChipGroundingData chip) : ChipGroundingContracts chip where
  migrated := data.migrated
  wiring := by
    intro witness constraints balanced decoded hchip decodedMem real program decode openInputs
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have spec := decoded.chipSpec_of_openSoundnessInputs witness constraints balanced decodedMem
      openInputs
    have facts := data.specFacts decoded witness.data hchip real spec
    have requirements := fullRequirements_of_openSoundnessInputs witness constraints balanced
      decoded decodedMem openInputs
    have producedEq := producedMemoryMessages_eq_of_itypeShape data.memoryShape decoded
      witness.data hchip real
    have writeMem : rtypeWriteMessage (decoded.toChipRow witness.data).view ∈
        decoded.producedMemoryMessages witness.data := by
      rw [producedEq]
      exact List.mem_cons_of_mem _ List.mem_cons_self
    have writeU64 : Word.isU64 (decoded.toChipRow witness.data).view.rdWrite :=
      producedMemoryMessages_isU64_of_fullRequirements decoded witness.data requirements _ writeMem
    have zeroIndex : (decoded.toChipRow witness.data).view.adapter.op_a_0 = 1 →
        (decoded.toChipRow witness.data).view.adapter.op_a = 0 := by
      intro flag
      apply decode.op_a_eq_zero_of_op_a_0_eq_one
      simpa only [programAccess, ProgramAccess.toRow] using flag
    exact rowWiring_itypeDestination_of_shape data.memoryShape decoded witness.data hchip real
      bounds (data.commit_eq decoded witness.data hchip) facts.1 decode.register_bounds.1
      writeU64 zeroIndex facts.2
  assumptions := data.assumptions
  routing := data.routing
  readiness := data.readiness
  rowAligned := by
    intro witness constraints balanced decoded hchip decodedMem real program decode _timestampHigh
    refine ⟨itypeTouches (decoded.toChipRow witness.data).view
      (decoded.ordinaryRowFacts witness.data), ?_⟩
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have timestamps := data.timestampBounds decoded witness.data hchip byteG real
    exact rowAligned_itype_of_shape data.memoryShape decoded witness.data hchip real bounds
      timestamps decode.register_bounds.1
      (decode.register_bounds.2.1
        (by simpa only [programAccess, ProgramAccess.toRow] using
          data.imm_b_eq decoded witness.data hchip))

end ConditionalITypeContracts

/-! ## Immutable I-type constructor -/

section ImmutableITypeContracts

variable [Fact (2 ^ 25 < p)]

/-- Chip-specific residue for a two-source, no-register-write I-type row. -/
structure ImmutableITypeChipGroundingData (chip : SupportedChip p) : Prop where
  migrated : chip.kind.advance.isSome = true
  memoryShape : ImmutableITypeMemoryInteractionShape chip
  viewClockBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ViewClockBounds (decoded.toChipRow data).view
  timestampBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ImmutableITypeTimestampBounds (decoded.toChipRow data).view
  commit_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).view.commit = Trace.CommitEffect.noWrite
  assumptions : ChipAssumptionsContract chip
  routing : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ (program : GuestProgram),
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
          RdGuardFact chip (decoded.toChipRow witness.data).view
  readiness : ChipReadinessContract chip

/-- Assemble the complete grounding contract for a no-write immutable I-type chip. -/
theorem ImmutableITypeChipGroundingData.toContracts {chip : SupportedChip p}
    (data : ImmutableITypeChipGroundingData chip) : ChipGroundingContracts chip where
  migrated := data.migrated
  wiring := by
    intro witness constraints balanced decoded hchip decodedMem real program decode openInputs
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    exact rowWiring_immutableItype_of_shape data.memoryShape decoded witness.data hchip real
      bounds (data.commit_eq decoded witness.data hchip) decode.register_bounds.1
  assumptions := data.assumptions
  routing := data.routing
  readiness := data.readiness
  rowAligned := by
    intro witness constraints balanced decoded hchip decodedMem real program decode _timestampHigh
    refine ⟨immutableItypeTouches (decoded.toChipRow witness.data).view
      (decoded.ordinaryRowFacts witness.data), ?_⟩
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have timestamps := data.timestampBounds decoded witness.data hchip byteG real
    exact rowAligned_immutableItype_of_shape data.memoryShape decoded witness.data hchip real
      bounds timestamps decode.register_bounds.1
      (decode.register_bounds.2.1
        (by simpa only [programAccess, ProgramAccess.toRow] using
          data.memoryShape.imm_b_eq_zero decoded witness.data hchip))

end ImmutableITypeContracts

/-! ## RAM load family constructor -/

section LoadMemoryContracts

variable [Fact (2 ^ 25 < p)]

/-- Chip-specific residue for one normal register-writing load. The shared constructor owns the
three-message RAM/register pull set, the `+1/+3/+4` push set, exact Memory requirements, timestamp
ordering, and the aligned carrier. -/
structure LoadMemoryChipGroundingData (chip : SupportedChip p)
    (memoryShape : LoadMemoryInteractionShape chip) : Prop where
  migrated : chip.kind.advance.isSome = true
  viewClockBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ViewClockBounds (decoded.toChipRow data).view
  timestampBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ConstraintsHold (decoded.environment data) →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      LoadMemoryTimestampBounds (decoded.toChipRow data).view
        (memoryShape.access decoded data)
  isRam : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ConstraintsHold (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      RamAccessIsRam (memoryShape.access decoded data)
  commit_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).view.commit = Trace.CommitEffect.regWrite
  imm_b_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (programAccess (decoded.toChipRow data).view).toRow.imm_b = 0
  imm_c_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).view.adapter.imm_c = 1
  ram_unchanged : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (memoryShape.access decoded data).newValue =
        (memoryShape.access decoded data).priorValue
  assumptions : ChipAssumptionsContract chip
  rdGuard_eq : chip.rdGuard = .nonX0
  routingFlag : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
        (decoded.toChipRow witness.data).view.adapter.op_a_0 = 0
  readiness : ChipReadinessContract chip

/-- Assemble the complete grounding contract for a normal load. -/
theorem LoadMemoryChipGroundingData.toContracts {chip : SupportedChip p}
    {memoryShape : LoadMemoryInteractionShape chip}
    (data : LoadMemoryChipGroundingData chip memoryShape) : ChipGroundingContracts chip where
  migrated := data.migrated
  wiring := by
    intro witness constraints balanced decoded hchip decodedMem real program decode openInputs
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have requirements := fullRequirements_of_openSoundnessInputs witness constraints balanced
      decoded decodedMem openInputs
    have producedEq := producedMemoryMessages_eq_of_loadShape memoryShape decoded
      witness.data hchip real
    have writeMem : rtypeWriteMessage (decoded.toChipRow witness.data).view ∈
        decoded.producedMemoryMessages witness.data := by
      rw [producedEq]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
    have writeU64 : Word.isU64 (decoded.toChipRow witness.data).view.rdWrite :=
      producedMemoryMessages_isU64_of_fullRequirements decoded witness.data requirements _
        writeMem
    exact rowWiring_loadRam_of_shape memoryShape decoded witness.data hchip real bounds
      (data.commit_eq decoded witness.data hchip)
      (data.imm_c_eq decoded witness.data hchip)
      (data.isRam decoded witness.data hchip rowConstraints real)
      (data.ram_unchanged decoded witness.data hchip) decode.register_bounds.1 writeU64
  assumptions := data.assumptions
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    unfold RdGuardFact
    rw [data.rdGuard_eq]
    apply decode.op_a_ne_zero_of_op_a_0_eq_zero
    simpa only [programAccess, ProgramAccess.toRow] using
      data.routingFlag witness constraints decoded hchip decodedMem real
  readiness := data.readiness
  rowAligned := by
    intro witness constraints balanced decoded hchip decodedMem real program decode timestampHigh
    refine ⟨ramItypeTouches (decoded.toChipRow witness.data).view
      (memoryShape.access decoded witness.data)
      (decoded.ordinaryRowFacts witness.data)
      (rtypeWriteMessage (decoded.toChipRow witness.data).view), ?_⟩
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have timestamps :=
      data.timestampBounds decoded witness.data hchip rowConstraints byteG real
    have isRam := data.isRam decoded witness.data hchip rowConstraints real
    have ramHigh := ramPrevHigh_lt_of_loadShape memoryShape decoded witness.data
      hchip real timestampHigh
    exact rowAligned_loadRam_of_shape memoryShape decoded witness.data hchip real bounds
      timestamps isRam ramHigh decode.register_bounds.1
      (decode.register_bounds.2.1 (data.imm_b_eq decoded witness.data hchip))

end LoadMemoryContracts

/-! ## Immutable RAM-load family constructor -/

section ImmutableLoadMemoryContracts

variable [Fact (2 ^ 25 < p)]

/-- Chip-specific residue for LoadX0. The RAM word and both register sources are read back
unchanged, and the architectural effect commits no register or RAM write. -/
structure ImmutableLoadMemoryChipGroundingData (chip : SupportedChip p)
    (memoryShape : ImmutableRamMemoryInteractionShape chip) : Prop where
  migrated : chip.kind.advance.isSome = true
  viewClockBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ViewClockBounds (decoded.toChipRow data).view
  timestampBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ConstraintsHold (decoded.environment data) →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ImmutableRamTimestampBounds (decoded.toChipRow data).view
        (memoryShape.access decoded data)
  isRam : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ConstraintsHold (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      RamAccessIsRam (memoryShape.access decoded data)
  commit_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).view.commit = Trace.CommitEffect.noWrite
  imm_b_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (programAccess (decoded.toChipRow data).view).toRow.imm_b = 0
  imm_c_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).view.adapter.imm_c = 1
  ram_unchanged : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (memoryShape.access decoded data).newValue =
        (memoryShape.access decoded data).priorValue
  assumptions : ChipAssumptionsContract chip
  rdGuard_eq : chip.rdGuard = .onlyX0
  routingFlag : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
        (decoded.toChipRow witness.data).view.adapter.op_a_0 = 1
  readiness : ChipReadinessContract chip

/-- Assemble the complete grounding contract for LoadX0. -/
theorem ImmutableLoadMemoryChipGroundingData.toContracts {chip : SupportedChip p}
    {memoryShape : ImmutableRamMemoryInteractionShape chip}
    (data : ImmutableLoadMemoryChipGroundingData chip memoryShape) :
    ChipGroundingContracts chip where
  migrated := data.migrated
  wiring := by
    intro witness constraints balanced decoded hchip decodedMem real program decode openInputs
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    exact rowWiring_immutableLoadRam_of_shape memoryShape decoded witness.data hchip real
      bounds (data.commit_eq decoded witness.data hchip)
      (data.imm_c_eq decoded witness.data hchip)
      (data.isRam decoded witness.data hchip rowConstraints real)
      (data.ram_unchanged decoded witness.data hchip) decode.register_bounds.1
  assumptions := data.assumptions
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    unfold RdGuardFact
    rw [data.rdGuard_eq]
    apply decode.op_a_eq_zero_of_op_a_0_eq_one
    simpa only [programAccess, ProgramAccess.toRow] using
      data.routingFlag witness constraints decoded hchip decodedMem real
  readiness := data.readiness
  rowAligned := by
    intro witness constraints balanced decoded hchip decodedMem real program decode timestampHigh
    refine ⟨ramItypeTouches (decoded.toChipRow witness.data).view
      (memoryShape.access decoded witness.data)
      (decoded.ordinaryRowFacts witness.data)
      (rtypeReadBackMessage (decoded.toChipRow witness.data).view
        (decoded.toChipRow witness.data).view.adapter.op_a
        (decoded.toChipRow witness.data).view.adapter.op_a_memory 4), ?_⟩
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have timestamps :=
      data.timestampBounds decoded witness.data hchip rowConstraints byteG real
    have isRam := data.isRam decoded witness.data hchip rowConstraints real
    have ramHigh := ramPrevHigh_lt_of_immutableRamShape memoryShape decoded witness.data
      hchip real timestampHigh
    exact rowAligned_immutableRam_of_shape memoryShape decoded witness.data hchip real
      bounds timestamps isRam ramHigh decode.register_bounds.1
      (decode.register_bounds.2.1
        (by simpa only [programAccess, ProgramAccess.toRow] using
          data.imm_b_eq decoded witness.data hchip))

end ImmutableLoadMemoryContracts

/-! ## RAM-store family constructor -/

section StoreMemoryContracts

variable [Fact (2 ^ 25 < p)]

/-- Chip-specific residue for a genuine RAM store. Arithmetic remains in the chip `Spec`; the
shared constructor consumes only the resulting byte-addressed write, its cell-locality, and the
full-cell update equation needed by the machine memory model. -/
structure StoreMemoryChipGroundingData (chip : SupportedChip p)
    (memoryShape : ImmutableRamMemoryInteractionShape chip) : Prop where
  migrated : chip.kind.advance.isSome = true
  viewClockBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ViewClockBounds (decoded.toChipRow data).view
  timestampBounds : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ConstraintsHold (decoded.environment data) →
    decoded.chip.table.operations.ChannelGuarantees Channels.byteChannel.toRaw
      (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      ImmutableRamTimestampBounds (decoded.toChipRow data).view
        (memoryShape.access decoded data)
  isRam : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    decoded.chip.table.operations.ConstraintsHold (decoded.environment data) →
    (decoded.toChipRow data).view.is_real = 1 →
      RamAccessIsRam (memoryShape.access decoded data)
  imm_b_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (programAccess (decoded.toChipRow data).view).toRow.imm_b = 0
  imm_c_eq : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
      (decoded.toChipRow data).view.adapter.imm_c = 1
  storeFacts : ∀ (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p)),
    decoded.chip = chip →
    (decoded.toChipRow data).view.is_real = 1 →
    decoded.chip.kind.chipSpec (decoded.toChipRow data).inputs
      (decoded.toChipRow data).cols data →
      ∃ write : Trace.MemWrite (ZMod p),
        (decoded.toChipRow data).view.commit = Trace.CommitEffect.store write ∧
        write.InCell (ramCellOfAccess (memoryShape.access decoded data)) ∧
        RamCellUpdate write (ramCellOfAccess (memoryShape.access decoded data))
          (Word.toBitVec64 (memoryShape.access decoded data).priorValue)
          (Word.toBitVec64 (memoryShape.access decoded data).newValue)
  assumptions : ChipAssumptionsContract chip
  rdGuard_eq : chip.rdGuard = .any
  readiness : ChipReadinessContract chip

/-- Assemble the complete grounding contract for a genuine RAM store. -/
theorem StoreMemoryChipGroundingData.toContracts {chip : SupportedChip p}
    {memoryShape : ImmutableRamMemoryInteractionShape chip}
    (data : StoreMemoryChipGroundingData chip memoryShape) : ChipGroundingContracts chip where
  migrated := data.migrated
  wiring := by
    intro witness constraints balanced decoded hchip decodedMem real program decode openInputs
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have chipSpec := decoded.chipSpec_of_openSoundnessInputs witness constraints balanced
      decodedMem openInputs
    obtain ⟨write, commitEq, inCell, update⟩ :=
      data.storeFacts decoded witness.data hchip real chipSpec
    have requirements := fullRequirements_of_openSoundnessInputs witness constraints balanced
      decoded decodedMem openInputs
    have producedEq := producedMemoryMessages_eq_of_immutableRamShape memoryShape decoded
      witness.data hchip real
    have ramPushMem : ramPushMessage (decoded.toChipRow witness.data).view
        (memoryShape.access decoded witness.data) ∈
        decoded.producedMemoryMessages witness.data := by
      rw [producedEq]
      exact List.mem_cons_self
    have newU64 : Word.isU64 (memoryShape.access decoded witness.data).newValue := by
      have pushU64 := producedMemoryMessages_isU64_of_fullRequirements decoded witness.data
        requirements _ ramPushMem
      simpa only [ramPushMessage, MemoryMsg.isU64] using pushU64
    exact rowWiring_storeRam_of_shape memoryShape decoded witness.data hchip real bounds
      write commitEq (data.imm_c_eq decoded witness.data hchip)
      (data.isRam decoded witness.data hchip rowConstraints real) inCell update
      decode.register_bounds.1
      (decode.register_bounds.2.1
        (by simpa only [programAccess, ProgramAccess.toRow] using
          data.imm_b_eq decoded witness.data hchip))
      newU64
  assumptions := data.assumptions
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    unfold RdGuardFact
    rw [data.rdGuard_eq]
    trivial
  readiness := data.readiness
  rowAligned := by
    intro witness constraints balanced decoded hchip decodedMem real program decode timestampHigh
    refine ⟨ramItypeTouches (decoded.toChipRow witness.data).view
      (memoryShape.access decoded witness.data)
      (decoded.ordinaryRowFacts witness.data)
      (rtypeReadBackMessage (decoded.toChipRow witness.data).view
        (decoded.toChipRow witness.data).view.adapter.op_a
        (decoded.toChipRow witness.data).view.adapter.op_a_memory 4), ?_⟩
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := data.viewClockBounds decoded witness.data hchip byteG real
    have timestamps :=
      data.timestampBounds decoded witness.data hchip rowConstraints byteG real
    have isRam := data.isRam decoded witness.data hchip rowConstraints real
    have ramHigh := ramPrevHigh_lt_of_immutableRamShape memoryShape decoded witness.data
      hchip real timestampHigh
    exact rowAligned_immutableRam_of_shape memoryShape decoded witness.data hchip real
      bounds timestamps isRam ramHigh decode.register_bounds.1
      (decode.register_bounds.2.1
        (by simpa only [programAccess, ProgramAccess.toRow] using
          data.imm_b_eq decoded witness.data hchip))

end StoreMemoryContracts

/-! ## The LoadByte anchor -/

section LoadByteAnchor

variable [Fact (2 ^ 25 < p)]

set_option maxHeartbeats 1000000 in
private theorem loadByteChip_loadMemoryGroundingData_of_eq
    (chip : SupportedChip p) (shape : LoadMemoryInteractionShape chip)
    (chipEq : chip = loadByteChipDescriptor (p := p))
    (shapeEq : HEq shape (loadByteChip_loadMemoryInteractionShape (p := p))) :
    LoadMemoryChipGroundingData chip shape := by
  subst chip
  cases shapeEq
  constructor
  · exact rfl
  · exact loadByteChip_viewClockBounds
  · exact loadByteChip_timestampBounds
  · exact loadByteChip_isRam
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadByteChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadByteChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadByteChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadByteChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have pulled := loadPulledWords_isU64_of_shape
      loadByteChip_loadMemoryInteractionShape decoded witness.data hchip real memory
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadByteChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have immC :
        (programAccess
          ((DecodedInstructionRow.mk loadByteChipDescriptor physical).toChipRow
            witness.data).view).toRow.imm_c = 1 := by
      simp only [programAccess, ProgramAccess.toRow, loadByteViewOf_decoded,
        loadByteViewOf, LoadByteChip.rowView, Extracted.ITypeReader.toAdapterView]
    have immediate := decode.immediate_words_isU64.2 immC
    have base :
        Word.isU64 (loadByteViewOf env).adapter.op_b_memory.prev_value := by
      simpa only [loadByteViewOf_decoded, env] using pulled.2.2
    have immediate' : Word.isU64 (loadByteViewOf env).adapter.op_c := by
      simpa only [programAccess, ProgramAccess.toRow, loadByteViewOf_decoded, env]
        using immediate
    have ram : Word.isU64 (loadByteRamAccessOf env).priorValue := by
      simpa only [loadByteChip_loadMemoryInteractionShape,
        loadByteRamAccessOf_decoded, env] using pulled.1
    have assumptions :=
      loadByteAssumptions_env env witness.data base immediate' ram
    change LoadByteChip.Assumptions
      ((⟨LoadByteChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
      witness.data
    rw [← circuitRowInputOf_eq_component]
    exact assumptions
  · exact loadByteChipDescriptor_rdGuard
  · intro witness constraints decoded hchip decodedMem real
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadByteChipDescriptor (p := p) := hchip
    subst hchip'
    rw [loadByteViewOf_decoded, loadByteViewOf_opA0]
    let input : Var LoadByteChip.Inputs (ZMod p) := varFromOffset LoadByteChip.Inputs 0
    let offset := size LoadByteChip.Inputs
    have mainConstraints :
        Operations.ConstraintsHold (Environment.fromArray physical witness.data)
          ((LoadByteChip.main input).operations offset) :=
      (Component.constraintsHold_iff _).mp rowConstraints
    exact LoadByteChip.eval_inputOpA0_eq_zero_of_mainConstraints
      input offset (Environment.fromArray physical witness.data) mainConstraints
  · intro witness constraints balanced decoded hchip decodedMem real guard program decode
      openInputs state operands sourceA pulls
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    have chipSpec := decoded.chipSpec_of_openSoundnessInputs witness constraints balanced
      decodedMem openInputs
    have isRam := loadByteChip_isRam decoded witness.data hchip rowConstraints real
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadByteChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input := circuitRowInputOf (p := p) LoadByteChip.circuit env
    let cols := circuitRowOutputOf (p := p) LoadByteChip.circuit env
    have decodedSpec :
        ((loadByteChipDescriptor (p := p)).decodeRow witness.data physical).chipSpec
          witness.data := by
      exact chipSpec
    have spec : LoadByteChip.Spec input cols witness.data := by
      simpa only [input, cols, env] using
        loadByteSpec_of_decoded witness.data physical decodedSpec
    have realInput : LoadByteChip.isReal input = 1 := by
      have realView := real
      unfold ChipRow.is_real at realView
      rw [loadByteViewOf_decoded] at realView
      simpa only [input, loadByteViewOf, LoadByteChip.rowView] using realView
    have concreteAssumptions : LoadByteChip.Assumptions input witness.data := by
      exact (loadByteChipDescriptor_assumptions_iff env).mp openInputs.assumptions
    obtain ⟨baseBound, immediateBound, priorBound⟩ := concreteAssumptions
    have guardInput : input.adapter.op_a ≠ 0 := by
      have guardView := guard
      unfold RdGuardFact at guardView
      rw [loadByteChipDescriptor_rdGuard] at guardView
      change
        ((DecodedInstructionRow.mk loadByteChipDescriptor physical).toChipRow
          witness.data).view.adapter.op_a ≠ 0 at guardView
      rw [loadByteViewOf_decoded] at guardView
      simpa only [input, loadByteViewOf, LoadByteChip.rowView,
        Extracted.ITypeReader.toAdapterView] using guardView
    have pcBound : input.state.pc[0].val < 2 ^ 16 := by
      have bound := programSpec.2.1
      change
        ((DecodedInstructionRow.mk loadByteChipDescriptor physical).toChipRow
          witness.data).view.state.pc[0].val < 2 ^ 16 at bound
      rw [loadByteViewOf_decoded] at bound
      simpa only [input, loadByteViewOf, LoadByteChip.rowView] using bound
    have oneHot := loadByte_oneHot input cols witness.data spec realInput
    let addressInput : AddressOperation.Inputs (ZMod p) :=
      ⟨input.op_b_val, input.op_c_imm, input.offset_bit[0],
        input.offset_bit[1], input.offset_bit[2], LoadByteChip.isReal input⟩
    have addressFacts := AddressOperation.effectiveAddress_facts
      baseBound immediateBound
        (AddressOperation.validAddress_of_spec (spec.1.2.2.2 realInput))
    obtain ⟨index, indexEq, byteEq⟩ :=
      loadByte_selectedMemoryByte input cols witness.data spec realInput priorBound
    have stateByteRaw := ramPriorByte_of_loadShape
      loadByteChip_loadMemoryInteractionShape
      (DecodedInstructionRow.mk loadByteChipDescriptor physical) witness.data
      rfl real isRam pulls index
    have stateByte :
        state.mem.get?
          ((ramCellOfAccess (loadByteRamAccessOf env)).baseAddr.toNat + index.val) =
            some (wordBytes
              (Word.toBitVec64 (loadByteRamAccessOf env).priorValue))[index] := by
      simpa only [loadByteChip_loadMemoryInteractionShape,
        loadByteRamAccessOf_decoded, env] using stateByteRaw
    have accessAddress :
        (loadByteRamAccessOf env).address =
          AddressOperation.alignedValue addressInput cols.address_operation := by
      simp only [loadByteRamAccessOf, LoadByteChip.ramAccessView, addressInput,
        input, cols]
    have effectiveAddress :=
      effectiveAddress_eq_ramCellBase_add_offset addressInput cols.address_operation
        (loadByteRamAccessOf env) accessAddress (spec.1.2.2.2 realInput)
        baseBound immediateBound
    have memoryByteGet :
        state.mem.get? (AddressOperation.effectiveAddress addressInput).toNat =
          some (BitVec.ofNat 8 input.selected_byte.val) := by
      calc
        state.mem.get? (AddressOperation.effectiveAddress addressInput).toNat =
            state.mem.get? (
              (ramCellOfAccess (loadByteRamAccessOf env)).baseAddr.toNat +
                index.val) := by rw [effectiveAddress, indexEq]
        _ = some
            (wordBytes (Word.toBitVec64
              (loadByteRamAccessOf env).priorValue))[index] := stateByte
        _ = some (BitVec.ofNat 8 input.selected_byte.val) := by
          rw [show (loadByteRamAccessOf env).priorValue =
              input.memory_access.prev_value from by
            simp only [loadByteRamAccessOf, LoadByteChip.ramAccessView, input]]
          rw [byteEq]
    have memoryByte :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat]? =
          some (BitVec.ofNat 8 input.selected_byte.val) := memoryByteGet
    have ready : LoadByteChip.AdvanceReady input cols program state := by
      have highBound :
          (AddressOperation.effectiveAddress addressInput).toNat + 1 ≤ 2 ^ 48 :=
        Nat.succ_le_iff.mpr addressFacts.1
      refine ⟨guardInput, pcBound, oneHot, ?_, addressFacts.2.1, ?_⟩
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadByteChip.Inputs.op_b_val, LoadByteChip.Inputs.op_c_imm] using highBound
      · simpa only [addressInput,
          AddressOperation.effectiveAddress, LoadByteChip.Inputs.op_b_val,
          LoadByteChip.Inputs.op_c_imm] using memoryByte
    exact loadByteAdvanceReady_of_decoded witness.data physical program state
      (by simpa only [input, cols, env] using ready)

/-- LoadByte's residue for the shared register-writing load constructor. -/
theorem loadByteChip_loadMemoryGroundingData :
    LoadMemoryChipGroundingData (loadByteChipDescriptor (p := p))
      loadByteChip_loadMemoryInteractionShape :=
  loadByteChip_loadMemoryGroundingData_of_eq
    loadByteChipDescriptor loadByteChip_loadMemoryInteractionShape rfl (HEq.rfl)

/-- **The LoadByte bundle instance**, assembled by the shared load constructor. -/
theorem loadByteChip_groundingContracts :
    ChipGroundingContracts (loadByteChipDescriptor (p := p)) :=
  loadByteChip_loadMemoryGroundingData.toContracts

end LoadByteAnchor

/-! ## The LoadHalf anchor -/

section LoadHalfAnchor

variable [Fact (2 ^ 25 < p)]

set_option maxHeartbeats 1000000 in
private theorem loadHalfChip_loadMemoryGroundingData_of_eq
    (chip : SupportedChip p) (shape : LoadMemoryInteractionShape chip)
    (chipEq : chip = loadHalfChipDescriptor (p := p))
    (shapeEq : HEq shape (loadHalfChip_loadMemoryInteractionShape (p := p))) :
    LoadMemoryChipGroundingData chip shape := by
  subst chip
  cases shapeEq
  constructor
  · exact rfl
  · exact loadHalfChip_viewClockBounds
  · exact loadHalfChip_timestampBounds
  · exact loadHalfChip_isRam
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadHalfChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadHalfChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadHalfChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadHalfChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have pulled := loadPulledWords_isU64_of_shape
      loadHalfChip_loadMemoryInteractionShape decoded witness.data hchip real memory
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadHalfChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have immediate := decode.immediate_words_isU64.2 (by
      simp only [programAccess, ProgramAccess.toRow, loadHalfChip_viewOf_decoded,
        circuitRowViewOf_eq_typed, LoadHalfChip.rowView,
        Extracted.ITypeReader.toAdapterView])
    have base : Word.isU64
        ((circuitRowViewOf LoadHalfChip.circuit LoadHalfChip.rowView env).adapter.op_b_memory.prev_value) := by
      simpa only [loadHalfChip_viewOf_decoded, env] using pulled.2.2
    have immediate' : Word.isU64
        (circuitRowViewOf LoadHalfChip.circuit LoadHalfChip.rowView env).adapter.op_c := by
      simpa only [programAccess, ProgramAccess.toRow, loadHalfChip_viewOf_decoded, env]
        using immediate
    have ram : Word.isU64
        (circuitRamAccessOf LoadHalfChip.circuit LoadHalfChip.ramAccessView env).priorValue := by
      simpa only [loadHalfChip_loadMemoryInteractionShape,
        loadHalfChip_ramAccessOf_decoded, env] using pulled.1
    have assumptions :=
      loadHalfAssumptions_env env witness.data base immediate' ram
    change LoadHalfChip.Assumptions
      ((⟨LoadHalfChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
      witness.data
    rw [← circuitRowInputOf_eq_component]
    exact assumptions
  · exact loadHalfChipDescriptor_rdGuard
  · intro witness constraints decoded hchip decodedMem real
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadHalfChipDescriptor (p := p) := hchip
    subst hchip'
    rw [loadHalfChip_viewOf_decoded, loadHalfView_opA0]
    let input : Var LoadHalfChip.Inputs (ZMod p) := varFromOffset LoadHalfChip.Inputs 0
    let offset := size LoadHalfChip.Inputs
    have mainConstraints :
        Operations.ConstraintsHold (Environment.fromArray physical witness.data)
          ((LoadHalfChip.main input).operations offset) :=
      (Component.constraintsHold_iff _).mp rowConstraints
    exact LoadHalfChip.eval_inputOpA0_eq_zero_of_mainConstraints
      input offset (Environment.fromArray physical witness.data) mainConstraints
  · intro witness constraints balanced decoded hchip decodedMem real guard program decode
      openInputs state operands sourceA pulls
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    have chipSpec := decoded.chipSpec_of_openSoundnessInputs witness constraints balanced
      decodedMem openInputs
    have isRam := loadHalfChip_isRam decoded witness.data hchip rowConstraints real
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadHalfChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input := circuitRowInputOf (p := p) LoadHalfChip.circuit env
    let cols := circuitRowOutputOf (p := p) LoadHalfChip.circuit env
    let access :=
      circuitRamAccessOf LoadHalfChip.circuit LoadHalfChip.ramAccessView env
    have decodedSpec :
        ((loadHalfChipDescriptor (p := p)).decodeRow witness.data physical).chipSpec
          witness.data := chipSpec
    have spec : LoadHalfChip.Spec input cols witness.data := by
      simpa only [input, cols, env] using
        loadHalfSpec_of_decoded witness.data physical decodedSpec
    have realInput : LoadHalfChip.isReal input = 1 := by
      have realView := real
      unfold ChipRow.is_real at realView
      rw [loadHalfChip_viewOf_decoded, circuitRowViewOf_eq_typed] at realView
      simpa only [input, cols, LoadHalfChip.rowView] using realView
    have concreteAssumptions : LoadHalfChip.Assumptions input witness.data :=
      (loadHalfChipDescriptor_assumptions_iff env).mp openInputs.assumptions
    obtain ⟨baseBound, immediateBound, priorBound⟩ := concreteAssumptions
    have guardInput : input.adapter.op_a ≠ 0 := by
      have guardView := guard
      unfold RdGuardFact at guardView
      rw [loadHalfChipDescriptor_rdGuard] at guardView
      change
        ((DecodedInstructionRow.mk loadHalfChipDescriptor physical).toChipRow
          witness.data).view.adapter.op_a ≠ 0 at guardView
      rw [loadHalfChip_viewOf_decoded, circuitRowViewOf_eq_typed] at guardView
      simpa only [input, cols, LoadHalfChip.rowView,
        Extracted.ITypeReader.toAdapterView] using guardView
    have pcBound : input.state.pc[0].val < 2 ^ 16 := by
      have bound := programSpec.2.1
      change
        ((DecodedInstructionRow.mk loadHalfChipDescriptor physical).toChipRow
          witness.data).view.state.pc[0].val < 2 ^ 16 at bound
      rw [loadHalfChip_viewOf_decoded, circuitRowViewOf_eq_typed] at bound
      simpa only [input, cols, LoadHalfChip.rowView] using bound
    have oneHot := loadHalf_oneHot input cols witness.data spec realInput
    let addressInput : AddressOperation.Inputs (ZMod p) :=
      ⟨input.op_b_val, input.op_c_imm, 0, input.offset_bit[0],
        input.offset_bit[1], LoadHalfChip.isReal input⟩
    have addressFacts := AddressOperation.effectiveAddress_facts
      baseBound immediateBound
        (AddressOperation.validAddress_of_spec (spec.1.2.2.2 realInput))
    have alignment : (AddressOperation.effectiveAddress addressInput).toNat % 2 = 0 := by
      rw [← Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 8)]
      rw [← addressFacts.2.2]
      simp only [ZMod.val_zero, zero_add]
      omega
    have highBound :
        (AddressOperation.effectiveAddress addressInput).toNat + 2 ≤ 2 ^ 48 := by
      have high :
          (AddressOperation.effectiveAddress addressInput).toNat < 2 ^ 48 := by
        simpa only [addressInput] using addressFacts.1
      have divides : 2 ∣ (AddressOperation.effectiveAddress addressInput).toNat :=
        Nat.dvd_of_mod_eq_zero alignment
      obtain ⟨k, hk⟩ := divides
      omega
    obtain ⟨i₀, i₁, i₀Eq, i₁Eq, selectedBound, byte₀Eq, byte₁Eq⟩ :=
      loadHalf_selectedBytes input cols witness.data spec priorBound
    have stateByte₀Raw := ramPriorByte_of_loadShape
      loadHalfChip_loadMemoryInteractionShape
      (DecodedInstructionRow.mk loadHalfChipDescriptor physical) witness.data
      rfl real isRam pulls i₀
    have stateByte₁Raw := ramPriorByte_of_loadShape
      loadHalfChip_loadMemoryInteractionShape
      (DecodedInstructionRow.mk loadHalfChipDescriptor physical) witness.data
      rfl real isRam pulls i₁
    have stateByte₀ :
        state.mem.get? ((ramCellOfAccess access).baseAddr.toNat + i₀.val) =
          some (wordBytes (Word.toBitVec64 access.priorValue))[i₀] := by
      simpa only [loadHalfChip_loadMemoryInteractionShape,
        loadHalfChip_ramAccessOf_decoded, access, env] using stateByte₀Raw
    have stateByte₁ :
        state.mem.get? ((ramCellOfAccess access).baseAddr.toNat + i₁.val) =
          some (wordBytes (Word.toBitVec64 access.priorValue))[i₁] := by
      simpa only [loadHalfChip_loadMemoryInteractionShape,
        loadHalfChip_ramAccessOf_decoded, access, env] using stateByte₁Raw
    have accessAddress :
        access.address =
          AddressOperation.alignedValue addressInput cols.address_operation := by
      dsimp only [access]
      rw [circuitRamAccessOf_eq_typed]
      simp only [LoadHalfChip.ramAccessView, addressInput, input, cols]
    have effectiveAddress :=
      effectiveAddress_eq_ramCellBase_add_offset addressInput cols.address_operation
        access accessAddress (spec.1.2.2.2 realInput) baseBound immediateBound
    have priorValueEq :
        access.priorValue = input.memory_access.prev_value := by
      dsimp only [access]
      rw [circuitRamAccessOf_eq_typed]
      rfl
    have memoryByte₀Get :
        state.mem.get? (AddressOperation.effectiveAddress addressInput).toNat =
          some (BitVec.ofNat 8 input.selected_half.val) := by
      calc
        state.mem.get? (AddressOperation.effectiveAddress addressInput).toNat =
            state.mem.get? ((ramCellOfAccess access).baseAddr.toNat + i₀.val) := by
              rw [effectiveAddress, i₀Eq]
        _ = some (wordBytes (Word.toBitVec64 access.priorValue))[i₀] := stateByte₀
        _ = some (BitVec.ofNat 8 input.selected_half.val) := by
          rw [priorValueEq, byte₀Eq]
    have memoryByte₁Get :
        state.mem.get? ((AddressOperation.effectiveAddress addressInput).toNat + 1) =
          some (BitVec.ofNat 8 (input.selected_half.val >>> 8)) := by
      calc
        state.mem.get? ((AddressOperation.effectiveAddress addressInput).toNat + 1) =
            state.mem.get? ((ramCellOfAccess access).baseAddr.toNat + i₁.val) := by
              apply congrArg state.mem.get?
              rw [effectiveAddress, i₁Eq]
              simp only [addressInput]
              omega
        _ = some (wordBytes (Word.toBitVec64 access.priorValue))[i₁] := stateByte₁
        _ = some (BitVec.ofNat 8 (input.selected_half.val >>> 8)) := by
          rw [priorValueEq, byte₁Eq]
    have memoryByte₀ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat]? =
          some (BitVec.ofNat 8 input.selected_half.val) := memoryByte₀Get
    have memoryByte₁ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat + 1]? =
          some (BitVec.ofNat 8 (input.selected_half.val >>> 8)) := memoryByte₁Get
    have ready : LoadHalfChip.AdvanceReady input cols program state := by
      refine ⟨guardInput, pcBound, oneHot, selectedBound, alignment, highBound,
        addressFacts.2.1, ?_, ?_⟩
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadHalfChip.Inputs.op_b_val, LoadHalfChip.Inputs.op_c_imm] using memoryByte₀
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadHalfChip.Inputs.op_b_val, LoadHalfChip.Inputs.op_c_imm] using memoryByte₁
    exact loadHalfAdvanceReady_of_decoded witness.data physical program state
      (by simpa only [input, cols, env] using ready)

/-- LoadHalf's residue for the shared register-writing load constructor. -/
theorem loadHalfChip_loadMemoryGroundingData :
    LoadMemoryChipGroundingData (loadHalfChipDescriptor (p := p))
      loadHalfChip_loadMemoryInteractionShape :=
  loadHalfChip_loadMemoryGroundingData_of_eq
    loadHalfChipDescriptor loadHalfChip_loadMemoryInteractionShape rfl (HEq.rfl)

/-- **The LoadHalf bundle instance**, assembled by the shared load constructor. -/
theorem loadHalfChip_groundingContracts :
    ChipGroundingContracts (loadHalfChipDescriptor (p := p)) :=
  loadHalfChip_loadMemoryGroundingData.toContracts

end LoadHalfAnchor

/-! ## The LoadWord anchor -/

section LoadWordAnchor

variable [Fact (2 ^ 25 < p)]

set_option maxHeartbeats 1000000 in
private theorem loadWordChip_loadMemoryGroundingData_of_eq
    (chip : SupportedChip p) (shape : LoadMemoryInteractionShape chip)
    (chipEq : chip = loadWordChipDescriptor (p := p))
    (shapeEq : HEq shape (loadWordChip_loadMemoryInteractionShape (p := p))) :
    LoadMemoryChipGroundingData chip shape := by
  subst chip
  cases shapeEq
  constructor
  · exact rfl
  · exact loadWordChip_viewClockBounds
  · exact loadWordChip_timestampBounds
  · exact loadWordChip_isRam
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadWordChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadWordChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadWordChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadWordChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have pulled := loadPulledWords_isU64_of_shape
      loadWordChip_loadMemoryInteractionShape decoded witness.data hchip real memory
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadWordChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have immediate := decode.immediate_words_isU64.2 (by
      simp only [programAccess, ProgramAccess.toRow, loadWordChip_viewOf_decoded,
        circuitRowViewOf_eq_typed, LoadWordChip.rowView,
        Extracted.ITypeReader.toAdapterView])
    have base : Word.isU64
        ((circuitRowViewOf LoadWordChip.circuit LoadWordChip.rowView env).adapter.op_b_memory.prev_value) := by
      simpa only [loadWordChip_viewOf_decoded, env] using pulled.2.2
    have immediate' : Word.isU64
        (circuitRowViewOf LoadWordChip.circuit LoadWordChip.rowView env).adapter.op_c := by
      simpa only [programAccess, ProgramAccess.toRow, loadWordChip_viewOf_decoded, env]
        using immediate
    have ram : Word.isU64
        (circuitRamAccessOf LoadWordChip.circuit LoadWordChip.ramAccessView env).priorValue := by
      simpa only [loadWordChip_loadMemoryInteractionShape,
        loadWordChip_ramAccessOf_decoded, env] using pulled.1
    have assumptions :=
      loadWordAssumptions_env env witness.data base immediate' ram
    change LoadWordChip.Assumptions
      ((⟨LoadWordChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
      witness.data
    rw [← circuitRowInputOf_eq_component]
    exact assumptions
  · exact loadWordChipDescriptor_rdGuard
  · intro witness constraints decoded hchip decodedMem real
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadWordChipDescriptor (p := p) := hchip
    subst hchip'
    rw [loadWordChip_viewOf_decoded, loadWordView_opA0]
    let input : Var LoadWordChip.Inputs (ZMod p) := varFromOffset LoadWordChip.Inputs 0
    let offset := size LoadWordChip.Inputs
    have mainConstraints :
        Operations.ConstraintsHold (Environment.fromArray physical witness.data)
          ((LoadWordChip.main input).operations offset) :=
      (Component.constraintsHold_iff _).mp rowConstraints
    exact LoadWordChip.eval_inputOpA0_eq_zero_of_mainConstraints
      input offset (Environment.fromArray physical witness.data) mainConstraints
  · intro witness constraints balanced decoded hchip decodedMem real guard program decode
      openInputs state operands sourceA pulls
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    have chipSpec := decoded.chipSpec_of_openSoundnessInputs witness constraints balanced
      decodedMem openInputs
    have isRam := loadWordChip_isRam decoded witness.data hchip rowConstraints real
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadWordChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input := circuitRowInputOf (p := p) LoadWordChip.circuit env
    let cols := circuitRowOutputOf (p := p) LoadWordChip.circuit env
    let access :=
      circuitRamAccessOf LoadWordChip.circuit LoadWordChip.ramAccessView env
    have decodedSpec :
        ((loadWordChipDescriptor (p := p)).decodeRow witness.data physical).chipSpec
          witness.data := chipSpec
    have spec : LoadWordChip.Spec input cols witness.data := by
      simpa only [input, cols, env] using
        loadWordSpec_of_decoded witness.data physical decodedSpec
    have realInput : LoadWordChip.isReal input = 1 := by
      have realView := real
      unfold ChipRow.is_real at realView
      rw [loadWordChip_viewOf_decoded, circuitRowViewOf_eq_typed] at realView
      simpa only [input, cols, LoadWordChip.rowView] using realView
    have concreteAssumptions : LoadWordChip.Assumptions input witness.data :=
      (loadWordChipDescriptor_assumptions_iff env).mp openInputs.assumptions
    obtain ⟨baseBound, immediateBound, priorBound⟩ := concreteAssumptions
    have guardInput : input.adapter.op_a ≠ 0 := by
      have guardView := guard
      unfold RdGuardFact at guardView
      rw [loadWordChipDescriptor_rdGuard] at guardView
      change
        ((DecodedInstructionRow.mk loadWordChipDescriptor physical).toChipRow
          witness.data).view.adapter.op_a ≠ 0 at guardView
      rw [loadWordChip_viewOf_decoded, circuitRowViewOf_eq_typed] at guardView
      simpa only [input, cols, LoadWordChip.rowView,
        Extracted.ITypeReader.toAdapterView] using guardView
    have pcBound : input.state.pc[0].val < 2 ^ 16 := by
      have bound := programSpec.2.1
      change
        ((DecodedInstructionRow.mk loadWordChipDescriptor physical).toChipRow
          witness.data).view.state.pc[0].val < 2 ^ 16 at bound
      rw [loadWordChip_viewOf_decoded, circuitRowViewOf_eq_typed] at bound
      simpa only [input, cols, LoadWordChip.rowView] using bound
    have oneHot := loadWord_oneHot input cols witness.data spec realInput
    let addressInput : AddressOperation.Inputs (ZMod p) :=
      ⟨input.op_b_val, input.op_c_imm, 0, 0, input.offset_bit,
        LoadWordChip.isReal input⟩
    have addressFacts := AddressOperation.effectiveAddress_facts
      baseBound immediateBound
        (AddressOperation.validAddress_of_spec (spec.1.2.2.2 realInput))
    have alignment : (AddressOperation.effectiveAddress addressInput).toNat % 4 = 0 := by
      rw [← Nat.mod_mod_of_dvd _ (by norm_num : 4 ∣ 8)]
      rw [← addressFacts.2.2]
      simp only [ZMod.val_zero, zero_add]
      omega
    have highBound :
        (AddressOperation.effectiveAddress addressInput).toNat + 4 ≤ 2 ^ 48 := by
      have high :
          (AddressOperation.effectiveAddress addressInput).toNat < 2 ^ 48 := by
        simpa only [addressInput] using addressFacts.1
      have divides : 4 ∣ (AddressOperation.effectiveAddress addressInput).toNat :=
        Nat.dvd_of_mod_eq_zero alignment
      obtain ⟨k, hk⟩ := divides
      omega
    obtain ⟨i₀, i₁, i₂, i₃, i₀Eq, i₁Eq, i₂Eq, i₃Eq,
      selected₀Bound, selected₁Bound, byte₀Eq, byte₁Eq, byte₂Eq, byte₃Eq⟩ :=
      loadWord_selectedBytes input cols witness.data spec priorBound
    have stateBytes (i : Fin 8) :
        state.mem.get? ((ramCellOfAccess access).baseAddr.toNat + i.val) =
          some (wordBytes (Word.toBitVec64 access.priorValue))[i] := by
      have raw := ramPriorByte_of_loadShape loadWordChip_loadMemoryInteractionShape
        (DecodedInstructionRow.mk loadWordChipDescriptor physical) witness.data
        rfl real isRam pulls i
      simpa only [loadWordChip_loadMemoryInteractionShape,
        loadWordChip_ramAccessOf_decoded, access, env] using raw
    have accessAddress :
        access.address =
          AddressOperation.alignedValue addressInput cols.address_operation := by
      dsimp only [access]
      rw [circuitRamAccessOf_eq_typed]
      simp only [LoadWordChip.ramAccessView, addressInput, input, cols]
    have effectiveAddress :=
      effectiveAddress_eq_ramCellBase_add_offset addressInput cols.address_operation
        access accessAddress (spec.1.2.2.2 realInput) baseBound immediateBound
    have priorValueEq :
        access.priorValue = input.memory_access.prev_value := by
      dsimp only [access]
      rw [circuitRamAccessOf_eq_typed]
      rfl
    have memoryAt (i : Fin 8) (k : ℕ)
        (indexEq : i.val = addressOffset addressInput + k)
        (byteEq : (wordBytes (Word.toBitVec64 input.memory_access.prev_value))[i] =
          BitVec.ofNat 8
            (if k = 0 then input.selected_word[0].val
             else if k = 1 then input.selected_word[0].val >>> 8
             else if k = 2 then input.selected_word[1].val
             else input.selected_word[1].val >>> 8)) :
        state.mem.get? ((AddressOperation.effectiveAddress addressInput).toNat + k) =
          some (BitVec.ofNat 8
            (if k = 0 then input.selected_word[0].val
             else if k = 1 then input.selected_word[0].val >>> 8
             else if k = 2 then input.selected_word[1].val
             else input.selected_word[1].val >>> 8)) := by
      calc
        state.mem.get? ((AddressOperation.effectiveAddress addressInput).toNat + k) =
            state.mem.get? ((ramCellOfAccess access).baseAddr.toNat + i.val) := by
              apply congrArg state.mem.get?
              rw [effectiveAddress, indexEq]
              omega
        _ = some (wordBytes (Word.toBitVec64 access.priorValue))[i] := stateBytes i
        _ = _ := by rw [priorValueEq, byteEq]
    have memoryByte₀Get := memoryAt i₀ 0
      (by simpa only [addressInput, Nat.add_zero] using i₀Eq)
      (by simpa using byte₀Eq)
    have memoryByte₁Get := memoryAt i₁ 1 (by simpa only [addressInput] using i₁Eq)
      (by simpa using byte₁Eq)
    have memoryByte₂Get := memoryAt i₂ 2 (by simpa only [addressInput] using i₂Eq)
      (by simpa using byte₂Eq)
    have memoryByte₃Get := memoryAt i₃ 3 (by simpa only [addressInput] using i₃Eq)
      (by simpa using byte₃Eq)
    have memoryByte₀ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat]? =
          some (BitVec.ofNat 8 input.selected_word[0].val) := by
      simpa using memoryByte₀Get
    have memoryByte₁ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat + 1]? =
          some (BitVec.ofNat 8 (input.selected_word[0].val >>> 8)) := by
      simpa using memoryByte₁Get
    have memoryByte₂ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat + 2]? =
          some (BitVec.ofNat 8 input.selected_word[1].val) := by
      simpa using memoryByte₂Get
    have memoryByte₃ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat + 3]? =
          some (BitVec.ofNat 8 (input.selected_word[1].val >>> 8)) := by
      simpa using memoryByte₃Get
    have ready : LoadWordChip.AdvanceReady input cols program state := by
      refine ⟨guardInput, pcBound, oneHot, selected₀Bound, selected₁Bound, alignment,
        highBound, addressFacts.2.1, ?_, ?_, ?_, ?_⟩
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadWordChip.Inputs.op_b_val, LoadWordChip.Inputs.op_c_imm] using memoryByte₀
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadWordChip.Inputs.op_b_val, LoadWordChip.Inputs.op_c_imm] using memoryByte₁
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadWordChip.Inputs.op_b_val, LoadWordChip.Inputs.op_c_imm] using memoryByte₂
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadWordChip.Inputs.op_b_val, LoadWordChip.Inputs.op_c_imm] using memoryByte₃
    exact loadWordAdvanceReady_of_decoded witness.data physical program state
      (by simpa only [input, cols, env] using ready)

/-- LoadWord's residue for the shared register-writing load constructor. -/
theorem loadWordChip_loadMemoryGroundingData :
    LoadMemoryChipGroundingData (loadWordChipDescriptor (p := p))
      loadWordChip_loadMemoryInteractionShape :=
  loadWordChip_loadMemoryGroundingData_of_eq
    loadWordChipDescriptor loadWordChip_loadMemoryInteractionShape rfl (HEq.rfl)

/-- **The LoadWord bundle instance**, assembled by the shared load constructor. -/
theorem loadWordChip_groundingContracts :
    ChipGroundingContracts (loadWordChipDescriptor (p := p)) :=
  loadWordChip_loadMemoryGroundingData.toContracts

end LoadWordAnchor

/-! ## The LoadDouble anchor -/

section LoadDoubleAnchor

variable [Fact (2 ^ 25 < p)]

set_option maxHeartbeats 1000000 in
private theorem loadDoubleChip_loadMemoryGroundingData_of_eq
    (chip : SupportedChip p) (shape : LoadMemoryInteractionShape chip)
    (chipEq : chip = loadDoubleChipDescriptor (p := p))
    (shapeEq : HEq shape (loadDoubleChip_loadMemoryInteractionShape (p := p))) :
    LoadMemoryChipGroundingData chip shape := by
  subst chip
  cases shapeEq
  constructor
  · exact rfl
  · exact loadDoubleChip_viewClockBounds
  · exact loadDoubleChip_timestampBounds
  · exact loadDoubleChip_isRam
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadDoubleChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadDoubleChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadDoubleChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadDoubleChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have pulled := loadPulledWords_isU64_of_shape
      loadDoubleChip_loadMemoryInteractionShape decoded witness.data hchip real memory
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadDoubleChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have immediate := decode.immediate_words_isU64.2 (by
      simp only [programAccess, ProgramAccess.toRow, loadDoubleChip_viewOf_decoded,
        circuitRowViewOf_eq_typed, LoadDoubleChip.rowView,
        Extracted.ITypeReader.toAdapterView])
    have base : Word.isU64
        ((circuitRowViewOf LoadDoubleChip.circuit
          LoadDoubleChip.rowView env).adapter.op_b_memory.prev_value) := by
      simpa only [loadDoubleChip_viewOf_decoded, env] using pulled.2.2
    have immediate' : Word.isU64
        (circuitRowViewOf LoadDoubleChip.circuit LoadDoubleChip.rowView env).adapter.op_c := by
      simpa only [programAccess, ProgramAccess.toRow, loadDoubleChip_viewOf_decoded, env]
        using immediate
    have ram : Word.isU64
        (circuitRamAccessOf LoadDoubleChip.circuit
          LoadDoubleChip.ramAccessView env).priorValue := by
      simpa only [loadDoubleChip_loadMemoryInteractionShape,
        loadDoubleChip_ramAccessOf_decoded, env] using pulled.1
    have assumptions :=
      loadDoubleAssumptions_env env witness.data base immediate' ram
    change LoadDoubleChip.Assumptions
      ((⟨LoadDoubleChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
      witness.data
    rw [← circuitRowInputOf_eq_component]
    exact assumptions
  · exact loadDoubleChipDescriptor_rdGuard
  · intro witness constraints decoded hchip decodedMem real
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadDoubleChipDescriptor (p := p) := hchip
    subst hchip'
    rw [loadDoubleChip_viewOf_decoded, loadDoubleView_opA0]
    let input : Var LoadDoubleChip.Inputs (ZMod p) :=
      varFromOffset LoadDoubleChip.Inputs 0
    let offset := size LoadDoubleChip.Inputs
    have mainConstraints :
        Operations.ConstraintsHold (Environment.fromArray physical witness.data)
          ((LoadDoubleChip.main input).operations offset) :=
      (Component.constraintsHold_iff _).mp rowConstraints
    exact LoadDoubleChip.eval_inputOpA0_eq_zero_of_mainConstraints
      input offset (Environment.fromArray physical witness.data) mainConstraints
  · intro witness constraints balanced decoded hchip decodedMem real guard program decode
      openInputs state operands sourceA pulls
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    have chipSpec := decoded.chipSpec_of_openSoundnessInputs witness constraints balanced
      decodedMem openInputs
    have isRam := loadDoubleChip_isRam decoded witness.data hchip rowConstraints real
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadDoubleChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input := circuitRowInputOf (p := p) LoadDoubleChip.circuit env
    let cols := circuitRowOutputOf (p := p) LoadDoubleChip.circuit env
    let access :=
      circuitRamAccessOf LoadDoubleChip.circuit LoadDoubleChip.ramAccessView env
    have decodedSpec :
        ((loadDoubleChipDescriptor (p := p)).decodeRow witness.data physical).chipSpec
          witness.data := chipSpec
    have spec : LoadDoubleChip.Spec input cols witness.data := by
      simpa only [input, cols, env] using
        loadDoubleSpec_of_decoded witness.data physical decodedSpec
    have realInput : input.is_real = 1 := by
      have realView := real
      unfold ChipRow.is_real at realView
      rw [loadDoubleChip_viewOf_decoded, circuitRowViewOf_eq_typed] at realView
      simpa only [input, cols, LoadDoubleChip.rowView] using realView
    have concreteAssumptions : LoadDoubleChip.Assumptions input witness.data :=
      (loadDoubleChipDescriptor_assumptions_iff env).mp openInputs.assumptions
    obtain ⟨baseBound, immediateBound, priorBound⟩ := concreteAssumptions
    have guardInput : input.adapter.op_a ≠ 0 := by
      have guardView := guard
      unfold RdGuardFact at guardView
      rw [loadDoubleChipDescriptor_rdGuard] at guardView
      change
        ((DecodedInstructionRow.mk loadDoubleChipDescriptor physical).toChipRow
          witness.data).view.adapter.op_a ≠ 0 at guardView
      rw [loadDoubleChip_viewOf_decoded, circuitRowViewOf_eq_typed] at guardView
      simpa only [input, cols, LoadDoubleChip.rowView,
        Extracted.ITypeReader.toAdapterView] using guardView
    have pcBound : input.state.pc[0].val < 2 ^ 16 := by
      have bound := programSpec.2.1
      change
        ((DecodedInstructionRow.mk loadDoubleChipDescriptor physical).toChipRow
          witness.data).view.state.pc[0].val < 2 ^ 16 at bound
      rw [loadDoubleChip_viewOf_decoded, circuitRowViewOf_eq_typed] at bound
      simpa only [input, cols, LoadDoubleChip.rowView] using bound
    let addressInput : AddressOperation.Inputs (ZMod p) :=
      ⟨input.op_b_val, input.op_c_imm, 0, 0, 0, input.is_real⟩
    have addressFacts := AddressOperation.effectiveAddress_facts
      baseBound immediateBound
        (AddressOperation.validAddress_of_spec (spec.1.2.2.2 realInput))
    have alignment : (AddressOperation.effectiveAddress addressInput).toNat % 8 = 0 := by
      rw [← addressFacts.2.2]
      simp only [ZMod.val_zero, zero_add]
    have highBound :
        (AddressOperation.effectiveAddress addressInput).toNat + 8 ≤ 2 ^ 48 := by
      have high :
          (AddressOperation.effectiveAddress addressInput).toNat < 2 ^ 48 := by
        simpa only [addressInput] using addressFacts.1
      have divides : 8 ∣ (AddressOperation.effectiveAddress addressInput).toNat :=
        Nat.dvd_of_mod_eq_zero alignment
      obtain ⟨k, hk⟩ := divides
      omega
    have limbBounds := Word.lt_cases_of_isU64 priorBound
    have stateBytes (i : Fin 8) :
        state.mem.get? ((ramCellOfAccess access).baseAddr.toNat + i.val) =
          some (wordBytes (Word.toBitVec64 access.priorValue))[i] := by
      have raw := ramPriorByte_of_loadShape loadDoubleChip_loadMemoryInteractionShape
        (DecodedInstructionRow.mk loadDoubleChipDescriptor physical) witness.data
        rfl real isRam pulls i
      simpa only [loadDoubleChip_loadMemoryInteractionShape,
        loadDoubleChip_ramAccessOf_decoded, access, env] using raw
    have accessAddress :
        access.address =
          AddressOperation.alignedValue addressInput cols.address_operation := by
      dsimp only [access]
      rw [circuitRamAccessOf_eq_typed]
      simp only [LoadDoubleChip.ramAccessView, addressInput, input, cols]
    have effectiveAddress :=
      effectiveAddress_eq_ramCellBase_add_offset addressInput cols.address_operation
        access accessAddress (spec.1.2.2.2 realInput) baseBound immediateBound
    have priorValueEq :
        access.priorValue = input.memory_access.prev_value := by
      dsimp only [access]
      rw [circuitRamAccessOf_eq_typed]
      rfl
    have memoryAt (i : Fin 8) (k : ℕ) (indexEq : i.val = k)
        (byteEq : (wordBytes (Word.toBitVec64 input.memory_access.prev_value))[i] =
          BitVec.ofNat 8
            (if k = 0 then input.memory_access.prev_value[0].val
             else if k = 1 then input.memory_access.prev_value[0].val >>> 8
             else if k = 2 then input.memory_access.prev_value[1].val
             else if k = 3 then input.memory_access.prev_value[1].val >>> 8
             else if k = 4 then input.memory_access.prev_value[2].val
             else if k = 5 then input.memory_access.prev_value[2].val >>> 8
             else if k = 6 then input.memory_access.prev_value[3].val
             else input.memory_access.prev_value[3].val >>> 8)) :
        state.mem.get? ((AddressOperation.effectiveAddress addressInput).toNat + k) =
          some (BitVec.ofNat 8
            (if k = 0 then input.memory_access.prev_value[0].val
             else if k = 1 then input.memory_access.prev_value[0].val >>> 8
             else if k = 2 then input.memory_access.prev_value[1].val
             else if k = 3 then input.memory_access.prev_value[1].val >>> 8
             else if k = 4 then input.memory_access.prev_value[2].val
             else if k = 5 then input.memory_access.prev_value[2].val >>> 8
             else if k = 6 then input.memory_access.prev_value[3].val
             else input.memory_access.prev_value[3].val >>> 8)) := by
      calc
        state.mem.get? ((AddressOperation.effectiveAddress addressInput).toNat + k) =
            state.mem.get? ((ramCellOfAccess access).baseAddr.toNat + i.val) := by
              apply congrArg state.mem.get?
              rw [effectiveAddress, indexEq]
              simp only [addressInput, addressOffset, ZMod.val_zero]
              omega
        _ = some (wordBytes (Word.toBitVec64 access.priorValue))[i] := stateBytes i
        _ = _ := by rw [priorValueEq, byteEq]
    have memoryByte₀Get := memoryAt ⟨0, by omega⟩ 0 rfl
      (by simpa using wordBytes_zero input.memory_access.prev_value priorBound)
    have memoryByte₁Get := memoryAt ⟨1, by omega⟩ 1 rfl
      (by simpa using wordBytes_one input.memory_access.prev_value priorBound)
    have memoryByte₂Get := memoryAt ⟨2, by omega⟩ 2 rfl
      (by simpa using wordBytes_two input.memory_access.prev_value priorBound)
    have memoryByte₃Get := memoryAt ⟨3, by omega⟩ 3 rfl
      (by simpa using wordBytes_three input.memory_access.prev_value priorBound)
    have memoryByte₄Get := memoryAt ⟨4, by omega⟩ 4 rfl
      (by simpa using wordBytes_four input.memory_access.prev_value priorBound)
    have memoryByte₅Get := memoryAt ⟨5, by omega⟩ 5 rfl
      (by simpa using wordBytes_five input.memory_access.prev_value priorBound)
    have memoryByte₆Get := memoryAt ⟨6, by omega⟩ 6 rfl
      (by simpa using wordBytes_six input.memory_access.prev_value priorBound)
    have memoryByte₇Get := memoryAt ⟨7, by omega⟩ 7 rfl
      (by simpa using wordBytes_seven input.memory_access.prev_value priorBound)
    have memoryByte₀ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat]? =
          some (BitVec.ofNat 8 input.memory_access.prev_value[0].val) := by
      simpa using memoryByte₀Get
    have memoryByte₁ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat + 1]? =
          some (BitVec.ofNat 8 (input.memory_access.prev_value[0].val >>> 8)) := by
      simpa using memoryByte₁Get
    have memoryByte₂ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat + 2]? =
          some (BitVec.ofNat 8 input.memory_access.prev_value[1].val) := by
      simpa using memoryByte₂Get
    have memoryByte₃ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat + 3]? =
          some (BitVec.ofNat 8 (input.memory_access.prev_value[1].val >>> 8)) := by
      simpa using memoryByte₃Get
    have memoryByte₄ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat + 4]? =
          some (BitVec.ofNat 8 input.memory_access.prev_value[2].val) := by
      simpa using memoryByte₄Get
    have memoryByte₅ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat + 5]? =
          some (BitVec.ofNat 8 (input.memory_access.prev_value[2].val >>> 8)) := by
      simpa using memoryByte₅Get
    have memoryByte₆ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat + 6]? =
          some (BitVec.ofNat 8 input.memory_access.prev_value[3].val) := by
      simpa using memoryByte₆Get
    have memoryByte₇ :
        state.mem[(AddressOperation.effectiveAddress addressInput).toNat + 7]? =
          some (BitVec.ofNat 8 (input.memory_access.prev_value[3].val >>> 8)) := by
      simpa using memoryByte₇Get
    have ready : LoadDoubleChip.AdvanceReady input cols program state := by
      refine ⟨guardInput, pcBound, limbBounds.1, limbBounds.2.1, limbBounds.2.2.1,
        limbBounds.2.2.2, alignment, highBound, addressFacts.2.1,
        ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadDoubleChip.Inputs.op_b_val, LoadDoubleChip.Inputs.op_c_imm] using memoryByte₀
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadDoubleChip.Inputs.op_b_val, LoadDoubleChip.Inputs.op_c_imm] using memoryByte₁
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadDoubleChip.Inputs.op_b_val, LoadDoubleChip.Inputs.op_c_imm] using memoryByte₂
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadDoubleChip.Inputs.op_b_val, LoadDoubleChip.Inputs.op_c_imm] using memoryByte₃
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadDoubleChip.Inputs.op_b_val, LoadDoubleChip.Inputs.op_c_imm] using memoryByte₄
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadDoubleChip.Inputs.op_b_val, LoadDoubleChip.Inputs.op_c_imm] using memoryByte₅
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadDoubleChip.Inputs.op_b_val, LoadDoubleChip.Inputs.op_c_imm] using memoryByte₆
      · simpa only [addressInput, AddressOperation.effectiveAddress,
          LoadDoubleChip.Inputs.op_b_val, LoadDoubleChip.Inputs.op_c_imm] using memoryByte₇
    exact loadDoubleAdvanceReady_of_decoded witness.data physical program state
      (by simpa only [input, cols, env] using ready)

/-- LoadDouble's residue for the shared register-writing load constructor. -/
theorem loadDoubleChip_loadMemoryGroundingData :
    LoadMemoryChipGroundingData (loadDoubleChipDescriptor (p := p))
      loadDoubleChip_loadMemoryInteractionShape :=
  loadDoubleChip_loadMemoryGroundingData_of_eq
    loadDoubleChipDescriptor loadDoubleChip_loadMemoryInteractionShape rfl (HEq.rfl)

/-- **The LoadDouble bundle instance**, assembled by the shared load constructor. -/
theorem loadDoubleChip_groundingContracts :
    ChipGroundingContracts (loadDoubleChipDescriptor (p := p)) :=
  loadDoubleChip_loadMemoryGroundingData.toContracts

end LoadDoubleAnchor

/-! ## The LoadX0 anchor -/

section LoadX0Anchor

variable [Fact (2 ^ 25 < p)]

set_option maxHeartbeats 1000000 in
private theorem loadX0Chip_immutableLoadMemoryGroundingData_of_eq
    (chip : SupportedChip p) (shape : ImmutableRamMemoryInteractionShape chip)
    (chipEq : chip = loadX0ChipDescriptor (p := p))
    (shapeEq : HEq shape
      (loadX0Chip_immutableRamMemoryInteractionShape (p := p))) :
    ImmutableLoadMemoryChipGroundingData chip shape := by
  subst chip
  cases shapeEq
  constructor
  · exact rfl
  · exact loadX0Chip_viewClockBounds
  · exact loadX0Chip_timestampBounds
  · exact loadX0Chip_isRam
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadX0ChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadX0ChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadX0ChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadX0ChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have pulled := immutableRamPulledWords_isU64_of_shape
      loadX0Chip_immutableRamMemoryInteractionShape decoded witness.data hchip real memory
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadX0ChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have immediate := decode.immediate_words_isU64.2 (by
      simp only [programAccess, ProgramAccess.toRow, loadX0Chip_viewOf_decoded,
        circuitRowViewOf_eq_typed, LoadX0Chip.rowView,
        Extracted.ITypeReader.toAdapterView])
    have base : Word.isU64
        ((circuitRowViewOf LoadX0Chip.circuit
          LoadX0Chip.rowView env).adapter.op_b_memory.prev_value) := by
      simpa only [loadX0Chip_viewOf_decoded, env] using pulled.2.2
    have immediate' : Word.isU64
        (circuitRowViewOf LoadX0Chip.circuit LoadX0Chip.rowView env).adapter.op_c := by
      simpa only [programAccess, ProgramAccess.toRow, loadX0Chip_viewOf_decoded, env]
        using immediate
    have ram : Word.isU64
        (circuitRamAccessOf LoadX0Chip.circuit
          LoadX0Chip.ramAccessView env).priorValue := by
      simpa only [loadX0Chip_immutableRamMemoryInteractionShape,
        loadX0Chip_ramAccessOf_decoded, env] using pulled.1
    have assumptions := loadX0Assumptions_env env witness.data base immediate' ram
    change LoadX0Chip.Assumptions
      ((⟨LoadX0Chip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
      witness.data
    rw [← circuitRowInputOf_eq_component]
    exact assumptions
  · exact loadX0ChipDescriptor_rdGuard
  · intro witness constraints decoded hchip decodedMem real
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadX0ChipDescriptor (p := p) := hchip
    subst hchip'
    rw [loadX0Chip_viewOf_decoded, loadX0View_opA0]
    let input : Var LoadX0Chip.Inputs (ZMod p) :=
      varFromOffset LoadX0Chip.Inputs 0
    let offset := size LoadX0Chip.Inputs
    have mainConstraints :
        Operations.ConstraintsHold (Environment.fromArray physical witness.data)
          ((LoadX0Chip.main input).operations offset) :=
      (Component.constraintsHold_iff _).mp rowConstraints
    have realInput :
        Expression.eval (Environment.fromArray physical witness.data) input.is_lb +
          Expression.eval (Environment.fromArray physical witness.data) input.is_lbu +
          Expression.eval (Environment.fromArray physical witness.data) input.is_lh +
          Expression.eval (Environment.fromArray physical witness.data) input.is_lhu +
          Expression.eval (Environment.fromArray physical witness.data) input.is_lw +
          Expression.eval (Environment.fromArray physical witness.data) input.is_lwu +
          Expression.eval (Environment.fromArray physical witness.data) input.is_ld = 1 := by
      unfold ChipRow.is_real at real
      rw [loadX0Chip_viewOf_decoded, loadX0View_isReal] at real
      exact real
    exact LoadX0Chip.eval_inputOpA0_eq_one_of_mainConstraints
      input offset (Environment.fromArray physical witness.data) mainConstraints realInput
  · intro witness constraints balanced decoded hchip decodedMem real guard program decode
      openInputs state operands sourceA pulls
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    have chipSpec := decoded.chipSpec_of_openSoundnessInputs witness constraints balanced
      decodedMem openInputs
    have isRam := loadX0Chip_isRam decoded witness.data hchip rowConstraints real
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = loadX0ChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input := circuitRowInputOf (p := p) LoadX0Chip.circuit env
    let cols := circuitRowOutputOf (p := p) LoadX0Chip.circuit env
    let access := circuitRamAccessOf LoadX0Chip.circuit LoadX0Chip.ramAccessView env
    have decodedSpec :
        ((loadX0ChipDescriptor (p := p)).decodeRow witness.data physical).chipSpec
          witness.data := chipSpec
    have spec : LoadX0Chip.Spec input cols witness.data := by
      simpa only [input, cols, env] using
        loadX0Spec_of_decoded witness.data physical decodedSpec
    have realInput : LoadX0Chip.isReal input = 1 := by
      have realView := real
      unfold ChipRow.is_real at realView
      rw [loadX0Chip_viewOf_decoded, circuitRowViewOf_eq_typed] at realView
      simpa only [input, cols, LoadX0Chip.rowView] using realView
    have concreteAssumptions : LoadX0Chip.Assumptions input witness.data :=
      (loadX0ChipDescriptor_assumptions_iff env).mp openInputs.assumptions
    obtain ⟨baseBound, immediateBound, priorBound⟩ := concreteAssumptions
    have guardInput : input.adapter.op_a = 0 := by
      have guardView := guard
      unfold RdGuardFact at guardView
      rw [loadX0ChipDescriptor_rdGuard] at guardView
      change
        ((DecodedInstructionRow.mk loadX0ChipDescriptor physical).toChipRow
          witness.data).view.adapter.op_a = 0 at guardView
      rw [loadX0Chip_viewOf_decoded, circuitRowViewOf_eq_typed] at guardView
      simpa only [input, cols, LoadX0Chip.rowView,
        Extracted.ITypeReader.toAdapterView] using guardView
    have pcBound : input.state.pc[0].val < 2 ^ 16 := by
      have bound := programSpec.2.1
      change
        ((DecodedInstructionRow.mk loadX0ChipDescriptor physical).toChipRow
          witness.data).view.state.pc[0].val < 2 ^ 16 at bound
      rw [loadX0Chip_viewOf_decoded, circuitRowViewOf_eq_typed] at bound
      simpa only [input, cols, LoadX0Chip.rowView] using bound
    let addressInput : AddressOperation.Inputs (ZMod p) :=
      loadX0AddressInput input
    have accessAddress :
        access.address =
          AddressOperation.alignedValue addressInput cols.address_operation := by
      dsimp only [access]
      rw [circuitRamAccessOf_eq_typed]
      simp only [LoadX0Chip.ramAccessView, addressInput, loadX0AddressInput, input, cols]
    have effectiveAddress :=
      effectiveAddress_eq_ramCellBase_add_offset addressInput cols.address_operation
        access accessAddress (spec.1.2.2.2 realInput) baseBound immediateBound
    have stateBytes (i : Fin 8) :
        state.mem.get? ((ramCellOfAccess access).baseAddr.toNat + i.val) =
          some (wordBytes (Word.toBitVec64 access.priorValue))[i] := by
      have raw := ramPriorByte_of_immutableRamShape
        loadX0Chip_immutableRamMemoryInteractionShape
        (DecodedInstructionRow.mk loadX0ChipDescriptor physical) witness.data
        rfl real isRam pulls i
      simpa only [loadX0Chip_immutableRamMemoryInteractionShape,
        loadX0Chip_ramAccessOf_decoded, access, env] using raw
    have memoryAt (k : ℕ) (bound : addressOffset addressInput + k < 8) :
        ∃ byte : BitVec 8,
          state.mem[(AddressOperation.effectiveAddress addressInput).toNat + k]? =
            some byte := by
      let i : Fin 8 := ⟨addressOffset addressInput + k, bound⟩
      refine ⟨(wordBytes (Word.toBitVec64 access.priorValue))[i], ?_⟩
      have get :
          state.mem.get? ((AddressOperation.effectiveAddress addressInput).toNat + k) =
            some (wordBytes (Word.toBitVec64 access.priorValue))[i] := by
        calc
          state.mem.get? ((AddressOperation.effectiveAddress addressInput).toNat + k) =
              state.mem.get? ((ramCellOfAccess access).baseAddr.toNat + i.val) := by
                apply congrArg state.mem.get?
                rw [effectiveAddress]
                simp only [i]
                omega
          _ = some (wordBytes (Word.toBitVec64 access.priorValue))[i] := stateBytes i
      exact get
    refine loadX0AdvanceReady_of_decoded witness.data physical program state ?_
    change LoadX0Chip.advanceReady input cols program state
    apply loadX0AdvanceReady_of_semanticFacts input cols witness.data program state spec
      realInput guardInput pcBound baseBound immediateBound
    intro k bound
    change addressOffset addressInput + k < 8 at bound
    change ∃ byte : BitVec 8,
      state.mem[(AddressOperation.effectiveAddress addressInput).toNat + k]? =
        some byte
    exact memoryAt k bound

/-- LoadX0's residue for the shared immutable-load constructor. -/
theorem loadX0Chip_immutableLoadMemoryGroundingData :
    ImmutableLoadMemoryChipGroundingData
      (loadX0ChipDescriptor (p := p))
      loadX0Chip_immutableRamMemoryInteractionShape :=
  loadX0Chip_immutableLoadMemoryGroundingData_of_eq
    loadX0ChipDescriptor loadX0Chip_immutableRamMemoryInteractionShape rfl (HEq.rfl)

/-- **The LoadX0 bundle instance**, assembled by the shared immutable-load constructor. -/
theorem loadX0Chip_groundingContracts :
    ChipGroundingContracts (loadX0ChipDescriptor (p := p)) :=
  loadX0Chip_immutableLoadMemoryGroundingData.toContracts

end LoadX0Anchor

/-! ## The StoreByte anchor -/

section StoreByteAnchor

variable [Fact (2 ^ 25 < p)]

private theorem storeByteChip_storeMemoryGroundingData_of_eq
    (chip : SupportedChip p) (shape : ImmutableRamMemoryInteractionShape chip)
    (chipEq : chip = storeByteChipDescriptor (p := p))
    (shapeEq : HEq shape
      (storeByteChip_immutableRamMemoryInteractionShape (p := p))) :
    StoreMemoryChipGroundingData chip shape := by
  subst chip
  cases shapeEq
  constructor
  · exact rfl
  · exact storeByteChip_viewClockBounds
  · exact storeByteChip_timestampBounds
  · exact storeByteChip_isRam
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeByteChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeByteChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip real spec
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeByteChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical data
    let input := circuitRowInputOf (p := p) StoreByteChip.circuit env
    let cols := circuitRowOutputOf (p := p) StoreByteChip.circuit env
    have decodedSpec :
        ((storeByteChipDescriptor (p := p)).decodeRow data physical).chipSpec data :=
      spec
    have concreteSpec : StoreByteChip.Spec input cols data := by
      simpa only [input, cols, env] using
        storeByteSpec_of_decoded data physical decodedSpec
    have concreteReal : (StoreByteChip.rowView input cols).is_real = 1 := by
      simpa only [storeByteChip_viewOf_decoded, circuitRowViewOf_eq_typed,
        input, cols, env] using real
    have facts := storeByteChip_storeFacts input cols data concreteReal concreteSpec
    simpa only [storeByteChip_immutableRamMemoryInteractionShape,
      storeByteChip_viewOf_decoded, storeByteChip_ramAccessOf_decoded,
      circuitRowViewOf_eq_typed, circuitRamAccessOf_eq_typed, input, cols, env] using facts
  · intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have pulled := immutableRamPulledWords_isU64_of_shape
      storeByteChip_immutableRamMemoryInteractionShape decoded witness.data hchip real memory
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have byteG :=
      decodedInstructionRow_byteGuarantees witness constraints balanced decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeByteChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have immediate := decode.immediate_words_isU64.2 (by
      simp only [programAccess, ProgramAccess.toRow, storeByteChip_viewOf_decoded,
        circuitRowViewOf_eq_typed, StoreByteChip.rowView,
        Extracted.ITypeReader.toAdapterView])
    have base : Word.isU64
        ((circuitRowViewOf StoreByteChip.circuit
          StoreByteChip.rowView env).adapter.op_b_memory.prev_value) := by
      simpa only [storeByteChip_viewOf_decoded, env] using pulled.2.2
    have immediate' : Word.isU64
        (circuitRowViewOf StoreByteChip.circuit StoreByteChip.rowView env).adapter.op_c := by
      simpa only [programAccess, ProgramAccess.toRow, storeByteChip_viewOf_decoded, env]
        using immediate
    have prior : Word.isU64
        (circuitRowInputOf StoreByteChip.circuit env).memory_access.prev_value := by
      have priorAccess : Word.isU64
          (circuitRamAccessOf StoreByteChip.circuit
            StoreByteChip.ramAccessView env).priorValue := by
        simpa only [storeByteChip_immutableRamMemoryInteractionShape,
          storeByteChip_ramAccessOf_decoded, env] using pulled.1
      rw [circuitRamAccessOf_eq_typed] at priorAccess
      simpa only [StoreByteChip.ramAccessView] using priorAccess
    have realInput :
        (circuitRowInputOf StoreByteChip.circuit env).is_real = 1 := by
      have realView := real
      change
        ((DecodedInstructionRow.mk storeByteChipDescriptor physical).toChipRow
          witness.data).view.is_real = 1 at realView
      rw [storeByteChip_viewOf_decoded, circuitRowViewOf_eq_typed] at realView
      simpa only [StoreByteChip.rowView] using realView
    rw [storeByteChipDescriptor_table] at rowConstraints byteG
    have priorPhysical : Word.isU64
        ((⟨StoreByteChip.circuit (p := p)⟩ :
          Component (ZMod p)).rowInput env).memory_access.prev_value := by
      rw [← circuitRowInputOf_eq_component]
      exact prior
    have realPhysical :
        ((⟨StoreByteChip.circuit (p := p)⟩ :
          Component (ZMod p)).rowInput env).is_real = 1 := by
      rw [← circuitRowInputOf_eq_component]
      exact realInput
    have storeValuePhysical : Word.isU64
        ((⟨StoreByteChip.circuit (p := p)⟩ :
          Component (ZMod p)).rowInput env).store_value :=
      StoreByteChip.storeValue_isU64_of_constraints
        env rowConstraints byteG realPhysical priorPhysical
    have storeValue : Word.isU64
        (circuitRowInputOf StoreByteChip.circuit env).store_value := by
      rw [circuitRowInputOf_eq_component]
      exact storeValuePhysical
    have assumptions :=
      storeByteAssumptions_env env witness.data base immediate' storeValue
    exact (storeByteChipDescriptor_assumptions_iff env).mpr assumptions
  · exact storeByteChipDescriptor_rdGuard
  · intro witness constraints balanced decoded hchip decodedMem real guard program decode
      openInputs state operands sourceA pulls
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeByteChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input := circuitRowInputOf (p := p) StoreByteChip.circuit env
    let cols := circuitRowOutputOf (p := p) StoreByteChip.circuit env
    have concreteAssumptions : StoreByteChip.Assumptions input witness.data :=
      (storeByteChipDescriptor_assumptions_iff env).mp openInputs.assumptions
    obtain ⟨baseBound, immediateBound, _storeBound⟩ := concreteAssumptions
    have pcBound : input.state.pc[0].val < 2 ^ 16 := by
      have bound := programSpec.2.1
      change
        ((DecodedInstructionRow.mk storeByteChipDescriptor physical).toChipRow
          witness.data).view.state.pc[0].val < 2 ^ 16 at bound
      rw [storeByteChip_viewOf_decoded, circuitRowViewOf_eq_typed] at bound
      simpa only [input, cols, StoreByteChip.rowView] using bound
    have sourceAInput :
        ∀ idx : BitVec 5, (idx.toNat : ZMod p) = input.adapter.op_a →
          state.get_reg? idx =
            some (Word.toBitVec64 input.adapter.op_a_memory.prev_value) := by
      have sourceAView := sourceA
      unfold SourceAValueBound at sourceAView
      rw [storeByteChip_viewOf_decoded, circuitRowViewOf_eq_typed] at sourceAView
      simpa only [input, cols, StoreByteChip.rowView,
        Extracted.ITypeReader.toAdapterView] using sourceAView
    refine storeByteAdvanceReady_of_decoded witness.data physical program state ?_
    change StoreByteChip.AdvanceReady input cols program state
    exact ⟨sourceAInput, baseBound, immediateBound, pcBound⟩

/-- StoreByte's residue for the shared genuine-store constructor. -/
theorem storeByteChip_storeMemoryGroundingData :
    StoreMemoryChipGroundingData
      (storeByteChipDescriptor (p := p))
      storeByteChip_immutableRamMemoryInteractionShape :=
  storeByteChip_storeMemoryGroundingData_of_eq
    storeByteChipDescriptor storeByteChip_immutableRamMemoryInteractionShape rfl (HEq.rfl)

/-- **The StoreByte bundle instance**, assembled by the shared store constructor. -/
theorem storeByteChip_groundingContracts :
    ChipGroundingContracts (storeByteChipDescriptor (p := p)) :=
  storeByteChip_storeMemoryGroundingData.toContracts

end StoreByteAnchor

/-! ## The StoreHalf anchor -/

section StoreHalfAnchor

variable [Fact (2 ^ 25 < p)]

private theorem storeHalfChip_storeMemoryGroundingData_of_eq
    (chip : SupportedChip p) (shape : ImmutableRamMemoryInteractionShape chip)
    (chipEq : chip = storeHalfChipDescriptor (p := p))
    (shapeEq : HEq shape
      (storeHalfChip_immutableRamMemoryInteractionShape (p := p))) :
    StoreMemoryChipGroundingData chip shape := by
  subst chip
  cases shapeEq
  constructor
  · exact rfl
  · exact storeHalfChip_viewClockBounds
  · exact storeHalfChip_timestampBounds
  · exact storeHalfChip_isRam
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeHalfChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeHalfChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip real spec
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeHalfChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical data
    let input := circuitRowInputOf (p := p) StoreHalfChip.circuit env
    let cols := circuitRowOutputOf (p := p) StoreHalfChip.circuit env
    have decodedSpec :
        ((storeHalfChipDescriptor (p := p)).decodeRow data physical).chipSpec data :=
      spec
    have concreteSpec : StoreHalfChip.Spec input cols data := by
      simpa only [input, cols, env] using
        storeHalfSpec_of_decoded data physical decodedSpec
    have concreteReal : (StoreHalfChip.rowView input cols).is_real = 1 := by
      simpa only [storeHalfChip_viewOf_decoded, circuitRowViewOf_eq_typed,
        input, cols, env] using real
    have facts := storeHalfChip_storeFacts input cols data concreteReal concreteSpec
    simpa only [storeHalfChip_immutableRamMemoryInteractionShape,
      storeHalfChip_viewOf_decoded, storeHalfChip_ramAccessOf_decoded,
      circuitRowViewOf_eq_typed, circuitRamAccessOf_eq_typed, input, cols, env] using facts
  · intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have pulled := immutableRamPulledWords_isU64_of_shape
      storeHalfChip_immutableRamMemoryInteractionShape decoded witness.data hchip real memory
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeHalfChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have immediate := decode.immediate_words_isU64.2 (by
      simp only [programAccess, ProgramAccess.toRow, storeHalfChip_viewOf_decoded,
        circuitRowViewOf_eq_typed, StoreHalfChip.rowView,
        Extracted.ITypeReader.toAdapterView])
    have base : Word.isU64
        ((circuitRowViewOf StoreHalfChip.circuit
          StoreHalfChip.rowView env).adapter.op_b_memory.prev_value) := by
      simpa only [storeHalfChip_viewOf_decoded, env] using pulled.2.2
    have immediate' : Word.isU64
        (circuitRowViewOf StoreHalfChip.circuit StoreHalfChip.rowView env).adapter.op_c := by
      simpa only [programAccess, ProgramAccess.toRow, storeHalfChip_viewOf_decoded, env]
        using immediate
    have prior : Word.isU64
        (circuitRowInputOf StoreHalfChip.circuit env).memory_access.prev_value := by
      have priorAccess : Word.isU64
          (circuitRamAccessOf StoreHalfChip.circuit
            StoreHalfChip.ramAccessView env).priorValue := by
        simpa only [storeHalfChip_immutableRamMemoryInteractionShape,
          storeHalfChip_ramAccessOf_decoded, env] using pulled.1
      rw [circuitRamAccessOf_eq_typed] at priorAccess
      simpa only [StoreHalfChip.ramAccessView] using priorAccess
    have source : Word.isU64
        (circuitRowInputOf StoreHalfChip.circuit env).adapter.op_a_memory.prev_value := by
      have sourceView : Word.isU64
          ((circuitRowViewOf StoreHalfChip.circuit
            StoreHalfChip.rowView env).adapter.op_a_memory.prev_value) := by
        simpa only [storeHalfChip_viewOf_decoded, env] using pulled.2.1
      rw [circuitRowViewOf_eq_typed] at sourceView
      simpa only [StoreHalfChip.rowView,
        Extracted.ITypeReader.toAdapterView] using sourceView
    rw [storeHalfChipDescriptor_table] at rowConstraints
    have priorPhysical : Word.isU64
        ((⟨StoreHalfChip.circuit (p := p)⟩ :
          Component (ZMod p)).rowInput env).memory_access.prev_value := by
      rw [← circuitRowInputOf_eq_component]
      exact prior
    have sourcePhysical : Word.isU64
        ((⟨StoreHalfChip.circuit (p := p)⟩ :
          Component (ZMod p)).rowInput env).adapter.op_a_memory.prev_value := by
      rw [← circuitRowInputOf_eq_component]
      exact source
    have storeValuePhysical : Word.isU64
        ((⟨StoreHalfChip.circuit (p := p)⟩ :
          Component (ZMod p)).rowInput env).store_value :=
      StoreHalfChip.storeValue_isU64_of_constraints
        env rowConstraints priorPhysical sourcePhysical
    have storeValue : Word.isU64
        (circuitRowInputOf StoreHalfChip.circuit env).store_value := by
      rw [circuitRowInputOf_eq_component]
      exact storeValuePhysical
    have assumptions :=
      storeHalfAssumptions_env env witness.data base immediate' storeValue
    exact (storeHalfChipDescriptor_assumptions_iff env).mpr assumptions
  · exact storeHalfChipDescriptor_rdGuard
  · intro witness constraints balanced decoded hchip decodedMem real guard program decode
      openInputs state operands sourceA pulls
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeHalfChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input := circuitRowInputOf (p := p) StoreHalfChip.circuit env
    let cols := circuitRowOutputOf (p := p) StoreHalfChip.circuit env
    have concreteAssumptions : StoreHalfChip.Assumptions input witness.data :=
      (storeHalfChipDescriptor_assumptions_iff env).mp openInputs.assumptions
    obtain ⟨baseBound, immediateBound, _storeBound⟩ := concreteAssumptions
    have pcBound : input.state.pc[0].val < 2 ^ 16 := by
      have bound := programSpec.2.1
      change
        ((DecodedInstructionRow.mk storeHalfChipDescriptor physical).toChipRow
          witness.data).view.state.pc[0].val < 2 ^ 16 at bound
      rw [storeHalfChip_viewOf_decoded, circuitRowViewOf_eq_typed] at bound
      simpa only [input, cols, StoreHalfChip.rowView] using bound
    have sourceAInput :
        ∀ idx : BitVec 5, (idx.toNat : ZMod p) = input.adapter.op_a →
          state.get_reg? idx =
            some (Word.toBitVec64 input.adapter.op_a_memory.prev_value) := by
      have sourceAView := sourceA
      unfold SourceAValueBound at sourceAView
      rw [storeHalfChip_viewOf_decoded, circuitRowViewOf_eq_typed] at sourceAView
      simpa only [input, cols, StoreHalfChip.rowView,
        Extracted.ITypeReader.toAdapterView] using sourceAView
    refine storeHalfAdvanceReady_of_decoded witness.data physical program state ?_
    change StoreHalfChip.AdvanceReady input cols program state
    exact ⟨sourceAInput, baseBound, immediateBound, pcBound⟩

/-- StoreHalf's residue for the shared genuine-store constructor. -/
theorem storeHalfChip_storeMemoryGroundingData :
    StoreMemoryChipGroundingData
      (storeHalfChipDescriptor (p := p))
      storeHalfChip_immutableRamMemoryInteractionShape :=
  storeHalfChip_storeMemoryGroundingData_of_eq
    storeHalfChipDescriptor storeHalfChip_immutableRamMemoryInteractionShape rfl (HEq.rfl)

/-- **The StoreHalf bundle instance**, assembled by the shared store constructor. -/
theorem storeHalfChip_groundingContracts :
    ChipGroundingContracts (storeHalfChipDescriptor (p := p)) :=
  storeHalfChip_storeMemoryGroundingData.toContracts

end StoreHalfAnchor

/-! ## The StoreWord anchor -/

section StoreWordAnchor

variable [Fact (2 ^ 25 < p)]

private theorem storeWordChip_storeMemoryGroundingData_of_eq
    (chip : SupportedChip p) (shape : ImmutableRamMemoryInteractionShape chip)
    (chipEq : chip = storeWordChipDescriptor (p := p))
    (shapeEq : HEq shape
      (storeWordChip_immutableRamMemoryInteractionShape (p := p))) :
    StoreMemoryChipGroundingData chip shape := by
  subst chip
  cases shapeEq
  constructor
  · exact rfl
  · exact storeWordChip_viewClockBounds
  · exact storeWordChip_timestampBounds
  · exact storeWordChip_isRam
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeWordChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeWordChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip real spec
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeWordChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical data
    let input := circuitRowInputOf (p := p) StoreWordChip.circuit env
    let cols := circuitRowOutputOf (p := p) StoreWordChip.circuit env
    have decodedSpec :
        ((storeWordChipDescriptor (p := p)).decodeRow data physical).chipSpec data :=
      spec
    have concreteSpec : StoreWordChip.Spec input cols data := by
      simpa only [input, cols, env] using
        storeWordSpec_of_decoded data physical decodedSpec
    have concreteReal : (StoreWordChip.rowView input cols).is_real = 1 := by
      simpa only [storeWordChip_viewOf_decoded, circuitRowViewOf_eq_typed,
        input, cols, env] using real
    have facts := storeWordChip_storeFacts input cols data concreteReal concreteSpec
    simpa only [storeWordChip_immutableRamMemoryInteractionShape,
      storeWordChip_viewOf_decoded, storeWordChip_ramAccessOf_decoded,
      circuitRowViewOf_eq_typed, circuitRamAccessOf_eq_typed, input, cols, env] using facts
  · intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have pulled := immutableRamPulledWords_isU64_of_shape
      storeWordChip_immutableRamMemoryInteractionShape decoded witness.data hchip real memory
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeWordChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have immediate := decode.immediate_words_isU64.2 (by
      simp only [programAccess, ProgramAccess.toRow, storeWordChip_viewOf_decoded,
        circuitRowViewOf_eq_typed, StoreWordChip.rowView,
        Extracted.ITypeReader.toAdapterView])
    have base : Word.isU64
        ((circuitRowViewOf StoreWordChip.circuit
          StoreWordChip.rowView env).adapter.op_b_memory.prev_value) := by
      simpa only [storeWordChip_viewOf_decoded, env] using pulled.2.2
    have immediate' : Word.isU64
        (circuitRowViewOf StoreWordChip.circuit StoreWordChip.rowView env).adapter.op_c := by
      simpa only [programAccess, ProgramAccess.toRow, storeWordChip_viewOf_decoded, env]
        using immediate
    have prior : Word.isU64
        (circuitRowInputOf StoreWordChip.circuit env).memory_access.prev_value := by
      have priorAccess : Word.isU64
          (circuitRamAccessOf StoreWordChip.circuit
            StoreWordChip.ramAccessView env).priorValue := by
        simpa only [storeWordChip_immutableRamMemoryInteractionShape,
          storeWordChip_ramAccessOf_decoded, env] using pulled.1
      rw [circuitRamAccessOf_eq_typed] at priorAccess
      simpa only [StoreWordChip.ramAccessView] using priorAccess
    have source : Word.isU64
        (circuitRowInputOf StoreWordChip.circuit env).adapter.op_a_memory.prev_value := by
      have sourceView : Word.isU64
          ((circuitRowViewOf StoreWordChip.circuit
            StoreWordChip.rowView env).adapter.op_a_memory.prev_value) := by
        simpa only [storeWordChip_viewOf_decoded, env] using pulled.2.1
      rw [circuitRowViewOf_eq_typed] at sourceView
      simpa only [StoreWordChip.rowView,
        Extracted.ITypeReader.toAdapterView] using sourceView
    rw [storeWordChipDescriptor_table] at rowConstraints
    have priorPhysical : Word.isU64
        ((⟨StoreWordChip.circuit (p := p)⟩ :
          Component (ZMod p)).rowInput env).memory_access.prev_value := by
      rw [← circuitRowInputOf_eq_component]
      exact prior
    have sourcePhysical : Word.isU64
        ((⟨StoreWordChip.circuit (p := p)⟩ :
          Component (ZMod p)).rowInput env).adapter.op_a_memory.prev_value := by
      rw [← circuitRowInputOf_eq_component]
      exact source
    have storeValuePhysical : Word.isU64
        ((⟨StoreWordChip.circuit (p := p)⟩ :
          Component (ZMod p)).rowInput env).store_value :=
      StoreWordChip.storeValue_isU64_of_constraints
        env rowConstraints priorPhysical sourcePhysical
    have storeValue : Word.isU64
        (circuitRowInputOf StoreWordChip.circuit env).store_value := by
      rw [circuitRowInputOf_eq_component]
      exact storeValuePhysical
    have assumptions :=
      storeWordAssumptions_env env witness.data base immediate' storeValue
    exact (storeWordChipDescriptor_assumptions_iff env).mpr assumptions
  · exact storeWordChipDescriptor_rdGuard
  · intro witness constraints balanced decoded hchip decodedMem real guard program decode
      openInputs state operands sourceA pulls
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeWordChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input := circuitRowInputOf (p := p) StoreWordChip.circuit env
    let cols := circuitRowOutputOf (p := p) StoreWordChip.circuit env
    have concreteAssumptions : StoreWordChip.Assumptions input witness.data :=
      (storeWordChipDescriptor_assumptions_iff env).mp openInputs.assumptions
    obtain ⟨baseBound, immediateBound, _storeBound⟩ := concreteAssumptions
    have pcBound : input.state.pc[0].val < 2 ^ 16 := by
      have bound := programSpec.2.1
      change
        ((DecodedInstructionRow.mk storeWordChipDescriptor physical).toChipRow
          witness.data).view.state.pc[0].val < 2 ^ 16 at bound
      rw [storeWordChip_viewOf_decoded, circuitRowViewOf_eq_typed] at bound
      simpa only [input, cols, StoreWordChip.rowView] using bound
    have sourceAInput :
        ∀ idx : BitVec 5, (idx.toNat : ZMod p) = input.adapter.op_a →
          state.get_reg? idx =
            some (Word.toBitVec64 input.adapter.op_a_memory.prev_value) := by
      have sourceAView := sourceA
      unfold SourceAValueBound at sourceAView
      rw [storeWordChip_viewOf_decoded, circuitRowViewOf_eq_typed] at sourceAView
      simpa only [input, cols, StoreWordChip.rowView,
        Extracted.ITypeReader.toAdapterView] using sourceAView
    refine storeWordAdvanceReady_of_decoded witness.data physical program state ?_
    change StoreWordChip.AdvanceReady input cols program state
    exact ⟨sourceAInput, baseBound, immediateBound, pcBound⟩

/-- StoreWord's residue for the shared genuine-store constructor. -/
theorem storeWordChip_storeMemoryGroundingData :
    StoreMemoryChipGroundingData
      (storeWordChipDescriptor (p := p))
      storeWordChip_immutableRamMemoryInteractionShape :=
  storeWordChip_storeMemoryGroundingData_of_eq
    storeWordChipDescriptor storeWordChip_immutableRamMemoryInteractionShape rfl (HEq.rfl)

/-- **The StoreWord bundle instance**, assembled by the shared store constructor. -/
theorem storeWordChip_groundingContracts :
    ChipGroundingContracts (storeWordChipDescriptor (p := p)) :=
  storeWordChip_storeMemoryGroundingData.toContracts

end StoreWordAnchor

/-! ## The StoreDouble anchor -/

section StoreDoubleAnchor

variable [Fact (2 ^ 25 < p)]

private theorem storeDoubleChip_storeMemoryGroundingData_of_eq
    (chip : SupportedChip p) (shape : ImmutableRamMemoryInteractionShape chip)
    (chipEq : chip = storeDoubleChipDescriptor (p := p))
    (shapeEq : HEq shape
      (storeDoubleChip_immutableRamMemoryInteractionShape (p := p))) :
    StoreMemoryChipGroundingData chip shape := by
  subst chip
  cases shapeEq
  constructor
  · exact rfl
  · exact storeDoubleChip_viewClockBounds
  · exact storeDoubleChip_timestampBounds
  · exact storeDoubleChip_isRam
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeDoubleChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeDoubleChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  · intro decoded data hchip real spec
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeDoubleChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical data
    let input := circuitRowInputOf (p := p) StoreDoubleChip.circuit env
    let cols := circuitRowOutputOf (p := p) StoreDoubleChip.circuit env
    have decodedSpec :
        ((storeDoubleChipDescriptor (p := p)).decodeRow data physical).chipSpec data :=
      spec
    have concreteSpec : StoreDoubleChip.Spec input cols data := by
      simpa only [input, cols, env] using
        storeDoubleSpec_of_decoded data physical decodedSpec
    have concreteReal : (StoreDoubleChip.rowView input cols).is_real = 1 := by
      simpa only [storeDoubleChip_viewOf_decoded, circuitRowViewOf_eq_typed,
        input, cols, env] using real
    have facts := storeDoubleChip_storeFacts input cols data concreteReal concreteSpec
    simpa only [storeDoubleChip_immutableRamMemoryInteractionShape,
      storeDoubleChip_viewOf_decoded, storeDoubleChip_ramAccessOf_decoded,
      circuitRowViewOf_eq_typed, circuitRamAccessOf_eq_typed, input, cols, env] using facts
  · intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have pulled := immutableRamPulledWords_isU64_of_shape
      storeDoubleChip_immutableRamMemoryInteractionShape decoded witness.data hchip real memory
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeDoubleChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have immediate := decode.immediate_words_isU64.2 (by
      simp only [programAccess, ProgramAccess.toRow, storeDoubleChip_viewOf_decoded,
        circuitRowViewOf_eq_typed, StoreDoubleChip.rowView,
        Extracted.ITypeReader.toAdapterView])
    have base : Word.isU64
        ((circuitRowViewOf StoreDoubleChip.circuit
          StoreDoubleChip.rowView env).adapter.op_b_memory.prev_value) := by
      simpa only [storeDoubleChip_viewOf_decoded, env] using pulled.2.2
    have immediate' : Word.isU64
        (circuitRowViewOf StoreDoubleChip.circuit StoreDoubleChip.rowView env).adapter.op_c := by
      simpa only [programAccess, ProgramAccess.toRow, storeDoubleChip_viewOf_decoded, env]
        using immediate
    have assumptions := storeDoubleAssumptions_env env witness.data base immediate'
    exact (storeDoubleChipDescriptor_assumptions_iff env).mpr assumptions
  · exact storeDoubleChipDescriptor_rdGuard
  · intro witness constraints balanced decoded hchip decodedMem real guard program decode
      openInputs state operands sourceA pulls
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = storeDoubleChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input := circuitRowInputOf (p := p) StoreDoubleChip.circuit env
    let cols := circuitRowOutputOf (p := p) StoreDoubleChip.circuit env
    have concreteAssumptions : StoreDoubleChip.Assumptions input witness.data :=
      (storeDoubleChipDescriptor_assumptions_iff env).mp openInputs.assumptions
    obtain ⟨baseBound, immediateBound⟩ := concreteAssumptions
    have pcBound : input.state.pc[0].val < 2 ^ 16 := by
      have bound := programSpec.2.1
      change
        ((DecodedInstructionRow.mk storeDoubleChipDescriptor physical).toChipRow
          witness.data).view.state.pc[0].val < 2 ^ 16 at bound
      rw [storeDoubleChip_viewOf_decoded, circuitRowViewOf_eq_typed] at bound
      simpa only [input, cols, StoreDoubleChip.rowView] using bound
    have sourceAInput :
        ∀ idx : BitVec 5, (idx.toNat : ZMod p) = input.adapter.op_a →
          state.get_reg? idx =
            some (Word.toBitVec64 input.adapter.op_a_memory.prev_value) := by
      have sourceAView := sourceA
      unfold SourceAValueBound at sourceAView
      rw [storeDoubleChip_viewOf_decoded, circuitRowViewOf_eq_typed] at sourceAView
      simpa only [input, cols, StoreDoubleChip.rowView,
        Extracted.ITypeReader.toAdapterView] using sourceAView
    refine storeDoubleAdvanceReady_of_decoded witness.data physical program state ?_
    change StoreDoubleChip.AdvanceReady input cols program state
    exact ⟨sourceAInput, baseBound, immediateBound, pcBound⟩

/-- StoreDouble's residue for the shared genuine-store constructor. -/
theorem storeDoubleChip_storeMemoryGroundingData :
    StoreMemoryChipGroundingData
      (storeDoubleChipDescriptor (p := p))
      storeDoubleChip_immutableRamMemoryInteractionShape :=
  storeDoubleChip_storeMemoryGroundingData_of_eq
    storeDoubleChipDescriptor storeDoubleChip_immutableRamMemoryInteractionShape rfl (HEq.rfl)

/-- **The StoreDouble bundle instance**, assembled by the shared store constructor. -/
theorem storeDoubleChip_groundingContracts :
    ChipGroundingContracts (storeDoubleChipDescriptor (p := p)) :=
  storeDoubleChip_storeMemoryGroundingData.toContracts

end StoreDoubleAnchor

/-! ## The Addi anchor -/

section AddiAnchor

variable [Fact (2 ^ 25 < p)]

/-- Addi's chip-specific residue for the common I-type grounding constructor. -/
theorem addiChip_itypeGroundingData :
    ITypeChipGroundingData (addiChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := addiChip_itypeMemoryInteractionShape
  viewClockBounds := addiChip_viewClockBounds
  timestampBounds := addiChip_activeTimestampBounds
  commit_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addiChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_b_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addiChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have immediate := addiChip_immediate_isU64 decoded witness.data hchip decode
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addiChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    change Word.isU64
      ((⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter.op_c_imm
    have inputEq : Eval.eval env (varFromOffset AddiChip.Inputs 0) =
        (⟨AddiChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
      eval_varFromOffset_valueFromOffset AddiChip.Inputs 0 env
    rw [← inputEq]
    change Word.isU64
      (((addiChipDescriptor (p := p)).decodeRow witness.data physical).view.adapter.op_c)
      at immediate
    rw [addiViewOf_decodeRow, addiViewOf_adapter] at immediate
    simpa only [Extracted.ITypeReader.toAdapterView] using immediate
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addiChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input : Var AddiChip.Inputs (ZMod p) := varFromOffset AddiChip.Inputs 0
    let offset := size AddiChip.Inputs
    have mainConstraints : Operations.ConstraintsHold env
        ((AddiChip.main input).operations offset) :=
      (Component.constraintsHold_iff env).mp rowConstraints
    have inputFlag := AddiChip.eval_inputOpA0_eq_zero_of_mainConstraints
      input offset env mainConstraints
    have viewFlag : (addiViewOf env).adapter.op_a_0 = 0 := by
      rw [addiViewOf_opA0]
      exact inputFlag
    have decodedFlag :
        ((addiChipDescriptor (p := p)).decodeRow witness.data physical).view.adapter.op_a_0 = 0 := by
      rw [addiViewOf_decodeRow]
      exact viewFlag
    exact decode.op_a_ne_zero_of_op_a_0_eq_zero decodedFlag
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program decode
      _openInputs state _operands _sourceA _pulls
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addiChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    exact ⟨AddiChip.inputOutputAdapter env, AddiChip.inputOutputState env, guard⟩

/-- **The Addi bundle instance**, assembled by the shared I-type constructor. -/
theorem addiChip_groundingContracts :
    ChipGroundingContracts (addiChipDescriptor (p := p)) :=
  addiChip_itypeGroundingData.toContracts

end AddiAnchor

/-! ## The Addw anchor -/

section AddwAnchor

variable [Fact (2 ^ 25 < p)]

/-- Addw's residue for the shared immediate-capable ALU constructor. -/
theorem addwChip_aluTypeGroundingData :
    ALUTypeChipGroundingData (addwChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := addwChip_aluTypeMemoryInteractionShape.constrained
  viewClockBounds := addwChip_viewClockBounds
  timestampBounds := addwChip_activeTimestampBounds
  commit_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addwChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_b_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addwChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have operands := aluTypeOperandWords_isU64_of_shape
      addwChip_aluTypeMemoryInteractionShape.constrained decoded witness.data hchip
        rowConstraints real memory
    have opCU64 : Word.isU64
        (decoded.toChipRow witness.data).view.adapter.op_c_memory.prev_value := by
      rcases addwChip_immBinary decoded witness.data decode with register | immediate
      · exact operands.2 register
      · have binding := addwChip_opCBinding_of_constraints decoded witness.data hchip
          rowConstraints immediate
        rw [binding]
        exact addwChip_immediate_isU64 decoded witness.data decode immediate
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addwChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    change Word.isU64
      ((⟨AddwChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter.op_c_memory.prev_value
    rw [AddwChip.inputOutputAdapter env]
    simpa only [DecodedInstructionRow.toChipRow, addwViewOf_decodeRow, addwViewOf,
      AddwChip.rowView, Extracted.ALUTypeReader.toAdapterView, env] using opCU64
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addwChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input : Var AddwChip.Inputs (ZMod p) := varFromOffset AddwChip.Inputs 0
    let offset := size AddwChip.Inputs
    have mainConstraints : Operations.ConstraintsHold env
        ((AddwChip.main input).operations offset) :=
      (Component.constraintsHold_iff env).mp rowConstraints
    have inputFlag := AddwChip.eval_inputOpA0_eq_zero_of_mainConstraints
      input offset env mainConstraints
    have viewFlag : (addwViewOf env).adapter.op_a_0 = 0 := by
      rw [addwViewOf_opA0]
      exact inputFlag
    have decodedFlag :
        ((addwChipDescriptor (p := p)).decodeRow witness.data physical).view.adapter.op_a_0 = 0 := by
      rw [addwViewOf_decodeRow]
      exact viewFlag
    exact decode.op_a_ne_zero_of_op_a_0_eq_zero decodedFlag
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program decode
      _openInputs state _operands _sourceA _pulls
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    have immBinary := addwChip_immBinary decoded witness.data decode
    have binding := fun immediate => addwChip_opCBinding_of_constraints decoded witness.data hchip
      rowConstraints immediate
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addwChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    exact ⟨AddwChip.inputOutputAdapter env, programSpec.2.1, immBinary, binding, guard⟩

/-- **The Addw bundle instance**, assembled by the shared ALU-type constructor. -/
theorem addwChip_groundingContracts :
    ChipGroundingContracts (addwChipDescriptor (p := p)) :=
  addwChip_aluTypeGroundingData.toContracts

end AddwAnchor

/-! ## The Bitwise anchor -/

section BitwiseAnchor

variable [Fact (2 ^ 25 < p)]

/-- Bitwise's residue for the shared immediate-capable ALU constructor. -/
theorem bitwiseChip_aluTypeGroundingData :
    ALUTypeChipGroundingData (bitwiseChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := bitwiseChip_aluTypeMemoryInteractionShape.constrained
  viewClockBounds := bitwiseChip_viewClockBounds
  timestampBounds := bitwiseChip_activeTimestampBounds
  commit_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = bitwiseChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_b_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = bitwiseChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have operands := aluTypeOperandWords_isU64_of_shape
      bitwiseChip_aluTypeMemoryInteractionShape.constrained decoded witness.data hchip
        rowConstraints real memory
    have opCU64 : Word.isU64
        (decoded.toChipRow witness.data).view.adapter.op_c_memory.prev_value := by
      rcases bitwiseChip_immBinary decoded witness.data decode with register | immediate
      · exact operands.2 register
      · have binding := bitwiseChip_opCBinding_of_constraints decoded witness.data hchip
          rowConstraints immediate
        rw [binding]
        exact bitwiseChip_immediate_isU64 decoded witness.data decode immediate
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = bitwiseChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    change Word.isU64
        ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_b_memory.prev_value ∧
      Word.isU64
        ((⟨BitwiseChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_c_memory.prev_value
    rw [BitwiseChip.inputOutputAdapter env]
    simpa only [BitwiseChip.Inputs.op_b_val, BitwiseChip.Inputs.op_c_val,
      DecodedInstructionRow.toChipRow, bitwiseViewOf_decodeRow, bitwiseViewOf,
      BitwiseChip.physicalView, BitwiseChip.rowView, Extracted.ALUTypeReader.toAdapterView, env]
      using ⟨operands.1, opCU64⟩
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = bitwiseChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have flagZero := BitwiseChip.rowViewOpA0_eq_zero_of_constraints env rowConstraints
    exact decode.op_a_ne_zero_of_op_a_0_eq_zero flagZero
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program decode
      _openInputs state _operands _sourceA _pulls
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    have immBinary := bitwiseChip_immBinary decoded witness.data decode
    have binding := fun immediate => bitwiseChip_opCBinding_of_constraints decoded witness.data hchip
      rowConstraints immediate
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = bitwiseChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have active := BitwiseChip.rowViewSelectorActive_of_constraints env rowConstraints real
    exact ⟨BitwiseChip.inputOutputAdapter env, programSpec.2.1, immBinary, active, guard, binding⟩

/-- **The Bitwise bundle instance**, assembled by the shared ALU-type constructor. -/
theorem bitwiseChip_groundingContracts :
    ChipGroundingContracts (bitwiseChipDescriptor (p := p)) :=
  bitwiseChip_aluTypeGroundingData.toContracts

end BitwiseAnchor

/-! ## The Lt anchor -/

section LtAnchor

variable [Fact (2 ^ 25 < p)]

/-- Lt's residue for the shared immediate-capable ALU constructor. -/
theorem ltChip_aluTypeGroundingData :
    ALUTypeChipGroundingData (ltChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := ltChip_aluTypeMemoryInteractionShape.constrained
  viewClockBounds := ltChip_viewClockBounds
  timestampBounds := ltChip_activeTimestampBounds
  commit_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = ltChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_b_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = ltChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have operands := aluTypeOperandWords_isU64_of_shape
      ltChip_aluTypeMemoryInteractionShape.constrained decoded witness.data hchip
        rowConstraints real memory
    have opCU64 : Word.isU64
        (decoded.toChipRow witness.data).view.adapter.op_c_memory.prev_value := by
      rcases ltChip_immBinary decoded witness.data decode with register | immediate
      · exact operands.2 register
      · have binding := ltChip_opCBinding_of_constraints decoded witness.data hchip
          rowConstraints immediate
        rw [binding]
        exact ltChip_immediate_isU64 decoded witness.data decode immediate
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = ltChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    change Word.isU64
        ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_b_memory.prev_value ∧
      Word.isU64 ((⟨LtChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
        env).adapter.op_c_memory.prev_value
    rw [LtChip.inputOutputAdapter env]
    simpa only [LtChip.Inputs.op_b_val, LtChip.Inputs.op_c_val,
      DecodedInstructionRow.toChipRow, ltViewOf_decodeRow, ltViewOf, LtChip.physicalView,
      LtChip.rowView, Extracted.ALUTypeReader.toAdapterView, env] using ⟨operands.1, opCU64⟩
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = ltChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have flagZero := LtChip.rowViewOpA0_eq_zero_of_constraints env rowConstraints
    exact decode.op_a_ne_zero_of_op_a_0_eq_zero flagZero
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program decode
      _openInputs state _operands _sourceA _pulls
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    have immBinary := ltChip_immBinary decoded witness.data decode
    have binding := fun immediate => ltChip_opCBinding_of_constraints decoded witness.data hchip
      rowConstraints immediate
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = ltChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have active := LtChip.rowViewSelectorActive_of_constraints env rowConstraints real
    exact ⟨LtChip.inputOutputAdapter env, programSpec.2.1, immBinary, active, guard, binding⟩

/-- **The Lt bundle instance**, assembled by the shared ALU-type constructor. -/
theorem ltChip_groundingContracts :
    ChipGroundingContracts (ltChipDescriptor (p := p)) :=
  ltChip_aluTypeGroundingData.toContracts

end LtAnchor

/-! ## The ShiftLeft anchor -/

section ShiftLeftAnchor

variable [Fact (2 ^ 25 < p)]

/-- ShiftLeft's residue for the shared immediate-capable ALU constructor. -/
theorem shiftLeftChip_aluTypeGroundingData :
    ALUTypeChipGroundingData (shiftLeftChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := shiftLeftChip_aluTypeMemoryInteractionShape
  viewClockBounds := shiftLeftChip_viewClockBounds
  timestampBounds := shiftLeftChip_activeTimestampBounds
  commit_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = shiftLeftChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_b_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = shiftLeftChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have operands := aluTypeOperandWords_isU64_of_shape
      shiftLeftChip_aluTypeMemoryInteractionShape decoded witness.data hchip
        rowConstraints real memory
    have opCU64 : Word.isU64
        (decoded.toChipRow witness.data).view.adapter.op_c_memory.prev_value := by
      rcases shiftLeftChip_immBinary decoded witness.data decode with register | immediate
      · exact operands.2 register
      · have binding := shiftLeftChip_opCBinding_of_constraints decoded witness.data hchip
          rowConstraints immediate
        rw [binding]
        exact shiftLeftChip_immediate_isU64 decoded witness.data decode immediate
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = shiftLeftChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    change Word.isU64
        ((⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_b_memory.prev_value ∧
      Word.isU64
        ((⟨ShiftLeftChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_c_memory.prev_value
    rw [ShiftLeftChip.inputOutputAdapter env]
    simpa only [ShiftLeftChip.Inputs.op_b_val, ShiftLeftChip.Inputs.op_c_val,
      DecodedInstructionRow.toChipRow, shiftLeftViewOf_decodeRow, shiftLeftViewOf,
      ShiftLeftChip.physicalView, ShiftLeftChip.rowView,
      Extracted.ALUTypeReader.toAdapterView, env] using ⟨operands.1, opCU64⟩
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = shiftLeftChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have flagZero := ShiftLeftChip.rowViewOpA0_eq_zero_of_constraints env rowConstraints
    exact decode.op_a_ne_zero_of_op_a_0_eq_zero flagZero
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program decode
      _openInputs state _operands _sourceA _pulls
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    have immBinary := shiftLeftChip_immBinary decoded witness.data decode
    have binding := fun immediate =>
      shiftLeftChip_opCBinding_of_constraints decoded witness.data hchip
        rowConstraints immediate
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = shiftLeftChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have active := ShiftLeftChip.rowViewSelectorActive_of_constraints env rowConstraints real
    exact
      ⟨programSpec.2.1, ShiftLeftChip.inputOutputAdapter env, guard,
        immBinary, binding, active⟩

/-- **The ShiftLeft bundle instance**, assembled by the shared ALU-type constructor. -/
theorem shiftLeftChip_groundingContracts :
    ChipGroundingContracts (shiftLeftChipDescriptor (p := p)) :=
  shiftLeftChip_aluTypeGroundingData.toContracts

end ShiftLeftAnchor

/-! ## The ShiftRight anchor -/

section ShiftRightAnchor

variable [Fact (2 ^ 25 < p)]

/-- ShiftRight's residue for the shared immediate-capable ALU constructor. -/
theorem shiftRightChip_aluTypeGroundingData :
    ALUTypeChipGroundingData (shiftRightChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := shiftRightChip_aluTypeMemoryInteractionShape
  viewClockBounds := shiftRightChip_viewClockBounds
  timestampBounds := shiftRightChip_activeTimestampBounds
  commit_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = shiftRightChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_b_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = shiftRightChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have operands := aluTypeOperandWords_isU64_of_shape
      shiftRightChip_aluTypeMemoryInteractionShape decoded witness.data hchip
        rowConstraints real memory
    have opCU64 : Word.isU64
        (decoded.toChipRow witness.data).view.adapter.op_c_memory.prev_value := by
      rcases shiftRightChip_immBinary decoded witness.data decode with register | immediate
      · exact operands.2 register
      · have binding := shiftRightChip_opCBinding_of_constraints decoded witness.data hchip
          rowConstraints immediate
        rw [binding]
        exact shiftRightChip_immediate_isU64 decoded witness.data decode immediate
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = shiftRightChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    change Word.isU64
        ((⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_b_memory.prev_value ∧
      Word.isU64
        ((⟨ShiftRightChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_c_memory.prev_value
    rw [ShiftRightChip.inputOutputAdapter env]
    simpa only [DecodedInstructionRow.toChipRow, shiftRightViewOf_decodeRow, shiftRightViewOf,
      ShiftRightChip.physicalView, ShiftRightChip.rowView,
      Extracted.ALUTypeReader.toAdapterView, env] using ⟨operands.1, opCU64⟩
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = shiftRightChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have flagZero := ShiftRightChip.rowViewOpA0_eq_zero_of_constraints env rowConstraints
    exact decode.op_a_ne_zero_of_op_a_0_eq_zero flagZero
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program decode
      _openInputs state _operands _sourceA _pulls
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    have immBinary := shiftRightChip_immBinary decoded witness.data decode
    have binding := fun immediate =>
      shiftRightChip_opCBinding_of_constraints decoded witness.data hchip
        rowConstraints immediate
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = shiftRightChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have active := ShiftRightChip.rowViewSelectorActive_of_constraints env rowConstraints real
    exact
      ⟨programSpec.2.1, ShiftRightChip.inputOutputAdapter env, guard,
        immBinary, binding, active⟩

/-- **The ShiftRight bundle instance**, assembled by the shared ALU-type constructor. -/
theorem shiftRightChip_groundingContracts :
    ChipGroundingContracts (shiftRightChipDescriptor (p := p)) :=
  shiftRightChip_aluTypeGroundingData.toContracts

end ShiftRightAnchor

/-! ## The AluX0 anchor -/

section AluX0Anchor

variable [Fact (2 ^ 25 < p)]

/-- AluX0's residue for the immutable immediate-capable ALU constructor. -/
theorem aluX0Chip_immutableALUTypeGroundingData :
    ImmutableALUTypeChipGroundingData (aluX0ChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := aluX0Chip_immutableALUTypeMemoryInteractionShape
  viewClockBounds := aluX0Chip_viewClockBounds
  timestampBounds := aluX0Chip_activeTimestampBounds
  commit_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = aluX0ChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real program decode memory
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = aluX0ChipDescriptor (p := p) := hchip
    subst hchip'
    trivial
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = aluX0ChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input : Var AluX0Chip.Inputs (ZMod p) :=
      varFromOffset AluX0Chip.Inputs 0
    let offset := size AluX0Chip.Inputs
    have mainConstraints : ((AluX0Chip.main input).operations offset).ConstraintsHold env :=
      (Component.constraintsHold_iff env).mp rowConstraints
    have inputReal : (Eval.eval env input).is_real = 1 := by
      have realView := real
      change ((aluX0ChipDescriptor (p := p)).decodeRow witness.data physical).view.is_real = 1
        at realView
      rw [aluX0ViewOf_decodeRow, aluX0ViewOf_isReal] at realView
      exact realView
    have inputFlag := AluX0Chip.opA0_eq_one_of_constraints
      input offset env mainConstraints inputReal
    have viewFlag :
        (aluX0ViewOf env).adapter.op_a_0 = 1 := by
      rw [aluX0ViewOf_adapter]
      exact inputFlag
    apply decode.op_a_eq_zero_of_op_a_0_eq_one
    simpa only [programAccess, ProgramAccess.toRow,
      DecodedInstructionRow.toChipRow, aluX0ViewOf_decodeRow, env] using viewFlag
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program decode
      openInputs state _operands _sourceA _pulls
    have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
      decodedMem real
    have chipSpec := decoded.chipSpec_of_openSoundnessInputs witness constraints balanced
      decodedMem openInputs
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = aluX0ChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have decodedSpec :
        ((aluX0ChipDescriptor (p := p)).decodeRow witness.data physical).chipSpec
          witness.data := by
      change
        ((aluX0ChipDescriptor (p := p)).decodeRow witness.data physical).chipSpec
          witness.data at chipSpec
      exact chipSpec
    have circuitSpec :=
      ((aluX0ChipDescriptor (p := p)).decodeRow_chipSpec_iff witness.data physical).mp
        decodedSpec
    have concreteSpec : AluX0Chip.Spec
        ((aluX0ChipDescriptor (p := p)).decodeRow witness.data physical).inputs
        ((aluX0ChipDescriptor (p := p)).decodeRow witness.data physical).cols
        witness.data := by
      exact circuitSpec
    have inputReal :
        (Eval.eval env
          (varFromOffset (F := ZMod p) AluX0Chip.Inputs 0)).is_real = 1 := by
      have realView := real
      change ((aluX0ChipDescriptor (p := p)).decodeRow witness.data physical).view.is_real = 1
        at realView
      rw [aluX0ViewOf_decodeRow, aluX0ViewOf_isReal] at realView
      exact realView
    have decodedInputReal :
        ((aluX0ChipDescriptor (p := p)).decodeRow witness.data physical).inputs.is_real = 1 := by
      simpa only [SupportedChip.decodeRow, aluX0ChipDescriptor_table, Component.rowInput,
        ← eval_varFromOffset_valueFromOffset, env] using inputReal
    have inputOpcodeBound :=
      concreteSpec.2.2.2.2 decodedInputReal
    have viewOpcodeBound :
        ((aluX0ChipDescriptor (p := p)).decodeRow witness.data physical).view.opcode.val < 29 := by
      rw [aluX0ViewOf_decodeRow, aluX0ViewOf_opcode]
      simpa only [SupportedChip.decodeRow, aluX0ChipDescriptor_table, Component.rowInput,
        ← eval_varFromOffset_valueFromOffset, env] using inputOpcodeBound
    exact ⟨guard, programSpec.2.1, viewOpcodeBound⟩

/-- **The AluX0 bundle instance**, assembled by the immutable ALU constructor. -/
theorem aluX0Chip_groundingContracts :
    ChipGroundingContracts (aluX0ChipDescriptor (p := p)) :=
  aluX0Chip_immutableALUTypeGroundingData.toContracts

end AluX0Anchor

/-! ## The Add anchor -/

section AddAnchor

variable [Fact (2 ^ 25 < p)]

/-- Add's chip-specific residue for the common R-type grounding constructor. -/
theorem addChip_rtypeGroundingData :
    RTypeChipGroundingData (addChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := addChip_rtypeMemoryInteractionShape
  viewClockBounds := addChip_viewClockBounds
  timestampBounds := addChip_activeTimestampBounds
  commit_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_b_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_c_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real program decode memory
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addChipDescriptor (p := p) := hchip
    subst hchip'
    exact trivial
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have flagZero := AddChip.rowViewOpA0_eq_zero_of_constraints env rowConstraints
    exact decode.op_a_ne_zero_of_op_a_0_eq_zero flagZero
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program decode
      _openInputs state _operands _sourceA _pulls
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addChipDescriptor (p := p) := hchip
    subst hchip'
    exact ⟨AddChip.inputOutputAdapter (Environment.fromArray physical witness.data), guard⟩

/-- **The Add bundle instance**, assembled by the shared R-type constructor. -/
theorem addChip_groundingContracts :
    ChipGroundingContracts (addChipDescriptor (p := p)) :=
  addChip_rtypeGroundingData.toContracts

end AddAnchor

/-! ## The Sub anchor -/

section SubAnchor

variable [Fact (2 ^ 25 < p)]

/-- Sub's chip-specific residue for the common R-type grounding constructor. -/
theorem subChip_rtypeGroundingData :
    RTypeChipGroundingData (subChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := subChip_rtypeMemoryInteractionShape
  viewClockBounds := subChip_viewClockBounds
  timestampBounds := subChip_activeTimestampBounds
  commit_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = subChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_b_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = subChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_c_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = subChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real program decode memory
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = subChipDescriptor (p := p) := hchip
    subst hchip'
    exact trivial
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = subChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have flagZero := SubChip.rowViewOpA0_eq_zero_of_constraints env rowConstraints
    exact decode.op_a_ne_zero_of_op_a_0_eq_zero flagZero
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program decode
      _openInputs state _operands _sourceA _pulls
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = subChipDescriptor (p := p) := hchip
    subst hchip'
    exact ⟨SubChip.inputOutputAdapter (Environment.fromArray physical witness.data), guard⟩

/-- **The Sub bundle instance**, assembled by the shared R-type constructor. -/
theorem subChip_groundingContracts :
    ChipGroundingContracts (subChipDescriptor (p := p)) :=
  subChip_rtypeGroundingData.toContracts

end SubAnchor

/-! ## The Subw anchor -/

section SubwAnchor

variable [Fact (2 ^ 25 < p)]

/-- SUBW's chip-specific residue for the common R-type grounding constructor. -/
theorem subwChip_rtypeGroundingData :
    RTypeChipGroundingData (subwChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := subwChip_rtypeMemoryInteractionShape
  viewClockBounds := subwChip_viewClockBounds
  timestampBounds := subwChip_activeTimestampBounds
  commit_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = subwChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_b_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = subwChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_c_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = subwChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real program decode memory
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = subwChipDescriptor (p := p) := hchip
    subst hchip'
    exact trivial
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = subwChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have flagZero := SubwChip.rowViewOpA0_eq_zero_of_constraints env rowConstraints
    exact decode.op_a_ne_zero_of_op_a_0_eq_zero flagZero
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program decode
      _openInputs state _operands _sourceA _pulls
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = subwChipDescriptor (p := p) := hchip
    subst hchip'
    exact ⟨SubwChip.inputOutputAdapter (Environment.fromArray physical witness.data), guard⟩

/-- **The SUBW bundle instance**, assembled by the shared R-type constructor. -/
theorem subwChip_groundingContracts :
    ChipGroundingContracts (subwChipDescriptor (p := p)) :=
  subwChip_rtypeGroundingData.toContracts

end SubwAnchor

/-! ## The Mul anchor -/

section MulAnchor

variable [Fact (2 ^ 25 < p)]

local instance mulContractFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- MUL's chip-specific residue for the common R-type grounding constructor.  Its additional
five-way readiness fact is derived from the seven chip-owned physical control assertions. -/
theorem mulChip_rtypeGroundingData :
    RTypeChipGroundingData (mulChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := mulChip_rtypeMemoryInteractionShape
  viewClockBounds := mulChip_viewClockBounds
  timestampBounds := mulChip_activeTimestampBounds
  commit_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = mulChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_b_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = mulChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_c_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = mulChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real program decode memory
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = mulChipDescriptor (p := p) := hchip
    subst hchip'
    exact trivial
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = mulChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input : Var MulChip.Inputs (ZMod p) := varFromOffset MulChip.Inputs 0
    let offset := size MulChip.Inputs
    have shallow := shallowConstraints_of_componentConstraints
      (MulChip.circuit (p := p)) env rowConstraints
    have inputFlag := MulChip.eval_opA0_eq_zero_of_shallowConstraints input offset env shallow
    have outputEq : Eval.eval env ((MulChip.circuit (p := p)).output input offset) =
        (⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
      simp only [input, offset, Component.rowOutput, circuit_norm]
    have flagZero : (MulChip.rowView
        ((⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
        ((⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env)).adapter.op_a_0 = 0 := by
      change ((⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter.op_a_0 = 0
      rw [← outputEq, ← MulChip.eval_output_adapter input offset env]
      rw [MulChip.eval_inputs, Readers.RTypeReader.eval_opA0]
      exact inputFlag
    exact decode.op_a_ne_zero_of_op_a_0_eq_zero flagZero
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program decode
      _openInputs state _operands _sourceA _pulls
    have realView : (decoded.toChipRow witness.data).view.is_real = 1 := real
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = mulChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    let input : Var MulChip.Inputs (ZMod p) := varFromOffset MulChip.Inputs 0
    let offset := size MulChip.Inputs
    have shallow := shallowConstraints_of_componentConstraints
      (MulChip.circuit (p := p)) env rowConstraints
    have inputEq : Eval.eval env input =
        (⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
      eval_varFromOffset_valueFromOffset MulChip.Inputs 0 env
    have outputEq : Eval.eval env ((MulChip.circuit (p := p)).output input offset) =
        (⟨MulChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
      simp only [input, offset, Component.rowOutput, circuit_norm]
    have adapter := MulChip.eval_output_adapter input offset env
    rw [inputEq, outputEq] at adapter
    have realInput : Expression.eval env input.is_real = 1 := by
      change ((mulChipDescriptor (p := p)).decodeRow witness.data physical).view.is_real = 1 at realView
      rw [mulViewOf_decodeRow, mulViewOf_isReal, ← inputEq, MulChip.eval_isReal] at realView
      exact realView
    have oneHot := MulChip.selectorOneHot_of_shallowConstraints input offset env shallow realInput
    rw [MulChip.eval_selectors, outputEq] at oneHot
    exact ⟨adapter, guard, oneHot⟩

/-- **The MUL bundle instance**, assembled by the shared R-type constructor. -/
theorem mulChip_groundingContracts :
    ChipGroundingContracts (mulChipDescriptor (p := p)) :=
  mulChip_rtypeGroundingData.toContracts

end MulAnchor

/-! ## The DivRem anchor -/

section DivRemAnchor

variable [Fact (2 ^ 25 < p)]

local instance divRemContractFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- DivRem's chip-specific residue for the common R-type grounding constructor.  Its two operand
range assumptions are recovered from the active source pulls and the finished Memory channel. -/
theorem divRemChip_rtypeGroundingData :
    RTypeChipGroundingData (divRemChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := divRemChip_rtypeMemoryInteractionShape
  viewClockBounds := divRemChip_viewClockBounds
  timestampBounds := divRemChip_activeTimestampBounds
  commit_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = divRemChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_b_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = divRemChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  imm_c_eq := by
    intro decoded data hchip
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = divRemChipDescriptor (p := p) := hchip
    subst hchip'
    rfl
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real program decode memory
    have operands := rtypeOperandWords_isU64_of_shape divRemChip_rtypeMemoryInteractionShape
      decoded witness.data hchip real memory
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = divRemChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have adapter := DivRemChip.inputOutputAdapter env
    change Word.isU64
        ((⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter.op_b_memory.prev_value ∧
      Word.isU64
        ((⟨DivRemChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter.op_c_memory.prev_value
    rw [adapter]
    simpa only [env, DecodedInstructionRow.toChipRow, divRemViewOf_decodeRow, divRemViewOf,
      DivRemChip.rowView, Extracted.RTypeReader.toAdapterView] using operands
  routing := by
    intro witness constraints decoded hchip decodedMem real program decode
    have rowConstraints :=
      decodedInstructionRow_constraints witness constraints decoded decodedMem
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = divRemChipDescriptor (p := p) := hchip
    subst hchip'
    let env := Environment.fromArray physical witness.data
    have flagZero := DivRemChip.rowViewOpA0_eq_zero_of_constraints env rowConstraints
    exact decode.op_a_ne_zero_of_op_a_0_eq_zero flagZero
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program decode
      _openInputs state _operands _sourceA _pulls
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = divRemChipDescriptor (p := p) := hchip
    subst hchip'
    exact ⟨DivRemChip.inputOutputAdapter (Environment.fromArray physical witness.data), guard⟩

/-- **The DivRem bundle instance**, assembled by the shared R-type constructor. -/
theorem divRemChip_groundingContracts :
    ChipGroundingContracts (divRemChipDescriptor (p := p)) :=
  divRemChip_rtypeGroundingData.toContracts

end DivRemAnchor

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
private theorem wordFour_eta (word : Word (ZMod p)) :
    (#v[word[0], word[1], word[2], word[3]] : Word (ZMod p)) = word := by
  apply Vector.ext
  intro i hi
  interval_cases i <;> rfl

/-! ## The JAL anchor -/

section JalAnchor

variable [Fact (2 ^ 25 < p)]

/-- JAL's row view records its conditional destination effect exactly. -/
theorem jalChip_commitEq (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = jalChipDescriptor (p := p)) :
    (decoded.toChipRow data).view.commit =
      Trace.CommitEffect.destination (decoded.toChipRow data).view.adapter.op_a_0 := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalChipDescriptor (p := p) := hchip
  subst hchip'
  rfl

/-- The folded JAL chip `Spec` exposes the J-type reader's destination selector and x0 zeroing. -/
theorem jalChip_specFacts (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = jalChipDescriptor (p := p))
    (real : (decoded.toChipRow data).view.is_real = 1)
    (spec : (decoded.toChipRow data).chipSpec data) :
    ((decoded.toChipRow data).view.adapter.op_a_0 = 0 ∨
      (decoded.toChipRow data).view.adapter.op_a_0 = 1) ∧
    ((decoded.toChipRow data).view.adapter.op_a_0 = 1 →
      Word.toBitVec64 (decoded.toChipRow data).view.rdWrite = 0) := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalChipDescriptor (p := p) := hchip
  subst hchip'
  let env := Environment.fromArray physical data
  change JalChip.Spec
    ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) data at spec
  have realInput :
      ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_real = 1 := by
    change ((jalChipDescriptor (p := p)).decodeRow data physical).view.is_real = 1 at real
    rw [jalViewOf_decodeRow] at real
    simpa only [jalViewOf, JalChip.rowView] using real
  let readerInput : Readers.JTypeReader.Inputs (ZMod p) :=
    { cols := ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter
      is_real := ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_real
      is_trusted := ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_real
      clk_high := ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).state.clk_high
      clk_low := ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
          env).state.clk_0_16 +
        ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
          env).state.clk_16_24 * 65536
      pc := ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).state.pc
      opcode := 46
      wv0 := ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).op_a_operation.value[0]
      wv1 := ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).op_a_operation.value[1]
      wv2 := ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).op_a_operation.value[2]
      wv3 := ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).op_a_operation.value[3] }
  have reader : Readers.JTypeReader.Spec readerInput := by
    simpa only [readerInput] using spec.1
  have trusted : readerInput.is_trusted = 1 := by
    simpa only [readerInput] using realInput
  have facts :
      (readerInput.cols.op_a_0 = 0 ∨ readerInput.cols.op_a_0 = 1) ∧
      (readerInput.cols.op_a_0 = 1 →
        Word.toBitVec64
          (#v[readerInput.wv0, readerInput.wv1, readerInput.wv2, readerInput.wv3] :
            Word (ZMod p)) = 0) :=
    ⟨Readers.JTypeReader.opA0_binary_of_spec readerInput reader trusted,
      jtypeWrite_zero_of_spec readerInput reader⟩
  change
    (((jalChipDescriptor (p := p)).decodeRow data physical).view.adapter.op_a_0 = 0 ∨
      ((jalChipDescriptor (p := p)).decodeRow data physical).view.adapter.op_a_0 = 1) ∧
    (((jalChipDescriptor (p := p)).decodeRow data physical).view.adapter.op_a_0 = 1 →
      Word.toBitVec64
        ((jalChipDescriptor (p := p)).decodeRow data physical).view.rdWrite = 0)
  rw [jalViewOf_decodeRow]
  simp only [jalViewOf, JalChip.rowView, Extracted.JTypeReader.toAdapterView]
  simpa only [env, readerInput, wordFour_eta] using facts

set_option maxHeartbeats 2000000 in
/-- JAL's three circuit assumptions follow from the committed Program row on an active row. -/
theorem jalChip_assumptions :
    ChipAssumptionsContract (jalChipDescriptor (p := p)) := by
  intro witness constraints balanced decoded hchip decodedMem real program decode _memory
  have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
    decodedMem real
  have immBOne := jalChip_jtypeMemoryInteractionShape.imm_b_eq_one decoded witness.data hchip
  have immediate : Word.isU64 (decoded.toChipRow witness.data).view.adapter.op_b := by
    apply decode.immediate_words_isU64.1
    simpa only [programAccess, ProgramAccess.toRow] using immBOne
  have pcWord : Word.isU64
      (#v[(decoded.toChipRow witness.data).view.state.pc[0],
        (decoded.toChipRow witness.data).view.state.pc[1],
        (decoded.toChipRow witness.data).view.state.pc[2], 0] : Word (ZMod p)) :=
    Word.isU64_of_cases programSpec.2.1 programSpec.2.2.1 programSpec.2.2.2.1 (by simp)
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalChipDescriptor (p := p) := hchip
  subst hchip'
  let env := Environment.fromArray physical witness.data
  have inputEq : Eval.eval env (varFromOffset JalChip.Inputs 0) =
      ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset JalChip.Inputs 0 env
  change Word.isU64 (jalViewOf env).adapter.op_b at immediate
  rw [jalViewOf_adapter, inputEq] at immediate
  change Word.isU64
    (#v[(jalViewOf env).state.pc[0], (jalViewOf env).state.pc[1],
      (jalViewOf env).state.pc[2], 0] : Word (ZMod p)) at pcWord
  rw [jalViewOf_state, inputEq] at pcWord
  have concrete : JalChip.Assumptions
      ((⟨JalChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) witness.data := by
    exact ⟨immediate, pcWord⟩
  exact (jalChipDescriptor_assumptions_iff witness.data physical).mpr concrete

/-- JAL accepts either destination branch, so its registry routing guard is vacuous. -/
theorem jalChip_routing : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = jalChipDescriptor (p := p) →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ program : GuestProgram,
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
          RdGuardFact (jalChipDescriptor (p := p)) (decoded.toChipRow witness.data).view := by
  intros
  trivial

/-- JAL's explicit high-limb assertion supplies its sole `advanceReady` fact. -/
theorem jalChip_readiness : ChipReadinessContract (jalChipDescriptor (p := p)) := by
  intro witness constraints balanced decoded hchip decodedMem real guard program decode
    openInputs state operands sourceA _pulls
  have rowConstraints :=
    decodedInstructionRow_constraints witness constraints decoded decodedMem
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalChipDescriptor (p := p) := hchip
  subst hchip'
  exact JalChip.addValueHigh_eq_zero_of_constraints
    (Environment.fromArray physical witness.data) rowConstraints

/-- JAL's chip-specific residue for the destination-only J-type constructor. -/
theorem jalChip_jtypeGroundingData :
    JTypeChipGroundingData (jalChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := jalChip_jtypeMemoryInteractionShape
  viewClockBounds := jalChip_viewClockBounds
  timestampBound := jalChip_activeTimestampBound
  commit_eq := jalChip_commitEq
  specFacts := jalChip_specFacts
  assumptions := jalChip_assumptions
  routing := jalChip_routing
  readiness := jalChip_readiness

/-- **The JAL bundle instance**, assembled by the shared J-type constructor. -/
theorem jalChip_groundingContracts :
    ChipGroundingContracts (jalChipDescriptor (p := p)) :=
  jalChip_jtypeGroundingData.toContracts

end JalAnchor

/-! ## The U-type anchor -/

section UTypeAnchor

variable [Fact (2 ^ 25 < p)]

/-- U-type records the same conditional destination effect as the shared J-type reader. -/
theorem uTypeChip_commitEq (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = uTypeChipDescriptor (p := p)) :
    (decoded.toChipRow data).view.commit =
      Trace.CommitEffect.destination (decoded.toChipRow data).view.adapter.op_a_0 := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = uTypeChipDescriptor (p := p) := hchip
  subst hchip'
  rfl

/-- The folded U-type chip `Spec` exposes the J-type reader's selector and x0 zeroing facts. -/
theorem uTypeChip_specFacts (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = uTypeChipDescriptor (p := p))
    (real : (decoded.toChipRow data).view.is_real = 1)
    (spec : (decoded.toChipRow data).chipSpec data) :
    ((decoded.toChipRow data).view.adapter.op_a_0 = 0 ∨
      (decoded.toChipRow data).view.adapter.op_a_0 = 1) ∧
    ((decoded.toChipRow data).view.adapter.op_a_0 = 1 →
      Word.toBitVec64 (decoded.toChipRow data).view.rdWrite = 0) := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = uTypeChipDescriptor (p := p) := hchip
  subst hchip'
  let env := Environment.fromArray physical data
  change UTypeChip.Spec
    ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) data at spec
  have realInput :
      ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_real = 1 := by
    change ((uTypeChipDescriptor (p := p)).decodeRow data physical).view.is_real = 1 at real
    rw [uTypeViewOf_decodeRow] at real
    simpa only [uTypeViewOf, UTypeChip.rowView] using real
  let readerInput : Readers.JTypeReader.Inputs (ZMod p) :=
    { cols := ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter
      is_real := ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_real
      is_trusted := ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_real
      clk_high := ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).state.clk_high
      clk_low := ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
          env).state.clk_0_16 +
        ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
          env).state.clk_16_24 * 65536
      pc := ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).state.pc
      opcode :=
        ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_auipc * 48 +
          (1 - ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
            env).is_auipc) * 49
      wv0 := ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).add_operation.value[0]
      wv1 := ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).add_operation.value[1]
      wv2 := ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).add_operation.value[2]
      wv3 := ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).add_operation.value[3] }
  have reader : Readers.JTypeReader.Spec readerInput := by
    simpa only [readerInput] using spec.1
  have trusted : readerInput.is_trusted = 1 := by
    simpa only [readerInput] using realInput
  have facts :
      (readerInput.cols.op_a_0 = 0 ∨ readerInput.cols.op_a_0 = 1) ∧
      (readerInput.cols.op_a_0 = 1 →
        Word.toBitVec64
          (#v[readerInput.wv0, readerInput.wv1, readerInput.wv2, readerInput.wv3] :
            Word (ZMod p)) = 0) :=
    ⟨Readers.JTypeReader.opA0_binary_of_spec readerInput reader trusted,
      jtypeWrite_zero_of_spec readerInput reader⟩
  change
    (((uTypeChipDescriptor (p := p)).decodeRow data physical).view.adapter.op_a_0 = 0 ∨
      ((uTypeChipDescriptor (p := p)).decodeRow data physical).view.adapter.op_a_0 = 1) ∧
    (((uTypeChipDescriptor (p := p)).decodeRow data physical).view.adapter.op_a_0 = 1 →
      Word.toBitVec64
        ((uTypeChipDescriptor (p := p)).decodeRow data physical).view.rdWrite = 0)
  rw [uTypeViewOf_decodeRow]
  simp only [uTypeViewOf, UTypeChip.rowView, Extracted.JTypeReader.toAdapterView]
  simpa only [env, readerInput, wordFour_eta] using facts

set_option maxHeartbeats 1000000 in
/-- U-type's immediate, PC, padding, and U-immediate decode assumptions all come from the active
Program row plus its physical LUI/AUIPC selector gate. -/
theorem uTypeChip_assumptions :
    ChipAssumptionsContract (uTypeChipDescriptor (p := p)) := by
  intro witness constraints balanced decoded hchip decodedMem real program decode _memory
  have rowConstraints :=
    decodedInstructionRow_constraints witness constraints decoded decodedMem
  have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
    decodedMem real
  have immBOne := uTypeChip_jtypeMemoryInteractionShape.imm_b_eq_one decoded witness.data hchip
  have immediate : Word.isU64 (decoded.toChipRow witness.data).view.adapter.op_b := by
    apply decode.immediate_words_isU64.1
    simpa only [programAccess, ProgramAccess.toRow] using immBOne
  have pcWord : Word.isU64
      (#v[(decoded.toChipRow witness.data).view.state.pc[0],
        (decoded.toChipRow witness.data).view.state.pc[1],
        (decoded.toChipRow witness.data).view.state.pc[2], 0] : Word (ZMod p)) :=
    Word.isU64_of_cases programSpec.2.1 programSpec.2.2.1 programSpec.2.2.2.1 (by simp)
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = uTypeChipDescriptor (p := p) := hchip
  subst hchip'
  let env := Environment.fromArray physical witness.data
  have inputEq : Eval.eval env (varFromOffset UTypeChip.Inputs 0) =
      ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset UTypeChip.Inputs 0 env
  change Word.isU64 (uTypeViewOf env).adapter.op_b at immediate
  rw [uTypeViewOf_adapter, inputEq] at immediate
  change Word.isU64
    (#v[(uTypeViewOf env).state.pc[0], (uTypeViewOf env).state.pc[1],
      (uTypeViewOf env).state.pc[2], 0] : Word (ZMod p)) at pcWord
  rw [uTypeViewOf_state, inputEq] at pcWord
  have selector :=
    UTypeChip.isAuipc_binary_of_constraints env rowConstraints
  have decode' : decodedInROM program (programAccess (uTypeViewOf env)).toRow := by
    simpa only [DecodedInstructionRow.toChipRow, uTypeViewOf_decodeRow, env] using decode
  have decodeRelation :
      Word.toBitVec64
          ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
            env).adapter.op_b_imm =
        RV64.lui (UTypeChip.immOf
          ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter) := by
    rcases selector with selectorZero | selectorOne
    · have opcodeEq :
          (programAccess (uTypeViewOf env)).toRow.opcode =
            ((uopToOpcode uop.LUI).toNat : ZMod p) := by
        simp [programAccess, ProgramAccess.toRow, uTypeViewOf, UTypeChip.rowView,
          selectorZero, uopToOpcode, Opcode.toNat]
      have immC : (programAccess (uTypeViewOf env)).toRow.imm_c = 1 := rfl
      obtain ⟨word, imm, rd, fetch, decodedAll, opA, opB⟩ :=
        decodesUType uop.LUI decode' opcodeEq immC
      have opBInput :
          ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
              env).adapter.op_b_imm =
            bitVecToWord ((imm.signExtend 64) <<< 12) := by
        change (uTypeViewOf env).adapter.op_b =
          bitVecToWord ((imm.signExtend 64) <<< 12) at opB
        rw [uTypeViewOf_adapter, inputEq] at opB
        exact opB
      have immEq := SP1Clean.UTypeChip.immOf_bind imm
        ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter opBInput
      rw [opBInput, immEq, toBitVec64_bitVecToWord]
      exact uTypeSignExtend_shiftLeft imm
    · have opcodeEq :
          (programAccess (uTypeViewOf env)).toRow.opcode =
            ((uopToOpcode uop.AUIPC).toNat : ZMod p) := by
        simp [programAccess, ProgramAccess.toRow, uTypeViewOf, UTypeChip.rowView,
          selectorOne, uopToOpcode, Opcode.toNat]
      have immC : (programAccess (uTypeViewOf env)).toRow.imm_c = 1 := rfl
      obtain ⟨word, imm, rd, fetch, decodedAll, opA, opB⟩ :=
        decodesUType uop.AUIPC decode' opcodeEq immC
      have opBInput :
          ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
              env).adapter.op_b_imm =
            bitVecToWord ((imm.signExtend 64) <<< 12) := by
        change (uTypeViewOf env).adapter.op_b =
          bitVecToWord ((imm.signExtend 64) <<< 12) at opB
        rw [uTypeViewOf_adapter, inputEq] at opB
        exact opB
      have immEq := SP1Clean.UTypeChip.immOf_bind imm
        ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter opBInput
      rw [opBInput, immEq, toBitVec64_bitVecToWord]
      exact uTypeSignExtend_shiftLeft imm
  have concrete : UTypeChip.Assumptions
      ((⟨UTypeChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) witness.data := by
    exact ⟨immediate, pcWord, decodeRelation⟩
  exact (uTypeChipDescriptor_assumptions_iff witness.data physical).mpr concrete

/-- U-type accepts both destination branches. -/
theorem uTypeChip_routing : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = uTypeChipDescriptor (p := p) →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ program : GuestProgram,
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
          RdGuardFact (uTypeChipDescriptor (p := p)) (decoded.toChipRow witness.data).view := by
  intros
  trivial

/-- U-type readiness consists of the Program-row PC bound and the physical variant-selector gate. -/
theorem uTypeChip_readiness : ChipReadinessContract (uTypeChipDescriptor (p := p)) := by
  intro witness constraints balanced decoded hchip decodedMem real guard program decode
    openInputs state operands sourceA _pulls
  have rowConstraints :=
    decodedInstructionRow_constraints witness constraints decoded decodedMem
  have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
    decodedMem real
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = uTypeChipDescriptor (p := p) := hchip
  subst hchip'
  exact ⟨programSpec.2.1,
    UTypeChip.isAuipc_binary_of_constraints
      (Environment.fromArray physical witness.data) rowConstraints⟩

/-- U-type's chip-specific residue for the destination-only J-type constructor. -/
theorem uTypeChip_jtypeGroundingData :
    JTypeChipGroundingData (uTypeChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := uTypeChip_jtypeMemoryInteractionShape
  viewClockBounds := uTypeChip_viewClockBounds
  timestampBound := uTypeChip_activeTimestampBound
  commit_eq := uTypeChip_commitEq
  specFacts := uTypeChip_specFacts
  assumptions := uTypeChip_assumptions
  routing := uTypeChip_routing
  readiness := uTypeChip_readiness

/-- **The U-type bundle instance**, assembled by the shared J-type constructor. -/
theorem uTypeChip_groundingContracts :
    ChipGroundingContracts (uTypeChipDescriptor (p := p)) :=
  uTypeChip_jtypeGroundingData.toContracts

end UTypeAnchor

/-! ## The JALR anchor -/

section JalrAnchor

variable [Fact (2 ^ 25 < p)]

/-- JALR records its conditional destination effect exactly. -/
theorem jalrChip_commitEq (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = jalrChipDescriptor (p := p)) :
    (decoded.toChipRow data).view.commit =
      Trace.CommitEffect.destination (decoded.toChipRow data).view.adapter.op_a_0 := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalrChipDescriptor (p := p) := hchip
  subst hchip'
  rfl

/-- The folded JALR chip `Spec` exposes the mutable I-type reader's destination selector and x0
zeroing facts. -/
theorem jalrChip_specFacts (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = jalrChipDescriptor (p := p))
    (real : (decoded.toChipRow data).view.is_real = 1)
    (spec : (decoded.toChipRow data).chipSpec data) :
    ((decoded.toChipRow data).view.adapter.op_a_0 = 0 ∨
      (decoded.toChipRow data).view.adapter.op_a_0 = 1) ∧
    ((decoded.toChipRow data).view.adapter.op_a_0 = 1 →
      Word.toBitVec64 (decoded.toChipRow data).view.rdWrite = 0) := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalrChipDescriptor (p := p) := hchip
  subst hchip'
  let env := Environment.fromArray physical data
  change JalrChip.Spec
    ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env)
    ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env) data at spec
  have realInput :
      ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_real = 1 := by
    change ((jalrChipDescriptor (p := p)).decodeRow data physical).view.is_real = 1 at real
    rw [jalrViewOf_decodeRow] at real
    simpa only [jalrViewOf, JalrChip.rowView] using real
  let readerInput : Readers.ITypeReader.Inputs (ZMod p) :=
    { cols := ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter
      is_real := ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_real
      is_trusted := ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).is_real
      clk_high := ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).state.clk_high
      clk_low := ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
          env).state.clk_0_16 +
        ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
          env).state.clk_16_24 * 65536
      pc := ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).state.pc
      opcode := 47
      wv0 := ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).op_a_operation.value[0]
      wv1 := ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).op_a_operation.value[1]
      wv2 := ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).op_a_operation.value[2]
      wv3 := ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput
        env).op_a_operation.value[3] }
  have reader : Readers.ITypeReader.Spec readerInput := by
    simpa only [readerInput] using spec.1
  have trusted : readerInput.is_trusted = 1 := by
    simpa only [readerInput] using realInput
  have facts :
      (readerInput.cols.op_a_0 = 0 ∨ readerInput.cols.op_a_0 = 1) ∧
      (readerInput.cols.op_a_0 = 1 →
        Word.toBitVec64
          (#v[readerInput.wv0, readerInput.wv1, readerInput.wv2, readerInput.wv3] :
            Word (ZMod p)) = 0) :=
    ⟨Readers.ITypeReader.opA0_binary_of_spec readerInput reader trusted,
      itypeWrite_zero_of_spec readerInput reader⟩
  change
    (((jalrChipDescriptor (p := p)).decodeRow data physical).view.adapter.op_a_0 = 0 ∨
      ((jalrChipDescriptor (p := p)).decodeRow data physical).view.adapter.op_a_0 = 1) ∧
    (((jalrChipDescriptor (p := p)).decodeRow data physical).view.adapter.op_a_0 = 1 →
      Word.toBitVec64
        ((jalrChipDescriptor (p := p)).decodeRow data physical).view.rdWrite = 0)
  rw [jalrViewOf_decodeRow]
  simp only [jalrViewOf, JalrChip.rowView, Extracted.ITypeReader.toAdapterView]
  simpa only [env, readerInput, wordFour_eta] using facts

omit [Fact (2 ^ 25 < p)] in
private theorem jalrAssumptions_of_components
    {input : JalrChip.Inputs (ZMod p)} {data : ProverData (ZMod p)}
    (immediate : Word.isU64 input.adapter.op_c_imm)
    (source : Word.isU64
      (#v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
        input.adapter.op_b_memory.prev_value[2],
        input.adapter.op_b_memory.prev_value[3]] : Word (ZMod p)))
    (pc : Word.isU64
      (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p))) :
    JalrChip.Assumptions input data :=
  ⟨immediate, source, pc⟩

set_option maxHeartbeats 2000000 in
/-- JALR's immediate, source word, and PC assumptions are grounded by the committed
Program row and the exact source-B Memory pull. -/
theorem jalrChip_assumptions :
    ChipAssumptionsContract (jalrChipDescriptor (p := p)) := by
  intro witness constraints balanced decoded hchip decodedMem real program decode memory
  have sourceU64 := itypeOperandB_isU64_of_shape
    jalrChip_itypeMemoryInteractionShape decoded witness.data hchip real memory
  have immCOne :=
    jalrChip_itypeMemoryInteractionShape.imm_c_eq_one decoded witness.data hchip
  have immediate : Word.isU64 (decoded.toChipRow witness.data).view.adapter.op_c := by
    apply decode.immediate_words_isU64.2
    simpa only [programAccess, ProgramAccess.toRow] using immCOne
  have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
    decodedMem real
  have pcWord : Word.isU64
      (#v[(decoded.toChipRow witness.data).view.state.pc[0],
        (decoded.toChipRow witness.data).view.state.pc[1],
        (decoded.toChipRow witness.data).view.state.pc[2], 0] : Word (ZMod p)) :=
    Word.isU64_of_cases programSpec.2.1 programSpec.2.2.1 programSpec.2.2.2.1 (by simp)
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalrChipDescriptor (p := p) := hchip
  subst hchip'
  let env := Environment.fromArray physical witness.data
  have inputEq : Eval.eval env (varFromOffset JalrChip.Inputs 0) =
      ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset JalrChip.Inputs 0 env
  have sourceRaw : Word.isU64
      ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
        env).adapter.op_b_memory.prev_value := by
    simpa only [DecodedInstructionRow.toChipRow, jalrViewOf_decodeRow,
      jalrViewOf_adapter, inputEq, Extracted.ITypeReader.toAdapterView, env] using sourceU64
  have sourceInput : Word.isU64
      (#v[((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_b_memory.prev_value[0],
        ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_b_memory.prev_value[1],
        ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_b_memory.prev_value[2],
        ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_b_memory.prev_value[3]] : Word (ZMod p)) := by
    rw [wordFour_eta]
    exact sourceRaw
  have immediateInput : Word.isU64
      ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
        env).adapter.op_c_imm := by
    simpa only [DecodedInstructionRow.toChipRow, jalrViewOf_decodeRow,
      jalrViewOf_adapter, inputEq, Extracted.ITypeReader.toAdapterView, env] using immediate
  have pcInput : Word.isU64
      (#v[((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state.pc[0],
        ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state.pc[1],
        ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state.pc[2],
        0] : Word (ZMod p)) := by
    simpa only [DecodedInstructionRow.toChipRow, jalrViewOf_decodeRow,
      jalrViewOf_state, inputEq, env] using pcWord
  have concrete : JalrChip.Assumptions
      ((⟨JalrChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) witness.data :=
    jalrAssumptions_of_components immediateInput sourceInput pcInput
  exact (jalrChipDescriptor_assumptions_iff witness.data physical).mpr concrete

/-- JALR's source register is committed as a register operand. -/
theorem jalrChip_immBEq (decoded : DecodedInstructionRow p) (data : ProverData (ZMod p))
    (hchip : decoded.chip = jalrChipDescriptor (p := p)) :
    (programAccess (decoded.toChipRow data).view).toRow.imm_b = 0 := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalrChipDescriptor (p := p) := hchip
  subst hchip'
  rfl

/-- JALR accepts both destination branches. -/
theorem jalrChip_routing : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = jalrChipDescriptor (p := p) →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ program : GuestProgram,
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
          RdGuardFact (jalrChipDescriptor (p := p))
            (decoded.toChipRow witness.data).view := by
  intros
  trivial

/-- JALR has no residual `advanceReady` condition beyond the facts already in its `Spec`. -/
theorem jalrChip_readiness :
    ChipReadinessContract (jalrChipDescriptor (p := p)) := by
  intro witness constraints balanced decoded hchip decodedMem real guard program decode
    openInputs state operands sourceA _pulls
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = jalrChipDescriptor (p := p) := hchip
  subst hchip'
  exact True.intro

/-- JALR's residue for the conditional-destination I-type constructor. -/
theorem jalrChip_conditionalITypeGroundingData :
    ConditionalITypeChipGroundingData (jalrChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := jalrChip_itypeMemoryInteractionShape
  viewClockBounds := jalrChip_viewClockBounds
  timestampBounds := jalrChip_activeTimestampBounds
  commit_eq := jalrChip_commitEq
  imm_b_eq := jalrChip_immBEq
  specFacts := jalrChip_specFacts
  assumptions := jalrChip_assumptions
  routing := jalrChip_routing
  readiness := jalrChip_readiness

/-- **The JALR bundle instance**, assembled by the conditional I-type constructor. -/
theorem jalrChip_groundingContracts :
    ChipGroundingContracts (jalrChipDescriptor (p := p)) :=
  jalrChip_conditionalITypeGroundingData.toContracts

end JalrAnchor

/-! ## The Branch anchor -/

section BranchAnchor

variable [Fact (2 ^ 25 < p)]

/-- Branch commits neither a register nor RAM write. -/
theorem branchChip_commitEq (decoded : DecodedInstructionRow p)
    (data : ProverData (ZMod p))
    (hchip : decoded.chip = branchChipDescriptor (p := p)) :
    (decoded.toChipRow data).view.commit = Trace.CommitEffect.noWrite := by
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = branchChipDescriptor (p := p) := hchip
  subst hchip'
  rfl

omit [Fact (2 ^ 17 < p)] [Fact (2 ^ 25 < p)] in
private theorem branchAssumptions_of_components
    {input : BranchChip.Inputs (ZMod p)} {data : ProverData (ZMod p)}
    (immediate : Word.isU64 input.adapter.op_c_imm)
    (sourceA : Word.isU64
      (#v[input.adapter.op_a_memory.prev_value[0], input.adapter.op_a_memory.prev_value[1],
        input.adapter.op_a_memory.prev_value[2],
        input.adapter.op_a_memory.prev_value[3]] : Word (ZMod p)))
    (sourceB : Word.isU64
      (#v[input.adapter.op_b_memory.prev_value[0], input.adapter.op_b_memory.prev_value[1],
        input.adapter.op_b_memory.prev_value[2],
        input.adapter.op_b_memory.prev_value[3]] : Word (ZMod p)))
    (pc : Word.isU64
      (#v[input.state.pc[0], input.state.pc[1], input.state.pc[2], 0] : Word (ZMod p))) :
    BranchChip.Assumptions input data :=
  ⟨immediate, sourceA, sourceB, pc⟩

set_option maxHeartbeats 2000000 in
/-- Branch's immediate, both source words, and PC assumptions come respectively from the committed
Program row, exact immutable-reader pulls, and the Program-row limb bounds. -/
theorem branchChip_assumptions :
    ChipAssumptionsContract (branchChipDescriptor (p := p)) := by
  intro witness constraints balanced decoded hchip decodedMem real program decode memory
  have operands := immutableItypeOperandWords_isU64_of_shape
    branchChip_immutableItypeMemoryInteractionShape decoded witness.data hchip real memory
  have immCOne :=
    branchChip_immutableItypeMemoryInteractionShape.imm_c_eq_one decoded witness.data hchip
  have immediate : Word.isU64 (decoded.toChipRow witness.data).view.adapter.op_c := by
    apply decode.immediate_words_isU64.2
    simpa only [programAccess, ProgramAccess.toRow] using immCOne
  have programSpec := decodedInstructionRow_programRowSpec witness constraints balanced decoded
    decodedMem real
  have pcWord : Word.isU64
      (#v[(decoded.toChipRow witness.data).view.state.pc[0],
        (decoded.toChipRow witness.data).view.state.pc[1],
        (decoded.toChipRow witness.data).view.state.pc[2], 0] : Word (ZMod p)) :=
    Word.isU64_of_cases programSpec.2.1 programSpec.2.2.1 programSpec.2.2.2.1 (by simp)
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = branchChipDescriptor (p := p) := hchip
  subst hchip'
  let env := Environment.fromArray physical witness.data
  have inputEq : Eval.eval env (varFromOffset BranchChip.Inputs 0) =
      ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) :=
    eval_varFromOffset_valueFromOffset BranchChip.Inputs 0 env
  obtain ⟨sourceA, sourceB⟩ := operands
  have sourceARaw : Word.isU64
      ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
        env).adapter.op_a_memory.prev_value := by
    simpa only [DecodedInstructionRow.toChipRow, branchViewOf_decodeRow,
      branchViewOf_adapter, inputEq, Extracted.ITypeReader.toAdapterView, env] using sourceA
  have sourceAInput : Word.isU64
      (#v[((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_a_memory.prev_value[0],
        ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_a_memory.prev_value[1],
        ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_a_memory.prev_value[2],
        ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_a_memory.prev_value[3]] : Word (ZMod p)) := by
    rw [wordFour_eta]
    exact sourceARaw
  have sourceBRaw : Word.isU64
      ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
        env).adapter.op_b_memory.prev_value := by
    simpa only [DecodedInstructionRow.toChipRow, branchViewOf_decodeRow,
      branchViewOf_adapter, inputEq, Extracted.ITypeReader.toAdapterView, env] using sourceB
  have sourceBInput : Word.isU64
      (#v[((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_b_memory.prev_value[0],
        ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_b_memory.prev_value[1],
        ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_b_memory.prev_value[2],
        ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
          env).adapter.op_b_memory.prev_value[3]] : Word (ZMod p)) := by
    rw [wordFour_eta]
    exact sourceBRaw
  have immediateInput : Word.isU64
      ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput
        env).adapter.op_c_imm := by
    simpa only [DecodedInstructionRow.toChipRow, branchViewOf_decodeRow,
      branchViewOf_adapter, inputEq, Extracted.ITypeReader.toAdapterView, env] using immediate
  have pcInput : Word.isU64
      (#v[((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state.pc[0],
        ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state.pc[1],
        ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).state.pc[2],
        0] : Word (ZMod p)) := by
    simpa only [DecodedInstructionRow.toChipRow, branchViewOf_decodeRow,
      branchViewOf_state, inputEq, env] using pcWord
  have concrete : BranchChip.Assumptions
      ((⟨BranchChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env) witness.data :=
    branchAssumptions_of_components immediateInput sourceAInput sourceBInput pcInput
  exact (branchChipDescriptor_assumptions_iff witness.data physical).mpr concrete

/-- Branch accepts any source-A register, including x0. -/
theorem branchChip_routing : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = branchChipDescriptor (p := p) →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      ∀ program : GuestProgram,
        decodedInROM program (programAccess (decoded.toChipRow witness.data).view).toRow →
          RdGuardFact (branchChipDescriptor (p := p))
            (decoded.toChipRow witness.data).view := by
  intros
  trivial

/-- Branch readiness is exactly the grounded source-A binding; opcode one-hotness is now an honest
conjunct of the whole-chip semantic `Spec`. -/
theorem branchChip_readiness :
    ChipReadinessContract (branchChipDescriptor (p := p)) := by
  intro witness constraints balanced decoded hchip decodedMem real guard program decode
    openInputs state operands sourceA _pulls
  obtain ⟨chip, physical⟩ := decoded
  have hchip' : chip = branchChipDescriptor (p := p) := hchip
  subst hchip'
  exact sourceA

/-- Branch's residue for the immutable I-type constructor. -/
theorem branchChip_immutableITypeGroundingData :
    ImmutableITypeChipGroundingData (branchChipDescriptor (p := p)) where
  migrated := rfl
  memoryShape := branchChip_immutableItypeMemoryInteractionShape
  viewClockBounds := branchChip_viewClockBounds
  timestampBounds := branchChip_activeTimestampBounds
  commit_eq := branchChip_commitEq
  assumptions := branchChip_assumptions
  routing := branchChip_routing
  readiness := branchChip_readiness

/-- **The Branch bundle instance**, assembled by the immutable I-type constructor. -/
theorem branchChip_groundingContracts :
    ChipGroundingContracts (branchChipDescriptor (p := p)) :=
  branchChip_immutableITypeGroundingData.toContracts

end BranchAnchor

end SP1Clean.Soundness
