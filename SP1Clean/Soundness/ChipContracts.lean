import SP1Clean.Soundness.GroundingAdapter

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
`statePullTime_of_decodedStateWalk`; and the `RdGuardFact` routing residual (the `op_a = x0`
dispatch bit) comes from opcode routing.  All of these are hypotheses of the bundle's consumers,
never bundle fields.

**Shrunk fields (TODO(rollout)).**  `RowOK.touches`/`RowOK.chain_mono` are *not* yet stated in
their engine form here, deliberately:

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

What *is* per-chip and provable now is captured by two surfaces: the generic
`RowWiring.push_window` lemma (every push lands in `[t, t+4]`, with its loc/value classification
already in `RowWiring.push_classified`), and the `chainSlots` field (pairwise-distinct push times
— the per-loc strict slot ordering the aligned chains will need).  When arc B lands the aligned
carrier, `chainSlots` + `push_window` + the balance-conditional `pull_lt_push` upgrade into full
`RowOK.touches`/`chain_mono` producers here.

Add is the validation anchor: `addChip_groundingContracts` discharges the whole bundle from the
existing `GroundingAdapter`/`AddChip.Contracts` lemmas, with the reader-passthrough readiness
fact evaluated once in `addChip_adapterPassthrough`. -/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open Sail LeanRV64D LeanRV64D.Functions
open Air.Flat Circuit
open SP1Clean.Soundness.Target
open SP1Clean.Soundness.TimedGrounding
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The `rd == x0` routing residual for one decoded row, phrased against the descriptor's declared
`RdGuard`.  This is an assembly-level fact — SP1's trace generator routes an opcode to the chip
only when the guard accepts the decoded destination — so consumers take it as a hypothesis; a
chip's `readiness` field may consume it (the `.nonX0` chips' `op_a ≠ 0` write-routing invariant)
but never has to prove it. -/
def RdGuardFact (chip : SupportedChip p) (view : Trace.RowView (ZMod p)) : Prop :=
  match chip.rdGuard with
  | .any => True
  | .nonX0 => view.adapter.op_a ≠ 0
  | .onlyX0 => view.adapter.op_a = 0

omit [Fact (2 ^ 17 < p)] in
/-- Every push of a wired row lands inside the row's effect window `[t, t+4]` — the generic
`TouchOK.push_lo`/`push_hi` half of the touch discipline, already forced by
`RowWiring.push_classified` for every chip. -/
theorem RowWiring.push_window {view : Trace.RowView (ZMod p)} {rf : Semantics.RowFacts p}
    (wiring : RowWiring view rf) :
    ∀ m ∈ rf.memPushes, StateMsg.timeNat rf.statePull ≤ MemoryMsg.timeNat m ∧
      MemoryMsg.timeNat m ≤ StateMsg.timeNat rf.statePull + 4 := by
  intro m hm
  rcases wiring.push_classified m hm with ⟨mp, -, -, -, hlo, hhi⟩ | ⟨-, -, -, -, ht⟩ |
    ⟨-, mp, -, -, -, -, ht⟩
  · exact ⟨hlo, by omega⟩
  · omega
  · omega

section Contracts

variable [Fact (2 ^ 25 < p)]

/-- **The per-chip grounding-contract bundle.**  Everything the dynamic capstone seam needs from
one registered chip, quantified over the per-row residuals the assembly supplies (the canonical
witness with its constraints and balance, the decoded row with its registry membership and active
selector, the open circuit inputs, and the routing guard).  See the module doc for the field
rationale and the deliberately absent assembly-level facts. -/
structure ChipGroundingContracts (chip : SupportedChip p) : Prop where
  /-- The chip has migrated to the uniform `ChipKind.advance` payload. -/
  migrated : chip.kind.advance.isSome = true
  /-- The chip's register source operands are carried by exact Memory pulls of its own emitted
  interaction list (`RegisterOperandPullShape`), feeding `ValueOperandsBound` through timed
  grounding. -/
  operandPulls : DecodedInstructionRow.RegisterOperandPullShape chip
  /-- The per-row `RowWiring` producer: the message ↔ view correspondences the grounding adapter
  consumes, from the finished Byte channel (clock decode), the chip `Spec`, and the row's own push
  `Requirements`. -/
  wiring : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints → witness.BalancedChannels →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      DecodedRowOpenSoundnessInputs decoded witness.data →
      RowWiring (decoded.toChipRow witness.data).view (decoded.ordinaryRowFacts witness.data)
  /-- Shrunk `RowOK.chain_mono` producer (TODO(rollout)): the row's pushes occupy pairwise-distinct
  effect slots, so every per-location chain of the arc-B aligned carrier can be strictly
  time-ordered.  The full `touches`/`chain_mono` form additionally needs the aligned pull/push
  pairing and the balance-conditional `pull_lt_push`; see the module doc. -/
  chainSlots : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints → witness.BalancedChannels →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      List.Pairwise (fun a b => MemoryMsg.timeNat a ≠ MemoryMsg.timeNat b)
        (decoded.producedMemoryMessages witness.data)
  /-- The chip circuit's soundness-side `Assumptions` hold on every decoded row of the canonical
  witness.  For the audit-surface ALU chips this is `True`; helper-dependent chips discharge
  their remaining preconditions here at rollout. -/
  assumptions : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints → witness.BalancedChannels →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      decoded.chip.table.Assumptions (decoded.environment witness.data)
  /-- The `advanceReady` producer: the reader passthrough (`cols = main inp`, a decode-level
  evaluation fact) plus whatever the routing guard supplies (`op_a ≠ 0` for the `.nonX0`
  write-routing chips).  State-independent: the conclusion holds at every `program`/`state`. -/
  readiness : ∀ (witness : EnsembleWitness (sp1Ensemble (p := p))),
    witness.Constraints → witness.BalancedChannels →
    ∀ decoded : DecodedInstructionRow p, decoded.chip = chip →
      decoded ∈ decodedInstructionRows (p := p) witness.tables →
      (decoded.toChipRow witness.data).is_real = 1 →
      RdGuardFact chip (decoded.toChipRow witness.data).view →
      ∀ (program : GuestProgram) (state : SailState),
        (decoded.toChipRow witness.data).kind.advanceReady
          (decoded.toChipRow witness.data).inputs (decoded.toChipRow witness.data).cols
          program state

/-- **The engine-feed consumer**: any decoded row of a contracted chip produces both timed-engine
records — the chip-generic form of `addRow_engineFacts`.  `decode` remains the Program-grounding
residual and `guard` the routing residual; everything else comes from the bundle. -/
theorem ChipGroundingContracts.engineFacts
    {chip : SupportedChip p} (contracts : ChipGroundingContracts chip)
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (decoded : DecodedInstructionRow p) (hchip : decoded.chip = chip)
    (decodedMem : decoded ∈ decodedInstructionRows (p := p) witness.tables)
    (real : (decoded.toChipRow witness.data).is_real = 1)
    (guard : RdGuardFact chip (decoded.toChipRow witness.data).view)
    (program : GuestProgram)
    (decode : Target.decodedInROM program
      (programAccess (decoded.toChipRow witness.data).view).toRow)
    (initial : SailState) (initialClock : ℕ) :
    LocalStepFact program initial initialClock (decoded.ordinaryRowFacts witness.data) ∧
      FrameFact program initial initialClock (decoded.ordinaryRowFacts witness.data) := by
  have ready : ∀ s : SailState, (decoded.toChipRow witness.data).kind.advanceReady
      (decoded.toChipRow witness.data).inputs (decoded.toChipRow witness.data).cols program s :=
    fun s => contracts.readiness witness constraints balanced decoded hchip decodedMem real guard
      program s
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
      DecodedRowOpenSoundnessInputs decoded witness.data := fun hcurr =>
    { assumptions := contracts.assumptions witness constraints balanced decoded hchip decodedMem real
      memory := decoded.memoryChannelGuarantees_of_pullCurrency witness.data
        (fun mp hmp => ⟨(hcurr mp hmp).1, (hcurr mp hmp).2.1⟩) }
  refine engineFacts_of_kind migrated real decode ready initial initialClock
    (fun hcurr => contracts.wiring witness constraints balanced decoded hchip decodedMem real
      (mkOpenInputs hcurr))
    (fun hcurr => decoded.chipSpec_of_openSoundnessInputs witness constraints balanced decodedMem
      (mkOpenInputs hcurr))

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
    (grounded : TimedGrounding.Grounded program initial initialClock
      (decoded.ordinaryRowFacts witness.data))
    (guard : RdGuardFact decoded.chip (decoded.toChipRow witness.data).view)
    (chain : Target.SailChain steps initial state)
    (real : (decoded.toChipRow witness.data).is_real = 1)
    (rowTime : Semantics.StateMsg.timeNat
      (statePullMessage (decoded.toChipRow witness.data)) = initialClock + 8 * steps) :
    DynamicGroundedRow witness.data program (decoded.toChipRow witness.data) state := by
  have ready := contracts.readiness witness constraints balanced decoded rfl decodedMem real guard
    program state
  have assumptions := contracts.assumptions witness constraints balanced decoded rfl decodedMem
    real
  have pulls := DecodedInstructionRow.registerOperandPulls_of_shape decoded witness.data program
    state contracts.operandPulls ready
  exact decoded.dynamicGrounded_of_timedInputs witness constraints balanced decodedMem program
    initial state initialClock steps assumptions grounded ready pulls chain real rowTime

end Contracts

/-! ## The assembly theorem (statement, pending arc B)

The registry aggregator will close the capstone seam in the shape below — the exact
`supportedCore_orderedRows_dynamic` signature (`Soundness/AIR.lean`) plus the 25 bundle instances.
It is recorded here as a comment because its proof consumes the arc-B balance stack, which is not
yet derivable: the `TimedGrounding.walk` invocation needs the State/Memory multiset balances
restricted to the exhaustive real-row multiset, the `LiveOK` genesis frontier from the Memory
provider boundary, the boundary head-truth from `InitialBoundaryFacts`, and per-row `RowOK`
(whose `align8` comes from the state trail and whose `touches`/`chain_mono` need the aligned
`RowFacts` carrier discussed in the module doc); the per-row `RdGuardFact` comes from opcode
routing and `decodedInROM` from `supportedCore_orderedRows_programDecoded`.  Once those are
available, each row's `DynamicGroundedRow` is exactly
`DecodedInstructionRow.dynamicGrounded_of_contracts` fed by the walk's `Grounded` output and
`statePullTime_of_decodedStateWalk`.

```
theorem supportedCore_orderedRows_dynamic_of_contracts
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState)
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (boundary : InitialBoundaryFacts statement witness initial)
    (orderedRows : List (DecodedInstructionRow p))
    (exhaustive : orderedRows.Perm
      (realDecodedInstructionRows witness.data witness.tables))
    (stateWalk : Walk.IsWalk (decodedStateEdge witness.data)
      (initialBoundaryStateMessage statement.publicValues)
      (finalBoundaryStateMessage statement.publicValues) orderedRows)
    (contracts : ∀ chip ∈ supportedChips (p := p), ChipGroundingContracts chip) :
    ∀ done decoded suffix, orderedRows = done ++ decoded :: suffix →
      ∀ state, Target.SailChain done.length initial state →
        DynamicGroundedRow witness.data statement.program
          (decoded.toChipRow witness.data) state
```
-/

/-! ## The Add anchor -/

section AddAnchor

variable [Fact (2 ^ 25 < p)]

set_option maxHeartbeats 1000000 in
omit [Fact (2 ^ 25 < p)] in
/-- Add's reader passthrough, evaluated once: the decoded row's committed output `adapter` block is
the input `adapter` block (the elaborated output passes the reader columns through), which is the
first half of `AddChip.kind.advanceReady`. -/
theorem addChip_adapterPassthrough (env : Environment (ZMod p)) :
    ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env).adapter =
      ((⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env).adapter := by
  have inputEq : Eval.eval env (varFromOffset AddChip.Inputs 0) =
      (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowInput env :=
    eval_varFromOffset_valueFromOffset AddChip.Inputs 0 env
  have outputEq : Eval.eval env
      ((AddChip.circuit (p := p)).output (varFromOffset AddChip.Inputs 0)
        (size AddChip.Inputs)) =
      (⟨AddChip.circuit (p := p)⟩ : Component (ZMod p)).rowOutput env := by
    simp only [Component.rowOutput, circuit_norm]
  rw [← inputEq, ← outputEq]
  simp [AddChip.circuit, circuit_norm]

set_option maxHeartbeats 1000000 in
/-- **The Add bundle instance** — the rollout template.  Every field is assembled from the
already-landed `GroundingAdapter`/`AddChip.Contracts` closed forms; the only new evaluation is the
reader-passthrough readiness fact. -/
theorem addChip_groundingContracts :
    ChipGroundingContracts (⟨AddChip.kind, AddChip.circuit, rfl, [.ADD], .nonX0⟩ :
      SupportedChip p) where
  migrated := rfl
  operandPulls := addChip_registerOperandPullShape_descriptor
  wiring := by
    intro witness constraints balanced decoded hchip decodedMem real openInputs
    have realView : (decoded.toChipRow witness.data).view.is_real = 1 := real
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := addChip_viewClockBounds decoded witness.data hchip byteG realView
    have spec : (decoded.toChipRow witness.data).chipSpec witness.data :=
      decoded.chipSpec_of_openSoundnessInputs witness constraints balanced decodedMem openInputs
    have requirements := fullRequirements_of_openSoundnessInputs witness constraints balanced
      decoded decodedMem openInputs
    have consumed_eq := addChip_consumedMemoryMessages_eq decoded witness.data hchip realView
    have produced_eq := addChip_producedMemoryMessages_eq decoded witness.data hchip realView
    have writeU64 : Word.isU64 (decoded.toChipRow witness.data).view.rdWrite := by
      have hmem : rtypeWriteMessage (decoded.toChipRow witness.data).view ∈
          decoded.producedMemoryMessages witness.data := by
        rw [produced_eq]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      exact producedMemoryMessages_isU64_of_fullRequirements decoded witness.data requirements
        _ hmem
    have commit_eq : (decoded.toChipRow witness.data).view.commit =
        Trace.CommitEffect.regWrite := by
      obtain ⟨chip, physical⟩ := decoded
      have hchip' : chip = addChipDescriptor (p := p) := hchip
      subst hchip'
      rfl
    have opa_lt : (decoded.toChipRow witness.data).view.adapter.op_a.val < 32 := by
      obtain ⟨chip, physical⟩ := decoded
      have hchip' : chip = addChipDescriptor (p := p) := hchip
      subst hchip'
      -- Hypothesis-directed, metavariable-free (see `addRow_engineFacts`): extract the circuit
      -- `Spec` through the decoder's registered iff and destructure in place.
      obtain ⟨-, hrspec, -, -⟩ :=
        (SupportedChip.decodeRow_chipSpec_iff (addChipDescriptor (p := p))
          witness.data physical).mp spec
      obtain ⟨-, -, -, -, -, hbounds, -⟩ := hrspec
      exact (hbounds realView).1
    exact rowWiring_rtype_of_decoded decoded witness.data bounds commit_eq opa_lt
      writeU64 consumed_eq produced_eq
  chainSlots := by
    intro witness constraints balanced decoded hchip decodedMem real
    have realView : (decoded.toChipRow witness.data).view.is_real = 1 := real
    have byteG := decodedInstructionRow_byteGuarantees witness constraints balanced decoded
      decodedMem
    have bounds := addChip_viewClockBounds decoded witness.data hchip byteG realView
    have produced_eq := addChip_producedMemoryMessages_eq decoded witness.data hchip realView
    rw [produced_eq]
    have h3 := timeNat_rtypeReadBackMessage bounds
      ((decoded.toChipRow witness.data).view.adapter.op_b[0])
      (decoded.toChipRow witness.data).view.adapter.op_b_memory val_3_zmod_p (by omega)
    have h2 := timeNat_rtypeReadBackMessage bounds
      ((decoded.toChipRow witness.data).view.adapter.op_c[0])
      (decoded.toChipRow witness.data).view.adapter.op_c_memory val_2_zmod_p (by omega)
    have h4 := timeNat_rtypeWriteMessage bounds
    refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ (List.pairwise_singleton _ _))
    · intro b hb
      rcases List.mem_cons.mp hb with rfl | hb
      · rw [h3, h2]
        omega
      · rw [List.mem_singleton.mp hb, h3, h4]
        omega
    · intro b hb
      rw [List.mem_singleton.mp hb, h2, h4]
      omega
  assumptions := by
    intro witness constraints balanced decoded hchip decodedMem real
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addChipDescriptor (p := p) := hchip
    subst hchip'
    exact trivial
  readiness := by
    intro witness constraints balanced decoded hchip decodedMem real guard program state
    obtain ⟨chip, physical⟩ := decoded
    have hchip' : chip = addChipDescriptor (p := p) := hchip
    subst hchip'
    exact ⟨addChip_adapterPassthrough (Environment.fromArray physical witness.data), guard⟩

end AddAnchor

end SP1Clean.Soundness
