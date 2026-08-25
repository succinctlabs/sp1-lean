import SP1Clean.Proofs.Completeness.NativeTraceCompiler
import SP1Clean.Proofs.Completeness.ProviderInteractions

/-!
# Native compiler agreement with the built Memory tables

The execution compiler retains one chronological `MemoryHistoryAccess` stream.  The physical
ensemble does not: instruction accesses are partitioned across twenty-five tables, refreshes live
in `MemoryBump`, and the first and last records of every location live in the two boundary tables.
Given the named instruction-row and refresh-row projection seams, this module proves that the four
physical table components form exactly the canonical history ledger, up to permutation, and then
regroups that history by location into `memoryHandoffChains`.

The regrouping is a theorem about the deterministic compiler output.  It is not an admissibility
field and it does not use channel balance.
-/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels
open SP1Clean.Execution
open SP1Clean.LookupAccessList
open SP1Clean.Semantics
open SP1Clean.TraceGen

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance nativeMemoryAgreementFieldBound : Fact (2 ^ 24 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

private theorem scheduledAccess_separated_perm (base : ℕ) (access : ScheduledAccess) :
    ([MemoryHistoryAccess.ofStamped base access.stamped] ++
        access.memoryBump?.toList.map MemoryHistoryAccess.ofMemoryBump).Perm
      (MemoryHistoryAccess.ofScheduledAccess base access) := by
  rw [MemoryHistoryAccess.ofScheduledAccess]
  exact List.perm_append_comm

/-- Splitting one schedule into its instruction rows and refresh rows changes only physical order. -/
theorem accessSchedule_instruction_bump_perm (base : ℕ) (schedule : AccessSchedule) :
    ((schedule.stampedTouches.map (MemoryHistoryAccess.ofStamped base)) ++
        (schedule.memoryBumps.map MemoryHistoryAccess.ofMemoryBump)).Perm
      (MemoryHistoryAccess.ofAccessSchedule base schedule) := by
  rw [AccessSchedule.stampedTouches, AccessSchedule.memoryBumps,
    MemoryHistoryAccess.ofAccessSchedule, List.filterMap_eq_flatMap_toList,
    List.map_flatMap]
  simp only [List.map_map]
  refine (List.map_append_flatMap_perm schedule.accesses
    (fun access => MemoryHistoryAccess.ofStamped base access.stamped)
    (fun access => access.memoryBump?.toList.map MemoryHistoryAccess.ofMemoryBump)).trans ?_
  exact List.Perm.flatMap_left _ fun access _ => scheduledAccess_separated_perm base access

/-- Globally separating instruction and MemoryBump tables preserves the compiler's one history. -/
theorem compiledInstructionBumpHistoryPerm (compiled : CompiledExecution) :
    (compiled.instructionMemoryHistory ++ compiled.bumpMemoryHistory).Perm
      compiled.memoryHistory := by
  unfold CompiledExecution.instructionMemoryHistory CompiledExecution.bumpMemoryHistory
    CompiledExecution.memoryHistory CompiledExecution.memoryBumps
  rw [List.map_flatMap]
  refine (List.flatMap_append_perm compiled.rows
    (fun row => row.instruction.stamped.map
      (MemoryHistoryAccess.ofStamped row.clock))
    (fun row => row.instruction.memoryBumps.map
      MemoryHistoryAccess.ofMemoryBump)).trans ?_
  exact List.Perm.flatMap_left _ fun row _ =>
    accessSchedule_instruction_bump_perm row.clock row.instruction.schedule

omit [Fact (2 ^ 25 < p)] in
/-- The same split after projecting every history transition to its active pull/push pair. -/
theorem compiledInstructionBumpLedgerPerm (compiled : CompiledExecution) :
    ((compiled.instructionMemoryHistory.flatMap (MemoryHistoryAccess.ledger (p := p))) ++
        (compiled.bumpMemoryHistory.flatMap (MemoryHistoryAccess.ledger (p := p)))).Perm
      (compiled.memoryHistory.flatMap (MemoryHistoryAccess.ledger (p := p))) := by
  rw [← List.flatMap_append]
  exact (compiledInstructionBumpHistoryPerm compiled).flatMap_right _

/-! ## Canonical boundary regrouping -/

/-- The active init-provider access attached to one canonical location history. -/
def memoryLocationInitialAccess (history : MemoryLocationHistory) : LookupAccess :=
  accessAt (MemoryHistoryAccess.entryKey (p := p) history.initialEntry) 1

/-- The active finalize-provider access attached to one canonical location history. -/
def memoryLocationFinalAccess (history : MemoryLocationHistory) : LookupAccess :=
  accessAt (MemoryHistoryAccess.entryKey (p := p) history.finalEntry) (-1)

omit [Fact (2 ^ 25 < p)] in
@[simp] theorem MemoryLocationHistory.chainLedger_handoffChain
    (history : MemoryLocationHistory) :
    chainLedger (history.handoffChain (p := p)) =
      [memoryLocationInitialAccess (p := p) history,
        memoryLocationFinalAccess (p := p) history] ++
        history.accesses.flatMap (MemoryHistoryAccess.ledger (p := p)) := by
  simp only [chainLedger, MemoryLocationHistory.handoffChain,
    memoryLocationInitialAccess, memoryLocationFinalAccess, List.flatMap_map]
  rfl

omit [Fact (2 ^ 25 < p)] in
/-- Boundary rows plus the chronological access ledger are precisely the canonical per-location
chain ledgers.  This is the structural regrouping theorem; chronology is deliberately absent. -/
theorem memory_boundary_history_ledger_perm (stream : List MemoryHistoryAccess) :
    (((memoryInitialEntries stream).map fun entry =>
          accessAt (MemoryHistoryAccess.entryKey (p := p) entry) 1) ++
      (((memoryFinalEntries stream).map fun entry =>
          accessAt (MemoryHistoryAccess.entryKey (p := p) entry) (-1)) ++
        stream.flatMap (MemoryHistoryAccess.ledger (p := p)))).Perm
      ((memoryHandoffChains (p := p) stream).flatMap chainLedger) := by
  let histories := memoryLocationHistories stream
  have streamPerm := memoryStream_perm_locationHistories stream
  have accessPerm :
      (stream.flatMap (MemoryHistoryAccess.ledger (p := p))).Perm
        (histories.flatMap fun history =>
          history.accesses.flatMap (MemoryHistoryAccess.ledger (p := p))) :=
    by
      have projected :=
        streamPerm.flatMap_right (MemoryHistoryAccess.ledger (p := p))
      rw [List.flatMap_assoc] at projected
      simpa only [histories] using projected
  have boundaryPerm :
      ((histories.map fun history => memoryLocationInitialAccess (p := p) history) ++
        (histories.map fun history => memoryLocationFinalAccess (p := p) history)).Perm
      (histories.flatMap fun history =>
        [memoryLocationInitialAccess (p := p) history,
          memoryLocationFinalAccess (p := p) history]) := by
    simpa only [← List.map_eq_flatMap] using
      List.map_append_flatMap_perm histories
        (fun history => memoryLocationInitialAccess (p := p) history)
        (fun history => [memoryLocationFinalAccess (p := p) history])
  have allPerm := (boundaryPerm.append_right
      (stream.flatMap (MemoryHistoryAccess.ledger (p := p)))).trans
    ((List.Perm.refl _).append accessPerm)
  have grouped := allPerm.trans (List.flatMap_append_perm histories
    (fun history => [memoryLocationInitialAccess (p := p) history,
      memoryLocationFinalAccess (p := p) history])
    (fun history => history.accesses.flatMap
      (MemoryHistoryAccess.ledger (p := p))))
  simpa [histories, memoryInitialEntries, memoryFinalEntries, Function.comp_def,
    memoryLocationInitialAccess, memoryLocationFinalAccess, List.append_assoc,
    memoryHandoffChains, List.flatMap_map,
    MemoryLocationHistory.chainLedger_handoffChain] using grouped

/-! ## Boundary-provider rows -/

/-- Clean-oriented access emitted by one decoded Memory-init input. -/
private def memoryInitInputCleanAccess
    (input : MemoryProviderChip.Inputs (ZMod p)) : LookupAccess :=
  (InteractionKind.Memory, "SP1Memory",
    [input.clk_high.val, input.clk_low.val, input.addr0.val, input.addr1.val,
      input.addr2.val, input.value[0].val, input.value[1].val, input.value[2].val,
      input.value[3].val],
    signedVal input.multiplicity)

/-- Clean-oriented access emitted by one decoded Memory-finalize input. -/
private def memoryFinalizeInputCleanAccess
    (input : MemoryFinalizeChip.Inputs (ZMod p)) : LookupAccess :=
  (InteractionKind.Memory, "SP1Memory",
    [input.clk_high.val, input.clk_low.val, input.addr0.val, input.addr1.val,
      input.addr2.val, input.value[0].val, input.value[1].val, input.value[2].val,
      input.value[3].val],
    signedVal (- input.multiplicity))

omit [Fact (2 ^ 25 < p)] in
private theorem memoryProviderEvalToMessage
    (env : Environment (ZMod p))
    (input : Var MemoryProviderChip.Inputs (ZMod p)) :
    ProvableStruct.eval env
        (input.toMessage : MemoryMsg (Expression (ZMod p))) =
      (Eval.eval env input).toMessage := by
  rw [← ProvableStruct.eval_field_var_eq_eval]
  cases input
  simp only [MemoryProviderChip.Inputs.toMessage, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem memoryFinalizeEvalToMessage
    (env : Environment (ZMod p))
    (input : Var MemoryFinalizeChip.Inputs (ZMod p)) :
    ProvableStruct.eval env
        (input.toMessage : MemoryMsg (Expression (ZMod p))) =
      (Eval.eval env input).toMessage := by
  rw [← ProvableStruct.eval_field_var_eq_eval]
  cases input
  simp only [MemoryFinalizeChip.Inputs.toMessage, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem memoryProviderToAccessEqInputCleanAccess
    (env : Environment (ZMod p))
    (input : Var MemoryProviderChip.Inputs (ZMod p)) :
    AbstractInteraction.toAccess env
        (pushedIf (channel := memoryChannel) input.multiplicity input.toMessage).toRaw =
      memoryInitInputCleanAccess (Eval.eval env input) := by
  rw [toAccess_pushIf_memory]
  simp only [memoryInitInputCleanAccess, circuit_norm]
  rw [memoryProviderEvalToMessage]
  have evaluated := ProvableStruct.eval_var_eq_eval env input
  simp only [MemoryProviderChip.Inputs.toMessage]
  rw [congrArg MemoryProviderChip.Inputs.clk_high evaluated,
    congrArg MemoryProviderChip.Inputs.clk_low evaluated,
    congrArg MemoryProviderChip.Inputs.addr0 evaluated,
    congrArg MemoryProviderChip.Inputs.addr1 evaluated,
    congrArg MemoryProviderChip.Inputs.addr2 evaluated,
    congrArg (fun x : MemoryProviderChip.Inputs (ZMod p) => x.value[0]) evaluated,
    congrArg (fun x : MemoryProviderChip.Inputs (ZMod p) => x.value[1]) evaluated,
    congrArg (fun x : MemoryProviderChip.Inputs (ZMod p) => x.value[2]) evaluated,
    congrArg (fun x : MemoryProviderChip.Inputs (ZMod p) => x.value[3]) evaluated]

omit [Fact (2 ^ 25 < p)] in
private theorem memoryFinalizeToAccessEqInputCleanAccess
    (env : Environment (ZMod p))
    (input : Var MemoryFinalizeChip.Inputs (ZMod p)) :
    AbstractInteraction.toAccess env
        (pulledIf (channel := memoryChannel) input.multiplicity input.toMessage).toRaw =
      memoryFinalizeInputCleanAccess (Eval.eval env input) := by
  rw [toAccess_pullIf_memory]
  simp only [memoryFinalizeInputCleanAccess, circuit_norm]
  rw [memoryFinalizeEvalToMessage]
  have evaluated := ProvableStruct.eval_var_eq_eval env input
  simp only [MemoryFinalizeChip.Inputs.toMessage]
  rw [congrArg MemoryFinalizeChip.Inputs.clk_high evaluated,
    congrArg MemoryFinalizeChip.Inputs.clk_low evaluated,
    congrArg MemoryFinalizeChip.Inputs.addr0 evaluated,
    congrArg MemoryFinalizeChip.Inputs.addr1 evaluated,
    congrArg MemoryFinalizeChip.Inputs.addr2 evaluated,
    congrArg (fun x : MemoryFinalizeChip.Inputs (ZMod p) => x.value[0]) evaluated,
    congrArg (fun x : MemoryFinalizeChip.Inputs (ZMod p) => x.value[1]) evaluated,
    congrArg (fun x : MemoryFinalizeChip.Inputs (ZMod p) => x.value[2]) evaluated,
    congrArg (fun x : MemoryFinalizeChip.Inputs (ZMod p) => x.value[3]) evaluated]

omit [Fact (2 ^ 25 < p)] in
private theorem wordToList {T : Type} (word : Vector T 4) :
    word.toList = [word[0], word[1], word[2], word[3]] := by
  apply List.ext_getElem (by simp)
  intro i _ indexBound
  simp only [List.length_cons, List.length_nil] at indexBound
  interval_cases i <;> simp

omit [Fact (2 ^ 25 < p)] in
private theorem memoryMsgElements {T : Type} (message : MemoryMsg T) :
    (toElements message).toList =
      [message.clk_high, message.clk_low, message.addr0, message.addr1, message.addr2,
        message.value[0], message.value[1], message.value[2], message.value[3]] := by
  change (#v[message.clk_high] ++ (#v[message.clk_low] ++ (#v[message.addr0] ++
    (#v[message.addr1] ++ (#v[message.addr2] ++
      (message.value ++ (#v[] : Vector T 0))))))).toList = _
  simp only [Vector.toList_append, Vector.toList_mk, List.append_nil,
    List.cons_append, List.nil_append]
  rw [wordToList]

omit [Fact (2 ^ 25 < p)] in
private theorem accessAtEntryKey (entry : MemRecordEntry) (multiplicity : ℤ) :
    accessAt (MemoryHistoryAccess.entryKey (p := p) entry) multiplicity =
      (InteractionKind.Memory, "SP1Memory",
        [(entry.toMemoryMsg (p := p)).clk_high.val,
          (entry.toMemoryMsg (p := p)).clk_low.val,
          (entry.toMemoryMsg (p := p)).addr0.val,
          (entry.toMemoryMsg (p := p)).addr1.val,
          (entry.toMemoryMsg (p := p)).addr2.val,
          (entry.toMemoryMsg (p := p)).value[0].val,
          (entry.toMemoryMsg (p := p)).value[1].val,
          (entry.toMemoryMsg (p := p)).value[2].val,
          (entry.toMemoryMsg (p := p)).value[3].val], multiplicity) := by
  unfold MemoryHistoryAccess.entryKey accessAt
  rw [memoryMsgElements]
  simp only [List.map_cons, List.map_nil]

omit [Fact (2 ^ 25 < p)] in
private theorem memoryInitInputCleanAccessOfEntry (entry : MemRecordEntry) :
    memoryInitInputCleanAccess (MemoryProviderChip.ofEntry (p := p) entry) =
      accessAt (MemoryHistoryAccess.entryKey (p := p) entry)
        (signedVal (entry.multiplicityField (p := p))) := by
  rw [accessAtEntryKey]
  simp only [memoryInitInputCleanAccess, MemoryProviderChip.ofEntry]

omit [Fact (2 ^ 25 < p)] in
private theorem memoryFinalizeInputCleanAccessOfEntry (entry : MemRecordEntry) :
    memoryFinalizeInputCleanAccess (MemoryFinalizeChip.ofEntry (p := p) entry) =
      accessAt (MemoryHistoryAccess.entryKey (p := p) entry)
        (signedVal (-(entry.multiplicityField (p := p)))) := by
  rw [accessAtEntryKey]
  simp only [memoryFinalizeInputCleanAccess, MemoryFinalizeChip.ofEntry]

omit [Fact (2 ^ 25 < p)] in
/-- Recovering a typed Memory message from a raw Clean interaction preserves its literal key. -/
theorem keyOf_toAccess_typedMemory
    (interaction : TypedInteraction (memoryChannel (p := p))) :
    keyOf (Interaction.toAccess interaction.raw) =
      msgToken memoryChannel interaction.message := by
  have messageEq : interaction.raw.msg = (toElements interaction.message).toArray :=
    (TypedInteraction.message_eq_iff interaction interaction.message).mp rfl
  change (kindOf interaction.raw.channel.name, interaction.raw.channel.name,
      interaction.raw.msg.toList.map ZMod.val) = _
  rw [interaction.channel_eq, messageEq]
  rfl

omit [Fact (2 ^ 25 < p)] in
/-- A typed Memory token retains every field of its message. -/
theorem msgToken_memory_injective :
    Function.Injective (msgToken (memoryChannel (p := p))) := by
  intro left right tokenEq
  have valuesEq : (toElements left).toList.map ZMod.val =
      (toElements right).toList.map ZMod.val := by
    simpa only [msgToken] using congrArg (fun key : LookupKey => key.2.2) tokenEq
  have elementsEq : (toElements left).toList = (toElements right).toList :=
    (List.map_injective_iff.mpr (ZMod.val_injective p)) valuesEq
  have vectorsEq : toElements left = toElements right := Vector.toList_inj.mp elementsEq
  calc
    left = fromElements (toElements left) := ProvableType.fromElements_toElements left |>.symm
    _ = fromElements (toElements right) := congrArg fromElements vectorsEq
    _ = right := ProvableType.fromElements_toElements right

omit [Fact (2 ^ 25 < p)] in
@[simp] theorem MemoryHistoryAccess.entryKey_eq_msgToken (entry : MemRecordEntry) :
    MemoryHistoryAccess.entryKey (p := p) entry =
      msgToken memoryChannel (entry.toMemoryMsg (p := p)) := by
  simp only [MemoryHistoryAccess.entryKey, msgToken, memoryChannel, kindOf, if_true]

omit [Fact (2 ^ 25 < p)] in
/-- An exact access-ledger projection recovers the corresponding typed Memory messages. -/
theorem typedMemoryMessages_of_accessLedger
    (interactions : List (TypedInteraction (memoryChannel (p := p))))
    (entries : List MemRecordEntry) (multiplicity : MemRecordEntry → ℤ)
    (ledgerEq : interactions.map (fun interaction => Interaction.toAccess interaction.raw) =
      entries.map fun entry =>
        accessAt (MemoryHistoryAccess.entryKey (p := p) entry) (multiplicity entry)) :
    interactions.map TypedInteraction.message =
      entries.map (MemRecordEntry.toMemoryMsg (p := p)) := by
  induction interactions generalizing entries with
  | nil =>
      cases entries with
      | nil => rfl
      | cons entry rest => simp at ledgerEq
  | cons interaction rest ih =>
      cases entries with
      | nil => simp at ledgerEq
      | cons entry entries =>
          simp only [List.map_cons, List.cons.injEq] at ledgerEq
          obtain ⟨headEq, tailEq⟩ := ledgerEq
          have tokenEq := congrArg keyOf headEq
          rw [keyOf_toAccess_typedMemory, keyOf_accessAt,
            MemoryHistoryAccess.entryKey_eq_msgToken] at tokenEq
          have messageEq := msgToken_memory_injective tokenEq
          simp only [List.map_cons, messageEq, List.cons.injEq, true_and]
          exact ih entries tailEq

/-- A canonical field-free location round-trips through the provider's three address limbs. -/
theorem MemoryHistoryAccess.locOf_toMemoryMsg_of_busAddress
    (loc : MemLoc) (canonical : MemoryHistoryAccess.CanonicalAddress loc)
    (entry : MemRecordEntry)
    (address : entry.addr = MemoryHistoryAccess.busAddress loc) :
    MemoryMsg.locOf (entry.toMemoryMsg (p := p)) = loc := by
  cases loc with
  | reg index =>
      apply MemoryMsg.locOf_register _ index
      · simp only [MemRecordEntry.toMemoryMsg, address, MemoryHistoryAccess.busAddress]
        rw [Nat.mod_eq_of_lt (lt_trans index.isLt (by norm_num))]
      · simp only [MemRecordEntry.toMemoryMsg, address, MemoryHistoryAccess.busAddress]
        have indexLt : index.toNat < 2 ^ 16 := lt_trans index.isLt (by norm_num)
        rw [Nat.div_eq_of_lt indexLt]
        norm_num
      · simp only [MemRecordEntry.toMemoryMsg, address, MemoryHistoryAccess.busAddress]
        have indexLt : index.toNat < 2 ^ 32 := lt_trans index.isLt (by norm_num)
        rw [Nat.div_eq_of_lt indexLt]
        norm_num
  | ram cell =>
      simp only [MemoryHistoryAccess.CanonicalAddress] at canonical
      let base := cell.toNat * 8
      have hp : 2 ^ 16 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
      have lowLt : base % 2 ^ 16 < p :=
        lt_trans (Nat.mod_lt _ (by norm_num)) hp
      have midLt : base / 2 ^ 16 % 2 ^ 16 < p :=
        lt_trans (Nat.mod_lt _ (by norm_num)) hp
      have highLt : base / 2 ^ 32 % 2 ^ 16 < p :=
        lt_trans (Nat.mod_lt _ (by norm_num)) hp
      have recombine :
          (base % 2 ^ 16) + (base / 2 ^ 16 % 2 ^ 16) * 2 ^ 16 +
              (base / 2 ^ 32 % 2 ^ 16) * 2 ^ 32 = base := by
        have baseLt : base < 2 ^ 48 := by simpa only [base] using canonical.2
        omega
      unfold MemoryMsg.locOf
      simp only [MemRecordEntry.toMemoryMsg, address, MemoryHistoryAccess.busAddress,
        show cell.toNat * 8 = base from rfl]
      rw [ZMod.val_natCast_of_lt lowLt, ZMod.val_natCast_of_lt midLt,
        ZMod.val_natCast_of_lt highLt]
      rw [if_neg]
      · congr 1
        apply BitVec.eq_of_toNat_eq
        simp only [BitVec.toNat_ofNat]
        rw [recombine]
        simp [base, cell.isLt]
      · rintro ⟨lowSmall, midZero, highZero⟩
        have midValZero := congrArg ZMod.val midZero
        rw [ZMod.val_natCast_of_lt midLt] at midValZero
        simp only [ZMod.val_zero] at midValZero
        have highValZero := congrArg ZMod.val highZero
        rw [ZMod.val_natCast_of_lt highLt] at highValZero
        simp only [ZMod.val_zero] at highValZero
        have baseLower : 32 ≤ base := by simpa only [base] using canonical.1
        omega

/-- One honestly built Memory-init row emits its canonical boundary push. -/
theorem memoryInitBuildRowCleanAccesses
    (entry : MemRecordEntry) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (MemoryProviderChip.component (p := p)).operations.interactions.map
        (AbstractInteraction.toAccess
          (Environment.fromArray
            ((MemoryProviderChip.component (p := p)).buildRow
              (MemoryProviderChip.ofEntry (p := p) entry) data hint) data)) =
      [accessAt (MemoryHistoryAccess.entryKey (p := p) entry)
        (signedVal (entry.multiplicityField (p := p)))] := by
  let component := MemoryProviderChip.component (p := p)
  let input := MemoryProviderChip.ofEntry (p := p) entry
  let env := Environment.fromArray (component.buildRow input data hint) data
  rw [interactions_eq_interactionsWith_of_onlyChannel _ memoryChannel.toRaw
      Ledger.onlyChannel_MemoryProvider]
  unfold MemoryProviderChip.component
  rw [Component.interactionsWith_eq, Component.rowOperations_mk,
    show (MemoryProviderChip.circuit (p := p)).main = MemoryProviderChip.main from rfl,
    memoryInitProvider_memoryInteractions]
  simp only [List.map_cons, List.map_nil]
  rw [memoryProviderToAccessEqInputCleanAccess]
  change [memoryInitInputCleanAccess (Eval.eval env
    (varFromOffset MemoryProviderChip.Inputs 0 :
      Var MemoryProviderChip.Inputs (ZMod p)))] = _
  have decoded := component.rowInput_buildRow input data data hint
  change valueFromOffset MemoryProviderChip.Inputs 0 env = input at decoded
  have evaluated : Eval.eval env
      (varFromOffset MemoryProviderChip.Inputs 0 :
        Var MemoryProviderChip.Inputs (ZMod p)) = input :=
    (eval_varFromOffset_valueFromOffset MemoryProviderChip.Inputs 0 env).trans decoded
  rw [evaluated]
  rw [memoryInitInputCleanAccessOfEntry]

/-- One honestly built Memory-finalize row emits its canonical boundary pull. -/
theorem memoryFinalizeBuildRowCleanAccesses
    (entry : MemRecordEntry) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p)) :
    (MemoryFinalizeChip.component (p := p)).operations.interactions.map
        (AbstractInteraction.toAccess
          (Environment.fromArray
            ((MemoryFinalizeChip.component (p := p)).buildRow
              (MemoryFinalizeChip.ofEntry (p := p) entry) data hint) data)) =
      [accessAt (MemoryHistoryAccess.entryKey (p := p) entry)
        (signedVal (-(entry.multiplicityField (p := p))))] := by
  let component := MemoryFinalizeChip.component (p := p)
  let input := MemoryFinalizeChip.ofEntry (p := p) entry
  let env := Environment.fromArray (component.buildRow input data hint) data
  rw [interactions_eq_interactionsWith_of_onlyChannel _ memoryChannel.toRaw
      Ledger.onlyChannel_MemoryFinalize]
  unfold MemoryFinalizeChip.component
  rw [Component.interactionsWith_eq, Component.rowOperations_mk,
    show (MemoryFinalizeChip.circuit (p := p)).main = MemoryFinalizeChip.main from rfl,
    memoryFinalizeProvider_memoryInteractions]
  simp only [List.map_cons, List.map_nil]
  rw [memoryFinalizeToAccessEqInputCleanAccess]
  change [memoryFinalizeInputCleanAccess (Eval.eval env
    (varFromOffset MemoryFinalizeChip.Inputs 0 :
      Var MemoryFinalizeChip.Inputs (ZMod p)))] = _
  have decoded := component.rowInput_buildRow input data data hint
  change valueFromOffset MemoryFinalizeChip.Inputs 0 env = input at decoded
  have evaluated : Eval.eval env
      (varFromOffset MemoryFinalizeChip.Inputs 0 :
        Var MemoryFinalizeChip.Inputs (ZMod p)) = input :=
    (eval_varFromOffset_valueFromOffset MemoryFinalizeChip.Inputs 0 env).trans decoded
  rw [evaluated]
  rw [memoryFinalizeInputCleanAccessOfEntry]

/-! ## Boundary-table projections -/

/-- The stable Memory-init witness position is the trace's generated init table. -/
theorem SupportedCoreTraceWitness.memoryInitProviderTable_witness
    (trace : SupportedCoreTraceWitness p) :
    memoryInitProviderTable trace.witness = trace.providerTableFor .memoryInit := by
  unfold memoryInitProviderTable SupportedCoreTraceWitness.witness
  simp [SupportedCoreTraceWitness.tables, SupportedCoreTraceWitness.instructionTables,
    SupportedCoreTraceWitness.providerTables, memoryInitProviderIndex, programProviderIndex,
    instructionTableCount,
    byteProviderTableCount, rangeProviderTableCount, InstructionChipId.all,
    ProviderTableId.all, ByteProviderId.all]

/-- The stable Memory-finalize witness position is the trace's generated final table. -/
theorem SupportedCoreTraceWitness.memoryFinalizeProviderTable_witness
    (trace : SupportedCoreTraceWitness p) :
    memoryFinalizeProviderTable trace.witness =
      trace.providerTableFor .memoryFinalize := by
  unfold memoryFinalizeProviderTable SupportedCoreTraceWitness.witness
  simp [SupportedCoreTraceWitness.tables, SupportedCoreTraceWitness.instructionTables,
    SupportedCoreTraceWitness.providerTables, memoryFinalizeProviderIndex,
    programProviderIndex, instructionTableCount, byteProviderTableCount,
    rangeProviderTableCount, InstructionChipId.all, ProviderTableId.all, ByteProviderId.all]

/-- The literal Clean ledger of a generated Memory-init table is its entry-key push list. -/
theorem SupportedCoreTraceWitness.memoryInitTableCleanAccesses
    (trace : SupportedCoreTraceWitness p) :
    tableCleanAccesses (memoryInitProviderTable trace.witness) =
      (trace.providerOccurrences .memoryInit).map fun entry =>
        accessAt (MemoryHistoryAccess.entryKey (p := p) entry)
          (signedVal (entry.multiplicityField (p := p))) := by
  rw [trace.memoryInitProviderTable_witness]
  unfold SupportedCoreTraceWitness.providerTableFor MemoryProviderChip.traceInputs
  apply tableCleanAccesses_build_map_singleton
  intro entry _
  exact memoryInitBuildRowCleanAccesses entry trace.data trace.hint

/-- The literal Clean ledger of a generated Memory-finalize table is its entry-key pull list. -/
theorem SupportedCoreTraceWitness.memoryFinalizeTableCleanAccesses
    (trace : SupportedCoreTraceWitness p) :
    tableCleanAccesses (memoryFinalizeProviderTable trace.witness) =
      (trace.providerOccurrences .memoryFinalize).map fun entry =>
        accessAt (MemoryHistoryAccess.entryKey (p := p) entry)
          (signedVal (-(entry.multiplicityField (p := p)))) := by
  rw [trace.memoryFinalizeProviderTable_witness]
  unfold SupportedCoreTraceWitness.providerTableFor MemoryFinalizeChip.traceInputs
  apply tableCleanAccesses_build_map_singleton
  intro entry _
  exact memoryFinalizeBuildRowCleanAccesses entry trace.data trace.hint

omit [Fact (2 ^ 25 < p)] in
/-- On a single-channel table, the typed-channel access projection is the literal Clean ledger. -/
theorem typedTableAccessLedgerEqClean
    {Message : TypeMap} [ProvableType Message]
    (table : Table (ZMod p)) (channel : Channel (ZMod p) Message)
    (only : table.component.operations.interactions =
      table.component.operations.interactionsWith channel.toRaw) :
    ((typedTableInteractionsWith table channel).map fun interaction =>
        Interaction.toAccess interaction.raw) = tableCleanAccesses table := by
  have erased := congrArg (List.map Interaction.toAccess)
    (typedTableInteractionsWith_raw table channel)
  simp only [List.map_map, Function.comp_def] at erased
  rw [erased]
  unfold tableCleanAccesses Table.interactionsWith Table.interactions
  simp only [List.map_flatMap, Operations.interactionValuesWith_eq_map,
    Operations.interactionValues, List.map_map, Function.comp_def, only]

/-- Actual typed init-table accesses equal the canonical entry-key pushes. -/
theorem SupportedCoreTraceWitness.memoryInitTableAccessLedger
    (trace : SupportedCoreTraceWitness p) :
    (typedTableInteractionsWith (memoryInitProviderTable trace.witness)
      memoryChannel).map (fun interaction => Interaction.toAccess interaction.raw) =
      (trace.providerOccurrences .memoryInit).map fun entry =>
        accessAt (MemoryHistoryAccess.entryKey (p := p) entry)
          (signedVal (entry.multiplicityField (p := p))) := by
  rw [trace.memoryInitProviderTable_witness]
  calc
    _ = tableCleanAccesses (trace.providerTableFor .memoryInit) := by
      apply typedTableAccessLedgerEqClean
      exact interactions_eq_interactionsWith_of_onlyChannel _ memoryChannel.toRaw
        Ledger.onlyChannel_MemoryProvider
    _ = _ := by simpa only [trace.memoryInitProviderTable_witness] using
      trace.memoryInitTableCleanAccesses

/-- Actual typed finalize-table accesses equal the canonical entry-key pulls. -/
theorem SupportedCoreTraceWitness.memoryFinalizeTableAccessLedger
    (trace : SupportedCoreTraceWitness p) :
    (typedTableInteractionsWith (memoryFinalizeProviderTable trace.witness)
      memoryChannel).map (fun interaction => Interaction.toAccess interaction.raw) =
      (trace.providerOccurrences .memoryFinalize).map fun entry =>
        accessAt (MemoryHistoryAccess.entryKey (p := p) entry)
          (signedVal (-(entry.multiplicityField (p := p)))) := by
  rw [trace.memoryFinalizeProviderTable_witness]
  calc
    _ = tableCleanAccesses (trace.providerTableFor .memoryFinalize) := by
      apply typedTableAccessLedgerEqClean
      exact interactions_eq_interactionsWith_of_onlyChannel _ memoryChannel.toRaw
        Ledger.onlyChannel_MemoryFinalize
    _ = _ := by simpa only [trace.memoryFinalizeProviderTable_witness] using
      trace.memoryFinalizeTableCleanAccesses

/-- The typed init-table messages are exactly the messages of its canonical source entries. -/
theorem SupportedCoreTraceWitness.memoryInitTableMessages
    (trace : SupportedCoreTraceWitness p) :
    (typedTableInteractionsWith (memoryInitProviderTable trace.witness)
      memoryChannel).map TypedInteraction.message =
      (trace.providerOccurrences .memoryInit).map
        (MemRecordEntry.toMemoryMsg (p := p)) := by
  exact typedMemoryMessages_of_accessLedger _ _
    (fun entry => signedVal (entry.multiplicityField (p := p)))
    trace.memoryInitTableAccessLedger

/-- The typed finalize-table messages are exactly the messages of its canonical source entries. -/
theorem SupportedCoreTraceWitness.memoryFinalizeTableMessages
    (trace : SupportedCoreTraceWitness p) :
    (typedTableInteractionsWith (memoryFinalizeProviderTable trace.witness)
      memoryChannel).map TypedInteraction.message =
      (trace.providerOccurrences .memoryFinalize).map
        (MemRecordEntry.toMemoryMsg (p := p)) := by
  exact typedMemoryMessages_of_accessLedger _ _
    (fun entry => signedVal (-(entry.multiplicityField (p := p))))
    trace.memoryFinalizeTableAccessLedger

private theorem canonicalHistoryLocation {stream : List MemoryHistoryAccess}
    (canonical : MemoryAddressesCanonical stream) {history : MemoryLocationHistory}
    (member : history ∈ memoryLocationHistories stream) :
    MemoryHistoryAccess.CanonicalAddress history.loc := by
  apply canonical_of_mem_touched canonical
  rw [← memoryLocationHistories_map_loc]
  exact List.mem_map_of_mem member

/-- A field-free genesis fact lifts one canonical init entry to the typed provider contract. -/
theorem memoryInitialEntry_messageBound {initial : SailState} {initialClock : ℕ}
    {stream : List MemoryHistoryAccess}
    (canonical : MemoryAddressesCanonical stream)
    (genesis : NativeMemoryGenesis initial stream)
    {entry : MemRecordEntry} (member : entry ∈ memoryInitialEntries stream) :
    MemoryInitMessageBound initial initialClock (entry.toMemoryMsg (p := p)) := by
  obtain ⟨history, historyMem, rfl⟩ := List.mem_map.mp member
  have genesisHistory := genesis history historyMem
  constructor
  · rw [MemoryHistoryAccess.locOf_toMemoryMsg_of_busAddress history.loc
      (canonicalHistoryLocation canonical historyMem) history.initialEntry rfl]
    change SP1Clean.Semantics.locContent initial history.loc =
      some (Word.toBitVec64 (wordOfNat (p := p) history.initialEntry.value))
    rw [TraceGen.toBitVec64_wordOfNat]
    simpa only [MemoryLocationHistory.initialEntry, BitVec.ofNat_toNat,
      BitVec.setWidth_eq] using genesisHistory
  · simp only [MemoryMsg.timeNat, SP1Clean.Semantics.clkNat,
      MemRecordEntry.toMemoryMsg, MemoryLocationHistory.initialEntry, Nat.zero_div,
      Nat.cast_zero, ZMod.val_zero, zero_mul, Nat.zero_mod, zero_add, Nat.zero_le]

/-- Canonical init-entry messages are pairwise distinct at the semantic `MemLoc` granularity. -/
theorem memoryInitialEntries_messages_pairwise {stream : List MemoryHistoryAccess}
    (canonical : MemoryAddressesCanonical stream) :
    ((memoryInitialEntries stream).map
      (MemRecordEntry.toMemoryMsg (p := p))).Pairwise
        (fun left right => MemoryMsg.locOf left ≠ MemoryMsg.locOf right) := by
  have pairwiseLocations : (memoryLocationHistories stream).Pairwise
      (fun left right => left.loc ≠ right.loc) := by
    rw [← List.pairwise_map]
    exact List.nodup_iff_pairwise_ne.mp (memoryLocationHistories_nodup stream)
  simp only [memoryInitialEntries, List.map_map, List.pairwise_map]
  refine pairwiseLocations.imp_of_mem ?_
  intro left right leftMem rightMem distinct
  change MemoryMsg.locOf (left.initialEntry.toMemoryMsg (p := p)) ≠
    MemoryMsg.locOf (right.initialEntry.toMemoryMsg (p := p))
  rw [MemoryHistoryAccess.locOf_toMemoryMsg_of_busAddress left.loc
      (canonicalHistoryLocation canonical leftMem) left.initialEntry rfl,
    MemoryHistoryAccess.locOf_toMemoryMsg_of_busAddress right.loc
      (canonicalHistoryLocation canonical rightMem) right.initialEntry rfl]
  exact distinct

/-- Canonical finalize-entry messages are pairwise distinct at the semantic `MemLoc` granularity. -/
theorem memoryFinalEntries_messages_pairwise {stream : List MemoryHistoryAccess}
    (canonical : MemoryAddressesCanonical stream) :
    ((memoryFinalEntries stream).map
      (MemRecordEntry.toMemoryMsg (p := p))).Pairwise
        (fun left right => MemoryMsg.locOf left ≠ MemoryMsg.locOf right) := by
  have pairwiseLocations : (memoryLocationHistories stream).Pairwise
      (fun left right => left.loc ≠ right.loc) := by
    rw [← List.pairwise_map]
    exact List.nodup_iff_pairwise_ne.mp (memoryLocationHistories_nodup stream)
  simp only [memoryFinalEntries, List.map_map, List.pairwise_map]
  refine pairwiseLocations.imp_of_mem ?_
  intro left right leftMem rightMem distinct
  change MemoryMsg.locOf (left.finalEntry.toMemoryMsg (p := p)) ≠
    MemoryMsg.locOf (right.finalEntry.toMemoryMsg (p := p))
  rw [MemoryHistoryAccess.locOf_toMemoryMsg_of_busAddress left.loc
      (canonicalHistoryLocation canonical leftMem) left.finalEntry rfl,
    MemoryHistoryAccess.locOf_toMemoryMsg_of_busAddress right.loc
      (canonicalHistoryLocation canonical rightMem) right.finalEntry rfl]
  exact distinct

/-! ## Native boundary inventories and the row-projection payoff -/

@[simp] theorem nativeTrace_memoryInitOccurrences
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace) :
    (nativeTrace statement execution).providerOccurrences .memoryInit =
      memoryInitialEntries
        (TraceGen.compileExecution statement.program execution
          (nativeInitialClock statement)).memoryHistory := rfl

@[simp] theorem nativeTrace_memoryFinalizeOccurrences
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace) :
    (nativeTrace statement execution).providerOccurrences .memoryFinalize =
      memoryFinalEntries
        (TraceGen.compileExecution statement.program execution
          (nativeInitialClock statement)).memoryHistory := rfl

/-- The generated native init table has at most one row at each semantic Memory location. -/
theorem nativeTrace_memoryInitProviderUnique
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace)
    (canonical : MemoryAddressesCanonical
      (TraceGen.compileExecution statement.program execution
        (nativeInitialClock statement)).memoryHistory) :
    MemoryInitProviderUnique (nativeTrace statement execution).witness := by
  unfold MemoryInitProviderUnique
  have pairwiseMessages :
      ((typedTableInteractionsWith
        (memoryInitProviderTable (nativeTrace statement execution).witness)
        memoryChannel).map TypedInteraction.message).Pairwise
          (fun left right => MemoryMsg.locOf left ≠ MemoryMsg.locOf right) := by
    rw [(nativeTrace statement execution).memoryInitTableMessages,
      nativeTrace_memoryInitOccurrences]
    exact memoryInitialEntries_messages_pairwise canonical
  rw [List.pairwise_map] at pairwiseMessages
  exact pairwiseMessages.imp fun distinct _ _ => distinct

/-- The generated native finalize table has at most one row at each semantic Memory location. -/
theorem nativeTrace_memoryFinalizeProviderUnique
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace)
    (canonical : MemoryAddressesCanonical
      (TraceGen.compileExecution statement.program execution
        (nativeInitialClock statement)).memoryHistory) :
    MemoryFinalizeProviderUnique (nativeTrace statement execution).witness := by
  unfold MemoryFinalizeProviderUnique
  have pairwiseMessages :
      ((typedTableInteractionsWith
        (memoryFinalizeProviderTable (nativeTrace statement execution).witness)
        memoryChannel).map TypedInteraction.message).Pairwise
          (fun left right => MemoryMsg.locOf left ≠ MemoryMsg.locOf right) := by
    rw [(nativeTrace statement execution).memoryFinalizeTableMessages,
      nativeTrace_memoryFinalizeOccurrences]
    exact memoryFinalEntries_messages_pairwise canonical
  rw [List.pairwise_map] at pairwiseMessages
  exact pairwiseMessages.imp fun distinct _ _ => distinct

/-- Field-free history genesis and the proved boundary-row projection supply the exact typed
Memory-init provider binding. -/
theorem nativeTrace_memoryInitProviderBound
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace)
    (canonical : MemoryAddressesCanonical
      (TraceGen.compileExecution statement.program execution
        (nativeInitialClock statement)).memoryHistory)
    (genesis : NativeMemoryGenesis execution.initialState
      (TraceGen.compileExecution statement.program execution
        (nativeInitialClock statement)).memoryHistory) :
    MemoryInitProviderBound (nativeTrace statement execution).witness
      execution.initialState (nativeInitialClock statement) := by
  intro interaction member _
  let rebound : TypedInteraction memoryChannel :=
    { raw := interaction
      channel_eq := (memoryInitProviderTable
        (nativeTrace statement execution).witness).channel_eq_of_mem_interactionsWith member }
  have rawMember : interaction ∈
      ((typedTableInteractionsWith
        (memoryInitProviderTable (nativeTrace statement execution).witness)
        memoryChannel).map TypedInteraction.raw) := by
    rw [typedTableInteractionsWith_raw]
    exact member
  obtain ⟨typed, typedMem, rawEq⟩ := List.mem_map.mp rawMember
  have reboundEq : rebound = typed :=
    TypedInteraction.raw_injective rawEq.symm
  have messageMem : typed.message ∈
      ((typedTableInteractionsWith
        (memoryInitProviderTable (nativeTrace statement execution).witness)
        memoryChannel).map TypedInteraction.message) := List.mem_map_of_mem typedMem
  rw [(nativeTrace statement execution).memoryInitTableMessages,
    nativeTrace_memoryInitOccurrences] at messageMem
  obtain ⟨entry, entryMem, messageEq⟩ := List.mem_map.mp messageMem
  change MemoryInitMessageBound execution.initialState (nativeInitialClock statement)
    rebound.message
  rw [reboundEq, ← messageEq]
  exact memoryInitialEntry_messageBound canonical genesis entryMem

/-- Readiness exposes the derived typed Memory-init provider contract without storing it. -/
theorem NativeTraceReady.memoryProviderBound
    {statement : SupportedCoreStatement p} {execution : Machine.EventExecutionTrace}
    (ready : NativeTraceReady statement execution) :
    MemoryInitProviderBound (nativeTrace statement execution).witness
      execution.initialState (nativeInitialClock statement) :=
  nativeTrace_memoryInitProviderBound statement execution
    ready.memoryAddresses ready.memoryGenesis

omit [Fact (2 ^ 25 < p)] in
private theorem memoryInitialEntryMultiplicity {stream : List MemoryHistoryAccess}
    {entry : MemRecordEntry} (member : entry ∈ memoryInitialEntries stream) :
    entry.multiplicity = true := by
  obtain ⟨history, _, rfl⟩ := List.mem_map.mp member
  rfl

omit [Fact (2 ^ 25 < p)] in
private theorem memoryFinalEntryMultiplicity {stream : List MemoryHistoryAccess}
    {entry : MemRecordEntry} (member : entry ∈ memoryFinalEntries stream) :
    entry.multiplicity = true := by
  obtain ⟨history, _, rfl⟩ := List.mem_map.mp member
  rfl

/-- The active native init table is exactly one positive canonical access per touched location. -/
theorem nativeTrace_activeMemoryInitLedger
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace) :
    active ((typedTableInteractionsWith
      (memoryInitProviderTable (nativeTrace statement execution).witness)
      memoryChannel).map fun interaction => Interaction.toAccess interaction.raw) =
      (memoryInitialEntries
        (TraceGen.compileExecution statement.program execution
          (nativeInitialClock statement)).memoryHistory).map fun entry =>
        accessAt (MemoryHistoryAccess.entryKey (p := p) entry) 1 := by
  rw [(nativeTrace statement execution).memoryInitTableAccessLedger]
  simp only [nativeTrace_memoryInitOccurrences]
  have accesses :
      (memoryInitialEntries
        (TraceGen.compileExecution statement.program execution
          (nativeInitialClock statement)).memoryHistory).map (fun entry =>
          accessAt (MemoryHistoryAccess.entryKey (p := p) entry)
            (signedVal (entry.multiplicityField (p := p)))) =
      (memoryInitialEntries
        (TraceGen.compileExecution statement.program execution
          (nativeInitialClock statement)).memoryHistory).map (fun entry =>
          accessAt (MemoryHistoryAccess.entryKey (p := p) entry) 1) := by
    apply List.map_congr_left
    intro entry member
    change accessAt (MemoryHistoryAccess.entryKey (p := p) entry)
      (signedVal (if entry.multiplicity then 1 else 0)) = _
    rw [memoryInitialEntryMultiplicity member]
    simp only [if_true]
    have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
    rw [signedVal_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod,
      Nat.mod_eq_of_lt (by omega)]
    norm_num
  rw [accesses]
  simp [active]

/-- The active native finalize table is exactly one negative canonical access per touched location. -/
theorem nativeTrace_activeMemoryFinalizeLedger
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace) :
    active ((typedTableInteractionsWith
      (memoryFinalizeProviderTable (nativeTrace statement execution).witness)
      memoryChannel).map fun interaction => Interaction.toAccess interaction.raw) =
      (memoryFinalEntries
        (TraceGen.compileExecution statement.program execution
          (nativeInitialClock statement)).memoryHistory).map fun entry =>
        accessAt (MemoryHistoryAccess.entryKey (p := p) entry) (-1) := by
  rw [(nativeTrace statement execution).memoryFinalizeTableAccessLedger]
  simp only [nativeTrace_memoryFinalizeOccurrences]
  have accesses :
      (memoryFinalEntries
        (TraceGen.compileExecution statement.program execution
          (nativeInitialClock statement)).memoryHistory).map (fun entry =>
          accessAt (MemoryHistoryAccess.entryKey (p := p) entry)
            (signedVal (-(entry.multiplicityField (p := p))))) =
      (memoryFinalEntries
        (TraceGen.compileExecution statement.program execution
          (nativeInitialClock statement)).memoryHistory).map (fun entry =>
          accessAt (MemoryHistoryAccess.entryKey (p := p) entry) (-1)) := by
    apply List.map_congr_left
    intro entry member
    change accessAt (MemoryHistoryAccess.entryKey (p := p) entry)
      (signedVal (-(if entry.multiplicity then 1 else 0))) = _
    rw [memoryFinalEntryMultiplicity member]
    simp only [if_true]
    have hp : 2 < p := by have := Fact.out (p := 2 ^ 25 < p); omega
    rw [signedVal_neg_is_real hp (Or.inr rfl), ZMod.val_one_eq_one_mod,
      Nat.mod_eq_of_lt (by omega)]
    norm_num
  rw [accesses]
  simp [active]

/-- The deterministic native trace's active Memory ledger is the canonical family of location
handoff chains.  Only the instruction/refresh row projection remains as an explicit seam. -/
theorem nativeTrace_memoryLedgerPermHandoffChains
    (statement : SupportedCoreStatement p) (execution : Machine.EventExecutionTrace)
    (projection : NativeMemoryRowProjection statement execution) :
    (active (nativeTrace statement execution).memoryLedger).Perm
      ((memoryHandoffChains (p := p)
        (TraceGen.compileExecution statement.program execution
          (nativeInitialClock statement)).memoryHistory).flatMap chainLedger) := by
  let trace := nativeTrace statement execution
  let compiled := TraceGen.compileExecution statement.program execution
    (nativeInitialClock statement)
  let instructionLedger := compiled.instructionMemoryHistory.flatMap
    (MemoryHistoryAccess.ledger (p := p))
  let initLedger := (memoryInitialEntries compiled.memoryHistory).map fun entry =>
    accessAt (MemoryHistoryAccess.entryKey (p := p) entry) 1
  let finalizeLedger := (memoryFinalEntries compiled.memoryHistory).map fun entry =>
    accessAt (MemoryHistoryAccess.entryKey (p := p) entry) (-1)
  let bumpLedger := compiled.bumpMemoryHistory.flatMap
    (MemoryHistoryAccess.ledger (p := p))
  rw [memoryLedger_eq, active_append, active_append, active_append,
    nativeTrace_activeMemoryInitLedger, nativeTrace_activeMemoryFinalizeLedger]
  have projected' :
      (active (physicalInstructionMemoryLedger trace) ++
        (initLedger ++ (finalizeLedger ++ active (physicalMemoryBumpLedger trace)))).Perm
      (instructionLedger ++ (initLedger ++ (finalizeLedger ++ bumpLedger))) := by
    simpa only [trace, compiled, instructionLedger, initLedger, finalizeLedger,
      bumpLedger] using projection.instruction.append
        ((List.Perm.refl initLedger).append
          ((List.Perm.refl finalizeLedger).append projection.bumps))
  have reordered :
      (instructionLedger ++ (initLedger ++ (finalizeLedger ++ bumpLedger))).Perm
        (initLedger ++ (finalizeLedger ++ (instructionLedger ++ bumpLedger))) := by
    have swapped : (instructionLedger ++ (initLedger ++ finalizeLedger)).Perm
        ((initLedger ++ finalizeLedger) ++ instructionLedger) := List.perm_append_comm
    simpa only [List.append_assoc] using swapped.append_right
      bumpLedger
  have splitHistory : (instructionLedger ++ bumpLedger).Perm
      (compiled.memoryHistory.flatMap (MemoryHistoryAccess.ledger (p := p))) := by
    simpa only [instructionLedger, bumpLedger] using
      compiledInstructionBumpLedgerPerm (p := p) compiled
  have grouped :
      (initLedger ++ (finalizeLedger ++ (instructionLedger ++ bumpLedger))).Perm
        ((memoryHandoffChains (p := p) compiled.memoryHistory).flatMap chainLedger) :=
    ((List.Perm.refl initLedger).append
      ((List.Perm.refl finalizeLedger).append splitHistory)).trans
        (by simpa only [initLedger, finalizeLedger] using
          memory_boundary_history_ledger_perm (p := p) compiled.memoryHistory)
  have finished := projected'.trans (reordered.trans grouped)
  simpa only [trace, compiled, physicalInstructionMemoryLedger,
    physicalMemoryBumpLedger, instructionLedger, initLedger, finalizeLedger,
    bumpLedger, List.append_assoc] using finished

/-- Memory row projection plus the compiler's per-location chronology supplies the complete active
Memory handoff consumed by ensemble balance. -/
theorem NativeTraceReady.memoryLedgerPerm
    {statement : SupportedCoreStatement p} {execution : Machine.EventExecutionTrace}
    (ready : NativeTraceReady statement execution) :
    (active (nativeTrace statement execution).memoryLedger).Perm
      (handoff ((memoryHandoffChains (p := p)
        (TraceGen.compileExecution statement.program execution
          (nativeInitialClock statement)).memoryHistory).flatMap chainTokens)) := by
  refine (nativeTrace_memoryLedgerPermHandoffChains statement execution
    ready.memoryProjection).trans ?_
  exact memoryChainsLedger_perm_handoff
    (memoryRecordChains_of_chronology ready.memoryChronology)

end SP1Clean.Soundness
