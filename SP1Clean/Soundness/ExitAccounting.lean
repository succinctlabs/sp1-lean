import SP1Clean.Soundness.TypedState
import SP1Clean.Soundness.TypedMemoryBalance
import SP1Clean.Soundness.EnsembleChannels

/-! # Exit-channel accounting (the halt-table wave)

The Exit bus has exactly two parties: the Halt table pushes one gated hand-off message per
physical row (the reduced `x10` word when real, the zero code when padding), and the
state-boundary verifier pulls the committed `⟨exit_code⟩` exactly once, ungated.  Balance therefore
forces the Halt table to carry **exactly one physical row**, and binds the public exit code:

* `witness_exit_code_zero_of_haltFree` — with no active halt row, `exit_code = 0`;
* `witness_realHaltRows_eq_of_mem` — an active halt row is the *only* active halt row, and its
  reduced `x10` word is the committed exit code.

These are the ordinary-branch/halting-branch dichotomy facts the grounding capstone's case split
consumes.  The channel decomposition mirrors `TypedProgram`'s partition: the verifier's closed
form, the instruction block's silence, and the provider suffix collapsing to the Halt table. -/

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

omit [Fact (2 ^ 24 < p)] in
/-- Evaluation commutes with the single-cell exit-code projection. -/
theorem eval_exitCodeMessage (env : Environment (ZMod p))
    (input : Var SP1PublicIO (ZMod p)) :
    Eval.eval env (⟨input.exit_code⟩ : ExitMsg (Expression (ZMod p))) =
      (⟨(Eval.eval env input).exit_code⟩ : ExitMsg (ZMod p)) := by
  simp only [circuit_norm]

/-- The verifier table contributes exactly the ungated public exit-code pull. -/
theorem witness_verifierExitInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedTableInteractionsWith witness.verifierTable exitChannel =
      [TypedInteraction.pulledIfValue exitChannel 1
        (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p))] := by
  have inputEval : Eval.eval (Environment.fromInput witness.publicInput witness.data)
      (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)) = witness.publicInput :=
    ProvableType.eval_fromInput_varFromOffset_zero witness.publicInput witness.data
  have exitEval : Eval.eval (Environment.fromInput witness.publicInput witness.data)
      (⟨(varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).exit_code⟩ :
        ExitMsg (Expression (ZMod p))) =
      (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p)) := by
    rw [eval_exitCodeMessage, inputEval]
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedTableInteractionsWith_raw]
  unfold Table.interactionsWith
  rw [EnsembleWitness.verifierTable_flatMap]
  rw [Operations.interactionValuesWith_eq_map, Component.interactionsWith_eq]
  change List.map (AbstractInteraction.eval (Environment.fromInput witness.publicInput witness.data))
      (((sp1StateVerifierMain
        (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p))).operations
          (size SP1PublicIO)).interactionsWith exitChannel.toRaw) = _
  rw [sp1StateVerifierMain_exitInteractions]
  simp only [List.map_cons, List.map_nil]
  rw [Channel.eval_pulled, exitEval]
  rfl

/-- The 25-chip instruction block is silent on the Exit bus. -/
theorem witness_instructionExitInteractions_eq_nil
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    decodedWitnessInstructionInteractionsWith witness.data witness.tables exitChannel = [] := by
  rw [decodedWitnessInstructionInteractionsWith_eq_tables witness exitChannel,
    List.flatMap_eq_nil_iff]
  intro table tableMem
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  refine sp1Tables_exitChannel_not_mem table.component ?_
  have h := List.mem_map_of_mem (f := (·.component)) tableMem
  rw [List.map_take, witness.tables_map_component] at h
  exact h

/-- Every provider-table position except the Halt table is silent on the Exit bus. -/
theorem witness_nonHaltProviderTable_exitInteractions_eq_nil
    (witness : EnsembleWitness (sp1Ensemble (p := p))) (i : ℕ)
    (lower : instructionTableCount ≤ i) (upper : i < ensembleTableCount)
    (witnessBound : i < witness.tables.length) (notHalt : i ≠ haltIndex) :
    typedTableInteractionsWith witness.tables[i] exitChannel = [] := by
  change 25 ≤ i at lower
  change i < 54 at upper
  change i ≠ 53 at notHalt
  apply List.map_eq_nil_iff.mp
  rw [typedTableInteractionsWith_raw]
  apply Table.interactionsWith_nil_of_channel_not_mem
  have ensembleBound : i < (sp1Ensemble (p := p)).tables.length := by
    rw [witness.same_length]
    exact witnessBound
  have componentEq := witness.same_circuits i ensembleBound
  have providerBound : i - 25 < (sp1ProviderTables (p := p)).length := by
    simp only [sp1ProviderTables_length]
    omega
  have componentProviderEq : witness.tables[i].component =
      (sp1ProviderTables (p := p))[i - 25] := by
    rw [← componentEq]
    change (sp1Tables (p := p) ++ sp1ProviderTables (p := p))[i] = _
    rw [List.getElem_append_right (by simpa only [sp1Tables_length] using lower)]
    simp only [sp1Tables_length]
  rw [componentProviderEq]
  exact sp1ProviderTables_exitChannel_not_mem (i - 25) providerBound (by omega)

/-- The whole provider suffix's Exit interactions are exactly the Halt table's. -/
theorem witness_providerExitInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (witness.tables.drop 25).flatMap (typedTableInteractionsWith · exitChannel) =
      typedTableInteractionsWith (haltTable witness) exitChannel := by
  have tablesLength : witness.tables.length = 54 := by
    rw [← witness.same_length]
    simp [sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length]
  have interactionsAtOther (i : ℕ) (lower : instructionTableCount ≤ i)
      (upper : i < ensembleTableCount) (bound : i < witness.tables.length)
      (notHalt : i ≠ haltIndex) :
      typedTableInteractionsWith witness.tables[i] exitChannel = [] :=
    witness_nonHaltProviderTable_exitInteractions_eq_nil witness i lower upper bound notHalt
  repeat rw [List.drop_eq_getElem_cons (by omega)]
  rw [List.drop_eq_nil_of_le (by omega)]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  rw [show witness.tables[53] = haltTable witness from rfl]
  simp [interactionsAtOther, instructionTableCount, ensembleTableCount, haltIndex,
    stateSilentProviderTableCount]

/-- Exact Exit-channel decomposition of the whole ensemble witness: the verifier's ungated pull,
then the Halt table's per-row gated hand-off pair. -/
theorem typedEnsembleExitInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedEnsembleInteractionsWith witness exitChannel =
      [TypedInteraction.pulledIfValue exitChannel 1
        (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p))] ++
      (haltTable witness).table.flatMap fun row =>
        [TypedInteraction.pushedIfValue exitChannel
           (haltRow (haltTable witness) row).is_real
           (HaltChip.exitMessage (haltRow (haltTable witness) row)),
         TypedInteraction.pushedIfValue exitChannel
           (1 - (haltRow (haltTable witness) row).is_real)
           (⟨0⟩ : ExitMsg (ZMod p))] := by
  rw [typedEnsembleInteractionsWith_partition, witness_verifierExitInteractions_eq,
    witness_instructionExitInteractions_eq_nil, witness_providerExitInteractions_eq,
    haltTable_typedExit, List.append_nil]

omit [Fact (2 ^ 24 < p)] in
/-- One gated hand-off pair contributes exactly one produced message: the reduced word on a real
row, the zero code on a padding row. -/
private theorem producedMessages_exitPair (hp : 2 < p) {gate : ZMod p}
    (hbool : gate = 0 ∨ gate = 1) (m : ExitMsg (ZMod p)) :
    producedMessages [TypedInteraction.pushedIfValue exitChannel gate m,
        TypedInteraction.pushedIfValue exitChannel (1 - gate) (⟨0⟩ : ExitMsg (ZMod p))] =
      [if gate = 1 then m else (⟨0⟩ : ExitMsg (ZMod p))] := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hbool' : (1 : ZMod p) - gate = 0 ∨ (1 : ZMod p) - gate = 1 := by
    rcases hbool with h0 | h1
    · right; rw [h0, sub_zero]
    · left; rw [h1, sub_self]
  have hpush1 : signedVal gate = (gate.val : ℤ) := signedVal_is_real hp hbool
  have hpush2 : signedVal ((1 : ZMod p) - gate) = (((1 : ZMod p) - gate).val : ℤ) :=
    signedVal_is_real hp hbool'
  unfold producedMessages
  rcases hbool with h0 | h1
  · have hval : gate.val = 0 := by rw [h0, ZMod.val_zero]
    have hval' : ((1 : ZMod p) - gate).val = 1 := by rw [h0, sub_zero, ZMod.val_one]
    rw [if_neg (by rw [h0]; exact zero_ne_one),
      List.filter_cons_of_neg (by simp [hpush1, hval]),
      List.filter_cons_of_pos (by simp [hpush2, hval']),
      List.filter_nil, List.map_cons, List.map_nil, TypedInteraction.pushedIfValue_message]
  · have hval : gate.val = 1 := by rw [h1, ZMod.val_one]
    have hval' : ((1 : ZMod p) - gate).val = 0 := by rw [h1, sub_self, ZMod.val_zero]
    rw [if_pos h1,
      List.filter_cons_of_pos (by simp [hpush1, hval]),
      List.filter_cons_of_neg (by simp [hpush2, hval']),
      List.filter_nil, List.map_cons, List.map_nil, TypedInteraction.pushedIfValue_message]

omit [Fact (2 ^ 24 < p)] in
/-- A gated hand-off pair consumes nothing: both entries are pushes. -/
private theorem consumedMessages_exitPair (hp : 2 < p) {gate : ZMod p}
    (hbool : gate = 0 ∨ gate = 1) (m : ExitMsg (ZMod p)) :
    consumedMessages [TypedInteraction.pushedIfValue exitChannel gate m,
        TypedInteraction.pushedIfValue exitChannel (1 - gate) (⟨0⟩ : ExitMsg (ZMod p))] = [] := by
  haveI : Fact (1 < p) := ⟨by omega⟩
  have hbool' : (1 : ZMod p) - gate = 0 ∨ (1 : ZMod p) - gate = 1 := by
    rcases hbool with h0 | h1
    · right; rw [h0, sub_zero]
    · left; rw [h1, sub_self]
  have hpush1 : signedVal gate = (gate.val : ℤ) := signedVal_is_real hp hbool
  have hpush2 : signedVal ((1 : ZMod p) - gate) = (((1 : ZMod p) - gate).val : ℤ) :=
    signedVal_is_real hp hbool'
  have hval : gate.val = 0 ∨ gate.val = 1 := by
    rcases hbool with h | h
    · left; rw [h, ZMod.val_zero]
    · right; rw [h, ZMod.val_one]
  have hval' : ((1 : ZMod p) - gate).val = 0 ∨ ((1 : ZMod p) - gate).val = 1 := by
    rcases hbool' with h | h
    · left; rw [h, ZMod.val_zero]
    · right; rw [h, ZMod.val_one]
  unfold consumedMessages
  rw [List.filter_cons_of_neg (by
      simp only [TypedInteraction.pushedIfValue_mult, hpush1, decide_eq_true_eq]
      rcases hval with h | h <;> rw [h] <;> decide),
    List.filter_cons_of_neg (by
      simp only [TypedInteraction.pushedIfValue_mult, hpush2, decide_eq_true_eq]
      rcases hval' with h | h <;> rw [h] <;> decide),
    List.filter_nil, List.map_nil]

/-- Every Exit interaction of the witness carries a `{-1, 0, 1}` signed multiplicity. -/
theorem witness_exitInteractions_signedBinary
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    ∀ interaction ∈ typedEnsembleInteractionsWith witness exitChannel,
      signedVal interaction.mult = -1 ∨ signedVal interaction.mult = 0 ∨
        signedVal interaction.mult = 1 := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  haveI : Fact (1 < p) := ⟨by omega⟩
  rw [typedEnsembleExitInteractions_eq]
  intro interaction interactionMem
  rcases List.mem_append.mp interactionMem with hverifier | hhalt
  · rw [List.mem_singleton.mp hverifier]
    left
    rw [TypedInteraction.pulledIfValue_mult]
    calc
      signedVal (-(1 : ZMod p)) = -((1 : ZMod p).val : ℤ) :=
        signedVal_neg_is_real hp (Or.inr rfl)
      _ = -1 := by rw [ZMod.val_one]; norm_num
  · obtain ⟨row, rowMem, hmem⟩ := List.mem_flatMap.mp hhalt
    have hbool := witness_haltRows_selectorBinary witness constraints row rowMem
    have hbool' : (1 : ZMod p) - (haltRow (haltTable witness) row).is_real = 0 ∨
        (1 : ZMod p) - (haltRow (haltTable witness) row).is_real = 1 := by
      rcases hbool with h0 | h1
      · right; rw [h0, sub_zero]
      · left; rw [h1, sub_self]
    rcases List.mem_cons.mp hmem with rfl | hmem
    · rw [TypedInteraction.pushedIfValue_mult, signedVal_is_real hp hbool]
      rcases hbool with h0 | h1
      · right; left; rw [h0, ZMod.val_zero]; rfl
      · right; right; rw [h1, ZMod.val_one]; rfl
    · rcases List.mem_cons.mp hmem with rfl | hnil
      · rw [TypedInteraction.pushedIfValue_mult, signedVal_is_real hp hbool']
        rcases hbool' with h0 | h1
        · right; left; rw [h0, ZMod.val_zero]; rfl
        · right; right; rw [h1, ZMod.val_one]; rfl
      · exact absurd hnil List.not_mem_nil

/-- Produced Exit messages of the whole witness: exactly one hand-off message per physical Halt
row (the reduced word when real, the zero code when padding). -/
theorem witness_exitProduced_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    producedMessages (typedEnsembleInteractionsWith witness exitChannel) =
      (haltTable witness).table.map fun row =>
        if (haltRow (haltTable witness) row).is_real = 1
        then HaltChip.exitMessage (haltRow (haltTable witness) row)
        else (⟨0⟩ : ExitMsg (ZMod p)) := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  rw [typedEnsembleExitInteractions_eq, producedMessages_append]
  have hverifier : producedMessages
      [TypedInteraction.pulledIfValue exitChannel 1
        (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p))] = [] := by
    haveI : Fact (1 < p) := ⟨by omega⟩
    unfold producedMessages
    rw [List.filter_cons_of_neg (by
        simp only [TypedInteraction.pulledIfValue_mult,
          signedVal_neg_is_real hp (Or.inr rfl : (1 : ZMod p) = 0 ∨ (1 : ZMod p) = 1),
          ZMod.val_one, decide_eq_true_eq]
        norm_num),
      List.filter_nil, List.map_nil]
  rw [hverifier, List.nil_append, producedMessages_flatMap]
  rw [show ((haltTable witness).table.map fun row =>
      if (haltRow (haltTable witness) row).is_real = 1
      then HaltChip.exitMessage (haltRow (haltTable witness) row)
      else (⟨0⟩ : ExitMsg (ZMod p))) =
    (haltTable witness).table.flatMap fun row =>
      [if (haltRow (haltTable witness) row).is_real = 1
       then HaltChip.exitMessage (haltRow (haltTable witness) row)
       else (⟨0⟩ : ExitMsg (ZMod p))] from List.map_eq_flatMap ..]
  apply List.flatMap_congr
  intro row rowMem
  exact producedMessages_exitPair hp
    (witness_haltRows_selectorBinary witness constraints row rowMem) _

/-- Consumed Exit messages of the whole witness: exactly the verifier's committed exit code. -/
theorem witness_exitConsumed_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    consumedMessages (typedEnsembleInteractionsWith witness exitChannel) =
      [(⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p))] := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  rw [typedEnsembleExitInteractions_eq, consumedMessages_append]
  have hverifier : consumedMessages
      [TypedInteraction.pulledIfValue exitChannel 1
        (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p))] =
      [(⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p))] := by
    haveI : Fact (1 < p) := ⟨by omega⟩
    unfold consumedMessages
    rw [List.filter_cons_of_pos (by
        simp only [TypedInteraction.pulledIfValue_mult,
          signedVal_neg_is_real hp (Or.inr rfl : (1 : ZMod p) = 0 ∨ (1 : ZMod p) = 1),
          ZMod.val_one, decide_eq_true_eq]
        norm_num),
      List.filter_nil, List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_message]
  have hhalt : consumedMessages ((haltTable witness).table.flatMap fun row =>
      [TypedInteraction.pushedIfValue exitChannel
         (haltRow (haltTable witness) row).is_real
         (HaltChip.exitMessage (haltRow (haltTable witness) row)),
       TypedInteraction.pushedIfValue exitChannel
         (1 - (haltRow (haltTable witness) row).is_real)
         (⟨0⟩ : ExitMsg (ZMod p))]) = [] := by
    rw [consumedMessages_flatMap, List.flatMap_eq_nil_iff]
    intro row rowMem
    exact consumedMessages_exitPair hp
      (witness_haltRows_selectorBinary witness constraints row rowMem) _
  rw [hverifier, hhalt, List.append_nil]

/-- **The Exit hand-off, balanced.**  Every physical Halt row's hand-off message list is a
permutation of the singleton committed exit code — so the Halt table has exactly one physical row,
whose hand-off message *is* the committed exit code. -/
theorem witness_exitMessages_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((haltTable witness).table.map fun row =>
      if (haltRow (haltTable witness) row).is_real = 1
      then HaltChip.exitMessage (haltRow (haltTable witness) row)
      else (⟨0⟩ : ExitMsg (ZMod p))) =
      [(⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p))] := by
  classical
  have channelBalanced := typedInteractions_balanced witness balanced exitChannel
    (by simp [sp1Ensemble_channels])
  have messagePerm := producedMessages_perm_consumedMessages
    (typedEnsembleInteractionsWith witness exitChannel) channelBalanced
    (witness_exitInteractions_signedBinary witness constraints)
  rw [witness_exitProduced_eq witness constraints,
    witness_exitConsumed_eq witness constraints] at messagePerm
  exact List.perm_singleton.mp messagePerm

/-- On a shard with no active Halt row the committed public exit code is zero. -/
theorem witness_exit_code_zero_of_haltFree
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (haltFree : realHaltRows witness = []) :
    witness.publicInput.exit_code = 0 := by
  have handoff := witness_exitMessages_eq witness constraints balanced
  have noReal : ∀ row ∈ (haltTable witness).table,
      ¬ (haltRow (haltTable witness) row).is_real = 1 := by
    intro row rowMem hreal
    have : row ∈ realHaltRows witness := by
      rw [realHaltRows, List.mem_filter]
      exact ⟨rowMem, by simpa using hreal⟩
    rw [haltFree] at this
    exact List.not_mem_nil this
  have memberZero : (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p)) ∈
      ((haltTable witness).table.map fun row =>
        if (haltRow (haltTable witness) row).is_real = 1
        then HaltChip.exitMessage (haltRow (haltTable witness) row)
        else (⟨0⟩ : ExitMsg (ZMod p))) := by
    rw [handoff]
    exact List.mem_singleton_self _
  obtain ⟨row, rowMem, entryEq⟩ := List.mem_map.mp memberZero
  rw [if_neg (noReal row rowMem)] at entryEq
  exact congrArg ExitMsg.value entryEq.symm

/-- **The active Halt row is unique and binds the exit code**: any active Halt row is the whole
active list, and its reduced `x10` word is the committed public exit code. -/
theorem witness_realHaltRows_eq_of_mem
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {h : Array (ZMod p)} (hmem : h ∈ realHaltRows witness) :
    realHaltRows witness = [h] ∧
      HaltChip.exitMessage (haltRow (haltTable witness) h) =
        (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p)) := by
  have handoff := witness_exitMessages_eq witness constraints balanced
  have lengthOne : (haltTable witness).table.length = 1 := by
    have := congrArg List.length handoff
    simpa using this
  obtain ⟨r, tableEq⟩ := List.length_eq_one_iff.mp lengthOne
  obtain ⟨hTable, hReal⟩ := mem_realHaltRows witness hmem
  have hr : h = r := by
    rw [tableEq, List.mem_singleton] at hTable
    exact hTable
  subst hr
  have realEq : realHaltRows witness = [h] := by
    rw [realHaltRows, tableEq, List.filter_cons_of_pos (by simpa using hReal),
      List.filter_nil]
  refine ⟨realEq, ?_⟩
  rw [tableEq, List.map_cons, List.map_nil, if_pos hReal] at handoff
  exact List.cons_eq_cons.mp handoff |>.1

/-- The halting shard's whole physical Halt table is its one active row (the exit hand-off's
exactly-one-row consequence, exposed for the memory-guarantee assembly). -/
theorem witness_haltTable_table_eq_of_mem
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {h : Array (ZMod p)} (hmem : h ∈ realHaltRows witness) :
    (haltTable witness).table = [h] := by
  have handoff := witness_exitMessages_eq witness constraints balanced
  have lengthOne : (haltTable witness).table.length = 1 := by
    have := congrArg List.length handoff
    simpa using this
  obtain ⟨r, tableEq⟩ := List.length_eq_one_iff.mp lengthOne
  obtain ⟨hTable, -⟩ := mem_realHaltRows witness hmem
  rw [tableEq] at hTable ⊢
  rw [List.mem_singleton] at hTable
  rw [hTable]

end SP1Clean.Soundness
