import SP1Clean.Soundness.TypedState
import SP1Clean.Soundness.TypedMemoryBalance
import SP1Clean.Soundness.EnsembleChannels

/-! # Exit-channel accounting

The public verifier pulls the committed exit code once. Every physical Halt row pushes one
handoff message: the reduced `x10` word when active, zero when padding. Every syscall row with
`is_halt = 1` contributes another push. The exact ledger retains disabled occurrences; its active
messages balance to the singleton public exit code.

A nonempty Halt table therefore has exactly one physical row and excludes syscall HALT pushes.
With that explicit premise, no active Halt row implies a zero public exit code. An active Halt row
is unique and binds its reduced `x10` value to the public code. An empty Halt table leaves room for
a syscall HALT; balance alone does not exclude that case.

These specializations serve the legacy two-contributor ensemble. They can disappear when its
remaining capstone consumers adopt the native host/Exit boundary and retire the separate Halt table.
-/

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

/-- The public verifier contributes exactly the ungated public exit-code pull. -/
theorem stateVerifier_exitInteractions
    (input : SP1PublicIO (ZMod p)) (data : ProverData (ZMod p)) :
    typedInteractionValuesWith (sp1StateVerifierProgram (p := p)).circuitOperations exitChannel
      (Environment.fromInput input data) =
      [TypedInteraction.pulledIfValue exitChannel 1
        (⟨input.exit_code⟩ : ExitMsg (ZMod p))] := by
  have inputEval : Eval.eval (Environment.fromInput input data)
      (varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)) = input :=
    ProvableType.eval_fromInput_varFromOffset_zero input data
  have exitEval : Eval.eval (Environment.fromInput input data)
      (⟨(varFromOffset SP1PublicIO 0 : Var SP1PublicIO (ZMod p)).exit_code⟩ :
        ExitMsg (Expression (ZMod p))) =
      (⟨input.exit_code⟩ : ExitMsg (ZMod p)) := by
    rw [eval_exitCodeMessage, inputEval]
  apply (List.map_injective_iff.mpr TypedInteraction.raw_injective)
  rw [typedInteractionValuesWith_raw, Operations.interactionValuesWith_eq_map]
  simp only [Operations.interactionsWith, sp1StateVerifierProgram]
  change List.map (AbstractInteraction.eval (Environment.fromInput input data))
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

/-- The provider suffix retains exactly the Halt and syscall Exit ledgers, in physical order. -/
theorem witness_providerExitInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    (witness.tables.drop 25).flatMap (typedTableInteractionsWith · witness.data exitChannel) =
      typedTableInteractionsWith (haltTable witness) witness.data exitChannel ++
        typedTableInteractionsWith (syscallInstrsTable witness) witness.data exitChannel := by
  have length : witness.tables.length = 55 := by
    rw [← witness.same_length]
    simp [sp1Ensemble_tables, sp1Tables_length, sp1ProviderTables_length]
  have silent : ((witness.tables.drop 25).take 28).flatMap
      (typedTableInteractionsWith · witness.data exitChannel) = [] := by
    have checked : ((sp1ProviderTables (p := p)).take 28).all
        (fun component => !(component.circuit.channels.map RawChannel.name).contains
          (exitChannel (p := p)).toRaw.name) = true := rfl
    apply List.flatMap_eq_nil_iff.mpr
    intro table member
    apply List.map_eq_nil_iff.mp
    rw [typedTableInteractionsWith_raw]
    apply Table.interactionsWith_nil_of_channel_not_mem
    have mapped := List.mem_map_of_mem (f := fun table : Table (ZMod p) => table.component) member
    rw [List.map_take, List.map_drop, witness.tables_map_component] at mapped
    change table.component ∈ (sp1ProviderTables (p := p)).take 28 at mapped
    have absent := List.all_eq_true.mp checked table.component mapped
    intro used
    rw [List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)] at absent
    contradiction
  have tail : (witness.tables.drop 25).drop 28 = [haltTable witness, syscallInstrsTable witness] := by
    rw [List.drop_drop, List.drop_eq_getElem_cons (by omega),
      List.drop_eq_getElem_cons (by omega), List.drop_eq_nil_of_le (by omega)]
    rfl
  have split := congrArg (List.flatMap (typedTableInteractionsWith · witness.data exitChannel))
    (List.take_append_drop 28 (witness.tables.drop 25))
  rw [List.flatMap_append, silent, List.nil_append, tail] at split
  simpa only [List.flatMap_cons, List.flatMap_nil, List.append_nil] using split.symm

/-- Exact Exit-channel decomposition of the whole ensemble witness: the verifier's ungated pull,
the Halt table's per-row gated hand-off pair, then the `SyscallInstrs` table's `is_halt`-gated
pushes. -/
theorem typedEnsembleExitInteractions_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p))) :
    typedEnsembleInteractionsWith witness exitChannel =
      [TypedInteraction.pulledIfValue exitChannel 1
        (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p))] ++
      (((haltTable witness).table.flatMap fun row =>
        [TypedInteraction.pushedIfValue exitChannel
           (haltRow witness.data row).is_real
           (HaltChip.exitMessage (haltRow witness.data row)),
         TypedInteraction.pushedIfValue exitChannel
           (1 - (haltRow witness.data row).is_real)
           (⟨0⟩ : ExitMsg (ZMod p))]) ++
      ((syscallInstrsTable witness).table.flatMap fun row =>
        [TypedInteraction.pushedIfValue exitChannel
           (syscallInstrsRow witness.data row).is_halt
           (SyscallInstrsChip.exitMessage
             (syscallInstrsRow witness.data row))])) := by
  have verifier := stateVerifier_exitInteractions witness.publicInput witness.data
  change typedInteractionValuesWith (sp1Ensemble (p := p)).verifierOperations exitChannel
    (Environment.fromInput witness.publicInput witness.data) = _ at verifier
  rw [typedEnsembleInteractionsWith_partition, verifier,
    witness_instructionExitInteractions_eq_nil, witness_providerExitInteractions_eq,
    haltTable_typedExit, syscallInstrsTable_typedExit, List.append_nil]

omit [Fact (2 ^ 24 < p)] in
/-- One gated hand-off pair contributes exactly one produced message: the reduced word on a real
row, the zero code on a padding row. -/
private theorem producedMessages_exitPair (hp : 2 < p) {gate : ZMod p}
    (hbool : gate = 0 ∨ gate = 1) (m : ExitMsg (ZMod p)) :
    producedMessages [TypedInteraction.pushedIfValue exitChannel gate m,
        TypedInteraction.pushedIfValue exitChannel (1 - gate) (⟨0⟩ : ExitMsg (ZMod p))] =
      [if gate = 1 then m else (⟨0⟩ : ExitMsg (ZMod p))] := by
  have : Fact (1 < p) := ⟨by omega⟩
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
/-- A single gated push produces its message exactly when the gate is live, and consumes nothing.
This is the syscall table's Exit shape — one push, with no anti-gated companion to balance the
verifier, which is the whole reason a many-row table cannot inherit the halt table's accounting. -/
private theorem producedMessages_exitPush (hp : 2 < p) {gate : ZMod p}
    (hbool : gate = 0 ∨ gate = 1) (m : ExitMsg (ZMod p)) :
    producedMessages [TypedInteraction.pushedIfValue exitChannel gate m] =
      (if gate = 1 then [m] else []) := by
  have : Fact (1 < p) := ⟨by omega⟩
  have hpush : signedVal gate = (gate.val : ℤ) := signedVal_is_real hp hbool
  unfold producedMessages
  rcases hbool with h0 | h1
  · rw [List.filter_cons_of_neg (by
        simp only [TypedInteraction.pushedIfValue_mult, hpush, decide_eq_true_eq]
        rw [show gate.val = 0 from by rw [h0]; exact ZMod.val_zero]
        norm_num), List.filter_nil, List.map_nil,
      if_neg (by rw [h0]; exact zero_ne_one)]
  · rw [List.filter_cons_of_pos (by
        simp only [TypedInteraction.pushedIfValue_mult, hpush, decide_eq_true_eq]
        rw [show gate.val = 1 from by rw [h1]; exact ZMod.val_one p]
        norm_num), List.filter_nil, List.map_cons, List.map_nil, if_pos h1,
      TypedInteraction.pushedIfValue_message]

omit [Fact (2 ^ 24 < p)] in
/-- The syscall table's Exit pushes consume nothing. -/
private theorem consumedMessages_exitPush (hp : 2 < p) {gate : ZMod p}
    (hbool : gate = 0 ∨ gate = 1) (m : ExitMsg (ZMod p)) :
    consumedMessages [TypedInteraction.pushedIfValue exitChannel gate m] = [] := by
  have : Fact (1 < p) := ⟨by omega⟩
  have hpush : signedVal gate = (gate.val : ℤ) := signedVal_is_real hp hbool
  have hval : gate.val = 0 ∨ gate.val = 1 := by
    rcases hbool with h | h
    · left; rw [h, ZMod.val_zero]
    · right; rw [h, ZMod.val_one]
  unfold consumedMessages
  rw [List.filter_cons_of_neg (by
      simp only [TypedInteraction.pushedIfValue_mult, hpush, decide_eq_true_eq]
      rcases hval with h | h <;> rw [h] <;> norm_num),
    List.filter_nil, List.map_nil]

omit [Fact (2 ^ 24 < p)] in
/-- A gated hand-off pair consumes nothing: both entries are pushes. -/
private theorem consumedMessages_exitPair (hp : 2 < p) {gate : ZMod p}
    (hbool : gate = 0 ∨ gate = 1) (m : ExitMsg (ZMod p)) :
    consumedMessages [TypedInteraction.pushedIfValue exitChannel gate m,
        TypedInteraction.pushedIfValue exitChannel (1 - gate) (⟨0⟩ : ExitMsg (ZMod p))] = [] := by
  have : Fact (1 < p) := ⟨by omega⟩
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
  have : Fact (1 < p) := ⟨by omega⟩
  rw [typedEnsembleExitInteractions_eq]
  intro interaction interactionMem
  rcases List.mem_append.mp interactionMem with hverifier | htail
  · rw [List.mem_singleton.mp hverifier]
    left
    rw [TypedInteraction.pulledIfValue_mult]
    calc
      signedVal (-(1 : ZMod p)) = -((1 : ZMod p).val : ℤ) :=
        signedVal_neg_is_real hp (Or.inr rfl)
      _ = -1 := by rw [ZMod.val_one]; norm_num
  rcases List.mem_append.mp htail with hhalt | hsyscall
  · obtain ⟨row, rowMem, hmem⟩ := List.mem_flatMap.mp hhalt
    have hbool := witness_haltRows_selectorBinary witness constraints row rowMem
    have hbool' : (1 : ZMod p) - (haltRow witness.data row).is_real = 0 ∨
        (1 : ZMod p) - (haltRow witness.data row).is_real = 1 := by
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
  · obtain ⟨row, rowMem, hmem⟩ := List.mem_flatMap.mp hsyscall
    have hbool := witness_syscallInstrsRows_haltSelectorBinary witness constraints row rowMem
    rcases List.mem_cons.mp hmem with rfl | hnil
    · rw [TypedInteraction.pushedIfValue_mult, signedVal_is_real hp hbool]
      rcases hbool with h0 | h1
      · right; left; rw [h0, ZMod.val_zero]; rfl
      · right; right; rw [h1, ZMod.val_one]; rfl
    · exact absurd hnil List.not_mem_nil

/-- Produced Exit messages of the whole witness: exactly one hand-off message per physical Halt
row (the reduced word when real, the zero code when padding). -/
theorem witness_exitProduced_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) :
    producedMessages (typedEnsembleInteractionsWith witness exitChannel) =
      ((haltTable witness).table.map fun row =>
        if (haltRow witness.data row).is_real = 1
        then HaltChip.exitMessage (haltRow witness.data row)
        else (⟨0⟩ : ExitMsg (ZMod p))) ++
      ((syscallInstrsTable witness).table.flatMap fun row =>
        if (syscallInstrsRow witness.data row).is_halt = 1
        then [SyscallInstrsChip.exitMessage (syscallInstrsRow witness.data row)]
        else []) := by
  have hp : 2 < p := by have := Fact.out (p := 2 ^ 24 < p); omega
  rw [typedEnsembleExitInteractions_eq, producedMessages_append, producedMessages_append]
  have hverifier : producedMessages
      [TypedInteraction.pulledIfValue exitChannel 1
        (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p))] = [] := by
    have : Fact (1 < p) := ⟨by omega⟩
    unfold producedMessages
    rw [List.filter_cons_of_neg (by
        simp only [TypedInteraction.pulledIfValue_mult,
          signedVal_neg_is_real hp (Or.inr rfl : (1 : ZMod p) = 0 ∨ (1 : ZMod p) = 1),
          ZMod.val_one, decide_eq_true_eq]
        norm_num),
      List.filter_nil, List.map_nil]
  rw [hverifier, List.nil_append, producedMessages_flatMap, producedMessages_flatMap]
  refine congrArg₂ (· ++ ·) ?_ ?_
  · rw [show ((haltTable witness).table.map fun row =>
      if (haltRow witness.data row).is_real = 1
      then HaltChip.exitMessage (haltRow witness.data row)
      else (⟨0⟩ : ExitMsg (ZMod p))) =
    (haltTable witness).table.flatMap fun row =>
      [if (haltRow witness.data row).is_real = 1
       then HaltChip.exitMessage (haltRow witness.data row)
       else (⟨0⟩ : ExitMsg (ZMod p))] from List.map_eq_flatMap ..]
    apply List.flatMap_congr
    intro row rowMem
    exact producedMessages_exitPair hp
      (witness_haltRows_selectorBinary witness constraints row rowMem) _
  · apply List.flatMap_congr
    intro row rowMem
    exact producedMessages_exitPush hp
      (witness_syscallInstrsRows_haltSelectorBinary witness constraints row rowMem) _

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
    have : Fact (1 < p) := ⟨by omega⟩
    unfold consumedMessages
    rw [List.filter_cons_of_pos (by
        simp only [TypedInteraction.pulledIfValue_mult,
          signedVal_neg_is_real hp (Or.inr rfl : (1 : ZMod p) = 0 ∨ (1 : ZMod p) = 1),
          ZMod.val_one, decide_eq_true_eq]
        norm_num),
      List.filter_nil, List.map_cons, List.map_nil, TypedInteraction.pulledIfValue_message]
  have hhalt : consumedMessages ((haltTable witness).table.flatMap fun row =>
      [TypedInteraction.pushedIfValue exitChannel
         (haltRow witness.data row).is_real
         (HaltChip.exitMessage (haltRow witness.data row)),
       TypedInteraction.pushedIfValue exitChannel
         (1 - (haltRow witness.data row).is_real)
         (⟨0⟩ : ExitMsg (ZMod p))]) = [] := by
    rw [consumedMessages_flatMap, List.flatMap_eq_nil_iff]
    intro row rowMem
    exact consumedMessages_exitPair hp
      (witness_haltRows_selectorBinary witness constraints row rowMem) _
  have hsyscall : consumedMessages ((syscallInstrsTable witness).table.flatMap fun row =>
      [TypedInteraction.pushedIfValue exitChannel
         (syscallInstrsRow witness.data row).is_halt
         (SyscallInstrsChip.exitMessage
           (syscallInstrsRow witness.data row))]) = [] := by
    rw [consumedMessages_flatMap, List.flatMap_eq_nil_iff]
    intro row rowMem
    exact consumedMessages_exitPush hp
      (witness_syscallInstrsRows_haltSelectorBinary witness constraints row rowMem) _
  rw [consumedMessages_append, hverifier, hhalt, hsyscall, List.append_nil, List.append_nil]

/-- The complete Halt and syscall handoff lists together equal the singleton public exit code.
Each physical Halt row contributes one message; each active syscall HALT contributes one more. -/
theorem witness_exitMessages_eq
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels) :
    ((haltTable witness).table.map fun row =>
      if (haltRow witness.data row).is_real = 1
      then HaltChip.exitMessage (haltRow witness.data row)
      else (⟨0⟩ : ExitMsg (ZMod p))) ++
    ((syscallInstrsTable witness).table.flatMap fun row =>
      if (syscallInstrsRow witness.data row).is_halt = 1
      then [SyscallInstrsChip.exitMessage (syscallInstrsRow witness.data row)]
      else []) =
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

/-- **The interim two-contributor invariant.** The Halt table emits one Exit message per physical
row unconditionally and the `SyscallInstrs` table one per active `is_halt` row, so their counts sum
to one. A *non-empty* Halt table therefore accounts for the whole singleton on its own, forcing the
syscall table halt-free. Derived from balance, not assumed — and exactly what disappears when
`HaltChip` retires and D8's successor becomes the sole ungated contributor. -/
private theorem haltTable_length_one_of_ne_nil
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (hne : (haltTable witness).table ≠ []) :
    (haltTable witness).table.length = 1 ∧
      ((syscallInstrsTable witness).table.flatMap fun row =>
        if (syscallInstrsRow witness.data row).is_halt = 1
        then [SyscallInstrsChip.exitMessage (syscallInstrsRow witness.data row)]
        else []) = [] := by
  have hlen := congrArg List.length (witness_exitMessages_eq witness constraints balanced)
  rw [List.length_append, List.length_map, List.length_singleton] at hlen
  have hpos : 0 < (haltTable witness).table.length := by
    cases hcase : (haltTable witness).table with
    | nil => exact absurd hcase hne
    | cons a t => simp
  exact ⟨by omega, List.length_eq_zero_iff.mp (by omega)⟩

/-- With the syscall table halt-free, the hand-off reduces to the Halt table's own gated pushes —
the shape every consumer below was written against. -/
private theorem haltExitMessages_eq_of_ne_nil
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (hne : (haltTable witness).table ≠ []) :
    ((haltTable witness).table.map fun row =>
      if (haltRow witness.data row).is_real = 1
      then HaltChip.exitMessage (haltRow witness.data row)
      else (⟨0⟩ : ExitMsg (ZMod p))) =
      [(⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p))] := by
  have handoff := witness_exitMessages_eq witness constraints balanced
  rw [(haltTable_length_one_of_ne_nil witness constraints balanced hne).2,
    List.append_nil] at handoff
  exact handoff

/-- A nonempty Halt table with no active row forces the public exit code to zero. -/
theorem witness_exit_code_zero_of_haltFree
    (witness : EnsembleWitness (sp1Ensemble (p := p)))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    (haltPresent : (haltTable witness).table ≠ [])
    (haltFree : realHaltRows witness = []) :
    witness.publicInput.exit_code = 0 := by
  have handoff := haltExitMessages_eq_of_ne_nil witness constraints balanced haltPresent
  have noReal : ∀ row ∈ (haltTable witness).table,
      ¬ (haltRow witness.data row).is_real = 1 := by
    intro row rowMem hreal
    have : row ∈ realHaltRows witness := by
      rw [realHaltRows, List.mem_filter]
      exact ⟨rowMem, by simpa using hreal⟩
    rw [haltFree] at this
    exact List.not_mem_nil this
  have memberZero : (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p)) ∈
      ((haltTable witness).table.map fun row =>
        if (haltRow witness.data row).is_real = 1
        then HaltChip.exitMessage (haltRow witness.data row)
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
      HaltChip.exitMessage (haltRow witness.data h) =
        (⟨witness.publicInput.exit_code⟩ : ExitMsg (ZMod p)) := by
  have hTable0 := (mem_realHaltRows witness hmem).1
  have hne : (haltTable witness).table ≠ [] := fun hnil => by
    rw [hnil] at hTable0; exact List.not_mem_nil hTable0
  have handoff := haltExitMessages_eq_of_ne_nil witness constraints balanced hne
  have lengthOne : (haltTable witness).table.length = 1 :=
    (haltTable_length_one_of_ne_nil witness constraints balanced hne).1
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
  have hTable0 := (mem_realHaltRows witness hmem).1
  have hne : (haltTable witness).table ≠ [] := fun hnil => by
    rw [hnil] at hTable0; exact List.not_mem_nil hTable0
  have lengthOne : (haltTable witness).table.length = 1 :=
    (haltTable_length_one_of_ne_nil witness constraints balanced hne).1
  obtain ⟨r, tableEq⟩ := List.length_eq_one_iff.mp lengthOne
  obtain ⟨hTable, -⟩ := mem_realHaltRows witness hmem
  rw [tableEq] at hTable ⊢
  rw [List.mem_singleton] at hTable
  rw [hTable]

end SP1Clean.Soundness
