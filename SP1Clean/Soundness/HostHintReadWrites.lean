import SP1Clean.Soundness.HostHintReadCoverage
import SP1Clean.Soundness.HintReadWriteLedger

/-! # Complete HINT_READ execution and physical write agreement

The public statement identifies one successful concrete host call and exactly its padded RAM
word inventory. Consumer variants, walk order, and final-word arithmetic stay inside the proof.
Local circuit specifications, authenticated queue/word records, each call's cursor balance,
permission authentication, and incoming register observations remain explicit integration inputs.
The Memory ledger projection and readback theorem identify the actual transfers; global Memory
grounding must still authenticate their predecessors and prove the complete outgoing state.
-/

namespace SP1Clean.Soundness.HostHintReadWrites

open Circuit Air.Flat Model.Core Model.Core.HintQueue HostHintReadCoverage

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

/-- The handler's authenticated node fixes its complete padded write inventory before the
execution walk identifies that node with the current host queue. -/
theorem writes_of_records (env : Environment (ZMod p)) (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (valid : handler.Spec env)
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables)
    (wordSpecs : HintReadCoverage.Steps tables data)
    (balanced : BalancedInteractions
      (handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw env ++
        tables.flatMap (·.interactionsWith data HintReadWordChip.stateChannel.toRaw)))
    (store : Store) (header : (input env).node.Binds store) (ending : (input env).endStep.word.Binds store)
    (words : ∀ row ∈ TransitionView.readIndexedRows HintReadCoverage.variants tables data,
      ((HintReadCoverage.rowInput row).step row.1).word.Binds store) :
    ∃ node, node? store (Address.toNat (input env).node.pointer) = some node ∧
      ((TransitionView.readIndexedRows HintReadCoverage.variants tables data).map HintReadWrites.produced).Perm
        (wordWrites (Address.toNat (input env).span.start) node.bytes) := by
  have headerBinding := header
  obtain ⟨node, read, _, _⟩ := header
  obtain ⟨_, _, _, _, _, nodeLength, _, _, span, endStep, nodeValid⟩ := valid
  have count := (span.node_end (input env).node headerBinding nodeValid nodeLength (input env).endStep.word
    ending endStep.1 rfl rfl read).2.1
  rw [handler_cursor] at balanced
  obtain ⟨path, perm, _, inventory, _⟩ := HintReadWrites.ordered_writes tables data
    (input env).first (input env).final aligned wordSpecs balanced store node read words
    (by simp [HostHintReadChip.Inputs.first, Address.toNat]) count
  exact ⟨node, read, (perm.map HintReadWrites.produced).symm.trans (List.Perm.of_eq inventory)⟩

/-- The actual handler and authenticated consumers produce exactly the current hint's padded words. -/
theorem complete_writes (env : Environment (ZMod p)) (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (valid : handler.Spec env)
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables)
    (wordSpecs : HintReadCoverage.Steps tables data)
    (balanced : BalancedInteractions
      (handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw env ++
        tables.flatMap (·.interactionsWith data HintReadWordChip.stateChannel.toRaw)))
    (store : Store) (hints : List Bytes) (current : (input env).previous.Binds store hints)
    (header : (input env).node.Binds store) (ending : (input env).endStep.word.Binds store)
    (words : ∀ row ∈ TransitionView.readIndexedRows HintReadCoverage.variants tables data,
      ((HintReadCoverage.rowInput row).step row.1).word.Binds store) :
    ∃ bytes rest, hints = bytes :: rest ∧ (input env).next.Binds store rest ∧
      Word.toNat (input env).span.length.value = bytes.length ∧
      ((TransitionView.readIndexedRows HintReadCoverage.variants tables data).map HintReadWrites.produced).Perm
        (wordWrites (Address.toNat (input env).span.start) bytes) := by
  obtain ⟨node, rest, read, head, next, length, count⟩ :=
    HostHintReadChip.node_effect_of_spec (input env) valid store hints current header ending
  rw [handler_cursor] at balanced
  obtain ⟨path, perm, _, inventory, _⟩ := HintReadWrites.ordered_writes tables data
    (input env).first (input env).final aligned wordSpecs balanced store node read words
    (by simp [HostHintReadChip.Inputs.first, Address.toNat]) count
  refine ⟨node.bytes, rest, head, next, ?_, ?_⟩
  · have argument : (input env).call.arg2 = (input env).span.length.value := valid.2.2.2.2.1
    rwa [argument] at length
  · exact (perm.map HintReadWrites.produced).symm.trans (List.Perm.of_eq inventory)

omit [Fact (2 ^ 25 < p)] in
private theorem run_of_hint [Fact (2 ^ 17 < p)]
    (input : HostHintReadChip.Inputs (ZMod p)) (valid : HostHintReadChip.Spec input)
    (host : HostState) (store : Store) (current : input.previous.Binds store host.io.hints)
    (header : input.node.Binds store) (ending : input.endStep.word.Binds store)
    (bytes : Bytes) (rest : List Bytes) (hints : host.io.hints = bytes :: rest)
    (length : Word.toNat input.span.length.value = bytes.length)
    (running : host.exitCode = none) (policy : HostPolicy) (context : HostReadContext)
    (permitted : policy.memory.permits (Address.toNat input.span.start) (hintWriteBytes bytes).length = true)
    (code : context.register 5 = some (Word.toBitVec64 input.call.code))
    (arg1 : context.register 10 = some (Word.toBitVec64 input.call.arg1))
    (arg2 : context.register 11 = some (Word.toBitVec64 input.call.arg2)) :
    host.run policy context = some (HostHintReadChip.execution input host bytes rest) := by
  rw [hintWriteBytes_length, ← length] at permitted
  obtain ⟨actual, suffix, actualHints, _, _, executed⟩ := HostHintReadChip.run_of_spec input valid
    host store current header ending running policy context permitted code arg1 arg2
  obtain ⟨rfl, rfl⟩ := List.cons.inj (hints.symm.trans actualHints)
  exact executed

/-- The physical consumer subsystem agrees with the full concrete call, including padded memory effects. -/
theorem run_of_tables (env : Environment (ZMod p)) (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (valid : handler.Spec env)
    (aligned : List.Forall₂ (fun last table => (HintReadCoverage.view last).component = table.component)
      HintReadCoverage.variants tables)
    (wordSpecs : HintReadCoverage.Steps tables data)
    (balanced : BalancedInteractions
      (handler.operations.interactionValuesWith HintReadWordChip.stateChannel.toRaw env ++
        tables.flatMap (·.interactionsWith data HintReadWordChip.stateChannel.toRaw)))
    (host : HostState) (store : Store) (current : (input env).previous.Binds store host.io.hints)
    (header : (input env).node.Binds store) (ending : (input env).endStep.word.Binds store)
    (words : ∀ row ∈ TransitionView.readIndexedRows HintReadCoverage.variants tables data,
      ((HintReadCoverage.rowInput row).step row.1).word.Binds store)
    (running : host.exitCode = none) (policy : HostPolicy) (context : HostReadContext)
    (permissions : ∀ request, WritePermissionProvider.channel.pulledValue request ∈
      tables.flatMap (·.interactionsWith data WritePermissionProvider.channel.toRaw) →
      policy.memory.permits (Address.toNat request) 1 = true)
    (code : context.register 5 = some (Word.toBitVec64 (input env).call.code))
    (arg1 : context.register 10 = some (Word.toBitVec64 (input env).call.arg1))
    (arg2 : context.register 11 = some (Word.toBitVec64 (input env).call.arg2)) :
    ∃ bytes rest, host.io.hints = bytes :: rest ∧ (input env).next.Binds store rest ∧
      host.run policy context = some (HostHintReadChip.execution (input env) host bytes rest) ∧
      ((TransitionView.readIndexedRows HintReadCoverage.variants tables data).map HintReadWrites.produced).Perm
        (wordWrites (Address.toNat (input env).span.start) bytes) := by
  obtain ⟨bytes, rest, hints, next, length, inventory⟩ :=
    complete_writes env tables data valid aligned wordSpecs balanced store host.io.hints current header ending words
  have permitted := HintReadWriteLedger.permitted_of_inventory tables data aligned wordSpecs policy.memory
    (Address.toNat (input env).span.start) bytes inventory permissions
  exact ⟨bytes, rest, hints, next, run_of_hint (input env) valid host store current header ending
    bytes rest hints length running policy context permitted code arg1 arg2, inventory⟩

end SP1Clean.Soundness.HostHintReadWrites
