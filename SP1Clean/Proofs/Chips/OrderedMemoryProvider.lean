import SP1Clean.FormalModel.Contracts.OrderedMemoryProvider
import SP1Clean.Native.Operations.OrderedBoundary
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Model.Semantics.Decode
import SP1Clean.Model.Core.MemoryTable

/-! # Canonical memory records with checked ordering

The same wrapper serves initialization and finalization. It preserves the provider's semantic
record contract and constrains the control key to the canonical address plus one. The sentinel
zero therefore precedes x0, and the increment cannot wrap for canonical 48-bit locations.
-/

namespace SP1Clean.OrderedMemoryProvider

open Circuit SP1Clean.Model.Core SP1Clean.Semantics SP1Clean.Channels SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]
variable {Payload : TypeMap} [ProvableType Payload]

private def oneWord : Word (ZMod p) := bitVecToWord 1

omit [Fact (2 ^ 17 < p)] in
private theorem key_of_addition (record : MemoryMsg (ZMod p))
    (current : Word (ZMod p)) (valid : MemoryBoundary.CanonicalSpec record)
    (currentBound : Word.isU64 current)
    (addition : Word.toBitVec64 current = Word.toBitVec64 (MemoryBoundary.address record) + 1) :
    Word.toNat current = (MemoryMsg.locOf record).busAddress + 1 := by
  have address := valid.2
  have bound := MemLoc.busAddress_lt_two_pow_48 valid.1
  have equal := congrArg BitVec.toNat addition
  rw [Word.toBitVec64_toNat currentBound, BitVec.toNat_add,
    Word.toBitVec64_toNat address.1, address.2,
    show (1 : BitVec 64).toNat = 1 by decide] at equal
  exact equal.trans (Nat.mod_eq_of_lt (by omega))

def main (name : String) (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (input : Var (Inputs Payload) (ZMod p)) : Circuit (ZMod p) (Var MemoryMsg (ZMod p)) := do
  let record ← provider input.payload
  let _ ← OrderedBoundary.circuit name input.link
  assertion AddOperation.circuit
    ⟨MemoryBoundary.address record, const oneWord, ⟨input.link.current⟩, 1⟩
  return record

/-- Retain the provider's chosen metadata explicitly, including when its input and output
are both Memory messages. Re-synthesizing its output instance can obscure that identity. -/
instance elaborated (name : String) (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg) :
    ElaboratedCircuit (ZMod p) (Inputs Payload) MemoryMsg (main name provider) where
  localLength input := provider.localLength input.payload + 128
  output input offset := provider.output input.payload offset
  channelsWithGuarantees := provider.channelsWithGuarantees ++
    [byteChannel.toRaw, (OrderedBoundary.channel name).toRaw,
      byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw]

/-- The wrapper's control interactions are precisely the checked predecessor/current pair.
The provider's interface must omit this private channel; its Memory/Byte effects remain intact. -/
theorem main_interactions (name : String) (distinct : name ≠ "SP1Byte")
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (privateChannel : (OrderedBoundary.channel name).toRaw ∉ provider.channels)
    (input : Var (Inputs Payload) (ZMod p)) (offset : ℕ) :
    ((main name provider input).operations offset).interactionsWith (OrderedBoundary.channel name).toRaw =
      [((OrderedBoundary.channel name).pulled input.link.previous).toRaw,
       ((OrderedBoundary.channel name).pushed input.link.current).toRaw] := by
  have providerEmpty (payload : Var Payload (ZMod p)) (n : ℕ) :=
    InteractionRecovery.interactionsWith_main_eq_nil provider.base
      (OrderedBoundary.channel name).toRaw payload n privateChannel
  have addEmpty (args : Var AddOperation.Inputs (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil AddOperation.circuit
      (OrderedBoundary.channel name).toRaw args
      (by change (OrderedBoundary.channel (p := p) name).toRaw ∉
            [Channels.byteChannel.toRaw, Channels.byteChannel.toRaw, Channels.byteChannel.toRaw, Channels.byteChannel.toRaw]
          simp only [List.mem_cons, List.not_mem_nil, OrderedBoundary.channel_ne_byte name distinct, or_self, not_false_eq_true])
      (by change (OrderedBoundary.channel (p := p) name).toRaw ∉ []; exact List.not_mem_nil) (n := n)
  simp only [main, circuit_norm, addEmpty, List.append_nil]
  have linkExact (n : ℕ) := OrderedBoundary.main_interactions name distinct input.link n
  simp only [Operations.interactionsWith] at providerEmpty linkExact
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, providerEmpty,
    OrderedBoundary.circuit, linkExact, List.nil_append]
  rfl

/-- Ordering adds no Memory interactions: the provider's ledger is retained verbatim. -/
theorem main_memory_interactions (name : String)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (input : Var (Inputs Payload) (ZMod p)) (offset : ℕ) :
    ((main name provider input).operations offset).interactionsWith memoryChannel.toRaw =
      ((provider.main input.payload).operations offset).interactionsWith memoryChannel.toRaw := by
  have linkEmpty (n : ℕ) := InteractionRecovery.interactionsWith_main_eq_nil
    (OrderedBoundary.circuit (p := p) name).base memoryChannel.toRaw input.link n (by
      simp [OrderedBoundary.circuit, circuit_norm,
        OrderedBoundary.channel, memoryChannel, byteChannel])
  have addEmpty (args : Var AddOperation.Inputs (ZMod p)) (n : ℕ) :=
    InteractionRecovery.filter_interactions_formalAssertion_eq_nil AddOperation.circuit
      memoryChannel.toRaw args
      (by change memoryChannel.toRaw ∉ [byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw, byteChannel.toRaw]
          simp only [List.mem_cons, List.not_mem_nil, memoryChannel_eq_byteChannel_false, or_self, not_false_eq_true])
      (by change memoryChannel.toRaw ∉ []; exact List.not_mem_nil) (n := n)
  simp only [main, circuit_norm, addEmpty, List.append_nil]
  simp only [Operations.interactionsWith] at linkEmpty ⊢
  simp only [GeneralFormalCircuit.toSubcircuit_interactions, linkEmpty, List.append_nil]

def circuit (name : String) (recordSpec : MemoryMsg (ZMod p) → Prop)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (binds : ∀ input output data, provider.Spec input output data → recordSpec output)
    (canonical : ∀ record, recordSpec record → MemoryBoundary.CanonicalSpec record) :
    GeneralFormalCircuit (ZMod p) (Inputs Payload) MemoryMsg where
  name := s!"{provider.name}.{name}"
  main := main name provider
  elaborated := elaborated name provider
  Assumptions input data := provider.Assumptions input.payload data
  Spec input output _ := Spec recordSpec input.link output
  ProverAssumptions input data hint :=
    provider.ProverAssumptions input.payload data hint ∧ provider.Assumptions input.payload data ∧
      OrderedBoundary.ProverAssumptions input.link ∧
        ∀ output, provider.Spec input.payload output data →
          Word.toBitVec64 input.link.current = Word.toBitVec64 (MemoryBoundary.address output) + 1
  channelsWithRequirements := provider.channelsWithRequirements ++ [(OrderedBoundary.channel name).toRaw]
  soundness := by
    circuit_proof_start [OrderedBoundary.circuit, MemoryBoundary.address]
    have one : Vector.map (Expression.eval env) (Vector.map Expression.const (oneWord (p := p))) =
        oneWord := by simp only [Vector.map_map, Function.comp_def, Expression.eval]; exact Vector.map_id _
    rw [one] at h_holds
    have valid := binds _ _ _ (h_holds.1 h_assumptions)
    have canonicalRecord := canonical _ valid
    -- `circuit_norm` puts the record's projections in the constraint form the goal carries
    have addition := h_holds.2.2 ⟨fun _ =>
      ⟨by simpa only [MemoryBoundary.address, circuit_norm] using canonicalRecord.2.1,
        isU64_bitVecToWord _⟩, Or.inr rfl⟩
    have key := key_of_addition _ _ canonicalRecord h_holds.2.1.2.1 (by
      simpa only [oneWord, toBitVec64_bitVecToWord, MemoryBoundary.address, circuit_norm]
        using (addition rfl).2)
    exact ⟨⟨valid, h_holds.2.1, key⟩, Or.inr h_assumptions⟩
  completeness := by
    circuit_proof_start [OrderedBoundary.circuit, MemoryBoundary.address]
    have one : Vector.map (Expression.eval env.toEnvironment)
        (Vector.map Expression.const (oneWord (p := p))) = oneWord := by
      simp only [Vector.map_map, Function.comp_def, Expression.eval]
      exact Vector.map_id _
    rw [one]
    have spec := (h_env.1 h_assumptions.1).1 h_assumptions.2.1
    have valid := binds _ _ _ spec
    have canonicalRecord := canonical _ valid
    refine ⟨h_assumptions.1, h_assumptions.2.2.1,
      ⟨⟨fun _ => ⟨by simpa only [MemoryBoundary.address, circuit_norm] using canonicalRecord.2.1,
        isU64_bitVecToWord _⟩, Or.inr rfl⟩, ?_⟩⟩
    intro _
    refine ⟨h_assumptions.2.2.1.1.2.1, ?_⟩
    simpa only [oneWord, toBitVec64_bitVecToWord, MemoryBoundary.address, circuit_norm]
      using h_assumptions.2.2.2 _ spec

/-- Construct the control columns from the payload and its semantic address. -/
def populate (payload : Payload (ZMod p)) (previous address : ℕ) : Inputs Payload (ZMod p) :=
  ⟨payload, OrderedBoundary.populate (bitVecToWord (BitVec.ofNat 64 previous))
    (bitVecToWord (BitVec.ofNat 64 (address + 1)))⟩

/-- A provider that preserves its query admits the ordered wrapper's honest constructor.
In particular, the universally quantified internal output condition is discharged here rather
than left as a compiler-readiness condition on an execution. -/
theorem populate_assumptions (name : String) (recordSpec : MemoryMsg (ZMod p) → Prop)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (query : Payload (ZMod p) → ℕ)
    (bindsAt : ∀ input output data,
      provider.Spec input output data → recordSpec output ∧
        Word.toNat (MemoryBoundary.address output) = query input)
    (canonical : ∀ record, recordSpec record → MemoryBoundary.CanonicalSpec record)
    (payload : Payload (ZMod p)) (previous : ℕ) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    (prover : provider.ProverAssumptions payload data hint) (assumes : provider.Assumptions payload data)
    (bound : query payload < 2 ^ 48) (increases : previous < query payload + 1) :
    (circuit name recordSpec provider (fun input output data spec => (bindsAt input output data spec).1) canonical).ProverAssumptions
      (populate payload previous (query payload)) data hint := by
  have previousBound : previous < 2 ^ 64 := by omega
  have currentBound : query payload + 1 < 2 ^ 64 := by omega
  refine ⟨prover, assumes, ?_, ?_⟩
  · apply OrderedBoundary.populate_assumptions _ _ (isU64_bitVecToWord _) (isU64_bitVecToWord _)
    rw [endpoint_toNat _ previousBound, endpoint_toNat _ currentBound]
    exact increases
  · intro output spec
    have valid := bindsAt payload output data spec
    have canonicalRecord := canonical _ valid.1
    change Word.toBitVec64 (bitVecToWord (BitVec.ofNat 64 (query payload + 1))) = _
    rw [toBitVec64_bitVecToWord]
    apply BitVec.eq_of_toNat_eq
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt currentBound, BitVec.toNat_add,
      Word.toBitVec64_toNat canonicalRecord.2.1, valid.2,
      show (1 : BitVec 64).toNat = 1 by decide, Nat.mod_eq_of_lt currentBound]

/-- Ordering preserves every provider lookup occurrence, including repeated keys. -/
@[circuit_norm] theorem main_lookups (name : String)
    (provider : GeneralFormalCircuit (ZMod p) Payload MemoryMsg)
    (input : Var (Inputs Payload) (ZMod p)) (offset : ℕ) :
    ((main name provider input).operations offset).lookups =
      ((provider.main input.payload).operations offset).lookups := by
  simp [main, OrderedBoundary.circuit, AddOperation.circuit, AddOperation.main, circuit_norm]

end SP1Clean.OrderedMemoryProvider
