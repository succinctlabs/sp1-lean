import SP1Clean.Soundness.FinalMemoryCheckSoundness
import SP1Clean.Soundness.FinishedChannels
import SP1Clean.Model.SP1Field
import SP1CleanTest.Core.StaticMembership

/-! # Complete outgoing Memory assembly regression

The fixture executes the installed verifier, finalizers, target validators, and actual Byte/Range
providers. Every channel is registered and balanced, including Memory and final ordering. The
auxiliary Memory provider supplies zero-clock records: this checks the boundary subsystem, not
an execution from the source snapshot. Mixed execution grounding authenticates those records.
-/

namespace SP1CleanTest.Alignment.Core.FinalMemoryChecks

open Circuit Air.Flat SP1Clean SP1Clean.Soundness SP1Clean.Model.Core

private abbrev Fp := ZMod SP1Prime
private abbrev Row := ℕ × List Fp
private abbrev Ledger := List (String × List Fp × Fp)

private def source : MemorySnapshot := ⟨Vector.replicate 32 0, ⟨[]⟩⟩
private def target : MemorySnapshot :=
  ⟨source.registers.set 1 123, ⟨[(65536, 9), (65543, 17)]⟩⟩

private def auxiliary : List (Component Fp) :=
  { circuit := MemoryProviderChip.circuit } :: (sp1ProviderTables (p := SP1Prime)).take 23

private theorem names (target : MemorySnapshot) :
    (((FinalMemoryEnsemble.inventory (p := SP1Prime)).views.map TransitionView.component ++
      (Soundness.FinalMemoryChecks.checkTables target ++ auxiliary)).map
        (fun component : Component Fp => component.circuit.name)).Nodup := by
  simp only [Soundness.FinalMemoryChecks.checkTables, List.map_append, List.map_cons, List.map_nil,
    StaticTable.component, StaticTable.provider, FinalRegisterValue.membership, InitialMemoryLookup.membership]
  exact of_decide_eq_true rfl

private def assembly (target : MemorySnapshot) :=
  Soundness.FinalMemoryChecks.ensemble source target auxiliary [] (names target)

/-- The real provider family satisfies the static interface used by the soundness theorem. -/
theorem resourceInterface (target : MemorySnapshot) : Soundness.FinalMemoryChecks.Interface target auxiliary := by
  have members (component : Component Fp) (member : component ∈ auxiliary) :
      component ∈ (sp1Ensemble (p := SP1Prime)).tables := by
    apply List.mem_append_right
    rcases List.mem_cons.mp member with rfl | provider
    · rw [sp1ProviderTables_explicit]
      simp
    · exact List.mem_of_mem_take provider
  have silence : auxiliary.all (fun component =>
      !(component.circuit.channels.map RawChannel.name).contains "sp1.native.target_registers" &&
      !(component.circuit.channels.map RawChannel.name).contains "sp1.native.target_memory" &&
      !(component.circuit.channels.map RawChannel.name).contains "SP1FinalRegisterValue" &&
      !(component.circuit.channels.map RawChannel.name).contains "SP1FinalRamValue" &&
      !(component.circuit.channels.map RawChannel.name).contains "SP1FinalMemoryChange") = true := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro channel known component member used
    have silent := List.all_eq_true.mp silence component member
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    simp only [Soundness.FinalMemoryChecks.membershipChannels, List.mem_cons, List.not_mem_nil, or_false] at known
    rcases known with rfl | rfl <;>
      simp only [StaticTable.channel, FinalRegisterValue.membership, InitialMemoryLookup.membership, Channel.toRaw] at present <;>
      rw [present] at silent <;> simp at silent
  · intro component member env checked
    exact sp1_component_finished_requirements component (members component member)
      Channels.byteChannel.toRaw (by simp [Channels.byteChannel, Channels.stateChannel,
        Channels.memoryChannel, Channel.toRaw]) env checked
  · intro ram component member used
    have silent := List.all_eq_true.mp silence component member
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    cases ram <;> simp only [FinalMemoryValue.channel, Channel.toRaw, Bool.false_eq_true, ↓reduceIte] at present <;>
      rw [present] at silent <;> simp at silent
  · intro component member used
    have silent := List.all_eq_true.mp silence component member
    have present := List.contains_iff_mem.mpr (List.mem_map_of_mem (f := RawChannel.name) used)
    change (component.circuit.channels.map RawChannel.name).contains "SP1FinalMemoryChange" = true at present
    rw [present] at silent
    simp at silent

private def word (value : ℕ) : Word Fp := Target.bitVecToWord (BitVec.ofNat 64 value)

private def record (address value : ℕ) : Channels.MemoryMsg Fp :=
  ⟨0, 0, (word address)[0], (word address)[1], (word address)[2], word value⟩

private def registers := record 1 123
private def ram := record 65536 (target.memory.readWord 65536).toNat

private def finalizer (index previous : ℕ) (record : Channels.MemoryMsg Fp) : Row :=
  (index, (toElements (OrderedMemoryProvider.populate record previous
    (Word.toNat (MemoryBoundary.address record)))).toList)

private def memory (record : Channels.MemoryMsg Fp) : Row :=
  (7, (toElements (⟨record.clk_high, record.clk_low, record.addr0, record.addr1,
    record.addr2, record.value, 1⟩ : MemoryProviderChip.Inputs Fp)).toList)

private def registerCheck (record : Channels.MemoryMsg Fp) (selected : Fp) : Row :=
  (3, (toElements (⟨record, selected⟩ : FinalRegisterCheck.Inputs Fp)).toList)

private def ramCheck (record : Channels.MemoryMsg Fp) (selected : Fp) : Row :=
  (4, (toElements (⟨record, selected⟩ : FinalRamCheck.Inputs Fp)).toList)

private def terminal (previous : ℕ) : Row :=
  (2, (toElements (OrderedBoundaryEnd.populate (word previous)
    (OrderedMemoryEnsemble.endKey (p := SP1Prime)))).toList)

private def rows : List Row :=
  [finalizer 0 0 registers, finalizer 1 2 ram, terminal 65537,
    registerCheck registers 1, ramCheck ram 1, memory registers, memory ram]

private def evaluate (_target : MemorySnapshot) (component : Component Fp) (inputs : List Fp) :
    Bool × Ledger :=
  let program := component.circuit.main component.rowInputVar
  let env := (program.proverEnvironment (ProverHint.empty Fp) inputs).toEnvironment
  let operations := (program.operations component.rowOffset).toFlat
  let valid := inputs.length == component.rowOffset && operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup .. => false
    | .witness .. | .interact .. => true
  (valid, (FlatOperation.interactions operations).map fun interaction =>
    (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult))

private def evaluateRow (target : MemorySnapshot) (row : Row) : Bool × Ledger :=
  match (assembly target).tables[row.1]? with
  | none => (false, [])
  | some component => evaluate target component row.2

private def byteProvider (entry : String × List Fp × Fp) : Option Row :=
  if entry.1 != "SP1Byte" || entry.2.2 == 0 then none else
  match entry.2.1 with
  | [opcode, a, b, c] =>
    if opcode == 3 then some (9, [b, c, -entry.2.2])
    else if opcode == 4 then some (13, [b, c, -entry.2.2])
    else if opcode == 5 then some (9, [b, -entry.2.2])
    else if opcode == 6 && b.val < 17 then some (14 + b.val, [a, -entry.2.2])
    else some (31, [])
  | _ => some (31, [])

private def verifierLedger (target : MemorySnapshot) : Ledger :=
  let env : Environment Fp := Environment.fromInput (Input := unit) () (fun _ _ => #[])
  (assembly target).verifierOperations.interactions.map fun interaction =>
    let value := AbstractInteraction.eval env interaction
    (value.channel.name, value.msg.toList, value.mult)

private def check (target : MemorySnapshot) (rows : List Row) (supplyBytes : Bool := true) : Bool :=
  let initial := (true, verifierLedger target) :: rows.map (evaluateRow target)
  let providers := if supplyBytes then (initial.flatMap Prod.snd).filterMap byteProvider else []
  let evaluated := initial ++ providers.map (evaluateRow target)
  let consumerLedger := evaluated.flatMap Prod.snd
  let ledger := consumerLedger ++ StaticMembership.providerLedger
    (FinalRegisterValue.membership target) consumerLedger ++ StaticMembership.providerLedger
      (InitialMemoryLookup.membership target.memory (2 ^ 48) "sp1.native.target_memory") consumerLedger
  evaluated.all Prod.fst && decide (ledger.length < SP1Prime) &&
    ledger.all fun (name, message, _) =>
      ((assembly target).channels.map RawChannel.name).contains name &&
        ((ledger.filter fun entry => entry.1 == name && entry.2.1 == message).map (·.2.2)).sum == 0

/-- Changed register and sparse RAM pass the complete installed boundary AIR. -/
theorem completeAcceptance : check target rows = true := by native_decide

private def projectedByteBalance : Bool :=
  let head := (true, verifierLedger target)
  let original := head :: rows.map (evaluateRow target)
  let providers := (original.flatMap Prod.snd).filterMap byteProvider
  let projected := head :: (rows.filter (fun row => row.1 != 4)).map (evaluateRow target)
  let ledger := (projected ++ providers.map (evaluateRow target)).flatMap Prod.snd
  let bytes := ledger.filter (fun entry => entry.1 == "SP1Byte")
  bytes.all fun entry => ((bytes.filter (fun other => other.2.1 == entry.2.1)).map (·.2.2)).sum == 0

/-- Dropping the target-RAM consumer from a valid full witness leaves its providers unmatched.
Proof views must inherit Byte guarantees; they cannot inherit whole Byte balance. -/
theorem projectionLosesByteBalance : projectedByteBalance = false := by native_decide

/-- Empty identity inventories still retain the canonical ordering terminal and its Byte closure. -/
theorem emptyIdentity : check source [terminal 0] = true := by native_decide

private def mutationResults : List Bool :=
    [check target (rows.filter (fun row => row.1 != 4)),
     check target (rows ++ [ramCheck ram 1]),
     check target (rows.map fun row => if row.1 == 3 then registerCheck registers 0 else row),
     check target (rows.map fun row => if row.1 == 3 then registerCheck registers 2 else row),
     check target (rows.map fun row => if row.1 == 4 then ramCheck { ram with clk_low := 1 } 1 else row),
     check { target with registers := target.registers.set 31 17 } rows,
     check { target with memory := target.memory.write 65544 1 } rows,
     check { target with memory := target.memory.write 65543 18 } rows,
     check target rows false,
     check target (rows.filter (fun row => row.1 != 2)),
     check target (rows.filter (fun row => row.1 != 7))]

/-- Complete-record matching, Boolean selection, target coverage, Byte closure, and final order
are all enforced by the same accepted witness. -/
theorem rejectsMutations : mutationResults = List.replicate 11 false := by native_decide

end SP1CleanTest.Alignment.Core.FinalMemoryChecks
