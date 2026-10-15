import SP1Clean.Soundness.FinalMemoryReceipts
import SP1Clean.Native.Operations.FinalRegisterValue
import SP1Clean.Native.Operations.FinalRamValue
import SP1Clean.Model.SP1Field

/-! # Physical finalizer receipt installation

The fixture builds the original ordered finalizers and real target-check consumers, then
installs receipts on the same arrays and reads Clean's canonical interaction ledger. Only the
two receipt balances are claimed here; execution Memory balance and target-check Byte closure
belong to the enclosing machine.
-/

namespace SP1CleanTest.Alignment.Core.FinalMemoryReceipts

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness

private abbrev Fp := ZMod SP1Prime

private def target : MemorySnapshot := ⟨Vector.replicate 32 0, ⟨[]⟩⟩

private def record (address clock : ℕ) : Channels.MemoryMsg Fp :=
  let word := Target.bitVecToWord (p := SP1Prime) (BitVec.ofNat 64 address)
  ⟨0, clock, word[0], word[1], word[2], Target.bitVecToWord 0⟩

private def consumers : List (Component Fp) :=
  [{ circuit := FinalRegisterValue.circuit target }, { circuit := FinalRamValue.circuit target }]

private theorem names :
    (((FinalMemoryEnsemble.inventory (p := SP1Prime)).views.map (·.component) ++ consumers).map
      (·.circuit.name)).Nodup := by decide

private def original (registers ram : List (Channels.MemoryMsg Fp))
    (checkedRegisters checkedRam : List (Channels.MemoryMsg Fp)) :
    EnsembleWitness (FinalMemoryEnsemble.ensemble consumers [] names) :=
  EnsembleWitness.ofTables _
    [Table.build { circuit := OrderedFinalProvider.registerCircuit }
      (registers.map fun item => OrderedMemoryProvider.populate item 0
        (Word.toNat (MemoryBoundary.address item))) (fun _ _ => #[]) (ProverHint.empty Fp),
     Table.build { circuit := OrderedFinalProvider.ramCircuit }
      (ram.map fun item => OrderedMemoryProvider.populate item 2
        (Word.toNat (MemoryBoundary.address item))) (fun _ _ => #[]) (ProverHint.empty Fp),
     Table.build (FinalMemoryEnsemble.viewFor .terminal).component []
      (fun _ _ => #[]) (ProverHint.empty Fp),
     Table.build { circuit := FinalRegisterValue.circuit target } checkedRegisters
      (fun _ _ => #[]) (ProverHint.empty Fp),
     Table.build { circuit := FinalRamValue.circuit target }
      checkedRam (fun _ _ => #[]) (ProverHint.empty Fp)]
    () (by rfl)

private def ledger {ens : Ensemble Fp unit} (witness : EnsembleWitness ens)
    (name : String) : List (Array Fp × Fp) :=
  (witness.interactions.filter fun interaction => interaction.channel.name == name).map
    fun interaction => (interaction.msg, interaction.mult)

private def balanced (interactions : List (Array Fp × Fp)) : Bool :=
  interactions.length < SP1Prime && interactions.all fun interaction =>
    ((interactions.filter fun other => other.1 == interaction.1).map Prod.snd).sum == 0

private def receipts (registers ram checkedRegisters checkedRam : List (Channels.MemoryMsg Fp)) : Bool :=
  let witness := Soundness.FinalMemoryReceipts.lift (original registers ram checkedRegisters checkedRam)
  balanced (ledger witness "SP1FinalRegisterValue") && balanced (ledger witness "SP1FinalRamValue")

/-- Receipt insertion retains the original arrays, heights, and decoded Memory inventory. -/
theorem physicalRoundTrip :
    let before := original [record 31 273, record 1 9] [record 65536 281]
      [record 1 9, record 31 273] [record 65536 281]
    let after := Soundness.FinalMemoryReceipts.lift before
    (after.tables.map (·.table)) = before.tables.map (·.table) ∧
      after.tableHeights = before.tableHeights ∧
      (FinalMemoryEnsemble.records (Soundness.FinalMemoryReceipts.original after)).map toElements =
        [record 31 273, record 1 9, record 65536 281].map toElements ∧
      ledger after "SP1Byte" = ledger before "SP1Byte" ∧
      ledger after "SP1Memory" = ledger before "SP1Memory" := by
  native_decide

/-- Actual installed receipts reject missing, duplicated, wrong-clock and wrong-kind consumers;
physical row order and empty inventories remain immaterial. -/
theorem receiptMutation :
    [receipts [record 31 273, record 1 9] [record 65536 281]
        [record 1 9, record 31 273] [record 65536 281],
     receipts [record 1 9] [] [] [],
     receipts [record 1 9] [] [record 1 9, record 1 9] [],
     receipts [record 1 9] [] [record 1 10] [],
     receipts [record 1 9] [] [] [record 1 9],
     receipts [] [] [] []] = [true, false, false, false, false, true] := by
  native_decide

end SP1CleanTest.Alignment.Core.FinalMemoryReceipts
