import SP1Clean.Soundness.HintReadWrites

/-! # Actual Memory and byte-permission ledgers of complete hint consumers

These projections retain every physical consumer occurrence. They connect the semantic word
inventory to the real Memory pull/push pairs and all eight requested byte permissions per row;
they do not supply predecessor currency or permission-provider authentication themselves.
-/

namespace SP1Clean.Soundness.HintReadWriteLedger

open Circuit Air.Flat HintReadCoverage
open Model.Core Model.Core.HintQueue

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

omit [Fact (2 ^ 25 < p)] in
private theorem eval_memory (env : Environment (ZMod p)) (input : Var HintReadWordChip.Inputs (ZMod p)) :
    Eval.eval env input.ram.prior = (Eval.eval env input).ram.prior ∧
      Eval.eval env input.ram.pushed = (Eval.eval env input).ram.pushed := by
  rcases input with ⟨ram, pointer, index, nextIndex, nextAddress⟩
  rcases ram with ⟨⟨value, ⟨previousHigh, previousLow⟩⟩, high, low0, low1, addr0, addr1, addr2, newValue⟩
  simp only [HostRamAccessChip.Inputs.prior, HostRamAccessChip.Inputs.pushed,
    HostRamAccessChip.Inputs.clockLow, circuit_norm]

omit [Fact (2 ^ 25 < p)] in
private theorem eval_permission (env : Environment (ZMod p))
    (input : Var HintReadWordChip.Inputs (ZMod p)) (index : ZMod p) :
    Eval.eval env (Address.offset input.address (.const index)) =
      Address.offset (Eval.eval env input).address index := by
  rcases input with ⟨ram, pointer, position, nextIndex, nextAddress⟩
  rcases ram with ⟨access, high, low0, low1, addr0, addr1, addr2, value⟩
  simp only [Address.offset, HintReadWordChip.Inputs.address, circuit_norm]

/-- One physical consumer emits precisely its prior/new Memory pair. -/
theorem row_memory_values (row : Row (p := p)) :
    (view row.1).component.operations.interactionValuesWith Channels.memoryChannel.toRaw row.2 =
      [Channels.memoryChannel.pulledValue (rowInput row).ram.prior,
       Channels.memoryChannel.pushedValue (rowInput row).ram.pushed] := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change ((HintReadWordChip.main row.1 (varFromOffset HintReadWordChip.Inputs 0)).operations
    (size HintReadWordChip.Inputs)).interactionValuesWith Channels.memoryChannel.toRaw row.2 = _
  rw [HintReadWordChip.memory_values, (eval_memory _ _).1, (eval_memory _ _).2,
    eval_varFromOffset_valueFromOffset]
  rfl

/-- The complete per-row permission list includes every byte in the padding word. -/
theorem row_permission_values (row : Row (p := p)) :
    (view row.1).component.operations.interactionValuesWith WritePermissionProvider.channel.toRaw row.2 =
      List.ofFn (fun index : Fin 8 => WritePermissionProvider.channel.pulledValue
        (Address.offset (rowInput row).address (index.val : ZMod p))) := by
  simp only [Operations.interactionValuesWith, Component.interactionsWith_eq]
  change (((HintReadWordChip.main row.1 (varFromOffset HintReadWordChip.Inputs 0)).operations
    (size HintReadWordChip.Inputs)).interactionsWith WritePermissionProvider.channel.toRaw).map
      (fun interaction => interaction.eval row.2) = _
  rw [HintReadWordChip.main_permission_interactions]
  simp only [List.map_ofFn, Function.comp_def, Channel.eval_pulled, eval_permission,
    eval_varFromOffset_valueFromOffset]
  rfl

/-- Physical table projection introduces no extra Memory transfers and drops none. -/
theorem memory_ledger (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables) :
    tables.flatMap (·.interactionsWith data Channels.memoryChannel.toRaw) =
      (TransitionView.readIndexedRows variants tables data).flatMap (fun row =>
        [Channels.memoryChannel.pulledValue (rowInput row).ram.prior,
         Channels.memoryChannel.pushedValue (rowInput row).ram.pushed]) := by
  rw [TransitionView.readIndexedRows_interactions variants (fun last => (view last).component)
    tables data Channels.memoryChannel.toRaw aligned]
  apply List.flatMap_congr
  intro row _
  exact row_memory_values row

/-- Physical table projection identifies every permission requested by the complete word inventory. -/
theorem permission_ledger (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables) :
    tables.flatMap (·.interactionsWith data WritePermissionProvider.channel.toRaw) =
      (TransitionView.readIndexedRows variants tables data).flatMap (fun row =>
        List.ofFn (fun index : Fin 8 => WritePermissionProvider.channel.pulledValue
          (Address.offset (rowInput row).address (index.val : ZMod p)))) := by
  rw [TransitionView.readIndexedRows_interactions variants (fun last => (view last).component)
    tables data WritePermissionProvider.channel.toRaw aligned]
  apply List.flatMap_congr
  intro row _
  exact row_permission_values row

/-- Authenticating the actual byte pulls permits the complete semantic write, including padding. -/
theorem permitted_of_inventory (tables : List (Table (ZMod p))) (data : ProverData (ZMod p))
    (aligned : List.Forall₂ (fun last table => (view last).component = table.component) variants tables)
    (valid : Steps tables data) (policy : HostMemoryPolicy) (address : ℕ) (bytes : Bytes)
    (inventory : ((TransitionView.readIndexedRows variants tables data).map HintReadWrites.produced).Perm
      (wordWrites address bytes))
    (permissions : ∀ request, WritePermissionProvider.channel.pulledValue request ∈
      tables.flatMap (·.interactionsWith data WritePermissionProvider.channel.toRaw) →
      policy.permits (Address.toNat request) 1 = true) :
    policy.permits address (hintWriteBytes bytes).length = true := by
  apply permits_of_word_bytes
  intro index bound slot
  have entry : (address + index * 8, wordValue bytes index) ∈ wordWrites address bytes :=
    List.mem_map.mpr ⟨index, List.mem_range.mpr bound, rfl⟩
  obtain ⟨row, member, equal⟩ := List.mem_map.mp (inventory.mem_iff.mpr entry)
  have requested := permissions (Address.offset (rowInput row).address (slot.val : ZMod p)) (by
    rw [permission_ledger tables data aligned]
    exact List.mem_flatMap.mpr ⟨row, member, List.mem_ofFn.mpr ⟨slot, rfl⟩⟩)
  have addressEqual := congrArg Prod.fst equal
  change Address.toNat (rowInput row).address = address + index * 8 at addressEqual
  have bounded : Address.Bounded (rowInput row).address := (valid row member).2.2.1
  rw [Address.toNat_offset _ bounded
    slot.val (by have := slot.isLt; omega), addressEqual] at requested
  exact requested

omit [Fact (2 ^ 25 < p)] in
/-- Each physically emitted new Memory value agrees with the byte-level host update. -/
theorem memory_readback (tables : List (Table (ZMod p))) (data : ProverData (ZMod p)) (address : ℕ) (bytes : Bytes)
    (inventory : ((TransitionView.readIndexedRows variants tables data).map HintReadWrites.produced).Perm
      (wordWrites address bytes)) (memory : ByteMemory)
    (row : Row (p := p)) (member : row ∈ TransitionView.readIndexedRows variants tables data) :
    (memory.writeBytes address (hintWriteBytes bytes)).readWord (Address.toNat (rowInput row).address) =
      Word.toBitVec64 (rowInput row).ram.pushed.value := by
  exact wordWrites_readback memory address bytes (HintReadWrites.produced row)
    (inventory.mem_iff.mp (List.mem_map.mpr ⟨row, member, rfl⟩))

end SP1Clean.Soundness.HintReadWriteLedger
