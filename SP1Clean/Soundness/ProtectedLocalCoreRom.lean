import SP1Clean.Soundness.ProtectedStoreFootprints
import SP1Clean.Soundness.LocalCoreDecode

/-! # ROM write exclusion for every decoded local instruction

Decoder provenance identifies the same physical row in the protected witness. Store permission
proofs apply to those rows; the other instruction views have no memory write. Instruction cases
and table positions remain inside this transport, leaving one uniform semantic footprint theorem.
-/

namespace SP1Clean.Soundness.ProtectedLocalCore

open Circuit Air.Flat SP1Clean.Model.Core

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

private theorem instructionRows_physical {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    {decoded : DecodedInstructionRow p}
    (member : decoded ∈ LocalCore.instructionRows (localWitness witness)) :
    ∃ index : Fin 25,
      decoded.chip = (supportedChips (p := p))[index.val]'(by rw [supportedChips_length]; exact index.isLt) ∧
      decoded.physical ∈ (witness.tables[7 + index.val]'(by
        rw [← witness.same_length]; change 7 + index.val < (tables image source).length
        rw [tables_length]; omega)).table := by
  obtain ⟨index, chipBound, tableBound, same, physical⟩ := position_of_mem_decodeInstructionTables member
  have bound : index < 25 := by simpa only [supportedChips_length] using chipBound
  refine ⟨⟨index, bound⟩, same, ?_⟩
  simp only [LocalCore.instructionTables, List.getElem_take, List.getElem_drop] at physical
  rw [localWitness_table witness ⟨7 + index, by omega⟩] at physical
  exact physical

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem no_write_permitted (image : ProgramImage) (row : Trace.RowView (ZMod p))
    (empty : row.commit.memWrite = none) : Target.RowWritePermitted image row := by
  intro write same
  rw [empty] at same
  contradiction

omit [Fact p.Prime] [Fact (2 ^ 24 < p)] in
private theorem destination_memWrite {F : Type} [DecidableEq F] [Zero F] (flag : F) :
    (Trace.CommitEffect.destination flag).memWrite = none := by
  unfold Trace.CommitEffect.destination
  split <;> rfl

/-- Only the four store families need byte permissions; all other instruction views have no RAM write. -/
theorem supported_write_property (property : Trace.RowView (ZMod p) → Prop)
    (noWrite : ∀ row, row.commit.memWrite = none → property row) (id : InstructionChipId)
    (env : Environment (ZMod p))
    (byte : id = .storeByte →
      (({ circuit := StoreByteChip.circuit } : Component (ZMod p)).rowInput env).is_real = 1 →
      property (StoreByteChip.rowView
        (({ circuit := StoreByteChip.circuit } : Component (ZMod p)).rowInput env)
        (({ circuit := StoreByteChip.circuit } : Component (ZMod p)).rowOutput env)))
    (half : id = .storeHalf →
      (({ circuit := StoreHalfChip.circuit } : Component (ZMod p)).rowInput env).is_real = 1 →
      property (StoreHalfChip.rowView
        (({ circuit := StoreHalfChip.circuit } : Component (ZMod p)).rowInput env)
        (({ circuit := StoreHalfChip.circuit } : Component (ZMod p)).rowOutput env)))
    (word : id = .storeWord →
      (({ circuit := StoreWordChip.circuit } : Component (ZMod p)).rowInput env).is_real = 1 →
      property (StoreWordChip.rowView
        (({ circuit := StoreWordChip.circuit } : Component (ZMod p)).rowInput env)
        (({ circuit := StoreWordChip.circuit } : Component (ZMod p)).rowOutput env)))
    (double : id = .storeDouble →
      (({ circuit := StoreDoubleChip.circuit } : Component (ZMod p)).rowInput env).is_real = 1 →
      property (StoreDoubleChip.rowView
        (({ circuit := StoreDoubleChip.circuit } : Component (ZMod p)).rowInput env)
        (({ circuit := StoreDoubleChip.circuit } : Component (ZMod p)).rowOutput env)))
    : let chip := (supportedChipFor (p := p) id)
      (chip.kind.view (chip.table.rowInput env) (chip.table.rowOutput env)).is_real = 1 →
      property (chip.kind.view (chip.table.rowInput env) (chip.table.rowOutput env)) := by
  dsimp only
  cases id with
  | storeByte =>
    intro active
    exact byte rfl active
  | storeHalf =>
    intro active
    exact half rfl active
  | storeWord =>
    intro active
    exact word rfl active
  | storeDouble =>
    intro active
    exact double rfl active
  | jal | jalr | uType =>
    intro _
    apply noWrite
    exact destination_memWrite _
  | _ => intro _; exact noWrite _ rfl

/-- Uniform ROM exclusion, with instruction cases shared by all footprint properties. -/
theorem supported_write_permitted (image : ProgramImage) (id : InstructionChipId)
    (env : Environment (ZMod p))
    (byte : id = .storeByte →
      (({ circuit := StoreByteChip.circuit } : Component (ZMod p)).rowInput env).is_real = 1 →
      Target.RowWritePermitted image (StoreByteChip.rowView
        (({ circuit := StoreByteChip.circuit } : Component (ZMod p)).rowInput env)
        (({ circuit := StoreByteChip.circuit } : Component (ZMod p)).rowOutput env)))
    (half : id = .storeHalf →
      (({ circuit := StoreHalfChip.circuit } : Component (ZMod p)).rowInput env).is_real = 1 →
      Target.RowWritePermitted image (StoreHalfChip.rowView
        (({ circuit := StoreHalfChip.circuit } : Component (ZMod p)).rowInput env)
        (({ circuit := StoreHalfChip.circuit } : Component (ZMod p)).rowOutput env)))
    (word : id = .storeWord →
      (({ circuit := StoreWordChip.circuit } : Component (ZMod p)).rowInput env).is_real = 1 →
      Target.RowWritePermitted image (StoreWordChip.rowView
        (({ circuit := StoreWordChip.circuit } : Component (ZMod p)).rowInput env)
        (({ circuit := StoreWordChip.circuit } : Component (ZMod p)).rowOutput env)))
    (double : id = .storeDouble →
      (({ circuit := StoreDoubleChip.circuit } : Component (ZMod p)).rowInput env).is_real = 1 →
      Target.RowWritePermitted image (StoreDoubleChip.rowView
        (({ circuit := StoreDoubleChip.circuit } : Component (ZMod p)).rowInput env)
        (({ circuit := StoreDoubleChip.circuit } : Component (ZMod p)).rowOutput env)))
    : let chip := (supportedChipFor (p := p) id)
      (chip.kind.view (chip.table.rowInput env) (chip.table.rowOutput env)).is_real = 1 →
      Target.RowWritePermitted image (chip.kind.view (chip.table.rowInput env) (chip.table.rowOutput env)) := by
  exact supported_write_property (Target.RowWritePermitted image) (no_write_permitted image)
    id env byte half word double

/-- Raw protected AIR constraints and balance exclude every ordinary write to instruction bytes. -/
theorem instructionRows_write_permitted {image : ProgramImage} {source : ExecutionSnapshot}
    (witness : EnsembleWitness (ensemble (p := p) image source))
    (constraints : witness.Constraints) (balanced : witness.BalancedChannels)
    {decoded : DecodedInstructionRow p}
    (member : decoded ∈ LocalCore.instructionRows (localWitness witness))
    (active : (decoded.toChipRow (localWitness witness).data).is_real = 1) :
    Target.RowWritePermitted image (decoded.toChipRow (localWitness witness).data).view := by
  obtain ⟨index, same, physicalMem⟩ := instructionRows_physical witness member
  let table := witness.tables[7 + index.val]'(by
    rw [← witness.same_length]; change 7 + index.val < (tables image source).length
    rw [tables_length]; omega)
  have tableMem : table ∈ witness.tables := List.getElem_mem _
  change (decoded.toChipRow (localWitness witness).data).view.is_real = 1 at active
  rw [DecodedInstructionRow.toChipRow_setData decoded (localWitness witness).data witness.data,
    DecodedInstructionRow.toChipRow_view] at active ⊢
  rw [same] at active ⊢
  have descriptor : (supportedChips (p := p))[index.val]'(by
      rw [supportedChips_length]; exact index.isLt) =
      supportedChipFor (InstructionChipId.all[index.val]'index.isLt) := List.getElem_map _
  rw [descriptor] at active ⊢
  apply supported_write_permitted image _ (Environment.fromArray decoded.physical witness.data) ?_ ?_ ?_ ?_ active
  · intro identity real
    have position : index.val = 18 := by
      exact (InstructionChipId.all_nodup.getElem_inj_iff (hi := index.isLt) (hj := by decide)).mp identity
    apply byte_write_permitted witness constraints balanced table tableMem
      decoded.physical physicalMem ?_ real
    dsimp only [table]
    rw [← witness.same_circuits _ (by
      change 7 + index.val < (tables (p := p) image source).length
      rw [tables_length]; omega)]
    simp only [position]
    rfl
  · intro identity real
    have position : index.val = 19 := by
      exact (InstructionChipId.all_nodup.getElem_inj_iff (hi := index.isLt) (hj := by decide)).mp identity
    apply half_write_permitted witness constraints balanced table tableMem
      decoded.physical physicalMem ?_ real
    dsimp only [table]
    rw [← witness.same_circuits _ (by
      change 7 + index.val < (tables (p := p) image source).length
      rw [tables_length]; omega)]
    simp only [position]
    rfl
  · intro identity real
    have position : index.val = 20 := by
      exact (InstructionChipId.all_nodup.getElem_inj_iff (hi := index.isLt) (hj := by decide)).mp identity
    apply word_write_permitted witness constraints balanced table tableMem
      decoded.physical physicalMem ?_ real
    dsimp only [table]
    rw [← witness.same_circuits _ (by
      change 7 + index.val < (tables (p := p) image source).length
      rw [tables_length]; omega)]
    simp only [position]
    rfl
  · intro identity real
    have position : index.val = 21 := by
      exact (InstructionChipId.all_nodup.getElem_inj_iff (hi := index.isLt) (hj := by decide)).mp identity
    apply double_write_permitted witness constraints balanced table tableMem
      decoded.physical physicalMem ?_ real
    dsimp only [table]
    rw [← witness.same_circuits _ (by
      change 7 + index.val < (tables (p := p) image source).length
      rw [tables_length]; omega)]
    simp only [position]
    rfl

end SP1Clean.Soundness.ProtectedLocalCore
