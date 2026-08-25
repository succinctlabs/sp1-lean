import SP1Clean.Composition.Chips
import SP1Clean.Soundness.SP1Ensemble

/-! # Transported tables *are* the ensemble's instruction tables

The step that inverts the external PR #110 report's Finding 1 measurement. `Transport/Chips.lean`
turns each chip's extracted table into a valid native `Table`; this file shows the twenty-five of
them, in extraction order, are positionally the first twenty-five components of `sp1Ensemble` — the
same list `Soundness/AIR.lean`'s capstone quantifies over.

That identity is one `rfl`: `transportTable` records the component it was handed, and
`sp1Tables` is `supportedChips.map (·.table)`, which is the same `⟨circuit⟩` wrapper. So the
faithfulness anchors and the soundness capstone are no longer two families that merely share an
endpoint — a module importing both now proves something about both.

## Scope: the instruction segment

This module deliberately stops at the twenty-five instruction chips.  Six Byte tables, all
seventeen fixed-width Range tables, Program ROM, two memory-boundary tables, and two W3 bump tables
need redistribution rather than this row-for-row `ChipFaithful` transport;
`ProviderSegment.lean` constructs that 28-table tail and `CoreEnsemble.lean` appends it here.  The
active-access theorem below likewise names only this instruction segment. Native consumer recounting
later derives Byte/Program balance; State/Memory balance and semantic boundary binding remain explicit
in `CoreArtifact.lean`'s global contract. No declaration here claims a full exact-cluster ledger
equality.
-/

set_option autoImplicit false

namespace SP1Clean.Composition

-- The faithfulness vocabulary (`ChipOracle`, `ChipFaithful`, `ChipRowCodec`,
-- `nativeAccesses`) is at the stratum below; this namespace no longer encloses it since the
-- 2026-08 move out of `Faithful/Transport/`.
open SP1Clean.Faithful

open Circuit
open Air.Flat (Component Table)
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance transportEnsembleFieldBound : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- The generated Rust whole-chip column type selected by a stable instruction identity.  Every
arm is definitionally the row type used by that chip's `ChipOracle`; no equality casts mediate the
faithfulness boundary. -/
def ExtractedCols (p : ℕ) : InstructionChipId → Type
  | .add => Extracted.AddOracle.AddCols (ZMod p)
  | .addi => Extracted.AddiOracle.AddiCols (ZMod p)
  | .addw => Extracted.AddwOracle.AddwCols (ZMod p)
  | .sub => Extracted.SubOracle.SubCols (ZMod p)
  | .subw => Extracted.SubwOracle.SubwCols (ZMod p)
  | .bitwise => Extracted.BitwiseOracle.BitwiseCols (ZMod p)
  | .lt => Extracted.LtOracle.LtCols (ZMod p)
  | .shiftLeft => Extracted.ShiftLeftOracle.ShiftLeftCols (ZMod p)
  | .shiftRight => Extracted.ShiftRightOracle.ShiftRightCols (ZMod p)
  | .jal => Extracted.JalOracle.JalColumns (ZMod p)
  | .jalr => Extracted.JalrOracle.JalrColumns (ZMod p)
  | .branch => Extracted.BranchOracle.BranchColumns (ZMod p)
  | .uType => Extracted.UTypeOracle.UTypeColumns (ZMod p)
  | .loadByte => Extracted.LoadByteOracle.LoadByteColumns (ZMod p)
  | .loadHalf => Extracted.LoadHalfOracle.LoadHalfColumns (ZMod p)
  | .loadWord => Extracted.LoadWordOracle.LoadWordColumns (ZMod p)
  | .loadDouble => Extracted.LoadDoubleOracle.LoadDoubleColumns (ZMod p)
  | .loadX0 => Extracted.LoadX0Oracle.LoadX0Columns (ZMod p)
  | .storeByte => Extracted.StoreByteOracle.StoreByteColumns (ZMod p)
  | .storeHalf => Extracted.StoreHalfOracle.StoreHalfColumns (ZMod p)
  | .storeWord => Extracted.StoreWordOracle.StoreWordColumns (ZMod p)
  | .storeDouble => Extracted.StoreDoubleOracle.StoreDoubleColumns (ZMod p)
  | .mul => Extracted.MulOracle.MulCols (ZMod p)
  | .divRem => Extracted.DivRemOracle.DivRemCols (ZMod p)
  | .aluX0 => Extracted.AluX0Oracle.AluX0Cols (ZMod p)

/-- One shard's extracted instruction rows, indexed by the same neutral identity that fixes
`supportedChips` order. This is the Rust-side input of whole-chip transport. -/
structure ExtractedInstructionRows (p : ℕ) [Fact p.Prime] [Fact (2 ^ 24 < p)] where
  /-- Extracted rows for one instruction table. -/
  forId : (id : InstructionChipId) → List (ExtractedCols p id)

namespace ExtractedInstructionRows

variable (rows : ExtractedInstructionRows p) (data : ProverData (ZMod p))

/-- The extracted assertion list selected by an instruction identity. -/
def assertZerosFor : (id : InstructionChipId) → ExtractedCols p id → List (ZMod p)
  | .add => addChipOracle.assertZeros
  | .addi => addiChipOracle.assertZeros
  | .addw => addwChipOracle.assertZeros
  | .sub => subChipOracle.assertZeros
  | .subw => subwChipOracle.assertZeros
  | .bitwise => bitwiseChipOracle.assertZeros
  | .lt => ltChipOracle.assertZeros
  | .shiftLeft => shiftLeftChipOracle.assertZeros
  | .shiftRight => shiftRightChipOracle.assertZeros
  | .jal => jalChipOracle.assertZeros
  | .jalr => jalrChipOracle.assertZeros
  | .branch => branchChipOracle.assertZeros
  | .uType => uTypeChipOracle.assertZeros
  | .loadByte => loadByteChipOracle.assertZeros
  | .loadHalf => loadHalfChipOracle.assertZeros
  | .loadWord => loadWordChipOracle.assertZeros
  | .loadDouble => loadDoubleChipOracle.assertZeros
  | .loadX0 => loadX0ChipOracle.assertZeros
  | .storeByte => storeByteChipOracle.assertZeros
  | .storeHalf => storeHalfChipOracle.assertZeros
  | .storeWord => storeWordChipOracle.assertZeros
  | .storeDouble => storeDoubleChipOracle.assertZeros
  | .mul => mulChipOracle.assertZeros
  | .divRem => divRemChipOracle.assertZeros
  | .aluX0 => aluX0ChipOracle.assertZeros

/-- The extracted active access list selected by an instruction identity. -/
def rustAccessesFor : (id : InstructionChipId) → ExtractedCols p id → LookupAccessList
  | .add => addChipOracle.rustAccesses
  | .addi => addiChipOracle.rustAccesses
  | .addw => addwChipOracle.rustAccesses
  | .sub => subChipOracle.rustAccesses
  | .subw => subwChipOracle.rustAccesses
  | .bitwise => bitwiseChipOracle.rustAccesses
  | .lt => ltChipOracle.rustAccesses
  | .shiftLeft => shiftLeftChipOracle.rustAccesses
  | .shiftRight => shiftRightChipOracle.rustAccesses
  | .jal => jalChipOracle.rustAccesses
  | .jalr => jalrChipOracle.rustAccesses
  | .branch => branchChipOracle.rustAccesses
  | .uType => uTypeChipOracle.rustAccesses
  | .loadByte => loadByteChipOracle.rustAccesses
  | .loadHalf => loadHalfChipOracle.rustAccesses
  | .loadWord => loadWordChipOracle.rustAccesses
  | .loadDouble => loadDoubleChipOracle.rustAccesses
  | .loadX0 => loadX0ChipOracle.rustAccesses
  | .storeByte => storeByteChipOracle.rustAccesses
  | .storeHalf => storeHalfChipOracle.rustAccesses
  | .storeWord => storeWordChipOracle.rustAccesses
  | .storeDouble => storeDoubleChipOracle.rustAccesses
  | .mul => mulChipOracle.rustAccesses
  | .divRem => divRemChipOracle.rustAccesses
  | .aluX0 => aluX0ChipOracle.rustAccesses

/-- Transport the extracted rows selected by one stable instruction identity. -/
def transportedFor : InstructionChipId → Table (ZMod p)
  | .add => transportTable addChipRowCodec addChipOracle (rows.forId .add) data
  | .addi => transportTable addiChipRowCodec addiChipOracle (rows.forId .addi) data
  | .addw => transportTable addwChipRowCodec addwChipOracle (rows.forId .addw) data
  | .sub => transportTable subChipRowCodec subChipOracle (rows.forId .sub) data
  | .subw => transportTable subwChipRowCodec subwChipOracle (rows.forId .subw) data
  | .bitwise => transportTable bitwiseChipRowCodec bitwiseChipOracle (rows.forId .bitwise) data
  | .lt => transportTable ltChipRowCodec ltChipOracle (rows.forId .lt) data
  | .shiftLeft =>
      transportTable shiftLeftChipRowCodec shiftLeftChipOracle (rows.forId .shiftLeft) data
  | .shiftRight =>
      transportTable shiftRightChipRowCodec shiftRightChipOracle (rows.forId .shiftRight) data
  | .jal => transportTable jalChipRowCodec jalChipOracle (rows.forId .jal) data
  | .jalr => transportTable jalrChipRowCodec jalrChipOracle (rows.forId .jalr) data
  | .branch => transportTable branchChipRowCodec branchChipOracle (rows.forId .branch) data
  | .uType => transportTable uTypeChipRowCodec uTypeChipOracle (rows.forId .uType) data
  | .loadByte =>
      transportTable loadByteChipRowCodec loadByteChipOracle (rows.forId .loadByte) data
  | .loadHalf =>
      transportTable loadHalfChipRowCodec loadHalfChipOracle (rows.forId .loadHalf) data
  | .loadWord =>
      transportTable loadWordChipRowCodec loadWordChipOracle (rows.forId .loadWord) data
  | .loadDouble =>
      transportTable loadDoubleChipRowCodec loadDoubleChipOracle (rows.forId .loadDouble) data
  | .loadX0 => transportTable loadX0ChipRowCodec loadX0ChipOracle (rows.forId .loadX0) data
  | .storeByte =>
      transportTable storeByteChipRowCodec storeByteChipOracle (rows.forId .storeByte) data
  | .storeHalf =>
      transportTable storeHalfChipRowCodec storeHalfChipOracle (rows.forId .storeHalf) data
  | .storeWord =>
      transportTable storeWordChipRowCodec storeWordChipOracle (rows.forId .storeWord) data
  | .storeDouble =>
      transportTable storeDoubleChipRowCodec storeDoubleChipOracle (rows.forId .storeDouble) data
  | .mul => transportTable mulChipRowCodec mulChipOracle (rows.forId .mul) data
  | .divRem => transportTable divRemChipRowCodec divRemChipOracle (rows.forId .divRem) data
  | .aluX0 => transportTable aluX0ChipRowCodec aluX0ChipOracle (rows.forId .aluX0) data

/-- **The twenty-five transported tables**, in the ensemble's one neutral instruction order. -/
def transported : List (Table (ZMod p)) :=
  InstructionChipId.all.map (rows.transportedFor data)

/-- Pointwise component alignment between extracted transport and the circuit-bearing registry. -/
@[simp] theorem transportedFor_component (id : InstructionChipId) :
    (rows.transportedFor data id).component =
      (Soundness.supportedChipFor (p := p) id).table := by
  cases id <;> rfl

/-- **The transported tables are the ensemble's instruction tables**, component for component and in
order — one `rfl`. This is the sentence the report's Finding 1 says was missing: the objects the
faithfulness anchors produce are the objects the capstone consumes. -/
theorem transported_map_component :
    ((transported rows data).map (·.component)) = Soundness.sp1Tables := by
  simp only [transported, Soundness.sp1Tables, Soundness.supportedChips, List.map_map]
  exact List.map_congr_left fun id _ => rows.transportedFor_component data id

/-- Pointwise shared-data law for one transported table. -/
@[simp] theorem transportedFor_data (id : InstructionChipId) :
    (rows.transportedFor data id).data = data := by
  cases id <;> rfl

/-- Each transported table carries the extracted AIR's own committed prover data — the
`EnsembleWitness.same_data` obligation, discharged for the instruction segment. -/
theorem transported_data : ∀ table ∈ transported rows data, table.data = data := by
  intro table hmem
  rw [transported] at hmem
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp hmem
  exact rows.transportedFor_data data id

/-- Every extracted row of every instruction table satisfies its own chip's complete Rust assertion
list — what the extracted AIR asserts of a shard it accepts. -/
structure Valid : Prop where
  /-- Every row in every identity-indexed table satisfies that identity's complete Rust assertion
  list. -/
  forId : ∀ (id : InstructionChipId) (rustCols : ExtractedCols p id),
    rustCols ∈ rows.forId id → List.Forall (· = 0) (assertZerosFor id rustCols)

/-- Active extracted accesses for one identity-indexed instruction table. -/
def extractedActiveAccessesFor (id : InstructionChipId) : LookupAccessList :=
  (rows.forId id).flatMap fun rustCols =>
    LookupAccessList.active (rustAccessesFor id rustCols)

/-- The extracted instruction segment's active interaction ledger, concatenated in the exact
neutral instruction order fixed by `transported`. This includes no provider or boundary access. -/
def extractedInstructionActiveAccesses : LookupAccessList :=
  (InstructionChipId.all.map rows.extractedActiveAccessesFor).flatten

/-- Native active accesses for one identity-indexed transported table. -/
noncomputable def transportedActiveAccessesFor (id : InstructionChipId) : LookupAccessList :=
  LookupAccessList.active (tableNativeAccesses (rows.transportedFor data id))

/-- The native active interaction ledger of the twenty-five transported instruction tables. The
outer `active` erases exactly multiplicity-zero padding; providers remain outside this ledger. -/
noncomputable def transportedInstructionActiveAccesses : LookupAccessList :=
  (InstructionChipId.all.map (rows.transportedActiveAccessesFor data)).flatten

/-- Whole-chip faithfulness transported pointwise through the neutral instruction identity. -/
theorem transportedActiveAccessesFor_perm (valid : rows.Valid) (id : InstructionChipId) :
    List.Perm (rows.transportedActiveAccessesFor data id)
      (rows.extractedActiveAccessesFor id) := by
  cases id with
  | add => exact transportTable_activeAccesses_perm addChip_faithful _ data (valid.forId .add)
  | addi => exact transportTable_activeAccesses_perm addiChip_faithful _ data (valid.forId .addi)
  | addw => exact transportTable_activeAccesses_perm addwChip_faithful _ data (valid.forId .addw)
  | sub => exact transportTable_activeAccesses_perm subChip_faithful _ data (valid.forId .sub)
  | subw => exact transportTable_activeAccesses_perm subwChip_faithful _ data (valid.forId .subw)
  | bitwise =>
      exact transportTable_activeAccesses_perm bitwiseChip_faithful _ data
        (valid.forId .bitwise)
  | lt => exact transportTable_activeAccesses_perm ltChip_faithful _ data (valid.forId .lt)
  | shiftLeft =>
      exact transportTable_activeAccesses_perm shiftLeftChip_faithful _ data
        (valid.forId .shiftLeft)
  | shiftRight =>
      exact transportTable_activeAccesses_perm shiftRightChip_faithful _ data
        (valid.forId .shiftRight)
  | jal => exact transportTable_activeAccesses_perm jalChip_faithful _ data (valid.forId .jal)
  | jalr => exact transportTable_activeAccesses_perm jalrChip_faithful _ data (valid.forId .jalr)
  | branch =>
      exact transportTable_activeAccesses_perm branchChip_faithful _ data
        (valid.forId .branch)
  | uType => exact transportTable_activeAccesses_perm uTypeChip_faithful _ data (valid.forId .uType)
  | loadByte =>
      exact transportTable_activeAccesses_perm loadByteChip_faithful _ data
        (valid.forId .loadByte)
  | loadHalf =>
      exact transportTable_activeAccesses_perm loadHalfChip_faithful _ data
        (valid.forId .loadHalf)
  | loadWord =>
      exact transportTable_activeAccesses_perm loadWordChip_faithful _ data
        (valid.forId .loadWord)
  | loadDouble =>
      exact transportTable_activeAccesses_perm loadDoubleChip_faithful _ data
        (valid.forId .loadDouble)
  | loadX0 =>
      exact transportTable_activeAccesses_perm loadX0Chip_faithful _ data
        (valid.forId .loadX0)
  | storeByte =>
      exact transportTable_activeAccesses_perm storeByteChip_faithful _ data
        (valid.forId .storeByte)
  | storeHalf =>
      exact transportTable_activeAccesses_perm storeHalfChip_faithful _ data
        (valid.forId .storeHalf)
  | storeWord =>
      exact transportTable_activeAccesses_perm storeWordChip_faithful _ data
        (valid.forId .storeWord)
  | storeDouble =>
      exact transportTable_activeAccesses_perm storeDoubleChip_faithful _ data
        (valid.forId .storeDouble)
  | mul => exact transportTable_activeAccesses_perm mulChip_faithful _ data (valid.forId .mul)
  | divRem =>
      exact transportTable_activeAccesses_perm divRemChip_faithful _ data
        (valid.forId .divRem)
  | aluX0 =>
      exact transportTable_activeAccesses_perm aluX0Chip_faithful _ data
        (valid.forId .aluX0)

/-- **The complete active instruction ledger transports as a multiset.**  A valid extracted
instruction segment has, up to emission order, exactly the active accesses of its twenty-five
native transported tables.  The proof is the mechanical append of the twenty-five whole-chip
access transports; it neither mentions nor assumes anything about provider, boundary, or system
tables, and makes no equality claim about the full exact Core cluster ledger. -/
theorem transportedInstructionActiveAccesses_perm (valid : rows.Valid) :
    List.Perm (transportedInstructionActiveAccesses rows data)
      (extractedInstructionActiveAccesses rows) := by
  unfold transportedInstructionActiveAccesses extractedInstructionActiveAccesses
  apply List.Perm.flatten_congr
  induction InstructionChipId.all with
  | nil => exact .nil
  | cons id ids ih => exact .cons (rows.transportedActiveAccessesFor_perm data valid id) ih

/--
**A valid extracted instruction segment transports to a constraint-satisfying native one.**

Every one of the twenty-five transported tables satisfies Clean's `Table.Constraints` for its
native chip circuit: every `assertZero` of the whole flattened circuit, gadget subcircuits
included, on every transported row. Each conjunct is one citation of that chip's
`ChipFaithful.constraints`, so the content is exactly the twenty-five whole-chip faithfulness
proofs and nothing new.
-/
theorem transportedFor_constraints (valid : rows.Valid) (id : InstructionChipId) :
    (rows.transportedFor data id).Constraints := by
  cases id with
  | add => exact addChip_transportTable_constraints _ data (valid.forId .add)
  | addi => exact addiChip_transportTable_constraints _ data (valid.forId .addi)
  | addw => exact addwChip_transportTable_constraints _ data (valid.forId .addw)
  | sub => exact subChip_transportTable_constraints _ data (valid.forId .sub)
  | subw => exact subwChip_transportTable_constraints _ data (valid.forId .subw)
  | bitwise => exact bitwiseChip_transportTable_constraints _ data (valid.forId .bitwise)
  | lt => exact ltChip_transportTable_constraints _ data (valid.forId .lt)
  | shiftLeft => exact shiftLeftChip_transportTable_constraints _ data (valid.forId .shiftLeft)
  | shiftRight =>
      exact shiftRightChip_transportTable_constraints _ data (valid.forId .shiftRight)
  | jal => exact jalChip_transportTable_constraints _ data (valid.forId .jal)
  | jalr => exact jalrChip_transportTable_constraints _ data (valid.forId .jalr)
  | branch => exact branchChip_transportTable_constraints _ data (valid.forId .branch)
  | uType => exact uTypeChip_transportTable_constraints _ data (valid.forId .uType)
  | loadByte => exact loadByteChip_transportTable_constraints _ data (valid.forId .loadByte)
  | loadHalf => exact loadHalfChip_transportTable_constraints _ data (valid.forId .loadHalf)
  | loadWord => exact loadWordChip_transportTable_constraints _ data (valid.forId .loadWord)
  | loadDouble =>
      exact loadDoubleChip_transportTable_constraints _ data (valid.forId .loadDouble)
  | loadX0 => exact loadX0Chip_transportTable_constraints _ data (valid.forId .loadX0)
  | storeByte => exact storeByteChip_transportTable_constraints _ data (valid.forId .storeByte)
  | storeHalf => exact storeHalfChip_transportTable_constraints _ data (valid.forId .storeHalf)
  | storeWord => exact storeWordChip_transportTable_constraints _ data (valid.forId .storeWord)
  | storeDouble =>
      exact storeDoubleChip_transportTable_constraints _ data (valid.forId .storeDouble)
  | mul => exact mulChip_transportTable_constraints _ data (valid.forId .mul)
  | divRem => exact divRemChip_transportTable_constraints _ data (valid.forId .divRem)
  | aluX0 => exact aluX0Chip_transportTable_constraints _ data (valid.forId .aluX0)

theorem transported_constraints (valid : rows.Valid) :
    ∀ table ∈ transported rows data, table.Constraints := by
  intro table tableMem
  rw [transported] at tableMem
  obtain ⟨id, _, rfl⟩ := List.mem_map.mp tableMem
  exact rows.transportedFor_constraints data valid id


end ExtractedInstructionRows

end SP1Clean.Composition
