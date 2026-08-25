import SP1Clean.Faithful.Transport.Chips
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

namespace SP1Clean.Faithful.Transport

open Circuit
open Air.Flat (Component Table)
open scoped SP1Clean.ConstraintCoe

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance transportEnsembleFieldBound : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-- One shard's extracted instruction rows, table by table, in `supportedChips` order. This is the
Rust-side input of the transport: exactly what the pinned SP1 AIR's twenty-five instruction tables
contain. -/
structure ExtractedInstructionRows (p : ℕ) [Fact p.Prime] [Fact (2 ^ 24 < p)] where
  /-- The extracted `AddOracle` table's rows. -/
  add : List (Extracted.AddOracle.AddCols (ZMod p))
  /-- The extracted `AddiOracle` table's rows. -/
  addi : List (Extracted.AddiOracle.AddiCols (ZMod p))
  /-- The extracted `AddwOracle` table's rows. -/
  addw : List (Extracted.AddwOracle.AddwCols (ZMod p))
  /-- The extracted `SubOracle` table's rows. -/
  sub : List (Extracted.SubOracle.SubCols (ZMod p))
  /-- The extracted `SubwOracle` table's rows. -/
  subw : List (Extracted.SubwOracle.SubwCols (ZMod p))
  /-- The extracted `BitwiseOracle` table's rows. -/
  bitwise : List (Extracted.BitwiseOracle.BitwiseCols (ZMod p))
  /-- The extracted `LtOracle` table's rows. -/
  lt : List (Extracted.LtOracle.LtCols (ZMod p))
  /-- The extracted `ShiftLeftOracle` table's rows. -/
  shiftLeft : List (Extracted.ShiftLeftOracle.ShiftLeftCols (ZMod p))
  /-- The extracted `ShiftRightOracle` table's rows. -/
  shiftRight : List (Extracted.ShiftRightOracle.ShiftRightCols (ZMod p))
  /-- The extracted `JalOracle` table's rows. -/
  jal : List (Extracted.JalOracle.JalColumns (ZMod p))
  /-- The extracted `JalrOracle` table's rows. -/
  jalr : List (Extracted.JalrOracle.JalrColumns (ZMod p))
  /-- The extracted `BranchOracle` table's rows. -/
  branch : List (Extracted.BranchOracle.BranchColumns (ZMod p))
  /-- The extracted `UTypeOracle` table's rows. -/
  uType : List (Extracted.UTypeOracle.UTypeColumns (ZMod p))
  /-- The extracted `LoadByteOracle` table's rows. -/
  loadByte : List (Extracted.LoadByteOracle.LoadByteColumns (ZMod p))
  /-- The extracted `LoadHalfOracle` table's rows. -/
  loadHalf : List (Extracted.LoadHalfOracle.LoadHalfColumns (ZMod p))
  /-- The extracted `LoadWordOracle` table's rows. -/
  loadWord : List (Extracted.LoadWordOracle.LoadWordColumns (ZMod p))
  /-- The extracted `LoadDoubleOracle` table's rows. -/
  loadDouble : List (Extracted.LoadDoubleOracle.LoadDoubleColumns (ZMod p))
  /-- The extracted `LoadX0Oracle` table's rows. -/
  loadX0 : List (Extracted.LoadX0Oracle.LoadX0Columns (ZMod p))
  /-- The extracted `StoreByteOracle` table's rows. -/
  storeByte : List (Extracted.StoreByteOracle.StoreByteColumns (ZMod p))
  /-- The extracted `StoreHalfOracle` table's rows. -/
  storeHalf : List (Extracted.StoreHalfOracle.StoreHalfColumns (ZMod p))
  /-- The extracted `StoreWordOracle` table's rows. -/
  storeWord : List (Extracted.StoreWordOracle.StoreWordColumns (ZMod p))
  /-- The extracted `StoreDoubleOracle` table's rows. -/
  storeDouble : List (Extracted.StoreDoubleOracle.StoreDoubleColumns (ZMod p))
  /-- The extracted `MulOracle` table's rows. -/
  mul : List (Extracted.MulOracle.MulCols (ZMod p))
  /-- The extracted `DivRemOracle` table's rows. -/
  divRem : List (Extracted.DivRemOracle.DivRemCols (ZMod p))
  /-- The extracted `AluX0Oracle` table's rows. -/
  aluX0 : List (Extracted.AluX0Oracle.AluX0Cols (ZMod p))

namespace ExtractedInstructionRows

variable (rows : ExtractedInstructionRows p) (data : ProverData (ZMod p))

/-- **The twenty-five transported tables**, in the ensemble's own order. -/
def transported : List (Table (ZMod p)) :=
  [
    transportTable addChipRowCodec addChipOracle rows.add data,
    transportTable addiChipRowCodec addiChipOracle rows.addi data,
    transportTable addwChipRowCodec addwChipOracle rows.addw data,
    transportTable subChipRowCodec subChipOracle rows.sub data,
    transportTable subwChipRowCodec subwChipOracle rows.subw data,
    transportTable bitwiseChipRowCodec bitwiseChipOracle rows.bitwise data,
    transportTable ltChipRowCodec ltChipOracle rows.lt data,
    transportTable shiftLeftChipRowCodec shiftLeftChipOracle rows.shiftLeft data,
    transportTable shiftRightChipRowCodec shiftRightChipOracle rows.shiftRight data,
    transportTable jalChipRowCodec jalChipOracle rows.jal data,
    transportTable jalrChipRowCodec jalrChipOracle rows.jalr data,
    transportTable branchChipRowCodec branchChipOracle rows.branch data,
    transportTable uTypeChipRowCodec uTypeChipOracle rows.uType data,
    transportTable loadByteChipRowCodec loadByteChipOracle rows.loadByte data,
    transportTable loadHalfChipRowCodec loadHalfChipOracle rows.loadHalf data,
    transportTable loadWordChipRowCodec loadWordChipOracle rows.loadWord data,
    transportTable loadDoubleChipRowCodec loadDoubleChipOracle rows.loadDouble data,
    transportTable loadX0ChipRowCodec loadX0ChipOracle rows.loadX0 data,
    transportTable storeByteChipRowCodec storeByteChipOracle rows.storeByte data,
    transportTable storeHalfChipRowCodec storeHalfChipOracle rows.storeHalf data,
    transportTable storeWordChipRowCodec storeWordChipOracle rows.storeWord data,
    transportTable storeDoubleChipRowCodec storeDoubleChipOracle rows.storeDouble data,
    transportTable mulChipRowCodec mulChipOracle rows.mul data,
    transportTable divRemChipRowCodec divRemChipOracle rows.divRem data,
    transportTable aluX0ChipRowCodec aluX0ChipOracle rows.aluX0 data ]

/-- **The transported tables are the ensemble's instruction tables**, component for component and in
order — one `rfl`. This is the sentence the report's Finding 1 says was missing: the objects the
faithfulness anchors produce are the objects the capstone consumes. -/
theorem transported_map_component :
    ((transported rows data).map (·.component)) = Soundness.sp1Tables := rfl

/-- Each transported table carries the extracted AIR's own committed prover data — the
`EnsembleWitness.same_data` obligation, discharged for the instruction segment. -/
theorem transported_data : ∀ table ∈ transported rows data, table.data = data := by
  intro table hmem
  simp only [transported, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h |
    h | h | h | h | h <;> rw [h] <;> rfl

/-- Every extracted row of every instruction table satisfies its own chip's complete Rust assertion
list — what the extracted AIR asserts of a shard it accepts. -/
structure Valid : Prop where
  add : ∀ rustCols ∈ rows.add, List.Forall (· = 0) (addChipOracle.assertZeros rustCols)
  addi : ∀ rustCols ∈ rows.addi, List.Forall (· = 0) (addiChipOracle.assertZeros rustCols)
  addw : ∀ rustCols ∈ rows.addw, List.Forall (· = 0) (addwChipOracle.assertZeros rustCols)
  sub : ∀ rustCols ∈ rows.sub, List.Forall (· = 0) (subChipOracle.assertZeros rustCols)
  subw : ∀ rustCols ∈ rows.subw, List.Forall (· = 0) (subwChipOracle.assertZeros rustCols)
  bitwise : ∀ rustCols ∈ rows.bitwise, List.Forall (· = 0) (bitwiseChipOracle.assertZeros rustCols)
  lt : ∀ rustCols ∈ rows.lt, List.Forall (· = 0) (ltChipOracle.assertZeros rustCols)
  shiftLeft : ∀ rustCols ∈ rows.shiftLeft, List.Forall (· = 0) (shiftLeftChipOracle.assertZeros rustCols)
  shiftRight : ∀ rustCols ∈ rows.shiftRight, List.Forall (· = 0) (shiftRightChipOracle.assertZeros rustCols)
  jal : ∀ rustCols ∈ rows.jal, List.Forall (· = 0) (jalChipOracle.assertZeros rustCols)
  jalr : ∀ rustCols ∈ rows.jalr, List.Forall (· = 0) (jalrChipOracle.assertZeros rustCols)
  branch : ∀ rustCols ∈ rows.branch, List.Forall (· = 0) (branchChipOracle.assertZeros rustCols)
  uType : ∀ rustCols ∈ rows.uType, List.Forall (· = 0) (uTypeChipOracle.assertZeros rustCols)
  loadByte : ∀ rustCols ∈ rows.loadByte, List.Forall (· = 0) (loadByteChipOracle.assertZeros rustCols)
  loadHalf : ∀ rustCols ∈ rows.loadHalf, List.Forall (· = 0) (loadHalfChipOracle.assertZeros rustCols)
  loadWord : ∀ rustCols ∈ rows.loadWord, List.Forall (· = 0) (loadWordChipOracle.assertZeros rustCols)
  loadDouble : ∀ rustCols ∈ rows.loadDouble, List.Forall (· = 0) (loadDoubleChipOracle.assertZeros rustCols)
  loadX0 : ∀ rustCols ∈ rows.loadX0, List.Forall (· = 0) (loadX0ChipOracle.assertZeros rustCols)
  storeByte : ∀ rustCols ∈ rows.storeByte, List.Forall (· = 0) (storeByteChipOracle.assertZeros rustCols)
  storeHalf : ∀ rustCols ∈ rows.storeHalf, List.Forall (· = 0) (storeHalfChipOracle.assertZeros rustCols)
  storeWord : ∀ rustCols ∈ rows.storeWord, List.Forall (· = 0) (storeWordChipOracle.assertZeros rustCols)
  storeDouble : ∀ rustCols ∈ rows.storeDouble, List.Forall (· = 0) (storeDoubleChipOracle.assertZeros rustCols)
  mul : ∀ rustCols ∈ rows.mul, List.Forall (· = 0) (mulChipOracle.assertZeros rustCols)
  divRem : ∀ rustCols ∈ rows.divRem, List.Forall (· = 0) (divRemChipOracle.assertZeros rustCols)
  aluX0 : ∀ rustCols ∈ rows.aluX0, List.Forall (· = 0) (aluX0ChipOracle.assertZeros rustCols)

/-- The extracted instruction segment's active interaction ledger, concatenated in the exact
`supportedChips` order fixed by `transported`.  This is deliberately only the twenty-five
instruction tables: it includes no preprocessed provider, memory-boundary, MemoryBump, or
StateBump access, and therefore is not a name for the full Core cluster ledger. -/
def extractedInstructionActiveAccesses : LookupAccessList :=
  [ rows.add.flatMap fun rustCols =>
      LookupAccessList.active (addChipOracle.rustAccesses rustCols),
    rows.addi.flatMap fun rustCols =>
      LookupAccessList.active (addiChipOracle.rustAccesses rustCols),
    rows.addw.flatMap fun rustCols =>
      LookupAccessList.active (addwChipOracle.rustAccesses rustCols),
    rows.sub.flatMap fun rustCols =>
      LookupAccessList.active (subChipOracle.rustAccesses rustCols),
    rows.subw.flatMap fun rustCols =>
      LookupAccessList.active (subwChipOracle.rustAccesses rustCols),
    rows.bitwise.flatMap fun rustCols =>
      LookupAccessList.active (bitwiseChipOracle.rustAccesses rustCols),
    rows.lt.flatMap fun rustCols =>
      LookupAccessList.active (ltChipOracle.rustAccesses rustCols),
    rows.shiftLeft.flatMap fun rustCols =>
      LookupAccessList.active (shiftLeftChipOracle.rustAccesses rustCols),
    rows.shiftRight.flatMap fun rustCols =>
      LookupAccessList.active (shiftRightChipOracle.rustAccesses rustCols),
    rows.jal.flatMap fun rustCols =>
      LookupAccessList.active (jalChipOracle.rustAccesses rustCols),
    rows.jalr.flatMap fun rustCols =>
      LookupAccessList.active (jalrChipOracle.rustAccesses rustCols),
    rows.branch.flatMap fun rustCols =>
      LookupAccessList.active (branchChipOracle.rustAccesses rustCols),
    rows.uType.flatMap fun rustCols =>
      LookupAccessList.active (uTypeChipOracle.rustAccesses rustCols),
    rows.loadByte.flatMap fun rustCols =>
      LookupAccessList.active (loadByteChipOracle.rustAccesses rustCols),
    rows.loadHalf.flatMap fun rustCols =>
      LookupAccessList.active (loadHalfChipOracle.rustAccesses rustCols),
    rows.loadWord.flatMap fun rustCols =>
      LookupAccessList.active (loadWordChipOracle.rustAccesses rustCols),
    rows.loadDouble.flatMap fun rustCols =>
      LookupAccessList.active (loadDoubleChipOracle.rustAccesses rustCols),
    rows.loadX0.flatMap fun rustCols =>
      LookupAccessList.active (loadX0ChipOracle.rustAccesses rustCols),
    rows.storeByte.flatMap fun rustCols =>
      LookupAccessList.active (storeByteChipOracle.rustAccesses rustCols),
    rows.storeHalf.flatMap fun rustCols =>
      LookupAccessList.active (storeHalfChipOracle.rustAccesses rustCols),
    rows.storeWord.flatMap fun rustCols =>
      LookupAccessList.active (storeWordChipOracle.rustAccesses rustCols),
    rows.storeDouble.flatMap fun rustCols =>
      LookupAccessList.active (storeDoubleChipOracle.rustAccesses rustCols),
    rows.mul.flatMap fun rustCols =>
      LookupAccessList.active (mulChipOracle.rustAccesses rustCols),
    rows.divRem.flatMap fun rustCols =>
      LookupAccessList.active (divRemChipOracle.rustAccesses rustCols),
    rows.aluX0.flatMap fun rustCols =>
      LookupAccessList.active (aluX0ChipOracle.rustAccesses rustCols) ].flatten

/-- The native active interaction ledger of the twenty-five transported instruction tables.
The definition goes through the stable whole-table projection `tableNativeAccesses`; the outer
`active` erases exactly the multiplicity-zero padding before any later channel partition.  As with
`extractedInstructionActiveAccesses`, this is an instruction-segment ledger, not the full native
ensemble's access list. -/
noncomputable def transportedInstructionActiveAccesses : LookupAccessList :=
  ((transported rows data).map fun table =>
    LookupAccessList.active (tableNativeAccesses table)).flatten

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
  unfold transported
  simp only [List.map_cons, List.map_nil]
  refine .cons (transportTable_activeAccesses_perm addChip_faithful rows.add data valid.add) ?_
  refine .cons (transportTable_activeAccesses_perm addiChip_faithful rows.addi data valid.addi) ?_
  refine .cons (transportTable_activeAccesses_perm addwChip_faithful rows.addw data valid.addw) ?_
  refine .cons (transportTable_activeAccesses_perm subChip_faithful rows.sub data valid.sub) ?_
  refine .cons (transportTable_activeAccesses_perm subwChip_faithful rows.subw data valid.subw) ?_
  refine .cons
    (transportTable_activeAccesses_perm bitwiseChip_faithful rows.bitwise data valid.bitwise) ?_
  refine .cons (transportTable_activeAccesses_perm ltChip_faithful rows.lt data valid.lt) ?_
  refine .cons
    (transportTable_activeAccesses_perm shiftLeftChip_faithful rows.shiftLeft data valid.shiftLeft) ?_
  refine .cons
    (transportTable_activeAccesses_perm shiftRightChip_faithful rows.shiftRight data valid.shiftRight) ?_
  refine .cons (transportTable_activeAccesses_perm jalChip_faithful rows.jal data valid.jal) ?_
  refine .cons (transportTable_activeAccesses_perm jalrChip_faithful rows.jalr data valid.jalr) ?_
  refine .cons
    (transportTable_activeAccesses_perm branchChip_faithful rows.branch data valid.branch) ?_
  refine .cons (transportTable_activeAccesses_perm uTypeChip_faithful rows.uType data valid.uType) ?_
  refine .cons
    (transportTable_activeAccesses_perm loadByteChip_faithful rows.loadByte data valid.loadByte) ?_
  refine .cons
    (transportTable_activeAccesses_perm loadHalfChip_faithful rows.loadHalf data valid.loadHalf) ?_
  refine .cons
    (transportTable_activeAccesses_perm loadWordChip_faithful rows.loadWord data valid.loadWord) ?_
  refine .cons
    (transportTable_activeAccesses_perm loadDoubleChip_faithful rows.loadDouble data valid.loadDouble) ?_
  refine .cons
    (transportTable_activeAccesses_perm loadX0Chip_faithful rows.loadX0 data valid.loadX0) ?_
  refine .cons
    (transportTable_activeAccesses_perm storeByteChip_faithful rows.storeByte data valid.storeByte) ?_
  refine .cons
    (transportTable_activeAccesses_perm storeHalfChip_faithful rows.storeHalf data valid.storeHalf) ?_
  refine .cons
    (transportTable_activeAccesses_perm storeWordChip_faithful rows.storeWord data valid.storeWord) ?_
  refine .cons
    (transportTable_activeAccesses_perm storeDoubleChip_faithful rows.storeDouble data
      valid.storeDouble) ?_
  refine .cons (transportTable_activeAccesses_perm mulChip_faithful rows.mul data valid.mul) ?_
  refine .cons
    (transportTable_activeAccesses_perm divRemChip_faithful rows.divRem data valid.divRem) ?_
  refine .cons (transportTable_activeAccesses_perm aluX0Chip_faithful rows.aluX0 data valid.aluX0) ?_
  exact .nil

/--
**A valid extracted instruction segment transports to a constraint-satisfying native one.**

Every one of the twenty-five transported tables satisfies Clean's `Table.Constraints` for its
native chip circuit: every `assertZero` of the whole flattened circuit, gadget subcircuits
included, on every transported row. Each conjunct is one citation of that chip's
`ChipFaithful.constraints`, so the content is exactly the twenty-five whole-chip faithfulness
proofs and nothing new.
-/
theorem transported_constraints (valid : rows.Valid) :
    ∀ table ∈ transported rows data, table.Constraints := by
  simp only [transported, List.forall_mem_cons]
  refine ⟨
    addChip_transportTable_constraints _ _ valid.add,
    addiChip_transportTable_constraints _ _ valid.addi,
    addwChip_transportTable_constraints _ _ valid.addw,
    subChip_transportTable_constraints _ _ valid.sub,
    subwChip_transportTable_constraints _ _ valid.subw,
    bitwiseChip_transportTable_constraints _ _ valid.bitwise,
    ltChip_transportTable_constraints _ _ valid.lt,
    shiftLeftChip_transportTable_constraints _ _ valid.shiftLeft,
    shiftRightChip_transportTable_constraints _ _ valid.shiftRight,
    jalChip_transportTable_constraints _ _ valid.jal,
    jalrChip_transportTable_constraints _ _ valid.jalr,
    branchChip_transportTable_constraints _ _ valid.branch,
    uTypeChip_transportTable_constraints _ _ valid.uType,
    loadByteChip_transportTable_constraints _ _ valid.loadByte,
    loadHalfChip_transportTable_constraints _ _ valid.loadHalf,
    loadWordChip_transportTable_constraints _ _ valid.loadWord,
    loadDoubleChip_transportTable_constraints _ _ valid.loadDouble,
    loadX0Chip_transportTable_constraints _ _ valid.loadX0,
    storeByteChip_transportTable_constraints _ _ valid.storeByte,
    storeHalfChip_transportTable_constraints _ _ valid.storeHalf,
    storeWordChip_transportTable_constraints _ _ valid.storeWord,
    storeDoubleChip_transportTable_constraints _ _ valid.storeDouble,
    mulChip_transportTable_constraints _ _ valid.mul,
    divRemChip_transportTable_constraints _ _ valid.divRem,
    aluX0Chip_transportTable_constraints _ _ valid.aluX0,
    nofun⟩


end ExtractedInstructionRows

end SP1Clean.Faithful.Transport
