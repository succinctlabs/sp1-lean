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

## What remains for a whole-ensemble transport

Three segments, none of them instruction chips: the ten byte and range providers plus the Program
ROM (transportable by aggregation, since a provider's constraints never read its multiplicity
cell), the two memory boundary tables (from the extracted memory-boundary cluster), and the two W3
system tables — whose anchors are *not* `ChipFaithful` structures but bespoke conjunctions over an
input-keyed environment, so the generic transport does not reach them without their own codec.
Then the four channel balances transport from the extracted AIR's own ℕ-exact balance through the
per-table access permutations proved here. See `docs/roadmap.md`.
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
