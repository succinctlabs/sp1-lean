import SP1Clean.Faithful.CoreAIR
import SP1Clean.Faithful.Transport.Ensemble

set_option autoImplicit false

/-! # From the extracted Core AIR relation to valid native tables

The link that makes `Faithful/Transport/` apply to the *actual* extracted AIR rather than to an
abstract list of Rust rows. `Transport/Ensemble.lean` transports an `ExtractedInstructionRows`
record; this file reads that record off a witness the pinned upstream Core AIR accepts, and shows
its validity premise is exactly what the relation already asserts.

## Why the link is definitional

`SP1Clean.CoreAIR.Current.MainRow p .add` reduces to `Extracted.AddOracle.AddCols (ZMod p)` — the very row
type `addChipOracle` is stated over — and `SP1Clean.CoreAIR.Current.assertions publicValues .add row` reduces
to `AddOracle.AddCols.asserts row.main`, which is `addChipOracle.assertZeros row.main`. So the
relation's per-row conjunct *is* the transport's validity premise, with no re-derivation: the two
sides were already talking about the same list, and nothing had connected them.

The same holds for all twenty-five instruction tables, which is why `instructionRows_valid` is
twenty-five copies of one three-line argument rather than twenty-five separate proofs.

## Scope

Instruction segment only. The provider, memory-boundary and system-table segments of the extracted
cluster do not map row-for-row onto native tables — SP1 has one byte-lookup table where the native
ensemble has six opcode tables plus four range widths, and the native memory boundary is fed by the
*memory-boundary* cluster rather than the execution one — so those need redistribution arguments
rather than this file's definitional read-off. Likewise the four channel balances, which need the
extracted `Balance.Valid` transported through the per-table access permutations. See
`docs/roadmap.md`.
-/

namespace SP1Clean.Faithful.Transport

open Circuit
open Air.Flat (Component Table)
open scoped SP1Clean.ConstraintCoe
open SP1Clean.CoreAIR (Witness)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance transportExtractedFieldBound : Fact (2 ^ 17 < p) :=
  ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

variable {Digest : Type}

/-- **The extracted witness's instruction rows**, read off table by table. Each field is the
table's row list with the preprocessed half dropped — instruction tables have preprocessed width
zero, so nothing is discarded that any assertion reads. -/
def extractedInstructionRows (witness : Witness (SP1Clean.CoreAIR.Current.Row p)) :
    ExtractedInstructionRows p where
  add := (witness.trace.rows .add).map (·.main)
  addi := (witness.trace.rows .addi).map (·.main)
  addw := (witness.trace.rows .addw).map (·.main)
  sub := (witness.trace.rows .sub).map (·.main)
  subw := (witness.trace.rows .subw).map (·.main)
  bitwise := (witness.trace.rows .bitwise).map (·.main)
  lt := (witness.trace.rows .lt).map (·.main)
  shiftLeft := (witness.trace.rows .shiftLeft).map (·.main)
  shiftRight := (witness.trace.rows .shiftRight).map (·.main)
  jal := (witness.trace.rows .jal).map (·.main)
  jalr := (witness.trace.rows .jalr).map (·.main)
  branch := (witness.trace.rows .branch).map (·.main)
  uType := (witness.trace.rows .uType).map (·.main)
  loadByte := (witness.trace.rows .loadByte).map (·.main)
  loadHalf := (witness.trace.rows .loadHalf).map (·.main)
  loadWord := (witness.trace.rows .loadWord).map (·.main)
  loadDouble := (witness.trace.rows .loadDouble).map (·.main)
  loadX0 := (witness.trace.rows .loadX0).map (·.main)
  storeByte := (witness.trace.rows .storeByte).map (·.main)
  storeHalf := (witness.trace.rows .storeHalf).map (·.main)
  storeWord := (witness.trace.rows .storeWord).map (·.main)
  storeDouble := (witness.trace.rows .storeDouble).map (·.main)
  mul := (witness.trace.rows .mul).map (·.main)
  divRem := (witness.trace.rows .divRem).map (·.main)
  aluX0 := (witness.trace.rows .aluX0).map (·.main)

/--
**A valid extracted Core AIR witness satisfies the transport's validity premise.**

One `List.mem_map` per table, then the relation's own per-row assertion conjunct. Nothing is proved
about the rows here; the point is that no translation step exists to get it wrong.
-/
theorem extractedInstructionRows_valid
    {binds : SP1Clean.CoreAIR.Current.PreprocessedBinding p Digest}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : Witness (SP1Clean.CoreAIR.Current.Row p))
    (valid : SP1Clean.CoreAIR.Current.Relation binds .execution statement witness) :
    (extractedInstructionRows witness).Valid := by
  have rowAsserts : ∀ (table : CoreProfile.Table) (row : SP1Clean.CoreAIR.Current.Row p table),
      row ∈ witness.trace.rows table →
        List.Forall (· = 0) (SP1Clean.CoreAIR.Current.assertions statement.publicValues table row) :=
    valid.2.2.1
  refine {
  add := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .add row hrow
  addi := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .addi row hrow
  addw := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .addw row hrow
  sub := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .sub row hrow
  subw := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .subw row hrow
  bitwise := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .bitwise row hrow
  lt := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .lt row hrow
  shiftLeft := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .shiftLeft row hrow
  shiftRight := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .shiftRight row hrow
  jal := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .jal row hrow
  jalr := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .jalr row hrow
  branch := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .branch row hrow
  uType := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .uType row hrow
  loadByte := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .loadByte row hrow
  loadHalf := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .loadHalf row hrow
  loadWord := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .loadWord row hrow
  loadDouble := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .loadDouble row hrow
  loadX0 := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .loadX0 row hrow
  storeByte := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .storeByte row hrow
  storeHalf := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .storeHalf row hrow
  storeWord := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .storeWord row hrow
  storeDouble := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .storeDouble row hrow
  mul := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .mul row hrow
  divRem := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .divRem row hrow
  aluX0 := by
    intro rustCols hmem
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hmem
    exact rowAsserts .aluX0 row hrow }

/--
**The headline table-level transport: a valid extracted shard yields twenty-five valid native
tables.**

Every one of the twenty-five transported tables satisfies Clean's `Table.Constraints` for its
native chip circuit, and by `transported_map_component` those tables are positionally the
ensemble's instruction tables. This is the composition the external PR #110 report's Finding 1
found missing, stated against the real extracted relation.

What it is not yet: a whole `EnsembleWitness`. That needs the other fifteen tables and the four
channel balances.
-/
theorem extracted_instructionTables_constraints
    {binds : SP1Clean.CoreAIR.Current.PreprocessedBinding p Digest}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : Witness (SP1Clean.CoreAIR.Current.Row p))
    (valid : SP1Clean.CoreAIR.Current.Relation binds .execution statement witness)
    (data : ProverData (ZMod p)) :
    ∀ table ∈ (extractedInstructionRows witness).transported data, table.Constraints :=
  ExtractedInstructionRows.transported_constraints _ _
    (extractedInstructionRows_valid statement witness valid)

end SP1Clean.Faithful.Transport
