import SP1Clean.Proofs.Completeness.LoadByteStatic
import SP1Clean.Model.SP1Field

/-! # Executable LoadByte fixed-lookup comparison

The matrix uses actual `MemoryEvent.toLoadByteInputs` and both actual witness builders.
Provider rows are real existing Byte/Range circuits. Only the Byte ledger is closed here;
State, Memory and Program are retained as consumer demand, not claimed balanced.
-/

namespace SP1CleanTest.Alignment.Examples.LoadByteStatic

open Circuit Air.Flat SP1Clean SP1Clean.TraceGen
open SP1Clean.Soundness.LoadByteStatic

/-- Shared native field. -/
abbrev F := ZMod SP1Prime
/-- The row generators need no external data; checks derive data from physical tables. -/
def data : ProverData F := fun _ _ => #[]
/-- LoadByte's witness builder needs no external hint. -/
def hint : ProverHint F := ProverHint.empty F

/-- A genuine event-builder input for one byte position and signedness. -/
def event (signed : Bool) (offset value : ℕ) : MemoryEvent where
  clk := 9
  pc := 65536
  opcode := if signed then 29 else 32
  opA := 1
  opB := 2
  imm := offset
  b := 131072
  prevA := 0
  prevTsA := 0
  prevTsB := 0
  prevMem := value * 256 ^ offset
  prevTsMem := 0

/-- Inputs come from the existing memory-event compiler, not hand-written positive rows. -/
def input (signed : Bool) (offset value : ℕ) : LoadByteChip.Inputs F :=
  (event signed offset value).toLoadByteInputs

/-- Inactive selected-byte witnesses can exceed 255 while the original arithmetic still holds. -/
def inactive : LoadByteChip.Inputs F :=
  { input true 0 0 with
    is_lb := 0
    is_lbu := 0
    selected_limb_low_byte := 300
    selected_byte := 300 }

/-- Actual table assertions and authenticated upstream byte lookup enumeration. -/
def tableCheck (evaluationData : ProverData F) (table : Table F) : Bool :=
  table.table.all fun row =>
    let env := Environment.fromArray row evaluationData
    table.component.operations.constraints.all (fun expression => env expression == 0) &&
      table.component.operations.lookups.all (fun lookup =>
        lookup.table.name == (LoadByteStaticChip.fixedByteLookup (p := SP1Prime)).table.name &&
        (LoadByteStaticChip.fixedByteLookup (p := SP1Prime)).rows.any (fun fixed =>
          fixed.toArray == (lookup.entry.map env).toArray))

/-- Check each physical row at the data derived from the entire assembly. -/
def tablesCheck (tables : List (Table F)) : Bool :=
  tables.all (tableCheck (deriveProverData tables))

/-- Read all physical Byte interactions, including disabled occurrences. -/
def byteLedger (tables : List (Table F)) : List (Interaction F) :=
  (tables.flatMap (fun table => table.interactions (deriveProverData tables))).filter
    (fun interaction => interaction.channel.name == "SP1Byte")

/-- Finite support check with the exact raw occurrence count, including zeros. -/
def byteBalanced (tables : List (Table F)) : Bool :=
  let ledger := byteLedger tables
  decide (ledger.length < SP1Prime) &&
    ledger.all (fun interaction => balanceOf ledger interaction.msg == 0)

/-- A residual provider is generated from the actual replacement consumer's request. -/
def providerFor (interaction : Interaction F) : Option (Option (Table F)) :=
  if interaction.mult == 0 then some none else
  match interaction.msg.toList with
  | [opcode, a, b, c] =>
    if opcode == 3 then
      some (some (Table.build ByteChip.U8Range.component [⟨b, c, -(interaction.mult)⟩] data hint))
    else if opcode == 4 then
      some (some (Table.build ByteChip.Ltu.component [⟨b, c, -(interaction.mult)⟩] data hint))
    else if opcode == 5 then
      some (some (Table.build ByteChip.MSB.component [⟨b, -(interaction.mult)⟩] data hint))
    else if opcode == 6 then
      if bound : b.val < 17 then
        some (some (Table.build (RangeChip.componentFor ⟨b.val, bound⟩)
          [⟨a, -(interaction.mult)⟩] data hint))
      else none
    else none
  | _ => none

/-- Shared residual providers preserve reader demands even when their keys equal selectedRange. -/
def residual? (inputs : List (LoadByteChip.Inputs F)) : Option (List (Table F)) := do
  let rows ← (byteLedger [replacementTable inputs data hint]).mapM providerFor
  pure (rows.filterMap id)

/-- Both actual assemblies satisfy local constraints and Byte balance, with identical consumer cells. -/
def caseCheck (rowInput : LoadByteChip.Inputs F) : Bool :=
  match residual? [rowInput] with
  | none => false
  | some residual =>
    let old := originalAssembly [rowInput] data hint residual
    let new := replacementAssembly [rowInput] data hint residual
    tablesCheck old && tablesCheck new && byteBalanced old && byteBalanced new &&
      (originalTable [rowInput] data hint).table == (replacementTable [rowInput] data hint).table &&
      (byteLedger old).length == (byteLedger new).length + 2

/-- Signedness × all eight offsets × the four boundary byte values. -/
def matrix : List (Bool × ℕ × ℕ) :=
  [true, false].flatMap fun signed => (List.range 8).flatMap fun offset =>
    [0, 127, 128, 255].map fun value => (signed, offset, value)

/-- All 64 event-built comparisons pass. -/
theorem matrix_passes : matrix.length = 64 ∧
    matrix.all (fun sample => caseCheck (input sample.1 sample.2.1 sample.2.2)) = true := by
  native_decide

/-- Padding does not acquire a byte-range restriction from the static lookup replacement. -/
theorem inactive_passes : caseCheck inactive = true := by native_decide

/-- Invalid active byte fields and nonbinary opcode selectors fail actual replacement constraints. -/
def invalidCases : List (String × Bool) :=
  [("wrong-low-byte", tablesCheck [replacementTable
      [{ input true 0 127 with selected_limb_low_byte := 126 }] data hint]),
   ("wrong-selectors", tablesCheck [replacementTable
      [{ input true 0 127 with is_lbu := 1 }] data hint]),
   ("active-out-of-range", tablesCheck [replacementTable
      [{ inactive with is_lb := 1 }] data hint])]

/-- Every negative fixture is rejected. -/
theorem invalid_rejected : invalidCases.all (fun sample => !sample.2) = true := by native_decide

/-- A reader really requests the same key as the removed selected-limb occurrence. -/
def repeatedKeyRetained : Bool :=
  let rowInput := input true 0 0
  let selected := selectedPull rowInput
  let consumer := replacementTable [rowInput] data hint
  match residual? [rowInput] with
  | none => false
  | some residual =>
    let pulls := (byteLedger [consumer]).countP fun i => i.msg == selected.msg && i.mult == -1
    let pushes := (byteLedger residual).countP fun i => i.msg == selected.msg && i.mult == 1
    decide (0 < pulls) && pulls == pushes && byteBalanced (consumer :: residual)

/-- Removing a selected occurrence does not erase reader demand with an identical byte key. -/
theorem repeated_key_retained : repeatedKeyRetained = true := by native_decide

/-- Workload for the cost report: the same 64 active events and one inactive row on each side. -/
def workload : List (LoadByteChip.Inputs F) :=
  matrix.map (fun sample => input sample.1 sample.2.1 sample.2.2) ++ [inactive]

end SP1CleanTest.Alignment.Examples.LoadByteStatic
