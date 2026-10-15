import SP1Clean
import ToClean.Circuit.WitnessGenerationData
import SP1CleanTest.Core.Exportable
import SP1CleanTest.TraceGenTests.TraceGenerator

/-! # `witgenExport` — the witness-IR export driver (waves D2/D4a)

Serializes every registered chip's witness-generation programs (plus its complete
assert/lookup/interact list) in Clean's `version: 1` witgen wire format, the payload the
Rust reference interpreter (`rust/witgen-interp/`) consumes, together with a per-chip
manifest carrying what the wire format deliberately omits (field modulus, input width,
chip name, hint schema) and a top-level `index.json`.

Run from the repo root against built oleans:

    lake build SP1CleanTest
    WITGEN_ARGS="[--out DIR] [--chip NAME] [--stdout] [--testdata]" \
      lake env lean scripts/witgenExport.lean

Defaults: `--out .lake/witgen-export/manual`. `--chip NAME` restricts to one chip
and skips `index.json` (never a partial index); `--stdout` prints the payload instead of
writing files. `--testdata` writes differential fixtures at `testdata/<Chip>.trace.json`
under the output directory, anchored for **all 25 chips** to the committed SP1 trace dumps
(`export/sp1dump/`, always read from the repo tree): one `"event"` row per dumped
executor event with inputs recovered through the symbolic row map and empty hints,
**each recomputed and gated cell-for-cell against the dumped
`generate_trace` row before anything is written**, plus an honest padding row and
deterministic seeded synthetic rows. `expectedWitness` is always the Lean reference
evaluation (`witgen` below: Clean's `FlatOperation.witgen` at the empty commitment) over the
authored operation list — the same programs the built-in serializer carries.
Large shared expressions are authored using Clean's `Witgen.M`.

This is deliberately an interpreted script, not a `lean_exe`: elaborating the file runs
the trailing `#eval` against the already-built oleans (the same path as
`#assert_exportable`'s `#eval`s in `SP1CleanTest/Core/Exportable.lean`), where a compiled
executable would force native compilation of the whole import closure. Upstream Clean
drives its plonky3 fixture scripts the same way, via `lean --run` — unavailable here
because the generated Sail model (`LeanRV64D`) already owns the root `main`, hence the
`WITGEN_ARGS` environment variable instead of argv.

⚠ `lake env lean` exits 0 on a Lean stack overflow (repo-known trap), so callers must
validate the outputs, not the exit code — `scripts/check_witgen_export.py` does.

The serializer is Clean's `Operations.witgenJson?`
(`.lake/packages/Clean/Clean/Circuit/WitnessExport.lean`); this script only enumerates
the 25 chip circuits at `SP1Prime`, derives the manifests from the serialized payloads,
and writes files. Output is byte-stable: no timestamps or revisions are embedded, and
JSON key order is code-determined. -/

namespace WitgenExportScript

open Lean SP1Clean SP1Clean.ExportableTests

abbrev Fp := ZMod SP1Prime

/-- One chip's export entry: its SP1 name (= `ChipKind.name` = the file stem), the Lean
declaration it came from (manifest documentation), the input-row width occupying var
indices `0 .. inputWidth - 1` (the wire format does not record it), and the operations. -/
structure Entry where
  name : String
  leanName : String
  inputWidth : Nat
  ops : Operations Fp

def entry {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (name leanName : String) (c : GeneralFormalCircuit Fp Input Output) : Entry :=
  ⟨name, leanName, size Input, WitgenOps.operations (F := Fp) c⟩

/-- The 25 registered chips, in `Soundness.supportedChips` registry order (cross-checked
at startup — the order is a public witness-format matter). -/
def entries : List Entry := [
  entry "Add" "SP1Clean.AddChip.circuit" (AddChip.circuit (p := SP1Prime)),
  entry "Addi" "SP1Clean.AddiChip.circuit" (AddiChip.circuit (p := SP1Prime)),
  entry "Addw" "SP1Clean.AddwChip.circuit" (AddwChip.circuit (p := SP1Prime)),
  entry "Sub" "SP1Clean.SubChip.circuit" (SubChip.circuit (p := SP1Prime)),
  entry "Subw" "SP1Clean.SubwChip.circuit" (SubwChip.circuit (p := SP1Prime)),
  entry "Bitwise" "SP1Clean.BitwiseChip.circuit" (BitwiseChip.circuit (p := SP1Prime)),
  entry "Lt" "SP1Clean.LtChip.circuit" (LtChip.circuit (p := SP1Prime)),
  entry "ShiftLeft" "SP1Clean.ShiftLeftChip.circuit" (ShiftLeftChip.circuit (p := SP1Prime)),
  entry "ShiftRight" "SP1Clean.ShiftRightChip.circuit" (ShiftRightChip.circuit (p := SP1Prime)),
  entry "Jal" "SP1Clean.JalChip.circuit" (JalChip.circuit (p := SP1Prime)),
  entry "Jalr" "SP1Clean.JalrChip.circuit" (JalrChip.circuit (p := SP1Prime)),
  entry "Branch" "SP1Clean.BranchChip.circuit" (BranchChip.circuit (p := SP1Prime)),
  entry "UType" "SP1Clean.UTypeChip.circuit" (UTypeChip.circuit (p := SP1Prime)),
  entry "LoadByte" "SP1Clean.LoadByteChip.circuit" (LoadByteChip.circuit (p := SP1Prime)),
  entry "LoadHalf" "SP1Clean.LoadHalfChip.circuit" (LoadHalfChip.circuit (p := SP1Prime)),
  entry "LoadWord" "SP1Clean.LoadWordChip.circuit" (LoadWordChip.circuit (p := SP1Prime)),
  entry "LoadDouble" "SP1Clean.LoadDoubleChip.circuit" (LoadDoubleChip.circuit (p := SP1Prime)),
  entry "LoadX0" "SP1Clean.LoadX0Chip.circuit" (LoadX0Chip.circuit (p := SP1Prime)),
  entry "StoreByte" "SP1Clean.StoreByteChip.circuit" (StoreByteChip.circuit (p := SP1Prime)),
  entry "StoreHalf" "SP1Clean.StoreHalfChip.circuit" (StoreHalfChip.circuit (p := SP1Prime)),
  entry "StoreWord" "SP1Clean.StoreWordChip.circuit" (StoreWordChip.circuit (p := SP1Prime)),
  entry "StoreDouble" "SP1Clean.StoreDoubleChip.circuit" (StoreDoubleChip.circuit (p := SP1Prime)),
  entry "Mul" "SP1Clean.MulChip.circuit" (MulChip.circuit (p := SP1Prime)),
  entry "DivRem" "SP1Clean.DivRemChip.circuit" (DivRemChip.circuit (p := SP1Prime)),
  entry "AluX0" "SP1Clean.AluX0Chip.circuit" (AluX0Chip.circuit (p := SP1Prime))]

/-! ## Row maps

The wire payload carries witness programs; a full trace **row** is the circuit's output
struct (native layout) pushed through the audited native→Rust `reconfigure` map. The
reconfigure functions are fully polymorphic struct re-wirings, so applying them at
`Expression` yields the complete symbolic Rust row — `rustWidth` expressions over the
absolute cell indices — serializable with the existing `Expression` encoding. With it,
an external evaluator reproduces entire SP1 trace rows, not just witness cells. -/

/-- The symbolic Rust row of a chip: the circuit output at input offset `size Input`,
reconfigured to the Rust layout at the `Expression` level. -/
def rowMapOf {Input Output RustOutput : TypeMap} [ProvableType Input]
    [ProvableType Output] [ProvableType RustOutput]
    (c : GeneralFormalCircuit Fp Input Output)
    (reconfigure : Output (Expression Fp) → RustOutput (Expression Fp)) :
    List (Expression Fp) :=
  (toElements (reconfigure ((c.main (varFromOffset Input 0)).output (size Input)))).toList

/-- The 25 chips' symbolic Rust rows (`Faithful.<chip>Reconfigure`, the `ChipFaithful`
whole-row maps). -/
def rowMaps : List (String × List (Expression Fp)) := [
  ("Add", rowMapOf (AddChip.circuit (p := SP1Prime)) Faithful.addChipReconfigure),
  ("Addi", rowMapOf (AddiChip.circuit (p := SP1Prime)) Faithful.addiChipReconfigure),
  ("Addw", rowMapOf (AddwChip.circuit (p := SP1Prime)) Faithful.addwChipReconfigure),
  ("Sub", rowMapOf (SubChip.circuit (p := SP1Prime)) Faithful.subChipReconfigure),
  ("Subw", rowMapOf (SubwChip.circuit (p := SP1Prime)) Faithful.subwChipReconfigure),
  ("Bitwise", rowMapOf (BitwiseChip.circuit (p := SP1Prime)) Faithful.bitwiseChipReconfigure),
  ("Lt", rowMapOf (LtChip.circuit (p := SP1Prime)) Faithful.ltChipReconfigure),
  ("ShiftLeft",
    rowMapOf (ShiftLeftChip.circuit (p := SP1Prime)) Faithful.shiftLeftChipReconfigure),
  ("ShiftRight",
    rowMapOf (ShiftRightChip.circuit (p := SP1Prime)) Faithful.shiftRightChipReconfigure),
  ("Jal", rowMapOf (JalChip.circuit (p := SP1Prime)) Faithful.jalChipReconfigure),
  ("Jalr", rowMapOf (JalrChip.circuit (p := SP1Prime)) Faithful.jalrChipReconfigure),
  ("Branch", rowMapOf (BranchChip.circuit (p := SP1Prime)) Faithful.branchChipReconfigure),
  ("UType", rowMapOf (UTypeChip.circuit (p := SP1Prime)) Faithful.uTypeChipReconfigure),
  ("LoadByte", rowMapOf (LoadByteChip.circuit (p := SP1Prime)) Faithful.loadByteChipReconfigure),
  ("LoadHalf", rowMapOf (LoadHalfChip.circuit (p := SP1Prime)) Faithful.loadHalfChipReconfigure),
  ("LoadWord", rowMapOf (LoadWordChip.circuit (p := SP1Prime)) Faithful.loadWordChipReconfigure),
  ("LoadDouble",
    rowMapOf (LoadDoubleChip.circuit (p := SP1Prime)) Faithful.loadDoubleChipReconfigure),
  ("LoadX0", rowMapOf (LoadX0Chip.circuit (p := SP1Prime)) Faithful.loadX0ChipReconfigure),
  ("StoreByte",
    rowMapOf (StoreByteChip.circuit (p := SP1Prime)) Faithful.storeByteChipReconfigure),
  ("StoreHalf",
    rowMapOf (StoreHalfChip.circuit (p := SP1Prime)) Faithful.storeHalfChipReconfigure),
  ("StoreWord",
    rowMapOf (StoreWordChip.circuit (p := SP1Prime)) Faithful.storeWordChipReconfigure),
  ("StoreDouble",
    rowMapOf (StoreDoubleChip.circuit (p := SP1Prime)) Faithful.storeDoubleChipReconfigure),
  ("Mul", rowMapOf (MulChip.circuit (p := SP1Prime)) Faithful.mulChipReconfigure),
  ("DivRem", rowMapOf (DivRemChip.circuit (p := SP1Prime)) Faithful.divRemChipReconfigure),
  ("AluX0", rowMapOf (AluX0Chip.circuit (p := SP1Prime)) Faithful.aluX0ChipReconfigure)]

/-! ## Manifest derivation

The manifest's hint/data schema is derived from the *serialized* payload (a JSON walk for
`hintGet`/`dataGet` nodes), never hand-maintained — the payload is the single source of
truth. -/

/-- One `hintGet`/`dataGet` occurrence: is-hint, table, width, const row (if the row
expression is a literal), column. -/
structure GetUse where
  isHint : Bool
  table : String
  width : Nat
  constRow : Option Nat
  col : Nat

/-- Aggregated per-`(table, width)` schema entry. -/
structure TableUse where
  table : String
  width : Nat
  rows : List Nat
  cols : List Nat
  dynamicRow : Bool

private def insertSorted (n : Nat) : List Nat → List Nat
  | [] => [n]
  | m :: ms => if n ≤ m then n :: m :: ms else m :: insertSorted n ms

private def sortDedup (xs : List Nat) : List Nat :=
  xs.foldl (fun acc n => if acc.contains n then acc else insertSorted n acc) []

partial def collectGets (j : Json) (acc : Array GetUse := #[]) : Array GetUse :=
  let acc := match j.getObjVal? "type" with
    | .ok (Json.str t) =>
      if t == "hintGet" || t == "dataGet" then
        match j.getObjVal? "table", j.getObjVal? "width", j.getObjVal? "col" with
        | .ok (Json.str table), .ok w, .ok c =>
          let constRow := match j.getObjVal? "row" with
            | .ok r =>
              match r.getObjVal? "type", r.getObjVal? "value" with
              | .ok (Json.str "const"), .ok v => v.getNat?.toOption
              | _, _ => none
            | _ => none
          acc.push ⟨t == "hintGet", table,
            w.getNat?.toOption.getD 0, constRow, c.getNat?.toOption.getD 0⟩
        | _, _, _ => acc
      else acc
    | _ => acc
  match j with
  | .obj kvs => kvs.foldl (fun a _ v => collectGets v a) acc
  | .arr xs => xs.foldl (fun a v => collectGets v a) acc
  | _ => acc

def aggregate (uses : Array GetUse) : List TableUse :=
  uses.foldl (init := []) fun acc u =>
    match acc.partition fun t => t.table == u.table && t.width == u.width with
    | ([t], rest) =>
      let rows := match u.constRow with
        | some r => sortDedup (r :: t.rows)
        | none => t.rows
      let cols := sortDedup (u.col :: t.cols)
      rest ++ [{ t with rows, cols, dynamicRow := t.dynamicRow || u.constRow.isNone }]
    | _ =>
      acc ++ [⟨u.table, u.width, (u.constRow.map ([·])).getD [], [u.col], u.constRow.isNone⟩]

def tableUseJson (t : TableUse) : Json :=
  Json.mkObj <| [
    ("table", Json.str t.table),
    ("width", toJson t.width),
    ("rowsRead", toJson t.rows),
    ("colsRead", toJson t.cols)]
    ++ (if t.dynamicRow then [("dynamicRows", toJson true)] else [])

def fieldJson : Json :=
  Json.mkObj [("name", Json.str "KoalaBear"), ("modulus", toJson SP1Prime)]

def manifestFor (e : Entry) (payload : Json) : Json :=
  let ops := ((payload.getObjVal? "operations").toOption.bind (·.getArr?.toOption)).getD #[]
  let count (k : String) : Nat := ops.foldl (fun n op => if (op.getObjVal? k).isOk then n + 1 else n) 0
  let localLength := ((payload.getObjVal? "localLength").toOption.bind (·.getNat?.toOption)).getD 0
  let gets := collectGets payload
  Json.mkObj [
    ("wireVersion", toJson (1 : Nat)),
    ("witgenFile", Json.str s!"{e.name}.witgen.json"),
    ("name", Json.str e.name),
    ("lean", Json.str e.leanName),
    ("localLength", toJson localLength),
    ("inputWidth", toJson e.inputWidth),
    ("operationCounts", Json.mkObj [
      ("witness", toJson (count "witness")),
      ("assert", toJson (count "assert")),
      ("lookup", toJson (count "lookup")),
      ("interact", toJson (count "interact"))]),
    ("hints", Json.arr ((aggregate (gets.filter (·.isHint))).map tableUseJson).toArray),
    ("hintPolicy", Json.str "a missing table, wrong width, or out-of-range row reads as \
      the all-zero vector"),
    ("data", Json.arr ((aggregate (gets.filter (!·.isHint))).map tableUseJson).toArray),
    ("field", fieldJson)]

/-! ## Driver -/

def writeJson (path : System.FilePath) (j : Json) : IO Unit :=
  IO.FS.writeFile path (j.compress ++ "\n")

/-- Export one chip; returns its `index.json` row. -/
def exportChip (out : Option System.FilePath) (e : Entry) : IO Json := do
  let t0 ← IO.monoMsNow
  let payload ← match e.ops.witgenJson? with
    | .ok j => pure j
    | .error msg => throw (IO.userError s!"{e.name}: {msg}")
  let localLength := ((payload.getObjVal? "localLength").toOption.bind (·.getNat?.toOption)).getD 0
  let serialized := payload.compress ++ "\n"
  match out with
  | none => IO.print serialized
  | some dir =>
    IO.FS.writeFile (dir / s!"{e.name}.witgen.json") serialized
    writeJson (dir / s!"{e.name}.manifest.json") (manifestFor e payload)
  IO.eprintln s!"{e.name}: {(← IO.monoMsNow) - t0} ms, {serialized.utf8ByteSize} bytes"
  return Json.mkObj [
    ("name", Json.str e.name),
    ("witgenFile", Json.str s!"{e.name}.witgen.json"),
    ("manifestFile", Json.str s!"{e.name}.manifest.json"),
    ("inputWidth", toJson e.inputWidth),
    ("localLength", toJson localLength)]

/-! ## Test-data fixtures (`--testdata`)

Differential fixtures for `rust/witgen-interp`, anchored to the committed SP1 trace
dumps (`export/sp1dump/<Chip>.dump.json`, sole writer `scripts/update_sp1_dumps.sh`,
produced by the `chip_traces` binary committed at the pinned extraction branch). Per
chip:

- `"event"` rows — one per dumped executor event. Inputs are recovered from the dumped
  row itself through the symbolic row map; every native input cell is a bare `var`
  column of the Rust row. No hint tables or synthesized activity are used. **The
  generation-time gate:** every event row is recomputed — `witgen` over
  the authored operations, then the symbolic row map evaluated at the resulting cells —
  and must equal the dumped SP1 row cell-for-cell, or the exporter throws with
  chip/row/column detail and writes nothing.
- the padding row — inputs recovered from the dumped padding row (all-zero except
  SP1's nonzero pad templates, e.g. DivRem's `c = 1`). Chips whose padding SP1
  *derives* by populate (ShiftLeft/ShiftRight/DivRem) are gated against the dump too
  (`anchored: true`); the zero-fill chips' dumped padding is asserted all-zero and
  their padding fixture row is a plain differential vector.
- `"synthetic"` rows — deterministic seeded vectors (witness generation is total, so
  every input is valid).

A per-chip spot check pins the gate's Expression-level row evaluation to the
value-level `circuitTraceRowMapped` path (the audited `ChipFaithful` reconfigure at
field values) on event row 0. `expectedWitness` is always the Lean reference
evaluation over the authored flat operations — the same programs Clean serializes. -/

section Testdata
open SP1Clean.TraceGenTests

/-- Deterministic value stream (a 64-bit LCG; generated fixtures must be byte-stable,
so no runtime randomness). -/
def lcgStream (seed : ℕ) : ℕ → ℕ
  | 0 => (seed * 6364136223846793005 + 1442695040888963407) % (2 ^ 64)
  | j + 1 => (lcgStream seed j * 6364136223846793005 + 1442695040888963407) % (2 ^ 64)

/-- Seeded input row (values reduced into the field by the cast). -/
def synInputs (width seed : ℕ) : List Fp :=
  (List.range width).map fun j => ((lcgStream seed j : ℕ) : Fp)

/-- Clean's array-backed `FlatOperation.witgen` at the empty commitment, spelled through the
data-carrying `ToClean` generalization: Clean's own `Circuit/WitnessGeneration.lean` is orphaned
upstream (unwired, non-`module`), so the module-mode `ToClean` no longer reaches it. -/
def witgen (hint : ProverHint Fp) (ops : List (FlatOperation Fp)) (init : Array Fp) : Array Fp :=
  FlatOperation.witgenWithData (fun _ _ => #[]) hint ops init

/-- The Lean reference witness evaluation over the authored flat operations. -/
def expectedWitnessOf (flat : List (FlatOperation Fp)) (hint : ProverHint Fp)
    (inputs : List Fp) : List ℕ :=
  ((witgen hint flat inputs.toArray).toList.drop inputs.length).map ZMod.val

def rowJson (kind : String) (anchored : Bool) (seed : Option ℕ) (inputs : List Fp)
    (hints : Json) (expectedWitness : List ℕ) (expectedRow : Option (List ℕ)) : Json :=
  Json.mkObj <| [("kind", Json.str kind), ("anchored", toJson anchored)]
    ++ (seed.map fun s => [("seed", toJson s)]).getD []
    ++ [("inputs", toJson (inputs.map ZMod.val)), ("hints", hints),
        ("expectedWitness", toJson expectedWitness)]
    ++ (expectedRow.map fun r => [("expectedRow", toJson r)]).getD []

/-! ### SP1 dumps, input recovery, and the generation-time gate -/

/-- One parsed SP1 chip dump: the events and the full padded `generate_trace`
matrix. -/
structure Dump where
  events : List Nat
  rows : List (List Nat)
  width : Nat
  height : Nat

/-- Parse and shape-check `<Chip>.dump.json`. -/
def dumpOf (chip : String) (j : Json) : Except String Dump := do
  let nat (k : String) : Except String Nat :=
    match (j.getObjVal? k).toOption.bind (·.getNat?.toOption) with
    | some n => .ok n
    | none => .error s!"{chip}.dump.json: missing or non-numeric '{k}'"
  unless (← nat "schemaVersion") == 1 do throw s!"{chip}.dump.json: schemaVersion != 1"
  unless (j.getObjVal? "chip").toOption.bind (·.getStr?.toOption) == some chip do
    throw s!"{chip}.dump.json: chip name mismatch"
  let width ← nat "width"
  let height ← nat "height"
  let eventsJ ← match (j.getObjVal? "events").toOption.bind (·.getArr?.toOption) with
    | some a => pure a
    | none => .error s!"{chip}.dump.json: missing events array"
  let events ← eventsJ.toList.mapM fun e => do
    let opcode ← match ((e.getObjVal? "opcode").toOption.bind fun o =>
        (o.getObjVal? "discriminant").toOption).bind (·.getNat?.toOption) with
      | some d => Except.ok d
      | none => Except.error s!"{chip}.dump.json: event without opcode discriminant"
    return opcode
  let rowsJ ← match (j.getObjVal? "rows").toOption.bind (·.getArr?.toOption) with
    | some a => pure a
    | none => .error s!"{chip}.dump.json: missing rows array"
  let rows ← rowsJ.toList.mapM fun r =>
    match r.getArr?.toOption with
    | some cells => cells.toList.mapM fun c =>
        match c.getNat?.toOption with
        | some n => Except.ok n
        | none => Except.error s!"{chip}.dump.json: non-numeric row cell"
    | none => .error s!"{chip}.dump.json: non-array row"
  unless rows.length == height do throw s!"{chip}.dump.json: rows != height"
  unless rows.all (·.length == width) do throw s!"{chip}.dump.json: a row's length != width"
  unless !events.isEmpty do throw s!"{chip}.dump.json: no events"
  unless events.length < height do throw s!"{chip}.dump.json: no padding row"
  return ⟨events, rows, width, height⟩

/-- Every native input is a directly committed SP1 column. Missing inputs fail closed. -/
def inversionOf (chip : String) (inputWidth : Nat) (rowMap : List (Expression Fp)) :
    Except String (List Nat) :=
  (List.range inputWidth).mapM fun i =>
    match rowMap.zipIdx.find? fun (ex, _) =>
        match ex with
        | .var v => v.index == i
        | _ => false with
    | some (_, j) => .ok j
    | none => .error s!"{chip}: input cell {i} is not a bare row column (row map drifted)"

/-- Recover input columns without synthesizing selectors or activity. -/
def invertInputs (inv : List Nat) (row : List Nat) : List Fp :=
  inv.map fun j => ((row.getD j 0 : ℕ) : Fp)

/-- The chips whose padding rows SP1 *derives* by running populate on the pad template
(nonzero `padded_row_template`); the rest zero-fill without running populate. -/
def derivedPadChips : List String := ["ShiftLeft", "ShiftRight", "DivRem"]

/-- Evaluate the symbolic Rust row at the generated witness cells (canonical values).
The environment is exactly the one witness generation itself evaluates against
(`witgenWithData_eq_dynamicWitnessesWithData`). -/
def rowValsOf (rowMap : List (Expression Fp)) (cells : Array Fp) : List Nat :=
  let env :=
    (ProverEnvironment.fromArrayWithData cells (fun _ _ => #[]) (ProverHint.empty Fp)).toEnvironment
  rowMap.map fun ex => (Expression.eval env ex).val

/-- First differing column of two equal-length rows, as `(column, lean, sp1)`. -/
def firstMismatch (lean sp1 : List Nat) : Option (Nat × Nat × Nat) :=
  (lean.zip sp1).zipIdx.findSome? fun ((l, s), j) =>
    if l != s then some (j, l, s) else none

/-- The value-level spot-check generators: `circuitTraceRowMapped` through the audited
`ChipFaithful` reconfigure maps at field values. Run on event row 0 of every chip, this
pins the gate's Expression-level row evaluation to the value-level populate path. -/
def spotChecks : List (String × (List Fp → ProverHint Fp → List Fp)) := [
  ("Add", fun i h => circuitTraceRowMapped _
    (AddChip.circuit (p := SP1Prime)).main Faithful.addChipReconfigure i h),
  ("Addi", fun i h => circuitTraceRowMapped _
    (AddiChip.circuit (p := SP1Prime)).main Faithful.addiChipReconfigure i h),
  ("Addw", fun i h => circuitTraceRowMapped _
    (AddwChip.circuit (p := SP1Prime)).main Faithful.addwChipReconfigure i h),
  ("Sub", fun i h => circuitTraceRowMapped _
    (SubChip.circuit (p := SP1Prime)).main Faithful.subChipReconfigure i h),
  ("Subw", fun i h => circuitTraceRowMapped _
    (SubwChip.circuit (p := SP1Prime)).main Faithful.subwChipReconfigure i h),
  ("Bitwise", fun i h => circuitTraceRowMapped _
    (BitwiseChip.circuit (p := SP1Prime)).main Faithful.bitwiseChipReconfigure i h),
  ("Lt", fun i h => circuitTraceRowMapped _
    (LtChip.circuit (p := SP1Prime)).main Faithful.ltChipReconfigure i h),
  ("ShiftLeft", fun i h => circuitTraceRowMapped _
    (ShiftLeftChip.circuit (p := SP1Prime)).main Faithful.shiftLeftChipReconfigure i h),
  ("ShiftRight", fun i h => circuitTraceRowMapped _
    (ShiftRightChip.circuit (p := SP1Prime)).main Faithful.shiftRightChipReconfigure i h),
  ("Jal", fun i h => circuitTraceRowMapped _
    (JalChip.circuit (p := SP1Prime)).main Faithful.jalChipReconfigure i h),
  ("Jalr", fun i h => circuitTraceRowMapped _
    (JalrChip.circuit (p := SP1Prime)).main Faithful.jalrChipReconfigure i h),
  ("Branch", fun i h => circuitTraceRowMapped _
    (BranchChip.circuit (p := SP1Prime)).main Faithful.branchChipReconfigure i h),
  ("UType", fun i h => circuitTraceRowMapped _
    (UTypeChip.circuit (p := SP1Prime)).main Faithful.uTypeChipReconfigure i h),
  ("LoadByte", fun i h => circuitTraceRowMapped _
    (LoadByteChip.circuit (p := SP1Prime)).main Faithful.loadByteChipReconfigure i h),
  ("LoadHalf", fun i h => circuitTraceRowMapped _
    (LoadHalfChip.circuit (p := SP1Prime)).main Faithful.loadHalfChipReconfigure i h),
  ("LoadWord", fun i h => circuitTraceRowMapped _
    (LoadWordChip.circuit (p := SP1Prime)).main Faithful.loadWordChipReconfigure i h),
  ("LoadDouble", fun i h => circuitTraceRowMapped _
    (LoadDoubleChip.circuit (p := SP1Prime)).main Faithful.loadDoubleChipReconfigure i h),
  ("LoadX0", fun i h => circuitTraceRowMapped _
    (LoadX0Chip.circuit (p := SP1Prime)).main Faithful.loadX0ChipReconfigure i h),
  ("StoreByte", fun i h => circuitTraceRowMapped _
    (StoreByteChip.circuit (p := SP1Prime)).main Faithful.storeByteChipReconfigure i h),
  ("StoreHalf", fun i h => circuitTraceRowMapped _
    (StoreHalfChip.circuit (p := SP1Prime)).main Faithful.storeHalfChipReconfigure i h),
  ("StoreWord", fun i h => circuitTraceRowMapped _
    (StoreWordChip.circuit (p := SP1Prime)).main Faithful.storeWordChipReconfigure i h),
  ("StoreDouble", fun i h => circuitTraceRowMapped _
    (StoreDoubleChip.circuit (p := SP1Prime)).main Faithful.storeDoubleChipReconfigure i h),
  ("Mul", fun i h => circuitTraceRowMapped _
    (MulChip.circuit (p := SP1Prime)).main Faithful.mulChipReconfigure i h),
  ("DivRem", fun i h => circuitTraceRowMapped _
    (DivRemChip.circuit (p := SP1Prime)).main Faithful.divRemChipReconfigure i h),
  ("AluX0", fun i h => circuitTraceRowMapped _
    (AluX0Chip.circuit (p := SP1Prime)).main Faithful.aluX0ChipReconfigure i h)]

/-- Write one chip's differential fixture from its committed SP1 dump, running the
generation-time gate first. `idx` is the chip's position in the full registry (stable
seeds even under `--chip` filtering). -/
def writeTestdataChip (dumpDir dir : System.FilePath) (sp1Commit : String) (idx : ℕ)
    (e : Entry) : IO Unit := do
  let t0 ← IO.monoMsNow
  let payload ← match e.ops.witgenJson? with
    | .ok j => pure j
    | .error msg => throw (IO.userError s!"{e.name}: {msg}")
  unless ((collectGets payload).filter (·.isHint)).isEmpty do
    throw (IO.userError s!"{e.name}: instruction witnesses must not read prover hints")
  let flat := e.ops.toFlat
  let empty : ProverHint Fp := ProverHint.empty Fp
  -- The SP1 dump, the symbolic row map, and the input-recovery table.
  let dump ← match Json.parse (← IO.FS.readFile (dumpDir / s!"{e.name}.dump.json"))
      >>= dumpOf e.name with
    | .ok d => pure d
    | .error msg => throw (IO.userError msg)
  let rowMap ← match rowMaps.find? (·.1 == e.name) with
    | some (_, m) => pure m
    | none => throw (IO.userError s!"{e.name}: no row map registered")
  unless rowMap.length == dump.width do
    throw (IO.userError
      s!"{e.name}: row map width {rowMap.length} != dump width {dump.width}")
  let inv ← match inversionOf e.name e.inputWidth rowMap with
    | .ok i => pure i
    | .error msg => throw (IO.userError msg)
  let mut rows : Array Json := #[]
  -- Event rows: recover inputs, recompute, gate cell-for-cell against the dump.
  for (ev, k) in dump.events.zipIdx do
    let sp1Row := dump.rows.getD k []
    let inputs := invertInputs inv sp1Row
    let cells := witgen empty flat inputs.toArray
    if let some (j, l, s) := firstMismatch (rowValsOf rowMap cells) sp1Row then
      throw (IO.userError s!"{e.name}: GATE FAILED at event row {k} column {j}: \
        recomputed {l} != SP1 {s} (opcode {ev})")
    rows := rows.push (rowJson "event" true none inputs (Json.mkObj [])
      ((cells.toList.drop inputs.length).map ZMod.val) (some sp1Row))
  -- The value-level spot check on event row 0.
  let spot ← match spotChecks.find? (·.1 == e.name) with
    | some (_, f) => pure f
    | none => throw (IO.userError s!"{e.name}: no spot check registered")
  let row0 := dump.rows.getD 0 []
  let spotRow := spot (invertInputs inv row0)
    empty
  unless spotRow.map ZMod.val == row0 do
    throw (IO.userError
      s!"{e.name}: circuitTraceRowMapped spot check diverged from the dump on event row 0")
  -- The padding row: recovered inputs; gated for the derived-pad chips, asserted
  -- all-zero for the zero-fill chips. SP1 pads with one repeated template row.
  let padSp1 := dump.rows.getD dump.events.length []
  unless (dump.rows.drop dump.events.length).all (· == padSp1) do
    throw (IO.userError s!"{e.name}: padding rows are not uniform in the dump")
  let padInputs := invertInputs inv padSp1
  let padWitness := expectedWitnessOf flat empty padInputs
  if derivedPadChips.contains e.name then
    let padCells := witgen empty flat padInputs.toArray
    if let some (j, l, s) := firstMismatch (rowValsOf rowMap padCells) padSp1 then
      throw (IO.userError s!"{e.name}: GATE FAILED at the padding row, column {j}: \
        recomputed {l} != SP1 {s}")
    rows := rows.push (rowJson "padding" true none padInputs (Json.mkObj [])
      padWitness (some padSp1))
  else
    unless padSp1.all (· == 0) do
      throw (IO.userError s!"{e.name}: zero-fill padding row is not all-zero in the dump")
    rows := rows.push (rowJson "padding" false none padInputs (Json.mkObj [])
      padWitness none)
  let mut provenance : List (String × Json) := [("events", Json.str
    s!"SP1 chip_traces dump export/sp1dump/{e.name}.dump.json (sp1Commit {sp1Commit}); \
    inputs recovered through the symbolic row map; every event row and every derived \
    padding row recomputed via FlatOperation.witgen + row-map evaluation and matched \
    cell-for-cell at generation time (fail-closed), with a value-level \
    circuitTraceRowMapped spot check on event row 0")]
  let zero := List.replicate e.inputWidth (0 : Fp)
  rows := rows.push (rowJson "synthetic" false (some 0) zero (Json.mkObj [])
    (expectedWitnessOf flat empty zero) none)
  for s in [1, 2, 3, 4] do
    let seed := (idx + 1) * 1009 + s
    let inputs := synInputs e.inputWidth seed
    rows := rows.push (rowJson "synthetic" false (some seed) inputs
      (Json.mkObj []) (expectedWitnessOf flat empty inputs) none)
  provenance := provenance ++ [("synthetic", Json.str
    "deterministic seeded inputs; expectedWitness is the Lean reference evaluation \
    (FlatOperation.witgen) over the authored operations serialized by Clean")]
  writeJson (dir / s!"{e.name}.trace.json") <| Json.mkObj [
    ("wireVersion", toJson (1 : Nat)),
    ("chip", Json.str e.name),
    ("field", fieldJson),
    ("inputWidth", toJson e.inputWidth),
    ("localLength", toJson (FlatOperation.localLengthFold flat)),
    ("provenance", Json.mkObj provenance),
    ("rows", Json.arr rows)]
  IO.eprintln s!"{e.name}: testdata {(← IO.monoMsNow) - t0} ms, {rows.size} rows"

end Testdata

def run : IO Unit := do
  let args := ((← IO.getEnv "WITGEN_ARGS").getD "").splitOn " " |>.filter (· != "")
  let chipFilter := (args.dropWhile (· != "--chip")).drop 1 |>.head?
  let toStdout := args.contains "--stdout"
  let testdata := args.contains "--testdata"
  let outRoot := (← IO.getEnv "WITGEN_EXPORT_OUT").getD
    ((args.dropWhile (· != "--out")).drop 1 |>.head?.getD ".lake/witgen-export/manual")
  let regNames := (Soundness.supportedChips (p := SP1Prime)).map (·.kind.name)
  unless entries.map (·.name) == regNames do
    throw (IO.userError s!"chip list drifted from supportedChips:\n  \
      script:   {entries.map (·.name)}\n  registry: {regNames}")
  let selected := entries.zipIdx.filter fun (e, _) => chipFilter.all (· == e.name)
  if selected.isEmpty then
    throw (IO.userError s!"no chip named {chipFilter.getD "?"}; known: {entries.map (·.name)}")
  let t0 ← IO.monoMsNow
  if testdata then
    -- Dumps are an input, always read from the committed tree (never from --out).
    let dumpDir : System.FilePath := System.FilePath.mk "export" / "sp1dump"
    let sp1Commit ← match Json.parse (← IO.FS.readFile (dumpDir / "index.json"))
        >>= (·.getObjVal? "sp1Commit") with
      | .ok (Json.str c) => pure c
      | _ => throw (IO.userError "export/sp1dump/index.json: missing sp1Commit")
    let dir : System.FilePath := System.FilePath.mk outRoot / "testdata"
    IO.FS.createDirAll dir
    for (e, idx) in selected do
      writeTestdataChip dumpDir dir sp1Commit idx e
    IO.eprintln s!"total: {selected.length} chips (testdata), {(← IO.monoMsNow) - t0} ms"
    return
  let out ← if toStdout then pure none else do
    let dir : System.FilePath := System.FilePath.mk outRoot / "witgen"
    IO.FS.createDirAll dir
    pure (some dir)
  let mut indexRows : Array Json := #[]
  for (e, _) in selected do
    indexRows := indexRows.push (← exportChip out e)
    if let some dir := out then
      match rowMaps.find? (·.1 == e.name) with
      | some (_, row) =>
        writeJson (dir / s!"{e.name}.rowmap.json") <| Json.mkObj [
          ("wireVersion", toJson (1 : Nat)),
          ("name", Json.str e.name),
          ("rustWidth", toJson row.length),
          ("row", toJson row)]
      | none => throw (IO.userError s!"{e.name}: no row map registered")
  -- Never write a partial index: only the full, unfiltered run produces `index.json`.
  if chipFilter.isNone then
    if let some dir := out then
      writeJson (dir / "index.json") <| Json.mkObj [
        ("wireVersion", toJson (1 : Nat)),
        ("field", fieldJson),
        ("chips", Json.arr indexRows)]
  IO.eprintln s!"total: {selected.length} chips, {(← IO.monoMsNow) - t0} ms"

end WitgenExportScript

#eval WitgenExportScript.run
