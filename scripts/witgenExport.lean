import SP1CleanTest.Exportable
import SP1CleanTest.TraceGenTests.AddChipTraceWitness
import SP1CleanTest.TraceGenTests.SubChipTraceWitness
import SP1CleanTest.TraceGenTests.SubwChipTraceWitness
import SP1CleanTest.TraceGenTests.AddwChipTraceWitness
import SP1CleanTest.TraceGenTests.MulChipTraceWitness
import SP1CleanTest.TraceGenTests.DivRemChipTraceWitness
import SP1CleanTest.TraceGenTests.BitwiseChipTraceWitness
import SP1CleanTest.TraceGenTests.LtChipTraceWitness
import SP1CleanTest.TraceGenTests.ShiftLeftChipTraceWitness
import SP1CleanTest.TraceGenTests.ShiftRightChipTraceWitness

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

Defaults: `--out export` (writing `export/witgen/`). `--chip NAME` restricts to one chip
and skips `index.json` (never a partial index); `--stdout` prints the payload instead of
writing files. `--testdata` writes `export/testdata/<Chip>.trace.json` differential
fixtures instead: for the ten trace-anchored chips, one row per SP1-dumped event
(inputs via the `EventPopulate` flatteners, hints via the per-chip builders,
`expectedRow` copied from the dumped SP1 rows whose equality with the circuit-derived
rows is pinned by the `native_decide` anchors) plus an honest padding row; for all 25
chips, deterministic seeded synthetic rows. `expectedWitness` is always the Lean
reference evaluation (`FlatOperation.witgen`) over the **shared** operation list — the
same programs the wire carries, and `WitgenIR.eval_share` proves sharing changes no
evaluation.

This is deliberately an interpreted script, not a `lean_exe`: elaborating the file runs
the trailing `#eval` against the already-built oleans (the same path as
`#assert_exportable`'s `#eval`s in `SP1CleanTest/Exportable.lean`), where a compiled
executable would force native compilation of the whole import closure. Upstream Clean
drives its plonky3 fixture scripts the same way, via `lean --run` — unavailable here
because the generated Sail model (`LeanRV64D`) already owns the root `main`, hence the
`WITGEN_ARGS` environment variable instead of argv.

⚠ `lake env lean` exits 0 on a Lean stack overflow (repo-known trap), so callers must
validate the outputs, not the exit code — `scripts/check_witgen_export.sh` does.

The serializer is Clean's `Operations.witgenJson?`
(`.lake/packages/Clean/Clean/Circuit/WitnessExport.lean`); this script only enumerates
the 25 chip circuits at `SP1Prime`, derives the manifests from the serialized payloads,
and writes files. Output is byte-stable: no timestamps or revisions are embedded, and
JSON key order is code-determined. -/

namespace WitgenExportScript

open Lean SP1Clean SP1Clean.ExportableTests

abbrev Fp := ZMod SP1Prime

/-- Hash field elements by canonical value (for `WitgenIR.share`'s memo tables). -/
instance : Hashable Fp := ⟨fun x => hash x.val⟩

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
      the all-zero vector; padding rows rely on this default"),
    ("data", Json.arr ((aggregate (gets.filter (!·.isHint))).map tableUseJson).toArray),
    ("field", fieldJson)]

/-! ## Driver -/

def writeJson (path : System.FilePath) (j : Json) : IO Unit :=
  IO.FS.writeFile path (j.pretty ++ "\n")

/-- Export one chip; returns its `index.json` row. -/
def exportChip (out : Option System.FilePath) (e : Entry) : IO Json := do
  let t0 ← IO.monoMsNow
  let payload ← match e.ops.witgenJsonShared? with
    | .ok j => pure j
    | .error msg => throw (IO.userError s!"{e.name}: {msg}")
  let localLength := ((payload.getObjVal? "localLength").toOption.bind (·.getNat?.toOption)).getD 0
  match out with
  | none => IO.print (payload.pretty ++ "\n")
  | some dir =>
    writeJson (dir / s!"{e.name}.witgen.json") payload
    writeJson (dir / s!"{e.name}.manifest.json") (manifestFor e payload)
  IO.eprintln s!"{e.name}: {(← IO.monoMsNow) - t0} ms, {(payload.pretty.utf8ByteSize + 1)} bytes"
  return Json.mkObj [
    ("name", Json.str e.name),
    ("witgenFile", Json.str s!"{e.name}.witgen.json"),
    ("manifestFile", Json.str s!"{e.name}.manifest.json"),
    ("inputWidth", toJson e.inputWidth),
    ("localLength", toJson localLength)]

/-! ## Test-data fixtures (`--testdata`)

Differential fixtures for `rust/witgen-interp`: per row, the seeded input cells, the
hint tables, and the expected witness cells from the Lean reference evaluation
(`FlatOperation.witgen`) over the **shared** flat operations — the same programs the
wire carries (`WitgenIR.eval_share` proves sharing preserves evaluation). Rows carry
honest provenance: `"event"` rows come from SP1-dumped executor events whose full-row
equality with the circuit derivation is pinned by a `native_decide` trace anchor
(`expectedRow` is copied from the dumped SP1 rows verbatim); `"padding"` rows are
SP1-anchored only for the chips whose padding SP1 *derives* (ShiftLeft/ShiftRight/
DivRem — the rest zero-fill without running populate, so their zero-input padding row
is a plain differential vector); `"synthetic"` rows are deterministic seeded vectors
(witness generation is total, so every input is valid). -/

section Testdata
open SP1Clean.TraceGenTests

/-- Deterministic value stream (a 64-bit LCG; committed fixtures must be byte-stable,
so no runtime randomness). -/
def lcgStream (seed : ℕ) : ℕ → ℕ
  | 0 => (seed * 6364136223846793005 + 1442695040888963407) % (2 ^ 64)
  | j + 1 => (lcgStream seed j * 6364136223846793005 + 1442695040888963407) % (2 ^ 64)

/-- Seeded input row (values reduced into the field by the cast). -/
def synInputs (width seed : ℕ) : List Fp :=
  (List.range width).map fun j => ((lcgStream seed j : ℕ) : Fp)

/-- Seeded hint tables from the payload-derived schema: one row per declared table,
0/1-valued (the hint tables in these chips carry selector flags). -/
def synHint (uses : List TableUse) (seed : ℕ) : ProverHint Fp := fun key n =>
  if uses.any fun u => u.table == key && u.width == n then
    #[Vector.ofFn fun i : Fin n => ((lcgStream seed i.val % 2 : ℕ) : Fp)]
  else #[]

/-- Serialize the declared hint tables as read from a `ProverHint`. -/
def serializeHints (uses : List TableUse) (h : ProverHint Fp) : Json :=
  Json.mkObj <| uses.map fun u =>
    (u.table, Json.mkObj [
      ("width", toJson u.width),
      ("rows", toJson ((h u.table u.width).toList.map fun v => v.toList.map ZMod.val))])

/-- The Lean reference witness evaluation over the shared flat operations. -/
def expectedWitnessOf (flatShared : List (FlatOperation Fp)) (hint : ProverHint Fp)
    (inputs : List Fp) : List ℕ :=
  ((FlatOperation.witgen hint flatShared inputs.toArray).toList.drop inputs.length).map
    ZMod.val

def rowJson (kind : String) (anchored : Bool) (seed : Option ℕ) (inputs : List Fp)
    (hints : Json) (expectedWitness : List ℕ) (expectedRow : Option (List ℕ)) : Json :=
  Json.mkObj <| [("kind", Json.str kind), ("anchored", toJson anchored)]
    ++ (seed.map fun s => [("seed", toJson s)]).getD []
    ++ [("inputs", toJson (inputs.map ZMod.val)), ("hints", hints),
        ("expectedWitness", toJson expectedWitness)]
    ++ (expectedRow.map fun r => [("expectedRow", toJson r)]).getD []

/-- One trace-anchored chip's event data, pre-flattened to `(inputs, hint)` pairs. -/
structure AnchoredData where
  inputsHints : List (List Fp × ProverHint Fp)
  /-- The dumped SP1 rows, one per event (`<Chip>ChipTraceRows` truncated). -/
  expectedRows : List (List ℕ)
  padInputs : List Fp
  /-- Whether SP1 *derives* its padding rows by populate (ShiftLeft/ShiftRight/DivRem);
  the zero-fill chips write literal zero rows without running populate. -/
  padAnchored : Bool
  padExpectedRow : Option (List ℕ)
  /-- The `native_decide` anchor pinning derived rows == dumped rows. -/
  thm : String

/-- The ten trace-anchored chips (the whole-trace conformance battery). -/
def anchoredData : List (String × AnchoredData) := [
  ("Add", {
    inputsHints := AddChipTraceEvents.map fun e => (rTypeEventInputs e, ProverHint.empty _),
    expectedRows := (AddChipTraceRows.take AddChipTraceEvents.length).map (·.toList),
    padInputs := List.replicate 29 0, padAnchored := false, padExpectedRow := none,
    thm := "SP1Clean.TraceGenTests.addchip_trace_conforms" }),
  ("Sub", {
    inputsHints := SubChipTraceEvents.map fun e => (rTypeEventInputs e, ProverHint.empty _),
    expectedRows := (SubChipTraceRows.take SubChipTraceEvents.length).map (·.toList),
    padInputs := List.replicate 29 0, padAnchored := false, padExpectedRow := none,
    thm := "SP1Clean.TraceGenTests.subchip_trace_conforms" }),
  ("Subw", {
    inputsHints := SubwChipTraceEvents.map fun e => (rTypeEventInputs e, ProverHint.empty _),
    expectedRows := (SubwChipTraceRows.take SubwChipTraceEvents.length).map (·.toList),
    padInputs := List.replicate 29 0, padAnchored := false, padExpectedRow := none,
    thm := "SP1Clean.TraceGenTests.subwchip_trace_conforms" }),
  ("Addw", {
    inputsHints := AddwChipTraceEvents.map fun e => (aluTypeEventInputs e, ProverHint.empty _),
    expectedRows := (AddwChipTraceRows.take AddwChipTraceEvents.length).map (·.toList),
    padInputs := List.replicate 33 0, padAnchored := false, padExpectedRow := none,
    thm := "SP1Clean.TraceGenTests.addwchip_trace_conforms" }),
  ("Mul", {
    inputsHints := MulChipTraceEvents.map fun e => (rTypeOpEventInputs e, mulHint e.opcode),
    expectedRows := (MulChipTraceRows.take MulChipTraceEvents.length).map (·.toList),
    padInputs := List.replicate 29 0, padAnchored := false, padExpectedRow := none,
    thm := "SP1Clean.TraceGenTests.mulchip_trace_conforms" }),
  ("DivRem", {
    inputsHints := DivRemChipTraceEvents.map fun e =>
      (rTypeOpEventInputs e, divRemHint e.opcode),
    expectedRows := (DivRemChipTraceRows.take DivRemChipTraceEvents.length).map (·.toList),
    padInputs := divRemPadInputs, padAnchored := true,
    padExpectedRow :=
      (DivRemChipTraceRows.drop DivRemChipTraceEvents.length).head?.map (·.toList),
    thm := "SP1Clean.TraceGenTests.divremchip_trace_conforms" }),
  ("Bitwise", {
    inputsHints := BitwiseChipTraceEvents.map fun e =>
      (aluTypeOpEventInputs e, bitwiseHint e.opcode),
    expectedRows := (BitwiseChipTraceRows.take BitwiseChipTraceEvents.length).map (·.toList),
    padInputs := List.replicate 33 0, padAnchored := false, padExpectedRow := none,
    thm := "SP1Clean.TraceGenTests.bitwisechip_trace_conforms" }),
  ("Lt", {
    inputsHints := LtChipTraceEvents.map fun e => (aluTypeOpEventInputs e, ltHint e.opcode),
    expectedRows := (LtChipTraceRows.take LtChipTraceEvents.length).map (·.toList),
    padInputs := List.replicate 33 0, padAnchored := false, padExpectedRow := none,
    thm := "SP1Clean.TraceGenTests.ltchip_trace_conforms" }),
  ("ShiftLeft", {
    inputsHints := ShiftLeftChipTraceEvents.map fun e =>
      (aluTypeOpEventInputs e, shiftLeftHint e.opcode),
    expectedRows :=
      (ShiftLeftChipTraceRows.take ShiftLeftChipTraceEvents.length).map (·.toList),
    padInputs := List.replicate 33 0, padAnchored := true,
    padExpectedRow :=
      (ShiftLeftChipTraceRows.drop ShiftLeftChipTraceEvents.length).head?.map (·.toList),
    thm := "SP1Clean.TraceGenTests.shiftleftchip_trace_conforms" }),
  ("ShiftRight", {
    inputsHints := ShiftRightChipTraceEvents.map fun e =>
      (aluTypeOpEventInputs e, shiftRightHint e.opcode),
    expectedRows :=
      (ShiftRightChipTraceRows.take ShiftRightChipTraceEvents.length).map (·.toList),
    padInputs := List.replicate 33 0, padAnchored := true,
    padExpectedRow :=
      (ShiftRightChipTraceRows.drop ShiftRightChipTraceEvents.length).head?.map (·.toList),
    thm := "SP1Clean.TraceGenTests.shiftrightchip_trace_conforms" })]

/-- Write one chip's differential fixture. `idx` is the chip's position in the full
registry (stable seeds even under `--chip` filtering). -/
def writeTestdataChip (dir : System.FilePath) (idx : ℕ) (e : Entry) : IO Unit := do
  let t0 ← IO.monoMsNow
  let payload ← match e.ops.witgenJsonShared? with
    | .ok j => pure j
    | .error msg => throw (IO.userError s!"{e.name}: {msg}")
  let uses := aggregate ((collectGets payload).filter (·.isHint))
  let flatShared := e.ops.toFlat.map .share
  let empty : ProverHint Fp := ProverHint.empty Fp
  let mut rows : Array Json := #[]
  let mut provenance : List (String × Json) := []
  match anchoredData.find? (·.1 == e.name) with
  | some (_, a) =>
    unless a.inputsHints.all (·.1.length == e.inputWidth) do
      throw (IO.userError s!"{e.name}: event inputs drifted from inputWidth {e.inputWidth}")
    unless a.inputsHints.length == a.expectedRows.length do
      throw (IO.userError s!"{e.name}: event/row count mismatch")
    for (ih, row) in a.inputsHints.zip a.expectedRows do
      rows := rows.push (rowJson "event" true none ih.1 (serializeHints uses ih.2)
        (expectedWitnessOf flatShared ih.2 ih.1) (some row))
    rows := rows.push (rowJson "padding" a.padAnchored none a.padInputs
      (serializeHints uses empty) (expectedWitnessOf flatShared empty a.padInputs)
      a.padExpectedRow)
    provenance := provenance ++ [("events", Json.str
      s!"SP1 generate_trace dump; full-row equality pinned by {a.thm} (native_decide)")]
  | none => pure ()
  let zero := List.replicate e.inputWidth (0 : Fp)
  rows := rows.push (rowJson "synthetic" false (some 0) zero (serializeHints uses empty)
    (expectedWitnessOf flatShared empty zero) none)
  for s in [1, 2, 3, 4] do
    let seed := (idx + 1) * 1009 + s
    let inputs := synInputs e.inputWidth seed
    let hint := synHint uses (seed * 7919)
    rows := rows.push (rowJson "synthetic" false (some seed) inputs
      (serializeHints uses hint) (expectedWitnessOf flatShared hint inputs) none)
  provenance := provenance ++ [("synthetic", Json.str
    "deterministic seeded inputs; expectedWitness is the Lean reference evaluation \
    (FlatOperation.witgen) over the shared operations — WitgenIR.eval_share proves \
    sharing preserves evaluation")]
  writeJson (dir / s!"{e.name}.trace.json") <| Json.mkObj [
    ("wireVersion", toJson (1 : Nat)),
    ("chip", Json.str e.name),
    ("field", fieldJson),
    ("inputWidth", toJson e.inputWidth),
    ("localLength", toJson (FlatOperation.localLengthFold flatShared)),
    ("provenance", Json.mkObj provenance),
    ("rows", Json.arr rows)]
  IO.eprintln s!"{e.name}: testdata {(← IO.monoMsNow) - t0} ms, {rows.size} rows"

end Testdata

def run : IO Unit := do
  let args := ((← IO.getEnv "WITGEN_ARGS").getD "").splitOn " " |>.filter (· != "")
  let chipFilter := (args.dropWhile (· != "--chip")).drop 1 |>.head?
  let toStdout := args.contains "--stdout"
  let testdata := args.contains "--testdata"
  let outRoot := (args.dropWhile (· != "--out")).drop 1 |>.head?.getD "export"
  let regNames := (Soundness.supportedChips (p := SP1Prime)).map (·.kind.name)
  unless entries.map (·.name) == regNames do
    throw (IO.userError s!"chip list drifted from supportedChips:\n  \
      script:   {entries.map (·.name)}\n  registry: {regNames}")
  let selected := entries.zipIdx.filter fun (e, _) => chipFilter.all (· == e.name)
  if selected.isEmpty then
    throw (IO.userError s!"no chip named {chipFilter.getD "?"}; known: {entries.map (·.name)}")
  let t0 ← IO.monoMsNow
  if testdata then
    let dir : System.FilePath := System.FilePath.mk outRoot / "testdata"
    IO.FS.createDirAll dir
    for (e, idx) in selected do
      writeTestdataChip dir idx e
    IO.eprintln s!"total: {selected.length} chips (testdata), {(← IO.monoMsNow) - t0} ms"
    return
  let out ← if toStdout then pure none else do
    let dir : System.FilePath := System.FilePath.mk outRoot / "witgen"
    IO.FS.createDirAll dir
    pure (some dir)
  let mut indexRows : Array Json := #[]
  for (e, _) in selected do
    indexRows := indexRows.push (← exportChip out e)
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
