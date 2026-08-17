import SP1CleanTest.Exportable

/-! # `witgenExport` — the witness-IR export driver (wave D2)

Serializes every registered chip's witness-generation programs (plus its complete
assert/lookup/interact list) in Clean's `version: 1` witgen wire format, the payload the
Rust reference interpreter (`rust/witgen-interp/`) consumes, together with a per-chip
manifest carrying what the wire format deliberately omits (field modulus, input width,
chip name, hint schema) and a top-level `index.json`.

Run from the repo root against built oleans:

    lake build SP1CleanTest.Exportable
    WITGEN_ARGS="[--out DIR] [--chip NAME] [--stdout]" lake env lean scripts/witgenExport.lean

Defaults: `--out export` (writing `export/witgen/`). `--chip NAME` restricts to one chip
and skips `index.json` (never a partial index); `--stdout` prints the payload instead of
writing files.

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

def run : IO Unit := do
  let args := ((← IO.getEnv "WITGEN_ARGS").getD "").splitOn " " |>.filter (· != "")
  let chipFilter := (args.dropWhile (· != "--chip")).drop 1 |>.head?
  let toStdout := args.contains "--stdout"
  let outRoot := (args.dropWhile (· != "--out")).drop 1 |>.head?.getD "export"
  let regNames := (Soundness.supportedChips (p := SP1Prime)).map (·.kind.name)
  unless entries.map (·.name) == regNames do
    throw (IO.userError s!"chip list drifted from supportedChips:\n  \
      script:   {entries.map (·.name)}\n  registry: {regNames}")
  let selected := entries.filter fun e => chipFilter.all (· == e.name)
  if selected.isEmpty then
    throw (IO.userError s!"no chip named {chipFilter.getD "?"}; known: {entries.map (·.name)}")
  let out ← if toStdout then pure none else do
    let dir : System.FilePath := System.FilePath.mk outRoot / "witgen"
    IO.FS.createDirAll dir
    pure (some dir)
  let t0 ← IO.monoMsNow
  let mut indexRows : Array Json := #[]
  for e in selected do
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
