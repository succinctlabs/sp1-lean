import Batteries.Tactic.Lint

/-!
# sp1Lint — the project's `lake lint` driver (environment linters)

A thin wrapper around the Batteries `#lint` framework (`getChecks` / `lintCore`), adapted for this
project in the two ways the stock `runLinter` exe cannot do:

* **Decl filter by full module path.** `runLinter` scopes by namespace *root* (it lints
  `getDeclsInPackage module.getRoot`), so pointing it anywhere in this package lints every `SP1Clean.*`
  declaration — including the auto-generated `SP1Clean.Extracted.*` modules and the `*Vectors` trace
  batteries. We instead keep only hand-written declarations (`getHandwrittenDecls`). NOTE: the per-file
  `set_option linter.all false` headers on the generated files gate only the *syntactic* linters during
  elaboration; they do nothing against these *environment* linters, which run post-import over the built
  environment. `nolints.json` / `@[nolint]` are the only env-linter suppressions.

  INVARIANT: `getHandwrittenDecls` keeps the hand-written declarations of this project — the
  `SP1Clean.*` tree minus the auto-gen ones (the `SP1Clean.Extracted` prefix except its two
  hand-written members, `ExtractionDSL` and `InteractionModel`: the constraint structs
  + the main-lib `Circuit/` forms; and any module ending in "Vectors") — plus the two
  upstream-destined libraries `ToClean.*` / `ToMathlib.*`, which are hand-written and deliberately
  get no linter relaxation (material heading upstream should meet the same bar). Those two are
  imported only if their oleans exist, so this driver runs before and after they are created.
  The whole top-level **test** library `SP1CleanTest.*` (the witness/trace conformance anchors +
  their `update_extracted.py`-written `…Vectors`/`Vectors.*` modules) is excluded automatically,
  since none of the three kept prefixes is a prefix of `SP1CleanTest` — so `lake lint` covers the
  main + upstream libraries only (matching mathlib/batteries, which don't env-lint their test libs).

* **Curated linter set.** We run a low-noise subset via `runOnly`, omitting the doc-coverage linters
  (`docBlame`/`docBlameThm`/`tacticDocs`) that would swamp a proofs project. See `curatedLinters`
  below; grow it deliberately (and see AGENTS.md § Linters).

Wired as the package `lintDriver`, so `lake lint` runs it (after `lake build`, which the env linters need
for oleans). Residue is recorded in `scripts/nolints.json`; `lake exe sp1Lint --update` snapshots the
current violation set into it (the standard ratchet). Without `--update`, any *new* violation fails (exit 1).
-/

open Lean Core Elab Batteries.Tactic.Lint
open System (FilePath)

/-! ## The placement linter

`docs/layering.md` law 2: *a public declaration belongs in the lowest stratum that can state it* --
the join of the strata of the constants in its **type**, not its proof and not its first consumer.

Why the type and not the proof: for a theorem `T`, everything in `Prf(T) \ Stmt(T)` is kernel-checked
and cannot make `T` say something false, so the whole risk of proving the wrong thing lives in
`Stmt(T)` (`docs/audit-surface.md`). Placing by statement vocabulary therefore makes module altitude
and audit altitude the same number, and a declaration above its statement vocabulary is exactly one
that some legitimate consumer below it cannot reach.

`scripts/check_layering.sh` catches misplaced *files* (by import direction and namespace). This
catches misplaced *declarations*, which is a strictly finer net: `tableCleanAccesses` sat in
`Faithful/Transport/Table.lean` under a matching namespace with no upward import, so only this law
saw it.

Private declarations are exempt -- nothing below can cite them, so they cause no reachability harm.
So are internal names and anything whose type mentions no stratified constant at all.

The stratum map is read from `scripts/layering.txt`, the same file the shell gate uses, so the two
cannot drift. -/

/-- The stratum map, parsed once per lint run. `none` until first use. -/
initialize strataCache : IO.Ref (Option (Array (String × Nat))) ← IO.mkRef none

/-- `<stratum> <pillar> <path-prefix>` lines from `scripts/layering.txt`, most-specific first. -/
def loadStrata : IO (Array (String × Nat)) := do
  if let some cached ← strataCache.get then return cached
  let text ← IO.FS.readFile "scripts/layering.txt"
  let mut rows : Array (String × Nat) := #[]
  for line in text.splitOn "\n" do
    let line := (line.splitOn "#").headD ""
    let parts := line.splitOn " " |>.filter (!·.isEmpty)
    match parts with
    | [lvl, _pillar, pfx] => if let some n := lvl.toNat? then rows := rows.push (pfx, n)
    | _ => pure ()
  let sorted := rows.qsort (fun a b => a.1.length > b.1.length)
  strataCache.set (some sorted)
  return sorted

/-- Module name to repo path, e.g. `SP1Clean.Model.Foo` to `SP1Clean/Model/Foo.lean`. -/
def modulePath (m : Name) : String :=
  (m.components.map toString |> String.intercalate "/") ++ ".lean"

/-- The stratum of a module, or `none` when no prefix matches (globs in the map are skipped here;
the shell gate owns those, and a miss only makes this linter quieter, never wrong). -/
def stratumOf (rows : Array (String × Nat)) (m : Name) : Option Nat := Id.run do
  let path := modulePath m
  for (pfx, lvl) in rows do
    if !pfx.contains '*' && path.startsWith pfx then return some lvl
  return none

/-- Not `@[env_linter]`: `getChecks` reads the attribute extension of the *imported* environment
(`SP1Clean` + Batteries), which by construction never contains a linter declared in this driver. It
is appended to the run set in `main` instead. Registering it by attribute silently does nothing --
the lint run reports "passed" while never calling this at all. -/
def placementLinter : Batteries.Tactic.Lint.Linter where
  noErrorsFound := "No declaration sits above its statement vocabulary."
  errorsFound := "DECLARATIONS ABOVE THEIR STATEMENT VOCABULARY (docs/layering.md law 2). \
Each could be stated in a lower stratum, so a legitimate consumer below cannot reach it. Move it \
down, or record why it must stay in scripts/layering_allowlist.txt."
  test := fun declName => do
    if declName.isInternal || isPrivateName declName then return none
    let env ← getEnv
    let some ci := env.find? declName | return none
    let some myIdx := env.const2ModIdx[declName]? | return none
    let rows ← loadStrata
    let some myLevel := stratumOf rows env.header.moduleNames[myIdx]! | return none
    let mut best : Nat := 0
    let mut witness : Name := .anonymous
    for c in ci.type.getUsedConstants do
      if let some i := env.const2ModIdx[c]? then
        if let some l := stratumOf rows env.header.moduleNames[i]! then
          if l > best then best := l; witness := c
    if witness == .anonymous || best >= myLevel then return none
    return some m!"is at stratum {myLevel} but its type only reaches stratum {best} \
(highest: {witness})"

/-- The curated environment-linter set (short names, as registered by `@[env_linter]`). The
doc-coverage linters (`docBlame`, `docBlameThm`, `tacticDocs`) are intentionally omitted — they would
swamp a proofs project — see AGENTS.md § Linters. `structureInType` and `deprecatedNoSince` (both
Mathlib `@[env_linter]`s, reached via the transitive Mathlib import) ARE included: low-noise hygiene
checks for structures that should be `Prop` and `@[deprecated]` attributes missing a `since` date.

`unusedArguments` is also intentionally omitted: it flags only the project's *uniform* signature args
(`{p} [Fact p.Prime] [Fact (2^17 < p)]` / `NeZero p` instance binders, and the `ProverData`/`ProverHint`
args every chip `Spec`/`Assumptions`/`ProverAssumptions` carries by interface) — all structurally
required, none a real defect — and it grows a fresh false-positive per new chip, so even nolinting it
would be a permanent tax. Re-run it ad hoc (`getChecks` + this set + `unusedArguments`) if hunting
genuinely-dead args. -/
def curatedLinters : List Name :=
  [`dupNamespace, `defLemma, `unusedHavesSuffices,
   `checkUnivs, `checkType, `synTaut, `impossibleInstance, `nonClassInstance,
   `simpNF, `simpVarHead, `simpComm,
   `structureInType, `deprecatedNoSince]

/-- The list of `nolints` pulled from the `nolints.json` file (linter short-name × declaration). -/
abbrev NoLints := Array (Name × Name)

/-- Read the given file path and deserialize it as JSON. -/
def readJsonFile (α) [FromJson α] (path : FilePath) : IO α := do
  let _ : MonadExceptOf String IO := ⟨throw ∘ IO.userError, fun x _ => x⟩
  liftExcept <| fromJson? <|← liftExcept <| Json.parse <|← IO.FS.readFile path

/-- Serialize the given value `a : α` to the file as JSON. -/
def writeJsonFile [ToJson α] (path : FilePath) (a : α) : IO Unit :=
  IO.FS.writeFile path <| toJson a |>.pretty.push '\n'

/-- Hand-written declarations of this project only: everything under `SP1Clean.*` (minus the
auto-gen `SP1Clean.Extracted.*` and `*Vectors` batteries) plus the two upstream-destined libraries
`ToClean.*` / `ToMathlib.*`, which are hand-written and get no linter relaxation. Mirrors
`Batteries.Tactic.Lint.getDeclsInPackage`, but filters on the full module path instead of just the
namespace root. -/
def getHandwrittenDecls : CoreM (Array Name) := do
  let env ← getEnv
  -- `Extracted/` is dropped as auto-generated, but two of its modules are hand-written and say so
  -- in their own docstrings: `ExtractionDSL` (the vocabulary the constraint-compiler backend
  -- targets) and `InteractionModel` (its projection to `LookupAccess`). They live there because
  -- that is the stratum their vocabulary puts them at — see `docs/layering.md` — not because a
  -- script emitted them, so they get the same linting as any other hand-written file.
  let handWrittenExtracted : List Name :=
    [`SP1Clean.Extracted.ExtractionDSL, `SP1Clean.Extracted.InteractionModel]
  let keep := env.header.moduleNames.map fun m =>
    ((`SP1Clean).isPrefixOf m || (`ToClean).isPrefixOf m || (`ToMathlib).isPrefixOf m)
      && (!(`SP1Clean.Extracted).isPrefixOf m || handWrittenExtracted.contains m)
      && !m.toString.endsWith "Vectors"
  return env.constants.map₁.fold (init := #[]) fun decls declName _ =>
    if keep[env.const2ModIdx[declName]?.get! (α := Nat)]! then decls.push declName else decls

/--
Usage: `sp1Lint [--update] [--placement] [-v | --trace]`

`--placement` additionally runs the placement linter (`docs/layering.md` law 2). It is **advisory and
opt-in, not part of the `lake lint` gate**, and the reason is a measurement rather than a preference:
on the 2026-08 tree it reports 2392 declarations across 284 files whose types could be stated in a
lower stratum. That is a real standing hoist backlog — whole files in `Soundness/` are pure Mathlib,
and `Composition/PreprocessedProviders.lean` alone accounts for 33 — but it is not a defect list, and
ratcheting it would mean a 2392-entry `nolints.json` that buries the 20 genuine entries and makes
`lake lint` useless as a review artifact. Run it deliberately when hunting hoist candidates.

Runs the curated environment linters on the hand-written `SP1Clean.*` declarations (excluding the
auto-generated `Extracted/` modules and `*Vectors` batteries). The project must already be built
(`lake build SP1Clean`) — the env linters read the oleans.

If `--update` is set, `scripts/nolints.json` is overwritten with the current violation set (the standard
ratchet: accept the current state, then fail on any *new* violation). Otherwise, exits 1 if any violation
remains after subtracting `nolints.json`.
-/
unsafe def main (args : List String) : IO Unit := do
  let update := args.contains "--update"
  let verbose := args.contains "-v" || args.contains "--trace"
  -- Advisory, opt-in: see the `--placement` note in this file's header.
  let placement := args.contains "--placement"
  initSearchPath (← findSysroot)
  let projectModule := `SP1Clean
  let lintModule := `Batteries.Tactic.Lint
  -- The env linters need built oleans; require them rather than driving a build from here.
  for m in [projectModule, lintModule] do
    let olean ← findOLean m
    unless (← olean.pathExists) do
      IO.eprintln s!"sp1Lint: missing olean for `{m}` at:\n  {olean}\n\
        Run `lake build SP1Clean` first."
      IO.Process.exit 1
  -- The upstream-destined libraries are linted on the same terms, but they are optional: this
  -- script must run both before and after they exist on disk.
  let mut extraModules := #[]
  for m in [`ToClean, `ToMathlib] do
    if ← (← findOLean m).pathExists then extraModules := extraModules.push m
  let nolintsFile : FilePath := "scripts/nolints.json"
  let nolints ← if ← nolintsFile.pathExists then readJsonFile NoLints nolintsFile else pure #[]
  unsafe Lean.enableInitializersExecution
  let imports : Array Import :=
    (#[projectModule, lintModule] ++ extraModules).map fun m => { module := m }
  let env ← importModules imports {} (trustLevel := 1024) (loadExts := true)
  let opts : Options := if verbose then ({} : Options).setBool `trace.Batteries.Lint true else {}
  let ctx := { fileName := "", fileMap := default, options := opts }
  let state := { env }
  Prod.fst <$> (CoreM.toIO · ctx state) do
    let decls ← getHandwrittenDecls
    traceLint s!"Linting {decls.size} hand-written declarations…"
      (inIO := true) (currentModule := projectModule)
    let mut linters ← getChecks (slow := true) (runOnly := some curatedLinters) (runAlways := none)
    if placement then
      linters := linters.push
        { placementLinter with name := `placement, declName := `placementLinter }
    let results ← lintCore decls linters (inIO := true) (currentModule := projectModule)
    if update then
      traceLint s!"Updating nolints file at {nolintsFile}"
        (inIO := true) (currentModule := projectModule)
      writeJsonFile (α := NoLints) nolintsFile <|
        .qsort (lt := fun (a, b) (c, d) => a.lt c || (a == c && b.lt d)) <|
        .flatten <| results.map fun (linter, decls) =>
          decls.fold (fun res decl _ => res.push (linter.name, decl)) #[]
    let results := results.map fun (linter, decls) =>
      .mk linter <| nolints.foldl (init := decls) fun decls (linter', decl') =>
        if linter.name == linter' then decls.erase decl' else decls
    let failed := results.any (!·.2.isEmpty)
    if failed then
      let fmt ← formatLinterResults results decls (groupByFilename := true) (useErrorFormat := true)
        "in SP1Clean (hand-written)" (runSlowLinters := true) .medium linters.size
      IO.print (← fmt.toString)
      IO.Process.exit 1
    else
      IO.println "-- sp1Lint: linting passed."
  IO.Process.exit 0
