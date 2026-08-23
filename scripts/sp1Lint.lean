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
Usage: `sp1Lint [--update] [-v | --trace]`

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
    let linters ← getChecks (slow := true) (runOnly := some curatedLinters) (runAlways := none)
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
