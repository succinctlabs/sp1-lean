import Lean
import SP1Clean.Soundness.Shard.Machine

/-! # Compiled native capstone contract audit

The examples pin the currently conditional target types, independently spelling out the raw
acceptance and complete-state interpretation. They do not instantiate the missing targets.
The command writes a dependency manifest to `CAPSTONE_SURFACE_OUT`: declaration types and
definition bodies are followed, but theorem proof bodies are not. External declarations form
the boundary supplied by the immutable dependency pins. Structural fingerprints detect drift;
they are not cryptographic commitments or a substitute for reviewing the definitions.

Run through `scripts/check_capstone_contract.py`, which builds the dependency first, checks
completion and diagnostics, and diffs the manifest. No main-library declaration is introduced.
-/

open SP1Clean SP1Clean.Model.Core SP1Clean.Machine SP1Clean.FormalModel.Shard
  SP1Clean.Soundness.Shard Air.Flat

section Contract

variable {p : ℕ} [Fact p.Prime]
variable {PublicIO : TypeMap} [ProvableType PublicIO]
variable (ensemble : Ensemble (ZMod p) PublicIO) (limits : ResourceLimits)
  (image : ProgramImage) (source target : ExecutionSnapshot) (header : PublicIO (ZMod p))

example : ensemble.Statement header ↔
    ∃ witness : EnsembleWitness ensemble,
      witness.publicInput = header ∧ witness.Constraints ∧ witness.BalancedChannels := Iff.rfl

example : SoundnessTarget ensemble limits image source target header =
    (∀ publicInput, True → ensemble.Statement publicInput →
      ∃ events, publicInput = header ∧
        (∃ valid : ExecutionSourceValid image source,
          ExecutionPath (policy p image) (image.toGuestProgram valid.1.1)
            source.realize events target.realize ∧
          ExecutionPath.WritesPermitted (policy p image) (image.toGuestProgram valid.1.1)
            source.realize events) ∧ nativeProfile limits p image source target events) := rfl

example : CompilerTarget ensemble limits image source target header =
    EnsembleCompiler ensemble (List ExecutionEvent)
      (fun publicInput events => publicInput = header ∧
        (∃ valid : ExecutionSourceValid image source,
          ExecutionPath (policy p image) (image.toGuestProgram valid.1.1)
            source.realize events target.realize ∧
          ExecutionPath.WritesPermitted (policy p image) (image.toGuestProgram valid.1.1)
            source.realize events) ∧ nativeProfile limits p image source target events) := rfl

example (sound : SoundnessTarget ensemble limits image source target header)
    (compiler : CompilerTarget ensemble limits image source target header) :
    ensemble.Statement header ↔ ∃ events, AdmissibleExecution limits p image source target events :=
  SP1Clean.Soundness.Shard.statement_iff sound compiler

end Contract

namespace CapstoneContractAudit

open Lean

/-- Exact declarations whose types/definitions determine the audited target and machine view. -/
def roots : Array Name := #[
  ``SP1Clean.Soundness.Shard.statement_iff,
  ``SP1Clean.Soundness.Shard.SoundnessTarget,
  ``SP1Clean.Soundness.Shard.CompilerTarget,
  ``SP1Clean.FormalModel.Shard.Executes,
  ``SP1Clean.FormalModel.Shard.nativeProfile,
  ``SP1Clean.FormalModel.Shard.AdmissibleExecution,
  ``SP1Clean.FormalModel.Shard.sp1Machine,
  ``Air.Flat.Realizes]

/-- The owning module is used rather than the namespace, which is decoupled from paths. -/
def moduleOf (env : Environment) (name : Name) : Name :=
  match env.getModuleIdxFor? name with
  | some index => env.header.moduleNames[index.toNat]!
  | none => env.mainModule

/-- Traverse repository definitions; pinned upstream declarations remain explicit boundary nodes. -/
def localModule (name : Name) : Bool :=
  ["SP1Clean", "ToClean", "ToMathlib", "ToPolyFun"].any
    (fun rootName => name.toString.startsWith (rootName ++ "."))

/-- Theorem bodies are kernel-checked implementation, rather than definition dependencies. -/
def body? : ConstantInfo → Option Expr
  | .thmInfo _ => none
  | info => info.value? (allowOpaque := true)

/-- Iterative traversal retains types, constructors, instances and definition bodies. -/
def manifest (env : Environment) : Except String Json := do
  let mut pending := roots.toList
  let mut seen : NameSet := {}
  let mut entries : Array (String × Json) := #[]
  while !pending.isEmpty do
    let name := pending.head!
    pending := pending.tail!
    if seen.contains name then continue
    seen := seen.insert name
    let some info := env.find? name | throw s!"missing declaration: {name}"
    let owner := moduleOf env name
    let repository := localModule owner
    let body := body? info
    entries := entries.push (name.toString, Json.mkObj [
      ("name", toJson name.toString), ("module", toJson owner.toString),
      ("local", toJson repository), ("typeFingerprint", toJson (toString (hash info.type))),
      ("bodyFingerprint", toJson (body.map (fun value => toString (hash value))))])
    if repository then
      pending := info.type.getUsedConstants.toList ++ pending
      if let some value := body then
        pending := value.getUsedConstants.toList ++ pending
      if let .inductInfo declaration := info then
        pending := declaration.ctors ++ pending
  let sortedEntries := entries.qsort (fun left right => left.1 < right.1)
  return Json.mkObj [
    ("version", toJson (1 : Nat)),
    ("roots", toJson (roots.map Name.toString)),
    ("declarations", Json.arr (sortedEntries.map Prod.snd))]

run_cmd do
  let env ← Lean.getEnv
  let some destination ← IO.getEnv "CAPSTONE_SURFACE_OUT"
    | throwError "CAPSTONE_SURFACE_OUT is required; use scripts/check_capstone_contract.py"
  match manifest env with
  | .error message => throwError message
  | .ok result => IO.FS.writeFile destination (result.pretty ++ "\n")

end CapstoneContractAudit
