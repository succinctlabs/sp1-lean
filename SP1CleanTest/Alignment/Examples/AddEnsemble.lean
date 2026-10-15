import SP1CleanTest.Alignment.Support.HostFinalMemoryFixture
import Lean.Data.Json

/-! # Executable ADD and rejection walkthrough

Run through `python3 scripts/check_examples.py add`. JSON is deterministic fixture evidence from the
actual AIR interpreter; it is not a proof certificate or a full execution-equivalence claim.
-/

namespace SP1CleanTest.Alignment.Examples.AddEnsemble

open Lean SP1Clean
open SP1CleanTest.Alignment.Core.HostFinalMemory.Fixture

private def event := Audit.OneAddNativePremises.event

private def sourcePc : Nat :=
  header.init_pc0.val + 65536 * header.init_pc1.val + 4294967296 * header.init_pc2.val

private def targetPc : Nat :=
  header.final_pc0.val + 65536 * header.final_pc1.val + 4294967296 * header.final_pc2.val

private def targetClock : Nat :=
  header.final_clk_0_16.val + 65536 * header.final_clk_16_24.val +
    16777216 * header.final_clk_24_32.val + 4294967296 * header.final_clk_32_48.val

private def instruction : String := s!"ADD x{event.opA},x{event.opB},x{event.opC}"

private def registerJson (index : Nat) (value : BitVec 64) : Json :=
  Json.mkObj [("index", toJson index), ("value", toJson value.toNat)]

private def inputJson : Json := Json.mkObj [
  ("instruction", toJson instruction),
  ("source", Json.mkObj [
    ("pc", toJson sourcePc), ("clock", toJson source.clock),
    ("registers", toJson [registerJson event.opB (source.sail.memorySnapshot.registers.get ⟨event.opB % 32, Nat.mod_lt _ (by decide)⟩),
      registerJson event.opC (source.sail.memorySnapshot.registers.get ⟨event.opC % 32, Nat.mod_lt _ (by decide)⟩)])]),
  ("target", Json.mkObj [
    ("pc", toJson targetPc), ("clock", toJson targetClock),
    ("registers", toJson [registerJson event.opA (target.registers.get ⟨event.opA % 32, Nat.mod_lt _ (by decide)⟩)])])]

/-- Compare independently declared expectations with the actual interpreter results. -/
def allMatch (cases : List (String × Bool × Bool)) : Bool :=
  cases.all fun (_, expected, actual) => expected == actual

private def resultJson (result : String × Bool × Bool) : Json :=
  Json.mkObj [("id", toJson result.1), ("expected", toJson result.2.1), ("actual", toJson result.2.2)]

private def reportJson (revision : String) (dirty : Bool) (cases : List (String × Bool × Bool)) : Json :=
  Json.mkObj [("evidence", toJson "executable fixture checks; not proof certificates"),
    ("revision", toJson revision), ("dirty", toJson dirty),
    ("assembly", toJson "SP1Clean.Soundness.HostFinalMemory.ensemble"),
    ("table_count", toJson (assembly target).tables.length), ("input", inputJson),
    ("cases", toJson (cases.map resultJson))]

private def outcome (accepted : Bool) : String := if accepted then "accepted" else "rejected"

/-- Internal entry point; the shell runner supplies checked revision/working-tree metadata.
The final flag is used only by the runner regression to verify a real mismatch exits nonzero. -/
def main (args : List String) : IO UInt32 := do
  let (json, revision, dirty, invert) ← match args with
    | [mode, revision, status] | [mode, revision, status, "--invert-first-expectation"] => do
      unless (mode == "--json" || mode == "--text") && (status == "clean" || status == "dirty") do
        IO.eprintln "invalid mode or working-tree status"
        return 2
      pure (mode == "--json", revision, status == "dirty", args.length == 4)
    | _ =>
      IO.eprintln "Use python3 scripts/check_examples.py add [--json]"
      return 2
  let cases := if invert then results.modify 0 (fun (id, expected, actual) => (id, !expected, actual)) else results
  if json then
    IO.println (reportJson revision dirty cases).compress
  else
    IO.println "Executable fixture evidence (not proof certificates)"
    IO.println s!"Revision: {revision}{if dirty then " (dirty working tree)" else " (clean)"}"
    IO.println s!"Assembly: SP1Clean.Soundness.HostFinalMemory.ensemble ({(assembly target).tables.length} tables)"
    IO.println s!"{instruction}: x{event.opB}={event.b}, x{event.opC}={event.c}, x{event.opA}={event.a}"
    IO.println s!"PC {sourcePc} -> {targetPc}; clock {source.clock} -> {targetClock}"
    for (id, expected, actual) in cases do
      IO.println s!"{if expected == actual then "PASS" else "FAIL"} {id}: expected {outcome expected}, actual {outcome actual}"
  if allMatch cases then return 0 else
    IO.eprintln "Fixture expectation mismatch."
    return 1

end SP1CleanTest.Alignment.Examples.AddEnsemble
