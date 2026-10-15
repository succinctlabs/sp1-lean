import SP1CleanTest.Alignment.Audit.BranchCompilerRoundTrip

/-! Run after building `SP1CleanTest.Alignment.Audit.BranchCompilerRoundTrip`:
`lake env lean scripts/branchCompilerExample.lean`.
This computes the compiler result and its actual Clean row. Full official Sail retirement is
proved by the imported `joined` theorem; the driver does not execute the noncomputable Sail model.
-/

open Lean Circuit SP1Clean SP1Clean.Soundness SP1Clean.Soundness.Target
open SP1Clean.Audit.BranchCompilerRoundTrip

/-- Compute and check the compiler event and generated local row, then print their actual values. -/
private def runBranchCompilerExample : IO Unit := do
  let rowNext := (sndPcOf (stateAccess rowView)).toNat
  let real := (BranchChip.component.rowInput env).is_real.val
  let constraints := FlatOperation.constraints (BranchChip.component (p := SP1Prime)).operations.toFlat
  let summary := Json.mkObj [
    ("scope", toJson "one local Branch chip table; no assembled channel balance"),
    ("theorem", toJson "SP1Clean.Audit.BranchCompilerRoundTrip.joined"),
    ("sailEvidence", toJson "full official try_step and normal ExecutionStep proved in Lean; not executed by this driver"),
    ("instructionWord", toJson view.word.toNat),
    ("compiled", toJson compiled?.isSome),
    ("event", Json.mkObj [
      ("pc", toJson event.pc), ("clock", toJson event.clk), ("opcode", toJson event.opcode),
      ("rs1", toJson event.opA), ("rs2", toJson event.opB),
      ("rs1Value", toJson event.prevA), ("rs2Value", toJson event.b),
      ("immediate", toJson event.imm), ("taken", toJson event.branchTaken),
      ("nextPc", toJson event.branchNextPc),
      ("previousRs1Clock", toJson event.prevTsA), ("previousRs2Clock", toJson event.prevTsB)]),
    ("rowCount", toJson table.table.length), ("rowWidth", toJson row.size),
    ("rowIsReal", toJson real), ("rowNextPc", toJson rowNext),
    ("constraintCount", toJson constraints.length), ("flatConstraintCheck", toJson flatCheck)]
  IO.println summary.pretty
  unless compiled?.isSome && event.branchTaken && event.imm == 4092 &&
      event.branchNextPc == 69628 && rowNext == 69628 && real == 1 &&
      table.table.length == 1 && flatCheck do
    throw (IO.userError "branch compiler/circuit regression failed")

#eval runBranchCompilerExample
