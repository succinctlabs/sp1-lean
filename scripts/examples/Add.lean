import SP1CleanTest.Alignment.Examples.AddEnsemble

/-! # Interpreted driver for the test-layer walkthrough

The generated Sail model already owns root `main`, so this follows the existing witness
exporter's `#eval` entry pattern. The shell runner validates the complete JSON output as well
as the process status, because `lean` can exit zero after a stack overflow.
-/

#eval show IO Unit from do
  let revision ← IO.getEnv "SP1_EXAMPLE_REVISION"
  let status ← IO.getEnv "SP1_EXAMPLE_STATUS"
  let invert ← IO.getEnv "SP1_TALK_INVERT_EXPECTATION"
  let args := ["--json", revision.getD "unknown", status.getD "dirty"] ++
    (if invert == some "1" then ["--invert-first-expectation"] else [])
  let code ← SP1CleanTest.Alignment.Examples.AddEnsemble.main args
  if code != 0 then
    throw (IO.userError (if code == 1 then "Fixture expectation mismatch."
      else "Invalid fixture driver invocation."))
