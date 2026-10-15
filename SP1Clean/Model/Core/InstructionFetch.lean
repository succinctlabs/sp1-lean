import SP1Clean.Model.Core.SourceExecution
import SP1Clean.Model.Semantics.SailFetch

/-! # Official fetch at a checked finite execution boundary

Source validity authenticates the complete Sail configuration and all committed ROM bytes.
When an instruction executes at that boundary, its committed word is exactly the actual Sail
fetch result. No existence of a next instruction is imposed on empty or final boundaries.
-/

namespace SP1Clean.Model.Core

open LeanRV64D.Defs LeanRV64D.Functions SP1Clean.Advance

/-- The checked source fetches the committed word through official Sail, without any AIR row. -/
theorem ExecutionSourceValid.fetch_eq {image : ProgramImage} {source : ExecutionSnapshot}
    (valid : ExecutionSourceValid image source) {word : BitVec 32}
    (fetched : (image.toGuestProgram valid.1.1).fetchWord source.pc = some word) :
    (fetch ()).run source.sail.realize = .ok (FetchResult.F_Base word) source.sail.realize :=
  fetch_eq_of_romLoaded valid.configured valid.romLoaded valid.pc fetched

end SP1Clean.Model.Core
