import SP1Clean.FormalModel.Shard
import SP1Clean.Model.Core.ExecutionFrame
import SP1Clean.Model.Core.ExecutionMemory

/-! # ROM preservation and official fetch for the shard's semantic domain

These are consequences of the existing `Executes` contract. Source validation and mandatory
ordinary write permission supply every premise of the mixed-path induction. No resource profile,
AIR witness or extra intermediate-state invariant is required. The final boundary may lie outside
ROM, and an empty identity, including a stopped one, needs no fetch.
-/

namespace SP1Clean.FormalModel.Shard.Executes
open Model.Core Machine Soundness.Target LeanRV64D.Defs LeanRV64D.Functions

variable {characteristic : ℕ} {image : ProgramImage}
  {source target : ExecutionSnapshot} {events : List ExecutionEvent}

/-- The exact outgoing Sail state retains configuration, ROM and every protected incoming byte. -/
theorem frame (execution : Executes characteristic image source target events) :
    SailConfigured target.sail.realize ∧ RomLoaded (image.toGuestProgram execution.1.1.1) target.sail.realize ∧
      ∀ address, image.readOnly address = true →
        target.sail.realize.mem.get? address = source.sail.realize.mem.get? address :=
  execution.2.1.frame execution.1.1.1 execution.2.2 (fun _ selected => selected)
    execution.1.configured execution.1.romLoaded

/-- All actual prefix states, including the final and held endpoint, inherit authenticated ROM. -/
theorem frame_prefix (execution : Executes characteristic image source target events)
    {cut : ℕ} {current : ExecutionState}
    (replay : executionTrajectory (policy characteristic image) (image.toGuestProgram execution.1.1.1)
      source.realize events cut = some current) :
    SailConfigured current.sail ∧ RomLoaded (image.toGuestProgram execution.1.1.1) current.sail ∧
      ∀ address, image.readOnly address = true →
        current.sail.mem.get? address = source.sail.realize.mem.get? address :=
  execution.2.1.frame_prefix execution.1.1.1 execution.2.2 (fun _ selected => selected)
    execution.1.configured execution.1.romLoaded replay

/-- Every actual prefix has all bytes needed to materialize native RAM cells. This is derived
from complete incoming memory and actual writes, independently of final AIR grounding. -/
theorem memory_present_prefix (execution : Executes characteristic image source target events)
    {cut : ℕ} {current : ExecutionState}
    (replay : executionTrajectory (policy characteristic image) (image.toGuestProgram execution.1.1.1)
      source.realize events cut = some current)
    (address : ℕ) (inside : address < NativeLayout.sailMemory.upper) :
    (current.sail.mem.get? address).isSome :=
  execution.2.1.memory_present_prefix execution.1.1.1 execution.2.2 (fun _ selected => selected)
    execution.1.configured execution.1.romLoaded replay address inside

/-- Each executed position fetches its committed instruction through official Sail. The prefix
state and instruction are derived from the path, rather than supplied by a caller. -/
theorem fetch_at (execution : Executes characteristic image source target events)
    (cut : ℕ) (active : cut < events.length) :
    ∃ current pc word,
      executionTrajectory (policy characteristic image) (image.toGuestProgram execution.1.1.1)
        source.realize events cut = some current ∧
      current.sail.regs.get? Register.PC = some pc ∧ (image.toGuestProgram execution.1.1.1).fetchWord pc = some word ∧
      (fetch ()).run current.sail = .ok (FetchResult.F_Base word) current.sail :=
  execution.2.1.fetch_at execution.1.1.1 execution.2.2 (fun _ selected => selected)
    execution.1.configured execution.1.romLoaded cut active

end SP1Clean.FormalModel.Shard.Executes
