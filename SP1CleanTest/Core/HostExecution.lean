import SP1Clean.Model.Core.HostSail
import SP1Clean.Model.Core.HostReplay
import SP1Clean.Model.SP1Field

/-! # Stateful native host execution regressions

Exercise the public dispatcher and actual Sail memory/register adapter. These are executable
semantic regressions, not Rust trace conformance or evidence that the host effects are AIR-bound.
-/

namespace SP1CleanTest.Core.HostExecution

open SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target LeanRV64D LeanRV64D.Defs

private def policy : HostPolicy := ⟨⟨fun _ => false, NativeLayout.guestMemory⟩, SP1Prime⟩

private def context (code arg1 arg2 : BitVec 64) (length : Option (BitVec 64) := none)
    (memory : List (ℕ × BitVec 8) := []) : HostReadContext where
  register := fun index =>
    if index = 5 then some code else if index = 10 then some arg1 else
    if index = 11 then some arg2 else if index = 12 then length else none
  byte := fun address => (memory.find? (·.1 == address)).map Prod.snd

private def buffer : List (ℕ × BitVec 8) :=
  (List.range 64).map fun index => (65536 + index, BitVec.ofNat 8 index)

private def run (host : HostState) (kind : SyscallKind) (arg1 arg2 : BitVec 64)
    (length : Option (BitVec 64) := none) : Option SP1Clean.Model.Core.HostExecution :=
  host.run policy (context kind.code arg1 arg2 length buffer)

/-- All eight selected calls succeed on concrete legal observations. -/
theorem allCalls :
    (run {} .halt 0 0).isSome = true ∧
    (run {} .write 13 65537 (some 3)).isSome = true ∧
    (run {} .enterUnconstrained 0 0).map (·.result) = some 0 ∧
    (run {} .commit 7 0xffffffff).isSome = true ∧
    (run {} .commitDeferred 7 42).isSome = true ∧
    (run {} .verifyProof 65536 65568).isSome = true ∧
    (run { io.hints := [[7, 8]] } .hintLength 0 0).map (·.result) = some 2 ∧
    (run { io.hints := [[7, 8]] } .hintRead 65536 2).isSome = true := by native_decide

/-- WRITE obtains its unaligned slice from memory and x12, and rejects missing observations. -/
theorem observedWrite :
    (run {} .write 13 65537 (some 3)).map (·.effect.state.io.publicOutput) = some [1, 2, 3] ∧
    run {} .write 13 65537 = none ∧
    ({} : HostState).run policy (context 2 13 65537 (some 2) [(65537, 1)]) = none ∧
    run {} .write 13 (2 ^ 48 - 1) (some 2) = none ∧
    ({} : HostState).run policy (context 0x100000002 13 65537 (some 3) buffer) = none := by
  native_decide

/-- Standard streams use the full descriptor; other cases use its low-u32 view. -/
theorem descriptorDispatch :
    (run {} .write 1 65537 (some 2)).map (·.effect.state.stdout) = some [1, 2] ∧
    (run {} .write 2 65537 (some 2)).map (·.effect.state.stderr) = some [1, 2] ∧
    (run {} .write 0x100000001 65537 (some 2)).map (·.effect.state) = some {} ∧
    (run {} .write 0x10000000d 65537 (some 2)).map (·.effect.state.io.publicOutput) = some [1, 2] ∧
    (run { io.hints := [[9]] } .write 14 65537 (some 2)).map (·.effect.state.io.hints) =
      some [[1, 2], [9]] := by native_decide

private def hookHost : HostState :=
  { io := ⟨[[9]], [42]⟩, replies := [⟨⟨15, [1, 2]⟩, [[3], [4]]⟩] }

/-- Replies bind both descriptor and observed bytes, are consumed once, and preserve queue order. -/
theorem hookReplies :
    (run hookHost .write 15 65537 (some 2)).map (·.effect.state) =
      some { io := ⟨[[3], [4], [9]], [42]⟩, requests := [.hook ⟨15, [1, 2]⟩] } ∧
    run hookHost .write 16 65537 (some 2) = none ∧
    run hookHost .write 15 65538 (some 2) = none ∧
    run {} .write 15 65537 (some 2) = none := by native_decide

/-- Both banks update mutable slots. Distinct overwrites require separate exact-AIR refinement. -/
theorem commitmentUpdates :
    ((run {} .commit 3 7).bind fun first => run first.effect.state .commit 3 8).map
      (fun last => (last.effect.state.committed[3], last.effect.state.committed[2])) = some (8, 0) ∧
    (run {} .commitDeferred 3 9).map (fun last => last.effect.state.deferred[3]) = some 9 ∧
    run {} .commit 8 7 = none ∧
    run {} .commit 0 0x100000000 = none ∧
    run {} .commitDeferred 0 (BitVec.ofNat 64 SP1Prime) = none := by native_decide

/-- Verification requests record both actual 32-byte inputs without asserting proof acceptance. -/
theorem proofObservations :
    (run {} .verifyProof 65536 65568).map (·.effect.state.requests) =
      some [.proof ⟨(List.range 32).map (BitVec.ofNat 8),
        (List.range 32).map (fun index => BitVec.ofNat 8 (32 + index))⟩] ∧
    (run {} .verifyProof 65536 65568).map (·.effect.write) = some none ∧
    run {} .verifyProof 65536 65569 = none := by native_decide

/-- Every subsequent call is rejected after HALT; exit values use the canonical field range. -/
theorem terminality :
    (run {} .halt 70000 0).map (·.effect.state.exitCode) = some (some 70000) ∧
    run {} .halt (BitVec.ofNat 64 SP1Prime) 0 = none ∧
    run {} .halt 0x100000000 0 = none ∧
    SyscallKind.all.all (fun kind => (run { exitCode := some 0 } kind 0 0).isNone) = true ∧
    (run {} .hintLength 0 0).map (·.result) = some (BitVec.allOnes 64) := by native_decide

private def hintBytes (length : ℕ) : Bytes :=
  (List.range length).map (fun index => BitVec.ofNat 8 (index + 1))

private def hintMemory (length : ℕ) : Bool :=
  match run { io.hints := [hintBytes length, [99]] } .hintRead 65536 (BitVec.ofNat 64 length) with
  | none => false
  | some execution =>
    let old := (∅ : Std.ExtHashMap ℕ (BitVec 8)).insertMany
      ((List.range 32).map fun offset => (65535 + offset, 77))
    let memory := execution.effect.applyMemory old
    execution.effect.state.io.hints == [[99]] &&
      (List.range length).all (fun index => memory.get? (65536 + index) ==
        some (BitVec.ofNat 8 (index + 1))) &&
      (List.range (8 - length % 8)).all (fun index =>
        memory.get? (65536 + length + index) == some 0) &&
      memory.get? 65535 == some 77 &&
      memory.get? (65536 + 8 * (length / 8 + 1)) == some 77

/-- Actual Sail memory application includes padding and preserves adjacent cells. -/
theorem paddedHintMemory : [0, 7, 8, 9].all hintMemory = true ∧
    ({ io.hints := [[]] } : HostState).run
      { policy with memory.readOnly := fun address => address == 65543 }
      (context 241 65536 0) = none ∧
    run { io.hints := [[1]] } .hintRead 65537 1 = none ∧
    run { io.hints := [[1]] } .hintRead 65536 2 = none := by native_decide

private def sailSource : SailState :=
  let regs := (default : SailState).regs.insert Register.PC 65536
  let regs := (regs.insert Register.x5 241).insert Register.x10 65552
  let regs := (regs.insert Register.x11 2).insert Register.x12 88
  { (default : SailState) with
    regs
    mem := (∅ : Std.ExtHashMap ℕ (BitVec 8)).insertMany
      [(65536, 0x73), (65537, 0), (65538, 0), (65539, 0),
        (65551, 77), (65552, 99), (65560, 66)] }

private def sailApplication : Bool :=
  match ({ io.hints := [[7, 8]] } : HostState).run policy (.ofSail sailSource) with
  | none => false
  | some execution =>
    let target := execution.apply sailSource 65536
    target.regs.get? Register.PC == some 65540 && target.get_reg? 5 == some 241 &&
      target.get_reg? 10 == some 65552 && target.get_reg? 11 == some 2 &&
      target.get_reg? 12 == some 88 && target.mem.get? 65551 == some 77 &&
      target.mem.get? 65552 == some 7 && target.mem.get? 65553 == some 8 &&
      target.mem.get? 65559 == some 0 && target.mem.get? 65560 == some 66

/-- The adapter observes the actual source registers and applies the emitted memory update. -/
theorem sailAdapter : sailApplication = true := by native_decide

/-- Actual Sail application reaches the last native byte without creating a one-past entry.
An already-present out-of-window key is framed, while an extra padding word is rejected. -/
theorem nativeMemoryCeiling : [0, 7, 8, 9].all (fun length =>
    [false, true].all fun present =>
      let address := 2 ^ 48 - 8 * (length / 8 + 1)
      let initial := { sailSource with
        regs := (sailSource.regs.insert .x10 (BitVec.ofNat 64 address)).insert .x11 (BitVec.ofNat 64 length)
        mem := if present then (∅ : Std.ExtHashMap ℕ (BitVec 8)).insert (2 ^ 48) 93 else ∅ }
      match ({ io.hints := [hintBytes length] } : HostState).run policy (.ofSail initial) with
      | none => false
      | some execution =>
        let target := execution.apply initial 65536
        target.mem.get? (2 ^ 48 - 1) == some 0 &&
          target.mem.get? (2 ^ 48) == initial.mem.get? (2 ^ 48) &&
          target.mem.get? (2 ^ 48 + 1) == none) = true ∧
    run { io.hints := [hintBytes 8] } .hintRead (2 ^ 48 - 8) 8 = none := by native_decide

private def ecallProgram : GuestProgram where
  rom := [(65536, 0x73)]
  pc_start := 65536
  memImage := []
  rom_nodup := by simp
  rom_aligned := by simp
  rom_in_window := by simp
  rom_full_width := by simp

private def committedStep : Bool :=
  match ({ io.hints := [[7, 8]] } : HostState).step policy ecallProgram 8 sailSource with
  | none => false
  | some (host, target, event) =>
    host.io.hints.isEmpty && target.mem.get? 65552 == some 7 &&
      event.rawCode == 241 && event.arg1 == 65552 && event.arg2 == 2 &&
      event.result == 241 && event.clock == 8 && event.pc == 65536 && event.nextPc == 65540

/-- A host step requires the committed ECALL at the actual PC and produces its own event. -/
theorem committedDispatch : committedStep = true ∧
    (({} : HostState).step policy ecallProgram 8
      { sailSource with regs := sailSource.regs.insert Register.PC 65540 }).isNone = true := by
  native_decide

private def ioSequence : Option (HostState × Option (BitVec 8) × Option (BitVec 8)) := do
  let written ← run {} .write 14 65537 (some 2)
  let length ← run written.effect.state .hintLength 0 0
  let read ← run length.effect.state .hintRead 65552 length.result
  let memory := read.effect.applyMemory ((∅ : Std.ExtHashMap ℕ (BitVec 8)).insertMany buffer)
  let output ← read.effect.state.run policy
    { (context 2 13 65552 (some 2)) with byte := memory.get? }
  let halted ← run output.effect.state .halt 0 0
  some (halted.effect.state, memory.get? 65552, memory.get? 65559)

/-- Successive calls share queue state, written RAM, public output, and the terminal result. -/
theorem statefulSequence : ioSequence =
    some ({ io.publicOutput := [1, 2], exitCode := some 0 }, some 1, some 0) := by native_decide

private def continuationSource : HostState :=
  { io := ⟨[[1, 2], [3]], [41, 42]⟩
    committed := #v[10, 20, 30, 40, 50, 60, 70, 80]
    deferred := #v[101, 102, 103, 104, 105, 106, 107, 108]
    requests := [.hook ⟨15, [7]⟩, .proof ⟨[8], [9]⟩]
    replies := [⟨⟨16, [5]⟩, [[6]]⟩]
    stdout := [11, 12]
    stderr := [13] }

private def continuationTarget : HostState :=
  { continuationSource with
    io.hints := [[3]]
    committed := continuationSource.committed.set 7 99
    deferred := continuationSource.deferred.set 0 123 }

private def continuationRun : Option HostState :=
  ([(SyscallKind.enterUnconstrained, 0, 0), (.hintLength, 0, 0), (.hintRead, 65536, 2),
    (.commit, 7, 88), (.commitDeferred, 0, 123), (.commit, 7, 99)] :
      List (SyscallKind × BitVec 64 × BitVec 64)).foldlM
    (fun host call => (run host call.1 call.2.1 call.2.2).map (·.effect.state)) continuationSource

/-- Complete host equality preserves all pre-existing I/O, requests and replies through reads,
control calls and both banks. Continuing, HALT-zero, and an already stopped identity are distinct. -/
theorem completeHostContinuation :
    continuationRun = some continuationTarget ∧
    (continuationRun.bind fun host => run host .halt 0 0).map (·.effect.state) =
      some { continuationTarget with exitCode := some 0 } ∧
    run { continuationTarget with exitCode := some 0 } .enterUnconstrained 0 0 = none ∧
    ([] : List SP1Clean.Machine.ExecutionEvent).foldl hostExitAfter (some 17) = some 17 ∧
    ({} : HostState).exitCode ≠ ({ exitCode := some 0 } : HostState).exitCode := by
  native_decide

end SP1CleanTest.Core.HostExecution
