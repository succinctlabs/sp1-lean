import SP1CleanTest.Core.HostChecks
import Clean.Circuit.WitnessExport
import SP1Clean.Proofs.Operations.HintQueuePrepend
import SP1Clean.Proofs.Operations.HintNodeAllocateLedger

/-! # Native allocation after pops and across identity carries

Run the actual witness program, local assertions, and Byte requests. Cursor replay is checked
separately against the persistent-store compiler. These tests deliberately retain the distinction
between a checked header and authenticated bytes; host-call and byte-source integration is open.
-/

namespace SP1CleanTest.Core.HintNodeAllocate

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core HostChecks

private abbrev Fp := ZMod SP1Prime

private def checked (input : SP1Clean.HintNodeAllocate.Inputs Fp)
    (corrupt : Option ℕ := none) : Bool × Ledger :=
  evaluateProgram (do
    let _ ← SP1Clean.HintNodeAllocate.main (varFromOffset SP1Clean.HintNodeAllocate.Inputs 0)
    pure ()) (toElements input).toList corrupt

private def evaluatedOutput (input : SP1Clean.HintNodeAllocate.Inputs Fp) : HostHintQueue.State Fp :=
  let program := SP1Clean.HintNodeAllocate.main (varFromOffset SP1Clean.HintNodeAllocate.Inputs 0)
  let env := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  Eval.eval env (program.output (size SP1Clean.HintNodeAllocate.Inputs))

/-- Carries cross both limb boundaries, while the last available identity is still usable. -/
theorem carryBoundaries : [0, 65535, 2 ^ 32 - 1, 2 ^ 48 - 2].all (fun allocated =>
    [0, allocated].all fun head =>
      let input := SP1Clean.HintNodeAllocate.populate (HostHintQueue.State.encode 265 head allocated) [7, 8]
      let result := checked input
      let output := evaluatedOutput input
      result.1 && Address.toNat output.head == allocated + 1 &&
        Address.toNat output.allocated == allocated + 1 &&
        Semantics.clkNat output.clk_high output.clk_low == 265 &&
        Address.toNat input.node.tail == head && result.2.length == 3 &&
        result.2.all (fun item => item.1 == "SP1Byte" && item.2.2 == -1)) = true := by native_decide

/-- Empty or shortened queues retain their full allocation frontier; head-plus-one can reuse a node. -/
theorem historicalIdentityReuse : [0, 1].all (fun head =>
    let input := SP1Clean.HintNodeAllocate.populate (HostHintQueue.State.encode 265 head 3) [9]
    (checked input).1 && Address.toNat (evaluatedOutput input).head == 4 &&
      !(checked { input with node := { input.node with pointer := Address.ofNat (head + 1) } }).1) = true := by
  native_decide

/-- Overflow, invalid cursor bounds, wrong links, and malformed lengths fail the composed checks. -/
theorem rejectsMalformed :
    let input := SP1Clean.HintNodeAllocate.populate (HostHintQueue.State.encode 1 1 3) [9]
    [SP1Clean.HintNodeAllocate.populate (HostHintQueue.State.encode 1 0 (2 ^ 48 - 1)) [9],
     SP1Clean.HintNodeAllocate.populate (HostHintQueue.State.encode 1 4 3) [9],
     { input with previous := { input.previous with allocated := #v[65536, 0, 0] } },
     { input with node := { input.node with tail := 0 } },
     { input with node := { input.node with pointer := #v[65536, 0, 0] } },
     { input with node := { input.node with length := #v[65536, 0, 0, 0] } }].all
       (fun bad => !(checked bad).1) = true ∧
    [0, 63, 64, 127, 129, 131, 147, 148, 211].all (fun index => !(checked input (some index)).1) = true := by
  native_decide

private def prefixChecked (store : HintQueue.Store) (head : ℕ) (added : List Bytes) : Bool :=
  let rows := SP1Clean.HintNodeAllocate.compilePrepend (p := SP1Prime) 265 store head added
  let target := HintQueue.prepend store head added
  let initial := HostHintQueue.State.encode (p := SP1Prime) 265 head store.size
  rows.all (fun row => (checked row).1) && rows.length == added.length &&
    match SP1Clean.HintNodeAllocate.replayCursors initial rows with
    | none => false
    | some last => toElements last == toElements (HostHintQueue.State.encode 265 target.2 target.1.size)

/-- Hook prefixes retain their order, including empty replies and appends after prior pops. -/
theorem orderedPrefixes :
    let (store, _) := HintQueue.ofList [[1, 2, 3], [], [9]]
    [0, 1, 2, 3].all (fun head =>
      [[], [[]], [[7]], [[], [8], [9, 10]]].all (prefixChecked store head)) = true ∧
    let (store, head) := HintQueue.ofList [[1, 2, 3]]
    HintQueue.decode? (HintQueue.prepend store head [[], [8], [9, 10]]).1
      (HintQueue.prepend store head [[], [8], [9, 10]]).2 = some [[], [8], [9, 10], [1, 2, 3]] := by native_decide

/-- Wrong order, omission, duplication, and a reset frontier fail exact cursor continuity. -/
theorem cursorTampering :
    let (store, head) := HintQueue.ofList [[1]]
    let rows := SP1Clean.HintNodeAllocate.compilePrepend (p := SP1Prime) 265 store head [[7], [8], [9]]
    let initial := HostHintQueue.State.encode (p := SP1Prime) 265 head store.size
    [rows.reverse, rows.drop 1, rows ++ rows].all
      (fun bad => (SP1Clean.HintNodeAllocate.replayCursors initial bad).isNone) = true ∧
      (SP1Clean.HintNodeAllocate.replayCursors { initial with allocated := 0 } rows).isNone = true := by native_decide

/-- Identical metadata does not authenticate different bytes; the future byte provider must do that. -/
theorem headerIsNotByteAuthentication :
    let previous := HostHintQueue.State.encode (p := SP1Prime) 1 0 0
    let left := SP1Clean.HintNodeAllocate.populate previous [1, 2]
    let right := SP1Clean.HintNodeAllocate.populate previous [8, 9]
    toElements left = toElements right ∧ (checked left).1 = true ∧
      HintQueue.decode? #[⟨[1, 2], 0⟩] 1 ≠ HintQueue.decode? #[⟨[8, 9], 0⟩] 1 := by native_decide

/-- info: exportable ✓ (212 witness cells) -/
#guard_msgs in
#assert_exportable (SP1Clean.HintNodeAllocate.circuit (p := SP1Prime))

end SP1CleanTest.Core.HintNodeAllocate
