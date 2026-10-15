import SP1CleanTest.Core.HostChecks
import Clean.Circuit.WitnessExport
import SP1Clean.Proofs.Chips.HostHintLengthChip.Populate
import SP1Clean.Proofs.Chips.HostHintLengthChip.Bridge
import SP1Clean.Proofs.Chips.HostHintLengthChip.Ledger

/-! # Current-head HINT_LEN, source authentication, and instruction handoff

Evaluate the complete Clean witness programs and fixed source lookup. Joint checks balance
HostCall, node, and queue-state ledgers against explicit fixture endpoints; the instruction's
Memory/Program/State channels remain external. These are component integration regressions,
not a claim that the handler is installed in the full local-core ensemble.
-/

namespace SP1CleanTest.Core.HostHintLength

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core HostChecks

private abbrev Fp := ZMod SP1Prime

private def word (value : ℕ) : Word Fp := Soundness.Target.bitVecToWord (BitVec.ofNat 64 value)

private def host (hints : List Bytes) : HostState :=
  { io := ⟨hints, [4, 5]⟩, committed := Vector.replicate 8 17, deferred := Vector.replicate 8 19,
    stdout := [6], stderr := [7], requests := [.proof ⟨[8], [9]⟩] }

private def context : HostReadContext where
  register index := if index == 5 then some 240 else if index == 10 then some (2 ^ 64 - 1)
    else if index == 11 then some 12 else none
  byte _ := none

private def policy : HostPolicy := ⟨{ readOnly := fun _ => false }, SP1Prime⟩

private def input (hints : List Bytes) (previousClock clock : ℕ := 0) : HostHintLengthChip.Inputs Fp :=
  let (store, head) := HintQueue.ofList hints
  HostHintLengthChip.populate store head previousClock clock
    (((host hints).run policy context).getD ⟨.hintLength, 0, 0, 0, ⟨host hints, none⟩⟩)

private def evaluate (empty : Bool) (row : HostHintLengthChip.Inputs Fp)
    (corrupt : Option ℕ := none) : Bool × Ledger :=
  evaluateProgram (HostHintLengthChip.main empty (varFromOffset HostHintLengthChip.Inputs 0))
    (toElements row).toList corrupt

private def source (hints : List Bytes) (row : HintQueue.NodeRecord Fp) : Bool × Ledger :=
  evaluateProgram (HostHintQueue.sourceMain hints (varFromOffset HintQueue.NodeRecord 0))
    (toElements row).toList none [FiniteLookup.ofStatic (HintQueue.sourceTable hints)]

private def selected (names : List String) (ledger : Ledger) : Ledger :=
  ledger.filter (fun item => names.contains item.1)

private def balanced (ledger : Ledger) : Bool :=
  ledger.length < SP1Prime && ledger.all fun key =>
    ((ledger.filter (fun item => item.1 == key.1 && item.2.1 == key.2.1)).map (·.2.2)).sum == 0

private def instruction (result : Word Fp) : Bool × Ledger :=
  let row : SyscallInstrsChip.Inputs Fp :=
    { state := ⟨0, 0, 1, #v[0, 1, 0]⟩
      op_a := 5, op_a_memory := ⟨word 240, ⟨0, 4⟩⟩, op_a_0 := 0
      op_b := 10, op_b_memory := ⟨word (2 ^ 64 - 1), ⟨0, 3⟩⟩
      op_c := 11, op_c_memory := ⟨word 12, ⟨0, 2⟩⟩
      next_pc := #v[4, 1, 0], is_halt := 0, op_a_value := result
      syscall_id_bytes := U16toU8OperationSafe.populate (word 240)
      is_enter_unconstrained := IsZeroOperation.populate 237
      is_hint_len := IsZeroOperation.populate 0, is_halt_zero := IsZeroOperation.populate 240
      is_commit := IsZeroOperation.populate 224, is_commit_deferred := IsZeroOperation.populate 214
      digest_index_bits := Vector.replicate 8 0, digest_word := 0
      op_b_cmp := ⟨0⟩, op_c_cmp := ⟨1⟩, is_real := 1 }
  evaluateProgram (HostCallChip.main (varFromOffset HostCallChip.Inputs 0))
    (toElements (HostCallChip.populate row 0 0)).toList

private def endpoints (row : HostHintLengthChip.Inputs Fp) : Bool × Ledger :=
  evaluateProgram (do
    HostHintQueue.stateChannel.push (const row.previous)
    HostHintQueue.stateChannel.pull (const row.next)) []

private def joint (hints : List Bytes) : Bool :=
  let row := input hints 0 1
  let handler := evaluate hints.isEmpty row
  let origin := if hints.isEmpty then (true, []) else source hints row.node
  let cpu := instruction row.call.result
  let boundary := endpoints row
  handler.1 && origin.1 && cpu.1 && boundary.1 &&
    balanced (selected ["sp1.native.host_call", "sp1.native.hint_node", "sp1.native.hint_queue_state"]
      (handler.2 ++ origin.2 ++ cpu.2 ++ boundary.2)) &&
    selected ["SP1Memory", "SP1Exit", "SP1PublicValues"] handler.2 == []

/-- Both component routes agree with a full instruction and authenticated source node. -/
theorem jointLedgers : [[], [[]], [[1, 2, 3]], [[1, 2, 3], [], [9]]].all joint = true := by
  native_decide

/-- The complete interpreter constructs valid rows and preserves unrelated nonempty host fields. -/
theorem compiledRows : [[], [[]], [[1, 2, 3]], [[1], [2, 3]]].all (fun hints =>
    [(0, 1), (2 ^ 24 - 1, 2 ^ 24 + 1), (2 ^ 48 - 9, 2 ^ 48 - 1)].all fun (before, now) =>
      let row := input hints before now
      let checked := evaluate hints.isEmpty row
      checked.1 && (host hints).run policy context == some (HostHintLengthChip.execution row (host hints)) &&
        Word.toBitVec64 row.call.result == (host hints).io.hintLength &&
        (selected ["sp1.native.hint_node"] checked.2).length == (if hints.isEmpty then 0 else 1) &&
        (selected ["sp1.native.hint_queue_state"] checked.2).length == 2) = true := by native_decide

/-- Forging both the instruction return and a locally valid node length fails source authentication. -/
theorem forgedReturn :
    let hints : List Bytes := [[1, 2, 3]]
    let honest := input hints 0 1
    let forged := { honest with
      call := { honest.call with result := word 4 },
      node := { honest.node with length := word 4 } }
    (instruction forged.call.result).1 = true ∧ (evaluate false forged).1 = true ∧
      (source hints forged.node).1 = false ∧
      balanced (selected ["sp1.native.hint_node"] ((source hints honest.node).2 ++ (evaluate false forged).2)) = false ∧
      (evaluate false { honest with call := forged.call }).1 = false := by native_decide

/-- Empty routing cannot replace a genuine current head, even with a matching sentinel return. -/
theorem forgedEmpty :
    let honest := input [[1, 2, 3]] 0 1
    let forged := { honest with
      call := { honest.call with result := HostHintLengthChip.emptyWord },
      previous := { honest.previous with head := 0 } }
    (evaluate true forged).1 = true ∧
      balanced (selected ["sp1.native.hint_queue_state"] ((endpoints honest).2 ++ (evaluate true forged).2)) = false ∧
      (evaluate true { honest with call := forged.call }).1 = false := by native_decide

/-- Bounds, strict queue clocks, complete codes, and computed comparison witnesses fail closed. -/
theorem rejectsMalformed :
    let row := input [[1, 2, 3]] 0 1
    [{ row with call := { row.call with code := #v[240, 0, 0, 1] } },
     { row with call := { row.call with length := word 1 } },
     { row with previous := { row.previous with clk_low := 1 } },
     { row with previous := { row.previous with clk_high := 2 ^ 24 } },
     { row with node := { row.node with tail := row.node.pointer } },
     { row with node := { row.node with pointer := #v[65536, 0, 0] } },
     { row with node := { row.node with length := #v[65536, 0, 0, 0] } }].all
       (fun bad => !(evaluate false bad).1) = true ∧
    [0, 23, 47, 71, 95, 120].all (fun index => !(evaluate false row (some index)).1) = true := by native_decide

/-- Earlier pops may select any retained source head without rebuilding its node. -/
theorem historicalNodes :
    let hints : List Bytes := [[1, 2, 3], [], [9]]
    let (store, _) := HintQueue.ofList hints
    [1, 2, 3].all (fun head =>
      match HintQueue.decode? store head with
      | none => false
      | some current =>
        match (host current).run policy context with
        | none => false
        | some execution =>
          let row := HostHintLengthChip.populate (p := SP1Prime) store head 1 265 execution
          let checked := evaluate false row
          let origin := source hints row.node
          checked.1 && origin.1 && balanced
            (selected ["sp1.native.hint_node"] (checked.2 ++ origin.2))) = true := by native_decide

/-- HINT_LEN preserves historical allocation even at an empty head; endpoints reject a reset. -/
theorem frontierTampering :
    let (store, _) := HintQueue.ofList [[1], [], [9]]
    let execution := ((host []).run policy context).getD ⟨.hintLength, 0, 0, 0, ⟨host [], none⟩⟩
    let honest := HostHintLengthChip.populate (p := SP1Prime) store 0 1 265 execution
    let forged := { honest with previous := { honest.previous with allocated := 0 } }
    (evaluate true honest).1 = true ∧ Address.toNat honest.next.allocated = 3 ∧
      (evaluate true forged).1 = true ∧
      balanced (selected ["sp1.native.hint_queue_state"]
        ((endpoints honest).2 ++ (evaluate true forged).2)) = false := by native_decide

/-- info: exportable ✓ (122 witness cells) -/
#guard_msgs in
#assert_exportable (HostHintLengthChip.circuit (p := SP1Prime) false)

/-- info: exportable ✓ (122 witness cells) -/
#guard_msgs in
#assert_exportable (HostHintLengthChip.circuit (p := SP1Prime) true)

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (HostHintQueue.source (p := SP1Prime) [[1, 2, 3], []])

end SP1CleanTest.Core.HostHintLength
