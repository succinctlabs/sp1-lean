import Clean.Circuit.WitnessExport
import SP1CleanTest.Core.HintReadFixtures
import SP1Clean.Proofs.Chips.HostHintReadChip.Populate
import SP1Clean.Proofs.Chips.HostHintReadChip.Bridge
import SP1Clean.Proofs.Chips.HostHintReadChip.Ledger
import SP1Clean.Native.Operations.HintQueueSource

/-! # Executed HINT_READ handler and complete word transfers

Run the handler, instruction handoff, fixed node/word sources, physical word consumers, and
permission providers. The subsystem's entire non-Byte ledger balances against semantic queue
and RAM boundaries; Byte guarantees are checked directly. The instruction's other channels
remain external. These tests do not assert installation in the mixed shard ensemble.
-/

namespace SP1CleanTest.Core.HostHintRead

open Circuit Air.Flat SP1Clean Model.Core HintQueue HostChecks

private abbrev Fp := ZMod SP1Prime

private def host (hints : List Bytes) : HostState :=
  { io := ⟨hints, [4, 5]⟩, committed := Vector.replicate 8 17, deferred := Vector.replicate 8 19,
    stdout := [6], stderr := [7], requests := [.proof ⟨[8], [9]⟩] }

private def policy : HostPolicy := ⟨{ readOnly := fun _ => false }, SP1Prime⟩

private def context (address length : ℕ) : HostReadContext where
  register index := if index == 5 then some 241 else if index == 10 then some (BitVec.ofNat 64 address)
    else if index == 11 then some (BitVec.ofNat 64 length) else none
  byte _ := none

private def input (actual : Bytes) (address : ℕ) (previousClock : ℕ := 0) (clock : ℕ := 1) :
    HostHintReadChip.Inputs Fp :=
  let (store, head) := ofList [actual]
  let executed := ((host [actual]).run policy (context address actual.length)).getD
    ⟨.hintRead, 0, 0, 0, ⟨host [actual], none⟩⟩
  HostHintReadChip.populate store head previousClock clock executed

private def evaluate (row : HostHintReadChip.Inputs Fp) (corrupt : Option ℕ := none) : Bool × Ledger :=
  evaluateProgram (HostHintReadChip.main (varFromOffset HostHintReadChip.Inputs 0))
    (toElements row).toList corrupt

private def source (actual : Bytes) (row : NodeRecord Fp) : Bool × Ledger :=
  evaluateProgram (HostHintQueue.sourceMain [actual] (varFromOffset NodeRecord 0))
    (toElements row).toList none [FiniteLookup.ofStatic (sourceTable [actual])]

private def instruction (call : HostCallChip.Message Fp) : Bool × Ledger :=
  let row : SyscallInstrsChip.Inputs Fp :=
    { state := ⟨0, 0, 1, #v[0, 2, 0]⟩
      op_a := 5, op_a_memory := ⟨call.code, ⟨0, 4⟩⟩, op_a_0 := 0
      op_b := 10, op_b_memory := ⟨call.arg1, ⟨0, 3⟩⟩
      op_c := 11, op_c_memory := ⟨call.arg2, ⟨0, 2⟩⟩
      next_pc := #v[4, 2, 0], is_halt := 0, op_a_value := call.result
      syscall_id_bytes := U16toU8OperationSafe.populate call.code
      is_enter_unconstrained := IsZeroOperation.populate 238
      is_hint_len := IsZeroOperation.populate 1, is_halt_zero := IsZeroOperation.populate 241
      is_commit := IsZeroOperation.populate 225, is_commit_deferred := IsZeroOperation.populate 215
      digest_index_bits := Vector.replicate 8 0, digest_word := 0
      op_b_cmp := ⟨0⟩, op_c_cmp := ⟨1⟩, is_real := 1 }
  evaluateProgram (HostCallChip.main (varFromOffset HostCallChip.Inputs 0))
    (toElements (HostCallChip.populate row 0 0)).toList (programAddress := 131072)

private def boundaries (honest : HostHintReadChip.Inputs Fp) : Ledger :=
  (evaluateProgram (do
    HostHintQueue.stateChannel.push (const honest.previous)
    HostHintQueue.stateChannel.pull (const honest.next)) []).2

private def joint (actual : Bytes) (address : ℕ) (row : HostHintReadChip.Inputs Fp)
    (words : List HintReadFixtures.Row) : Bool :=
  let handler := evaluate row
  let node := source actual row.node
  let finalWord := HintReadFixtures.source actual row.endStep.word
  let cpu := instruction row.call
  let consumers := words.map HintReadFixtures.checked
  let sources := words.map fun row => HintReadFixtures.source actual (row.2.step row.1).word
  let permissions := words.flatMap fun row => (List.range 8).map fun index =>
    HintReadFixtures.permission HintReadFixtures.image (Address.toNat row.2.address + index)
  let memory := (HintReadFixtures.boundaries address actual).filter (fun item => item.1 == "SP1Memory")
  handler.1 && node.1 && finalWord.1 && cpu.1 && consumers.all (·.1) && sources.all (·.1) &&
    permissions.all (·.1) && HintReadFixtures.balanced
      (boundaries (input actual address) ++ memory ++ handler.2 ++ node.2 ++ finalWord.2 ++
        (cpu.2.filter (fun item => item.1 == "sp1.native.host_call")) ++
        consumers.flatMap (·.2) ++ sources.flatMap (·.2) ++ permissions.flatMap (·.2))

/-- The real handler closes the instruction, queue, word, and physical write subsystem. -/
theorem jointLedgers : (List.range 18).all (fun length =>
    let actual := HintReadFixtures.bytes length
    joint actual 65536 (input actual 65536) (HintReadFixtures.rows 65536 actual)) = true := by native_decide

/-- Physical row order is irrelevant, while missing or repeated words cannot satisfy the handler. -/
theorem wordCoverage :
    let actual := HintReadFixtures.bytes 16
    let words := HintReadFixtures.rows 65536 actual
    let row := input actual 65536
    joint actual 65536 row words.reverse = true ∧
      joint actual 65536 row (words.drop 1) = false ∧
      joint actual 65536 row (words.take 2) = false ∧
      joint actual 65536 row (words ++ words.take 1) = false := by native_decide

/-- No one-past address is encoded when padding finishes at the guest-window ceiling. -/
theorem finalCell : [0, 7, 8, 15, 16].all (fun length =>
    let actual := HintReadFixtures.bytes length
    let address := 2 ^ 48 - 8 * wordCount actual
    joint actual address (input actual address) (HintReadFixtures.rows address actual)) = true := by native_decide

/-- A locally valid final-word substitution is rejected by the immutable source and joint ledger. -/
theorem finalWordAuthentication :
    let actual : Bytes := [1, 2, 3]
    let row := input actual 65536
    let forged := { row with lastValue := 0 }
    (evaluate forged).1 = true ∧ (HintReadFixtures.source actual forged.endStep.word).1 = false ∧
      joint actual 65536 forged (HintReadFixtures.rows 65536 actual) = false := by native_decide

/-- Cursor balance alone admits an early stop followed by a late advance at a repeated address.
Authenticating each consumer's marker rejects this even when the handler's end word is honest. -/
theorem consumerMarkerAuthentication :
    let actual := HintReadFixtures.bytes 8
    let first := (HintReadFixtures.row 65536 actual 0).2
    let second := (HintReadFixtures.row 65528 actual 1).2
    let early := (true, HintReadWordChip.populate true first.ram first.pointer first.index)
    let late := (false, HintReadWordChip.populate false second.ram second.pointer second.index)
    let handler := input actual 65536
    (HintReadFixtures.checked early).1 = true ∧ (HintReadFixtures.checked late).1 = true ∧
      HintReadFixtures.balanced
        (((evaluate handler).2 ++ (HintReadFixtures.checked early).2 ++
          (HintReadFixtures.checked late).2).filter (fun item => item.1 == "sp1.native.hint_read_state")) = true ∧
      Address.toNat early.2.address = Address.toNat late.2.address ∧
      (HintReadFixtures.source actual handler.endStep.word).1 = true ∧
      (HintReadFixtures.source actual (early.2.step true).word).1 = false ∧
      (HintReadFixtures.source actual (late.2.step false).word).1 = false ∧
      joint actual 65536 handler [early, late] = false := by native_decide

/-- The actual host loses one hint and preserves all unrelated state across clock boundaries. -/
theorem semanticRows : [[], [1, 2, 3], [1, 2, 3, 4, 5, 6, 7, 8]].all (fun actual =>
    [(0, 1), (2 ^ 24 - 1, 2 ^ 24 + 1), (2 ^ 48 - 9, 2 ^ 48 - 1)].all fun (before, now) =>
      let row := input actual 65536 before now
      (evaluate row).1 &&
        (host [actual]).run policy (context 65536 actual.length) ==
          some (HostHintReadChip.execution row (host [actual]) actual []) &&
        Address.toNat row.next.head == 0 && Address.toNat row.next.allocated == 1) = true := by native_decide

/-- Historical source heads pop to the correct nonempty suffix and retain all allocated identities. -/
theorem historicalHeads :
    let hints : List Bytes := [[1, 2, 3], [], [9, 10]]
    let (store, _) := ofList hints
    [1, 2, 3].all (fun head =>
      match decode? store head with
      | some (bytes :: rest) =>
        match (host (bytes :: rest)).run policy (context 65536 bytes.length) with
        | none => false
        | some executed =>
          let row := HostHintReadChip.populate (p := SP1Prime) store head 1 265 executed
          let node := evaluateProgram (HostHintQueue.sourceMain hints (varFromOffset NodeRecord 0))
            (toElements row.node).toList none [FiniteLookup.ofStatic (sourceTable hints)]
          let word := evaluateProgram (HostHintQueue.sourceWordMain hints (varFromOffset WordRecord 0))
            (toElements row.endStep.word).toList none [FiniteLookup.ofStatic (sourceWordTable hints)]
          (evaluate row).1 && node.1 && word.1 &&
            executed == HostHintReadChip.execution row (host (bytes :: rest)) bytes rest &&
            Address.toNat row.next.head == head - 1 && Address.toNat row.next.allocated == 3
      | _ => false) = true := by native_decide

/-- The complete code, argument span, result, end index, and comparison witnesses are constrained. -/
theorem malformedRows :
    let row := input [1, 2, 3] 65536
    [{ row with call := { row.call with code := #v[241, 0, 0, 1] } },
     { row with call := { row.call with result := 0 } },
     { row with call := { row.call with length := #v[1, 0, 0, 0] } },
     { row with call := { row.call with arg1 := #v[0, 1, 0, 1] } },
     { row with call := { row.call with arg2 := #v[4, 0, 0, 0] } },
     { row with previous := { row.previous with clk_low := 1 } },
     { row with lastIndex := Address.ofNat 1 },
     { row with span := { row.span with last := Address.ofNat 65544 } },
     { row with span := { row.span with count := Address.ofNat 2 } }].all
      (fun bad => !(evaluate bad).1) = true ∧
    [0, 23, 95, 121, 122, 185, 237, 238, 301].all
      (fun index => !(evaluate row (some index)).1) = true := by native_decide

/-- A forged frontier can satisfy the row locally but cannot replace the fixed semantic endpoints. -/
theorem queueBoundary :
    let actual : Bytes := [1, 2, 3]
    let row := input actual 65536
    let forged := { row with previous := { row.previous with allocated := 0 } }
    (evaluate forged).1 = true ∧ joint actual 65536 forged (HintReadFixtures.rows 65536 actual) = false ∧
      (host []).run policy (context 65536 0) = none := by native_decide

/-- info: exportable ✓ (302 witness cells) -/
#guard_msgs in
#assert_exportable (HostHintReadChip.circuit (p := SP1Prime))

end SP1CleanTest.Core.HostHintRead
