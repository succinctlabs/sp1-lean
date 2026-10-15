import SP1CleanTest.Core.HostChecks
import Clean.Circuit.WitnessExport
import SP1Clean.Proofs.Chips.HostCommitChip.Ledger
import SP1Clean.Proofs.Chips.HostCommitChip.Populate
import SP1Clean.Proofs.Chips.HostCommitChip.Bridge
import SP1Clean.Proofs.Chips.HostCallChip.Populate
import SP1Clean.Model.SP1Field

/-! # Executed mutable commitment regressions

Evaluate complete witness programs and all local checks. Joint instruction/provider tests balance
actual HostCall and PublicValues messages, including distinct overwrites of the same slot. Bank
endpoints are explicit test fixtures; global endpoint authentication remains an ensemble obligation.
-/

namespace SP1CleanTest.Core.HostCommit

open Circuit Air.Flat SP1Clean SP1Clean.HostCommitChip SP1Clean.Model.Core

private abbrev Fp := ZMod SP1Prime
open HostChecks

private def evaluate (deferred : Bool) (slot : Fin 8) (input : Inputs Fp)
    (corrupt : Option ℕ := none) : Bool × Ledger :=
  evaluateProgram (HostCommitChip.main deferred slot (varFromOffset Inputs 0))
    (toElements input).toList corrupt

private def word (value : ℕ) : Word Fp :=
  Soundness.Target.bitVecToWord (BitVec.ofNat 64 value)

private def call (deferred : Bool) (slot : Fin 8) (clock value : ℕ) : HostCallChip.Message Fp :=
  ⟨0, clock, codeWord deferred, slotWord slot, word value, codeWord deferred, 0⟩

private def genesis : HostCommitChip.State Fp := ⟨0, 0, Vector.replicate 8 0⟩

private def row (deferred : Bool) (slot : Fin 8) (value : ℕ) : Inputs Fp :=
  HostCommitChip.populate deferred (call deferred slot 1 value) genesis

private def instruction (deferred : Bool) (slot : Fin 8) (clock value : ℕ) : HostCallChip.Inputs Fp :=
  let code : ℕ := if deferred then 26 else 16
  let input : SyscallInstrsChip.Inputs Fp :=
    { state := ⟨0, (clock / 65536 : ℕ), (clock % 65536 : ℕ), #v[0, 1, 0]⟩
      op_a := 5, op_a_memory := ⟨codeWord deferred, ⟨0, (clock + 3 : ℕ)⟩⟩, op_a_0 := 0
      op_b := 10, op_b_memory := ⟨slotWord slot, ⟨0, (clock + 2 : ℕ)⟩⟩
      op_c := 11, op_c_memory := ⟨word value, ⟨0, (clock + 1 : ℕ)⟩⟩
      next_pc := #v[4, 1, 0], is_halt := 0, op_a_value := codeWord deferred
      syscall_id_bytes := U16toU8OperationSafe.populate (codeWord deferred)
      is_enter_unconstrained := IsZeroOperation.populate ((code : Fp) - 3)
      is_hint_len := IsZeroOperation.populate ((code : Fp) - 240)
      is_halt_zero := IsZeroOperation.populate (code : Fp)
      is_commit := IsZeroOperation.populate ((code : Fp) - 16)
      is_commit_deferred := IsZeroOperation.populate ((code : Fp) - 26)
      digest_index_bits := Vector.ofFn (fun i : Fin 8 => if i == slot then 1 else 0)
      digest_word := if deferred then 0 else Vector.ofFn (fun i : Fin 4 => ((value / 256 ^ i.val % 256 : ℕ) : Fp))
      op_b_cmp := ⟨1⟩, op_c_cmp := ⟨if value / 65536 < 32512 then 1 else 0⟩, is_real := 1 }
  HostCallChip.populate input 0 0

private def instructionEvaluation (deferred : Bool) (slot : Fin 8) (clock value : ℕ) : Bool × Ledger :=
  evaluateProgram (HostCallChip.main (varFromOffset HostCallChip.Inputs 0))
    (toElements (instruction deferred slot clock value)).toList

private def balance (ledger : Ledger) : Bool :=
  ledger.all fun key =>
    ((ledger.filter (fun item => item.1 == key.1 && item.2.1 == key.2.1)).map (·.2.2)).sum == 0

private def handoff (ledger : Ledger) : Ledger :=
  ledger.filter fun item => item.1 == "sp1.native.host_call" || item.1 == "SP1PublicValues"

/-- All sixteen routed components execute genuine nonzero rows, including each value boundary. -/
theorem validUpdates : [false, true].all (fun deferred => (List.finRange 8).all fun slot =>
    [0, 65537, (if deferred then SP1Prime else 2 ^ 32) - 1].all fun value =>
      (evaluate deferred slot (row deferred slot value)).1) = true := by native_decide

/-- Both comparison branches work; equal, reversed, unbounded and wrapped clocks fail. -/
theorem clockChecks :
    (evaluate false 0 (HostCommitChip.populate false
      { (call false 0 0 17) with clk_high := 1 }
      { genesis with clk_low := 2 ^ 24 - 1 })).1 = true ∧
    [(0, 1, 0, 1), (0, 2, 0, 1), (1, 0, 0, 1), (0, 0, 0, 2 ^ 24),
     (2 ^ 24, 0, 1, 1), (0, -1, 0, 1), (0, 0, -1, 1)].all (fun (ph, pl, ch, cl) =>
      !(evaluate false 0 (HostCommitChip.populate false
        { (call false 0 1 17) with clk_high := ch, clk_low := cl }
        { genesis with clk_high := ph, clk_low := pl })).1) = true := by native_decide

/-- Full-word call fields, canonical value bounds, and computed witness columns are constrained. -/
theorem rejectsMalformed :
    [row false 0 (2 ^ 32), row false 0 (2 ^ 48),
     { (row false 0 17) with call := { (row false 0 17).call with code := #v[16, 0, 1, 0] } },
     { (row false 0 17) with call := { (row false 0 17).call with arg1 := word 8 } },
     { (row false 0 17) with call := { (row false 0 17).call with arg1 := #v[0, 0, 0, 1] } },
     { (row false 0 17) with call := { (row false 0 17).call with result := word 0 } },
     { (row false 0 17) with call := { (row false 0 17).call with length := word 1 } },
     { (row false 0 17) with bytes := ⟨#v[18, 0, 0, 0]⟩ }].all
      (fun input => !(evaluate false 0 input).1) = true ∧
    (evaluate true 0 (row true 0 SP1Prime)).1 = false ∧
    (evaluate true 0 (row false 0 17)).1 = false ∧
    (evaluate false 1 (row false 0 17)).1 = false ∧
    [0, 97, 121, 122, 185].all (fun index =>
      !(evaluate false 0 (row false 0 17) (some index)).1) = true := by native_decide

/-- The existing instruction's full handoff and PublicValues pulls cancel the native provider. -/
theorem jointLedgers : [false, true].all (fun deferred => (List.finRange 8).all fun slot =>
    [65537, (if deferred then SP1Prime else 2 ^ 32) - 1].all fun value =>
      let source := instructionEvaluation deferred slot 1 value
      let target := evaluate deferred slot (row deferred slot value)
      source.1 && target.1 && balance (handoff (source.2 ++ target.2))) = true := by native_decide

private def overwrite (deferred : Bool) (slot : Fin 8) : Bool :=
  let first := row deferred slot 65537
  let second := HostCommitChip.populate deferred (call deferred slot 265 131075) (first.next slot)
  let a := evaluate deferred slot first
  let b := evaluate deferred slot second
  let sourceA := instructionEvaluation deferred slot 1 65537
  let sourceB := instructionEvaluation deferred slot 265 131075
  let bank := (stateChannel (p := SP1Prime) deferred).name
  let bankLedger := (a.2 ++ b.2).filter fun item => item.1 == bank
  let endpoints : Ledger :=
    [(bank, (toElements genesis).toList, 1), (bank, (toElements (second.next slot)).toList, -1)]
  a.1 && b.1 && sourceA.1 && sourceB.1 && balance (bankLedger ++ endpoints) &&
    balance (handoff (a.2 ++ b.2 ++ sourceA.2 ++ sourceB.2)) &&
    (second.next slot).decode == (Vector.replicate 8 (0 : BitVec 32)).set slot 131075

/-- Different values in one slot compose through actual bank ledgers and leave the last value. -/
theorem repeatedWrites : [false, true].all (fun deferred =>
    (List.finRange 8).all (overwrite deferred)) = true := by native_decide

/-- Locally valid forks or omitted updates cannot pass the endpoint balance check. -/
theorem brokenHistories : [false, true].all (fun deferred =>
    let first := row deferred 0 65537
    let fork := HostCommitChip.populate deferred (call deferred 0 265 131075) genesis
    let a := evaluate deferred 0 first
    let b := evaluate deferred 0 fork
    let bank := (stateChannel (p := SP1Prime) deferred).name
    let endpoints : Ledger := [(bank, (toElements genesis).toList, 1),
      (bank, (toElements (fork.next 0)).toList, -1)]
    a.1 && b.1 &&
      !balance (((a.2 ++ b.2).filter (fun item => item.1 == bank)) ++ endpoints) &&
      !balance ((a.2.filter (fun item => item.1 == bank)) ++ endpoints)) = true := by native_decide

/-- info: exportable ✓ (186 witness cells) -/
#guard_msgs in
#assert_exportable (HostCommitChip.circuit (p := SP1Prime) false 0)

/-- info: exportable ✓ (186 witness cells) -/
#guard_msgs in
#assert_exportable (HostCommitChip.circuit (p := SP1Prime) true 7)

end SP1CleanTest.Core.HostCommit
