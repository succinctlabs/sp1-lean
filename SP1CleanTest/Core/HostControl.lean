import SP1CleanTest.Core.HostChecks
import Clean.Circuit.WitnessExport
import SP1Clean.Proofs.Chips.HostControlLedger
import SP1Clean.Proofs.Chips.HostHaltChip.Bridge
import SP1Clean.Proofs.Chips.HostEnterChip.Bridge
import SP1Clean.Proofs.Chips.HostControlPopulate

/-! # Native control handlers against instructions and host dispatch

Execute the complete instruction and handler witness programs. Their HostCall ledgers must
cancel exactly, while the public Exit remains solely on the instruction and the complete
terminal receipt comes from the HALT handler. This checks local guarantees
and handoff accounting, not an assembled boot-to-HALT witness. Interpreter checks include
nonempty host state, unrestricted unused arguments, canonical exits, and stopped dispatch.
-/

namespace SP1CleanTest.Core.HostControl

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core HostChecks

private abbrev Fp := ZMod SP1Prime

private def word (value : ℕ) : Word Fp :=
  Soundness.Target.bitVecToWord (BitVec.ofNat 64 value)

private def call (halt : Bool) (arg1 arg2 : ℕ) : HostCallChip.Message Fp :=
  ⟨0, 1, word (if halt then 0 else 3), word arg1, word arg2, 0, 0⟩

private def evaluateHalt (input : HostCallChip.Message Fp) (corrupt : Option ℕ := none) : Bool × Ledger :=
  evaluateProgram (HostHaltChip.main (varFromOffset HostHaltChip.Inputs 0))
    (toElements (HostHaltChip.populate input)).toList corrupt

private def evaluateEnter (input : HostCallChip.Message Fp) : Bool × Ledger :=
  evaluateProgram (HostEnterChip.main (varFromOffset HostEnterChip.Inputs 0)) (toElements input).toList

private def instruction (halt : Bool) (arg1 arg2 : ℕ) : HostCallChip.Inputs Fp :=
  let code : ℕ := if halt then 0 else 3
  let input : SyscallInstrsChip.Inputs Fp :=
    { state := ⟨0, 0, 1, #v[0, 1, 0]⟩
      op_a := 5, op_a_memory := ⟨word code, ⟨0, 4⟩⟩, op_a_0 := 0
      op_b := 10, op_b_memory := ⟨word arg1, ⟨0, 3⟩⟩
      op_c := 11, op_c_memory := ⟨word arg2, ⟨0, 2⟩⟩
      next_pc := if halt then #v[1, 0, 0] else #v[4, 1, 0], is_halt := if halt then 1 else 0
      op_a_value := 0, syscall_id_bytes := U16toU8OperationSafe.populate (word code)
      is_enter_unconstrained := IsZeroOperation.populate ((code : Fp) - 3)
      is_hint_len := IsZeroOperation.populate ((code : Fp) - 240)
      is_halt_zero := IsZeroOperation.populate (code : Fp)
      is_commit := IsZeroOperation.populate ((code : Fp) - 16)
      is_commit_deferred := IsZeroOperation.populate ((code : Fp) - 26)
      digest_index_bits := Vector.replicate 8 0, digest_word := 0
      op_b_cmp := ⟨if arg1 / 65536 < 32512 then 1 else 0⟩
      op_c_cmp := ⟨if arg2 / 65536 < 32512 then 1 else 0⟩, is_real := 1 }
  HostCallChip.populate input 0 0

private def sourceChecked (halt : Bool) (arg1 arg2 : ℕ) : Bool × Ledger :=
  evaluateProgram (HostCallChip.main (varFromOffset HostCallChip.Inputs 0))
    (toElements (instruction halt arg1 arg2)).toList

private def selected (channel : String) (ledger : Ledger) : Ledger :=
  ledger.filter (fun item => item.1 == channel)

private def balanced (ledger : Ledger) : Bool :=
  ledger.length < SP1Prime && ledger.all fun key =>
    ((ledger.filter (fun item => item.1 == key.1 && item.2.1 == key.2.1)).map (·.2.2)).sum == 0

/-- HALT supports the full canonical field range, including exits beyond the legacy 16-bit bound. -/
theorem canonicalExits : [0, 65535, 65536, SP1Prime - 1].all (fun exit =>
    (evaluateHalt (call true exit (2 ^ 64 - 1))).1 && (sourceChecked true exit (2 ^ 64 - 1)).1) = true ∧
    [SP1Prime, 2 ^ 32, 2 ^ 48, 2 ^ 64 - 1].all (fun exit =>
      !(evaluateHalt (call true exit 0)).1 && !(sourceChecked true exit 0).1) = true := by native_decide

/-- ENTER leaves both guest arguments unrestricted, including their full unsigned 64-bit range. -/
theorem unusedArguments : [(0, 0), (SP1Prime, 2 ^ 32), (2 ^ 64 - 1, 2 ^ 64 - 1)].all
    (fun (a, b) => (evaluateEnter (call false a b)).1) = true := by native_decide

/-- Full codes, returns, length fields, canonical limbs, and internal witness bits are checked. -/
theorem rejectsMalformed :
    [{ (call true 1 0) with code := #v[0, 0, 1, 0] },
     { (call true 1 0) with result := word 1 },
     { (call true 1 0) with length := word 1 },
     { (call true 1 0) with arg1 := #v[65536, 0, 0, 0] },
     { (call true 1 0) with arg1 := #v[-1, 0, 0, 0] }].all
      (fun input => !(evaluateHalt input).1) = true ∧
    [{ (call false 1 2) with code := #v[3, 0, 0, 1] },
     { (call false 1 2) with result := word 3 },
     { (call false 1 2) with length := word 1 }, call true 1 2].all
      (fun input => !(evaluateEnter input).1) = true ∧
    [0, 31, 63].all (fun index => !(evaluateHalt (call true 65536 0) (some index)).1) = true := by
  native_decide

private def joint (halt : Bool) (arg1 arg2 : ℕ) : Bool :=
  let source := sourceChecked halt arg1 arg2
  let target := if halt then evaluateHalt (call true arg1 arg2) else evaluateEnter (call false arg1 arg2)
  let host := "sp1.native.host_call"
  source.1 && target.1 && balanced (selected host (source.2 ++ target.2)) &&
    (selected host source.2).length == 1 && (selected host target.2).length == 1 &&
    selected "SP1Exit" target.2 == [] &&
    selected "SP1HostExit" target.2 ==
      (if halt then [("SP1HostExit", (toElements (word arg1)).toList, 1)] else []) &&
    selected "SP1HostExit" source.2 == [] &&
    selected "SP1Exit" source.2 == (if halt then [("SP1Exit", [arg1], 1)] else []) &&
    (selected "SP1Memory" source.2).length == 6 && selected "SP1Memory" target.2 == []

/-- Actual instruction/handler rows cancel their handoff; only the HALT instruction sends Exit. -/
theorem jointLedgers :
    [0, 65536, SP1Prime - 1].all (fun exit => joint true exit (2 ^ 64 - 1)) = true ∧
    [(0, 0), (SP1Prime, 2 ^ 32), (2 ^ 64 - 1, 2 ^ 64 - 1)].all
      (fun (a, b) => joint false a b) = true := by native_decide

/-- A locally valid handler cannot be substituted for another instruction's clock or arguments. -/
theorem handoffTampering : [false, true].all (fun halt =>
    let source := sourceChecked halt 7 9
    [{ (call halt 7 9) with clk_low := 265 }, call halt 8 9, call halt 7 10].all fun input =>
      let target := if halt then evaluateHalt input else evaluateEnter input
      source.1 && target.1 && !balanced (selected "sp1.native.host_call" (source.2 ++ target.2))) = true := by
  native_decide

private def host : HostState :=
  { io := ⟨[[1, 2], []], [3, 4]⟩
    committed := Vector.replicate 8 17, deferred := Vector.replicate 8 19
    stdout := [5], stderr := [6]
    requests := [.proof ⟨[7], [8]⟩] }

private def context (input : HostCallChip.Message Fp) : HostReadContext where
  register index := if index == 5 then some (Word.toBitVec64 input.code)
    else if index == 10 then some (Word.toBitVec64 input.arg1)
    else if index == 11 then some (Word.toBitVec64 input.arg2) else none
  byte _ := none

private def policy : HostPolicy := ⟨{ readOnly := fun _ => false }, SP1Prime⟩

/-- Dispatch preserves every unrelated host field, emits no RAM write, and cannot resume after HALT. -/
theorem interpreterEffects :
    [0, 65536, SP1Prime - 1].all (fun exit =>
      let input := call true exit (2 ^ 64 - 1)
      let expected := HostHaltChip.execution (HostHaltChip.populate input) host
      host.run policy (context input) == some expected && expected.effect.write == none &&
        expected.effect.state == { host with exitCode := some (BitVec.ofNat 32 exit) } &&
        (expected.effect.state.run policy (context (call false 0 0))).isNone &&
        (expected.effect.state.run policy (context input)).isNone) = true ∧
    [(0, 0), (2 ^ 64 - 1, 2 ^ 64 - 1)].all (fun (a, b) =>
      let input := call false a b
      let expected := HostEnterChip.execution input host
      host.run policy (context input) == some expected && expected.result == 0 &&
        expected.effect == ⟨host, none⟩) = true := by native_decide

/-- The interpreter's result for `call halt arg1 _` builds a checked row at each of four clocks
(across the clock-limb boundary), pulling exactly the canonical message. A `def` rather than an
inline statement: `let`s in a theorem type become `have`s, and the kernel then unfolds the
interpreter to identify the two spellings. -/
private def compiledControl (halt : Bool) (arg1 : ℕ) : Bool :=
  let input := call halt arg1 (2 ^ 64 - 1)
  match host.run policy (context input) with
  | none => false
  | some execution => [1, 2 ^ 24 - 7, 2 ^ 24 + 1, 2 ^ 48 - 7].all fun clock =>
      let message := SP1Clean.HostControl.message (p := SP1Prime) clock execution
      let checked := if halt then
        evaluateProgram (HostHaltChip.main (varFromOffset HostHaltChip.Inputs 0))
          (toElements (SP1Clean.HostControl.halt clock execution)).toList
        else evaluateProgram (HostEnterChip.main (varFromOffset HostEnterChip.Inputs 0))
          (toElements (SP1Clean.HostControl.enter clock execution)).toList
      checked.1 && Semantics.clkNat message.clk_high message.clk_low == clock &&
        selected "sp1.native.host_call" checked.2 ==
          [("sp1.native.host_call", (toElements message).toList, -1)]

/-- Successful interpreter results construct checked rows, including across clock-limb boundaries. -/
theorem compiledControls :
    [false, true].all (fun halt => [0, 65536, SP1Prime - 1].all (compiledControl halt)) = true := by
  native_decide

/-- info: exportable ✓ (64 witness cells) -/
#guard_msgs in
#assert_exportable (HostHaltChip.circuit (p := SP1Prime))

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (HostEnterChip.circuit (p := SP1Prime))

end SP1CleanTest.Core.HostControl
