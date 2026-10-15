import SP1Clean.Proofs.Chips.HostCallChip.Ledger
import SP1Clean.Proofs.Chips.HostCallChip.Populate
import SP1Clean.Model.SP1Field
import ToClean.Air.FiniteLookup
import Clean.Circuit.WitnessExport
import SP1Clean.Soundness.HostHintReadHandoff
import SP1Clean.Proofs.Chips.HostHintReadChip.Populate
import SP1Clean.Proofs.Chips.HostHintLengthChip.Populate
import SP1CleanTest.Core.HintReadFixtures
import ToClean.Air.TableBuild

/-! # Executed instruction-to-host handoff regressions

Run complete syscall rows through the witness program, all assertions, the fixed code lookup,
and Byte/Memory/Program local checks. State, Exit and PublicValues balance, and the host effects,
remain whole-ensemble obligations outside these local satisfiability tests.
-/

namespace SP1CleanTest.Core.HostCall

open Circuit Air.Flat SP1Clean SP1Clean.HostCallChip SP1Clean.Model.Core

private abbrev Fp := ZMod SP1Prime

private instance byteDecidable (op : ByteOpcode) (a b c : Fp) : Decidable (op.constrain a b c) := by
  cases op <;> unfold ByteOpcode.constrain <;> infer_instance

private def byteValid (values : List Fp) : Bool :=
  match values with
  | [opcode, a, b, c] =>
    [ByteOpcode.AND, .OR, .XOR, .U8Range, .LTU, .MSB, .Range].any fun op =>
      opcode == (op.idx : Fp) && decide (op.constrain a b c)
  | _ => false

private def memoryValid (values : List Fp) : Bool :=
  match values with
  | [_, low, _, _, _, a, b, c, d] =>
    low.val < 2 ^ 24 && [a, b, c, d].all (fun limb => limb.val < 65536)
  | _ => false

private def evaluate (input : Inputs Fp) (corruptSelector := false) :
    Bool × List (String × List Fp × Fp) :=
  let program := HostCallChip.main (varFromOffset Inputs 0)
  let honest := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  let env : Environment Fp := if corruptSelector then
      { honest with get := fun i => if i == size Inputs + 1 then 1 - honest.get i else honest.get i }
    else honest
  let operations := (program.operations (size Inputs)).toFlat
  let fixed := FiniteLookup.ofStatic (SyscallKind.fixedTable (p := SP1Prime))
  let valid := operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup lookup => lookup.table.name == fixed.table.name &&
      fixed.rows.any (fun row => row.toArray == (lookup.entry.map env).toArray)
    | .witness .. => true
    | .interact interaction =>
      if env interaction.mult == 0 then true
      else if interaction.channel.name == "SP1Byte" then byteValid (interaction.msg.map env).toList
      else if interaction.channel.name == "SP1Memory" then memoryValid (interaction.msg.map env).toList
      else if interaction.channel.name == "SP1Program" then
        (interaction.msg.map env).toList == [0, 1, 0, 50, 5, 10, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0]
      else ["SP1State", "SP1Exit", "SP1Syscall", "SP1PublicValues", "sp1.native.host_call"].contains
        interaction.channel.name
  (valid, (FlatOperation.interactions operations).filterMap fun interaction =>
    if env interaction.mult == 0 then none else
      some (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult))

private def row (code : ℕ) : Inputs Fp :=
  let instruction : SyscallInstrsChip.Inputs Fp :=
    { state := ⟨0, 0, 1, #v[0, 1, 0]⟩
      op_a := 5, op_a_memory := ⟨#v[code, 0, 0, 0], ⟨0, 4⟩⟩, op_a_0 := 0
      op_b := 10, op_b_memory := ⟨#v[0, 0, 0, 0], ⟨0, 3⟩⟩
      op_c := 11, op_c_memory := ⟨#v[0, 0, 0, 0], ⟨0, 2⟩⟩
      next_pc := if code == 0 then #v[1, 0, 0] else #v[4, 1, 0]
      is_halt := if code == 0 then 1 else 0
      op_a_value := if code == 3 then #v[0, 0, 0, 0] else #v[code, 0, 0, 0]
      syscall_id_bytes := ⟨#v[code, 0, 0, 0]⟩
      is_enter_unconstrained := IsZeroOperation.populate ((code : Fp) - 3)
      is_hint_len := IsZeroOperation.populate ((code : Fp) - 240)
      is_halt_zero := IsZeroOperation.populate (code : Fp)
      is_commit := IsZeroOperation.populate ((code : Fp) - 16)
      is_commit_deferred := IsZeroOperation.populate ((code : Fp) - 26)
      digest_index_bits := if code == 16 || code == 26 then #v[1, 0, 0, 0, 0, 0, 0, 0] else 0
      digest_word := 0, op_b_cmp := ⟨1⟩, op_c_cmp := ⟨1⟩, is_real := 1 }
  HostCallChip.populate instruction #v[17, 2, 3, 4] 0

/-- Every native code has a satisfying complete instruction-to-host row. -/
theorem supportedCalls : [0, 2, 3, 16, 26, 27, 240, 241].all
    (fun code => (evaluate (row code)).1) = true := by native_decide

/-- The extra x12 observation is an unchanged read-back at event time plus one. -/
theorem writeLedger : ((evaluate (row 2)).2.filter fun item =>
    item.1 == "sp1.native.host_call" ||
      (item.1 == "SP1Memory" && item.2.1[2]? == some 12)) =
    [("SP1Memory", [0, 0, 12, 0, 0, 17, 2, 3, 4], -1),
     ("SP1Memory", [0, 2, 12, 0, 0, 17, 2, 3, 4], 1),
     ("sp1.native.host_call", [0, 1, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 17, 2, 3, 4], 1)] := by
  native_decide

/-- Non-WRITE calls have six Memory interactions, one handoff, and zero length. -/
theorem otherCallLedgers : [0, 3, 16, 26, 27, 240, 241].all (fun code =>
    let ledger := (evaluate (row code)).2
    (ledger.filter (fun item => item.1 == "SP1Memory")).length == 6 &&
    (ledger.filter (fun item => item.1 == "sp1.native.host_call")).map (fun item => item.2.1.drop 18) ==
      [[0, 0, 0, 0]]) = true := by native_decide

/-- Equal/reversed prior clocks and unbounded length words fail on active WRITE. -/
theorem rejectedReads :
    [HostCallChip.populate (row 2).instruction #v[17, 0, 0, 0] 2,
     HostCallChip.populate (row 2).instruction #v[17, 0, 0, 0] 3,
     HostCallChip.populate (row 2).instruction #v[65536, 0, 0, 0] 0,
     HostCallChip.populate (row 2).instruction #v[17, 0, 0, 0] (-1)].all
      (fun input => !(evaluate input).1) = true ∧
    (evaluate (row 2) true).1 = false ∧ (evaluate (row 3) true).1 = false := by native_decide

/-- Unused length columns carry no read on another call or on padding. -/
theorem gatedReads :
    (evaluate (HostCallChip.populate (row 3).instruction #v[65536, 2, 3, 4] (-1))).1 = true ∧
    (evaluate { (row 2) with instruction := { (row 2).instruction with is_real := 0 } }).1 = true ∧
    (evaluate { (row 2) with instruction := { (row 2).instruction with is_real := 0 } }).2 = [] := by
  native_decide

/-- All four code limbs feed the native profile check, and corrupting the selector fails. -/
theorem rejectedAliases :
    [#v[2, 0, 1, 0], #v[2, 0, 0, 1], #v[2, 1, 0, 0], #v[4, 0, 0, 0]].all (fun code =>
      !(evaluate { (row 2) with instruction := { (row 2).instruction with
        op_a_memory := ⟨code, ⟨0, 4⟩⟩ } }).1) = true := by native_decide

/-- info: exportable ✓ (8 witness cells) -/
#guard_msgs in
#assert_exportable (HostCallChip.circuit (p := SP1Prime))

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (Readers.RegisterRead.circuit (p := SP1Prime))

private def hintHandler (clock : ℕ) : HostHintReadChip.Inputs Fp :=
  let host : HostState := { io := ⟨[[]], []⟩ }
  let context : HostReadContext :=
    ⟨fun index => if index == 5 then some 241
      else if index == 10 then some 65536 else if index == 11 then some 0 else none, fun _ => none⟩
  let executed := (host.run ⟨{ readOnly := fun _ => false }, SP1Prime⟩ context).getD
    ⟨.hintRead, 0, 0, 0, ⟨host, none⟩⟩
  HostHintReadChip.populate (HintQueue.ofList [[]]).1 1 0 clock executed

private def instructionOfCall (message : HostCallChip.Message Fp) : Inputs Fp :=
  let base := (row message.code[0].val).instruction
  { (row message.code[0].val) with instruction :=
    { base with
      state := { base.state with
        clk_high := message.clk_high
        clk_0_16 := (message.clk_low.val % 65536 : ℕ)
        clk_16_24 := (message.clk_low.val / 65536 : ℕ) }
      op_a_memory := ⟨message.code, ⟨0, message.clk_low + 3⟩⟩
      op_b_memory := ⟨message.arg1, ⟨0, message.clk_low + 2⟩⟩
      op_c_memory := ⟨message.arg2, ⟨0, message.clk_low + 1⟩⟩
      op_a_value := message.result } }

private def instructionTable (rows : List (Inputs Fp)) : Table Fp :=
  Table.build Soundness.HostCallLedger.producer rows (fun _ _ => #[]) (ProverHint.empty Fp)

private def handlerTable (rows : List (HostHintReadChip.Inputs Fp)) : Table Fp :=
  Table.build Soundness.HostHintReadCoverage.handler rows (fun _ _ => #[]) (ProverHint.empty Fp)

private def handoff (instructions : List (Inputs Fp)) (handlers : List (HostHintReadChip.Inputs Fp)) : Bool :=
  let tables := [instructionTable instructions, handlerTable handlers]
  let data := deriveProverData tables
  let ledger := tables.flatMap fun table =>
    table.table.flatMap fun physical =>
      let env := Environment.fromArray physical data
      (FlatOperation.interactions table.component.rowOperations.toFlat).filterMap fun interaction =>
        if interaction.channel.name == "sp1.native.host_call" then
          some (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult) else none
  HintReadFixtures.balanced ledger

/-- Physical decoding and the full handoff retain two clock epochs and discard only padding.
The instruction rows also pass the existing assertion, lookup, and local-channel checker. -/
theorem physicalHandoff :
    let handlers := [hintHandler 1, hintHandler (2 ^ 24 + 1)]
    let instructions := handlers.map fun handler => instructionOfCall handler.call
    let padding := { (row 2) with instruction := { (row 2).instruction with is_real := 0 } }
    instructions.all (fun input => (evaluate input).1) = true ∧
      handoff (padding :: instructions ++ [padding]) handlers.reverse = true ∧
      ((Soundness.HostCallLedger.calls (instructionTable (padding :: instructions ++ [padding]))
        (deriveProverData [instructionTable (padding :: instructions ++ [padding])])).map
        Soundness.HostCallLedger.clock) = [(0, 1), (1, 1)] := by native_decide

/-- An extra handler or a changed full return word cannot balance one instruction.
Duplicating both sides still balances, showing why CPU event uniqueness is essential. -/
theorem duplicateAndForgedHandoff :
    let handler := hintHandler 1
    let instruction := instructionOfCall handler.call
    handoff [instruction] [handler, handler] = false ∧
      handoff [instruction] [{ handler with call := { handler.call with result := #v[241, 0, 0, 1] } }] = false ∧
      handoff [instruction, instruction] [handler, handler] = true ∧
      decide (((Soundness.HostCallLedger.calls (instructionTable [instruction, instruction])
        (deriveProverData [instructionTable [instruction, instruction]])).map
        Soundness.HostCallLedger.clock).Nodup) = false := by native_decide

private def installed : Table Fp :=
  let image : ProgramImage := ⟨[(65536, 0x73)], 65536, []⟩
  let source : ExecutionSnapshot :=
    { sail := { registers := (Soundness.Target.configuredState 65536).regs, memory := image.initialMemory }
      host := {}, clock := 1 }
  let padding := { (row 2) with instruction := { (row 2).instruction with is_real := 0 } }
  (instructionTable [padding, row 2, padding]).withComponent
    ((Soundness.HostLocalCore.tables image source [Soundness.HostHintReadCoverage.handler])[58]'(by
      rw [Soundness.HostLocalCore.tables_length]; decide)) rfl rfl

private def physicalLedger (table : Table Fp) (name : String) : List (String × List Fp × Fp) :=
  table.table.flatMap fun physical =>
    let env := Environment.fromArray physical (deriveProverData [table])
    (FlatOperation.interactions table.component.rowOperations.toFlat).filterMap fun interaction =>
      if interaction.channel.name == name && env interaction.mult != 0 then
        some (name, (interaction.msg.map env).toList, env interaction.mult) else none

private def physicalChecks (table : Table Fp) : Bool :=
  let fixed := FiniteLookup.ofStatic (SyscallKind.fixedTable (p := SP1Prime))
  table.table.all fun physical =>
    let env := Environment.fromArray physical (deriveProverData [table])
    table.component.rowOperations.toFlat.all fun operation =>
      match operation with
      | .assert expression => env expression == 0
      | .lookup lookup => lookup.table.name == fixed.table.name &&
          fixed.rows.any (fun row => row.toArray == (lookup.entry.map env).toArray)
      | .witness .. | .interact .. => true

/-- An installed WRITE row plus padding retains its instruction prefix, original constraints, and State
edge. Its extra x12 read makes full Memory projection invalid: the very same closing frontier
balances the wrapper ledger and fails for the projected instruction ledger. -/
theorem installedMemoryProjection :
    let projected := installed.projectPrefix Soundness.HostCallProjection.original (by decide) rfl
    let originalMemory := physicalLedger projected "SP1Memory"
    let memory := physicalLedger installed "SP1Memory"
    let frontier := originalMemory.map (fun item => (item.1, item.2.1, - item.2.2)) ++
      [("SP1Memory", [0, 0, 12, 0, 0, 17, 2, 3, 4], 1),
       ("SP1Memory", [0, 2, 12, 0, 0, 17, 2, 3, 4], -1)]
    physicalChecks installed = true ∧ physicalChecks projected = true ∧
      projected.table = installed.table.map (·.extract 0 (Soundness.HostCallProjection.original (p := SP1Prime)).width) ∧
      physicalLedger projected "SP1State" = physicalLedger installed "SP1State" ∧
      (physicalLedger installed "SP1State").length = 2 ∧
      memory.length = 8 ∧ originalMemory.length = 6 ∧
      HintReadFixtures.balanced (memory ++ frontier) = true ∧
      HintReadFixtures.balanced (originalMemory ++ frontier) = false := by native_decide

private def lengthHandler : HostHintLengthChip.Inputs Fp :=
  let host : HostState := { io := ⟨[[1, 2, 3]], []⟩ }
  let context : HostReadContext := ⟨fun index => if index == 5 then some 240 else some 0, fun _ => none⟩
  let executed := (host.run ⟨{ readOnly := fun _ => false }, SP1Prime⟩ context).getD
    ⟨.hintLength, 0, 0, 0, ⟨host, none⟩⟩
  HostHintLengthChip.populate (HintQueue.ofList [[1, 2, 3]]).1 1 0 (2 ^ 24 + 1) executed

private def enterMessage : HostCallChip.Message Fp :=
  HostControl.enter 17 ⟨.enterUnconstrained, 0, 0, 0, ⟨{}, none⟩⟩

/-- Physical tables in the real 21-handler registry order, with three different active kinds. -/
private def registeredTables : List (Table Fp) :=
  let views := Soundness.HostHintReadHandoff.registeredReceivers (p := SP1Prime)
  List.ofFn fun index : Fin views.length =>
    if index.val = 0 then handlerTable [hintHandler 1]
    else if index.val = 2 then Table.build (Soundness.HostCallReceivers.enter (p := SP1Prime)).component
      [enterMessage] (fun _ _ => #[]) (ProverHint.empty Fp)
    else if index.val = 19 then Table.build (Soundness.HostCallReceivers.hintLength (p := SP1Prime) false).component
      [lengthHandler] (fun _ _ => #[]) (ProverHint.empty Fp)
    else Table.build views[index].component [] (fun _ _ => #[]) (ProverHint.empty Fp) (by
      have noFixed : views[index].component.fixedColumns = none := by fin_cases index <;> rfl
      simp only [Component.fixedRowsMatch, noFixed])

/-- The heterogeneous physical tables retain the exact registered components, without casts. -/
private theorem registeredTables_components :
    registeredTables.map (·.component) =
      (Soundness.HostHintReadHandoff.registeredReceivers (p := SP1Prime)).map (·.component) := by
  apply List.ext_getElem
  · simp only [registeredTables, List.length_map, List.length_ofFn]
  intro index bound otherBound
  have small : index < 21 := otherBound
  interval_cases index <;> rfl

/-- The actual heterogeneous registry reads every full call and balances reversed instructions
with padding. Removing or duplicating a handler fails the physical ledger. This is a handoff
regression; it does not claim that all the other channels form a complete execution witness. -/
theorem registeredReceiverHandoff :
    let views := Soundness.HostHintReadHandoff.registeredReceivers (p := SP1Prime)
    let messages := [(hintHandler 1).call, enterMessage, lengthHandler.call]
    let padding := { (row 2) with instruction := { (row 2).instruction with is_real := 0 } }
    let instructions := instructionTable (padding :: (messages.map instructionOfCall).reverse ++ [padding])
    let ledger := registeredTables.flatMap fun table => physicalLedger table "sp1.native.host_call"
    views.length = 21 ∧ registeredTables.all physicalChecks = true ∧ physicalChecks instructions = true ∧
      (ReceiverView.messages views registeredTables (deriveProverData registeredTables)).map toElements = messages.map toElements ∧
      HintReadFixtures.balanced (physicalLedger instructions "sp1.native.host_call" ++ ledger) = true ∧
      HintReadFixtures.balanced (physicalLedger instructions "sp1.native.host_call" ++ ledger.drop 1) = false ∧
      HintReadFixtures.balanced (physicalLedger instructions "sp1.native.host_call" ++ ledger ++ ledger.take 1) = false := by
  native_decide

end SP1CleanTest.Core.HostCall
