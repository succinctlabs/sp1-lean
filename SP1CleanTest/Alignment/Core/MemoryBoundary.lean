import SP1Clean.Proofs.Chips.OrderedInitialProvider
import SP1CleanTest.Core.InitialMemoryLookup
import SP1Clean.Soundness.InitialMemoryEnsemble
import SP1Clean.Soundness.FinalMemoryEnsemble
import SP1Clean.Soundness.NativeCoreBoundaries
import SP1Clean.Soundness.LocalCoreBoundaries

/-! # Initial/final records and ordered-key AIR regressions

These checks execute the actual witness programs, evaluate every assertion and initial-image
lookup, and validate every nonzero Byte interaction against the byte-op semantics. Memory and
ordering interactions are retained for the separate whole-ensemble balance argument.
-/

namespace SP1CleanTest.Core.MemoryBoundary

open Circuit SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target

private abbrev Fp := ZMod SP1Prime

private def image : ProgramImage :=
  ⟨[(65536, 0x00000013)], 65536, [(65543, 171), (131071, 255)]⟩

private instance byteDecidable (op : ByteOpcode) (a b c : Fp) : Decidable (op.constrain a b c) := by
  cases op <;> unfold ByteOpcode.constrain <;> infer_instance

private def byteValid (values : List Fp) : Bool :=
  match values with
  | [opcode, a, b, c] =>
    [ByteOpcode.AND, .OR, .XOR, .U8Range, .LTU, .MSB, .Range].any fun op =>
      opcode == (op.idx : Fp) && decide (op.constrain a b c)
  | _ => false

private def evaluate {Input : TypeMap} [ProvableType Input]
    (program : Var Input Fp → Circuit Fp (Var Channels.MemoryMsg Fp))
    (input : Input Fp) : Bool × List Fp :=
  let circuit := program (varFromOffset Input 0)
  let env := (circuit.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  let operations := (circuit.operations (size Input)).toFlat
  let bytes := (FlatOperation.interactions operations).all fun interaction =>
    interaction.channel.name != "SP1Byte" || env interaction.mult == 0 ||
      byteValid (interaction.msg.map env).toList
  (InitialMemoryLookup.localConstraints image.initialMemory (2 ^ 48) env operations && bytes,
    (toElements (ProvableType.eval env (circuit.output (size Input)))).toList)

private def word (address : ℕ) : Word Fp := bitVecToWord (BitVec.ofNat 64 address)

private def ramInput (previous address current : ℕ) :
    OrderedInitialProvider.Inputs Word Fp :=
  ⟨word address,
    OrderedBoundary.populate (word previous) (word current)⟩

private def registerInput (previous index current : ℕ) : OrderedInitialProvider.Inputs field Fp :=
  ⟨index, OrderedBoundary.populate (word previous) (word current)⟩

/-- info: exportable ✓ (872 witness cells) -/
#guard_msgs in
#assert_exportable (OrderedInitialProvider.ramCircuit (p := SP1Prime) image)

/-- info: exportable ✓ (133 witness cells) -/
#guard_msgs in
#assert_exportable (OrderedInitialProvider.registerCircuit (p := SP1Prime) image)

/-- Valid ordered RAM rows cross limb boundaries and reach the last aligned guest cell. -/
theorem constructedRamRows : [65536, 131064, 131072, 2 ^ 48 - 8].all (fun address =>
    ((OrderedSnapshotProvider.populateRam? 32 address).map fun input =>
      let result := evaluate (OrderedInitialProvider.ramCircuit image).main input
      result.1 && (result.2 ==
        ([(0 : Fp), 0, (word address)[0], (word address)[1], (word address)[2]] ++
          (bitVecToWord (p := SP1Prime) (image.initialMemory.readWord address)).toList))).getD false) = true := by
  native_decide

/-- All 32 register indices emit their exact zero-valued, zero-time boundary messages. -/
theorem constructedRegisterRows : (List.range 32).all (fun index =>
    evaluate (OrderedInitialProvider.registerCircuit image).main (registerInput index index (index + 1)) ==
      (true, [0, 0, (index : Fp), 0, 0, 0, 0, 0, 0])) = true := by
  native_decide

/-- The ordered key cannot be changed independently of the authenticated Memory record. -/
theorem rejectsUnrelatedKeys :
    [(evaluate (OrderedInitialProvider.ramCircuit image).main (ramInput 32 65536 65538)).1,
     (evaluate (OrderedInitialProvider.registerCircuit image).main (registerInput 0 0 2)).1] =
      [false, false] := by native_decide

/-- Equal/reversed links, reserved or misaligned RAM, and out-of-range registers fail the AIR. -/
theorem rejectsInvalidBoundaryRows :
    [(evaluate (OrderedInitialProvider.ramCircuit image).main (ramInput 65537 65536 65537)).1,
     (evaluate (OrderedInitialProvider.ramCircuit image).main (ramInput 65538 65536 65537)).1,
     (evaluate (OrderedInitialProvider.ramCircuit image).main (ramInput 0 32 33)).1,
     (evaluate (OrderedInitialProvider.ramCircuit image).main (ramInput 0 65537 65538)).1,
     (evaluate (OrderedInitialProvider.registerCircuit image).main (registerInput 0 32 33)).1] =
      [false, false, false, false, false] := by native_decide

private def controlRow {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (program : Var Input Fp → Circuit Fp (Var Output Fp)) (input : Input Fp)
    (channelName : String := OrderedInitialProvider.channelName) :
    Bool × List (List Fp × Fp) :=
  let circuit := program (varFromOffset Input 0)
  let env := (circuit.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  let operations := (circuit.operations (size Input)).toFlat
  let interactions := FlatOperation.interactions operations
  let bytes := interactions.all fun interaction =>
    interaction.channel.name != "SP1Byte" || env interaction.mult == 0 ||
      byteValid (interaction.msg.map env).toList
  (InitialMemoryLookup.localConstraints image.initialMemory (2 ^ 48) env operations && bytes,
    (interactions.filter (fun interaction => interaction.channel.name == channelName)).map
      (fun interaction => ((interaction.msg.map env).toList, env interaction.mult)))

private def controlValid (rows : List (Bool × List (List Fp × Fp))) : Bool :=
  let interactions := rows.flatMap Prod.snd
  rows.all Prod.fst && decide (interactions.length < SP1Prime) &&
    interactions.all fun (message, _) =>
      ((interactions.filter (fun interaction => interaction.1 == message)).map Prod.snd).sum == 0

private def verifierRow : Bool × List (List Fp × Fp) :=
  controlRow (OrderedBoundaryVerifier.circuit OrderedInitialProvider.channelName
    (Soundness.InitialMemoryEnsemble.startKey (p := SP1Prime))
    Soundness.InitialMemoryEnsemble.endKey).main ()

private def terminalRow (previous : ℕ) : Bool × List (List Fp × Fp) :=
  controlRow (OrderedBoundaryEnd.circuit OrderedInitialProvider.channelName
    (Soundness.InitialMemoryEnsemble.endKey (p := SP1Prime))).main
      (OrderedBoundaryEnd.populate (word previous) Soundness.InitialMemoryEnsemble.endKey)

private def initRegisterRow (previous index : ℕ) :=
  controlRow (OrderedInitialProvider.registerCircuit (p := SP1Prime) image).main
    (registerInput previous index (index + 1))

/-- info: exportable ✓ (128 witness cells) -/
#guard_msgs in
#assert_exportable (OrderedBoundaryEnd.circuit (p := SP1Prime) OrderedInitialProvider.channelName
  Soundness.InitialMemoryEnsemble.endKey)

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (OrderedBoundaryVerifier.circuit (p := SP1Prime) OrderedInitialProvider.channelName
  Soundness.InitialMemoryEnsemble.startKey Soundness.InitialMemoryEnsemble.endKey)

/-- The actual fixed verifier and terminal balance an empty inventory without padding rows. -/
theorem emptyInventory : controlValid [verifierRow, terminalRow 0] = true := by native_decide

/-- Register and RAM rows coordinate through their actual shared ledger, independent of physical order. -/
theorem mixedInventory : controlValid
    [verifierRow, initRegisterRow 1 31, initRegisterRow 0 0,
      controlRow (OrderedInitialProvider.ramCircuit image).main (ramInput 32 65536 65537),
      terminalRow 65537] = true := by native_decide

/-- Missing/duplicate terminal rows, duplicate initial records, and a disconnected strict row
fail actual control balance, even though each provider's value is locally authentic. -/
theorem rejectsMalformedInventories :
    [controlValid [verifierRow],
     controlValid [verifierRow, terminalRow 0, terminalRow 0],
     controlValid [verifierRow, initRegisterRow 0 0, initRegisterRow 0 0, terminalRow 1],
     controlValid [verifierRow, initRegisterRow 0 0, initRegisterRow 2 3, terminalRow 1],
     controlValid [verifierRow, terminalRow (2 ^ 48 + 1)]] =
       [false, false, false, false, false] := by native_decide

private def finalRecord (address value clock : ℕ) : Channels.MemoryMsg Fp :=
  ⟨((clock / 4 : ℕ) : Fp), ((clock % 4 : ℕ) : Fp), (word address)[0], (word address)[1], (word address)[2],
    word value⟩

private def finalInput (previous address current value clock : ℕ) :
    OrderedMemoryProvider.Inputs Channels.MemoryMsg Fp :=
  ⟨finalRecord address value clock, OrderedBoundary.populate (word previous) (word current)⟩

private def finalVerifierRow :=
  controlRow (OrderedBoundaryVerifier.circuit OrderedFinalProvider.channelName
    (Soundness.OrderedMemoryEnsemble.startKey (p := SP1Prime))
    Soundness.OrderedMemoryEnsemble.endKey).main () OrderedFinalProvider.channelName

private def finalTerminalRow (previous : ℕ) :=
  controlRow (OrderedBoundaryEnd.circuit OrderedFinalProvider.channelName
    (Soundness.OrderedMemoryEnsemble.endKey (p := SP1Prime))).main
      (OrderedBoundaryEnd.populate (word previous) Soundness.OrderedMemoryEnsemble.endKey)
      OrderedFinalProvider.channelName

private def finalRegisterRow (previous index : ℕ) :=
  controlRow OrderedFinalProvider.registerCircuit.main
    (finalInput previous index (index + 1) 9 16) OrderedFinalProvider.channelName

/-- info: exportable ✓ (133 witness cells) -/
#guard_msgs in
#assert_exportable (OrderedFinalProvider.registerCircuit (p := SP1Prime))

/-- info: exportable ✓ (196 witness cells) -/
#guard_msgs in
#assert_exportable (OrderedFinalProvider.ramCircuit (p := SP1Prime))

/-- Finalizer constructors preserve every record field across the register range and RAM boundaries. -/
theorem constructedFinalRows :
    (List.range 32).all (fun index =>
      ((OrderedFinalProvider.populateRegister? 0 (finalRecord index (index + 7) 16)).map fun input =>
        evaluate OrderedFinalProvider.registerCircuit.main input ==
          (true, (toElements (finalRecord index (index + 7) 16)).toList)).getD false) &&
    [65536, 131064, 131072, 2 ^ 48 - 8].all (fun address =>
      ((OrderedFinalProvider.populateRam? 32 (finalRecord address 123 24)).map fun input =>
        evaluate OrderedFinalProvider.ramCircuit.main input ==
          (true, (toElements (finalRecord address 123 24)).toList)).getD false) = true := by
  native_decide

/-- Invalid final addresses and unrelated ordering keys fail the actual circuit constraints. -/
theorem rejectsInvalidFinalRows :
    [(evaluate OrderedFinalProvider.registerCircuit.main (finalInput 0 32 33 9 16)).1,
     (evaluate OrderedFinalProvider.registerCircuit.main (finalInput 0 65536 65537 9 16)).1,
     (evaluate OrderedFinalProvider.registerCircuit.main (finalInput 0 0 2 9 16)).1,
     (evaluate OrderedFinalProvider.ramCircuit.main (finalInput 0 32 33 9 16)).1,
     (evaluate OrderedFinalProvider.ramCircuit.main (finalInput 0 65537 65538 9 16)).1,
     (evaluate OrderedFinalProvider.ramCircuit.main (finalInput 0 65536 65538 9 16)).1] =
      [false, false, false, false, false, false] := by native_decide

/-- Both empty and physically permuted mixed final inventories close their private control bus. -/
theorem finalInventories :
    controlValid [finalVerifierRow, finalTerminalRow 0] &&
    controlValid [finalVerifierRow, finalRegisterRow 1 31, finalRegisterRow 0 0,
      controlRow OrderedFinalProvider.ramCircuit.main (finalInput 32 65536 65537 19 24)
        OrderedFinalProvider.channelName, finalTerminalRow 65537] = true := by native_decide

/-- Finalization cannot duplicate records or borrow initialization's fixed control boundary. -/
theorem rejectsMalformedFinalInventories :
    [controlValid [finalVerifierRow],
     controlValid [finalVerifierRow, finalTerminalRow 0, finalTerminalRow 0],
     controlValid [finalVerifierRow, finalRegisterRow 0 0, finalRegisterRow 0 0, finalTerminalRow 1],
     controlValid [finalVerifierRow, finalRegisterRow 0 0, finalRegisterRow 2 3, finalTerminalRow 1],
     controlValid [controlRow (OrderedBoundaryVerifier.circuit OrderedInitialProvider.channelName
       (Soundness.OrderedMemoryEnsemble.startKey (p := SP1Prime))
       Soundness.OrderedMemoryEnsemble.endKey).main () OrderedFinalProvider.channelName,
       finalTerminalRow 0]] = [false, false, false, false, false] := by native_decide

/-- Initial/final physical Memory ledgers close only when every clock, location, and value agrees. -/
theorem pairedMemoryBoundary :
    let initial := controlRow (OrderedInitialProvider.ramCircuit image).main
      (ramInput 0 65536 65537) "SP1Memory"
    let final (value clock : ℕ) := controlRow OrderedFinalProvider.ramCircuit.main
      (finalInput 0 65536 65537 value clock) "SP1Memory"
    let value := (image.initialMemory.readWord 65536).toNat
    [controlValid [initial, final value 0], controlValid [initial, final (value + 1) 0],
      controlValid [initial, final value 8], controlValid [initial, final value 0, final value 0]] =
      [true, false, false, false] := by native_decide

private def finalMemoryFlags (program : Var Channels.MemoryMsg Fp → Circuit Fp (Var Channels.MemoryMsg Fp)) :
    List (Fp × Bool) :=
  let input := finalRecord 0 0 0
  let circuit := program (varFromOffset Channels.MemoryMsg 0)
  let env := (circuit.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  ((FlatOperation.interactions (circuit.operations (size Channels.MemoryMsg)).toFlat).filter
    (fun interaction => interaction.channel.name == "SP1Memory")).map
      (fun interaction => (env interaction.mult, interaction.assumeGuarantees))

/-- Finalizers consume the exact negative Memory interaction without a local semantic assumption.
Value and clock mismatches are still rejected by the paired full-message ledger above. -/
theorem finalizersDeferMemoryGuarantees :
    finalMemoryFlags FinalRegisterProvider.main = [(-1, false)] ∧
      finalMemoryFlags FinalRamProvider.main = [(-1, false)] := by native_decide

private def bootPublic : SP1PublicIO Fp where
  init_clk_0_16 := 1
  init_clk_16_24 := 0
  init_clk_24_32 := 0
  init_clk_32_48 := 0
  init_pc0 := 0
  init_pc1 := 1
  init_pc2 := 0
  final_clk_0_16 := 9
  final_clk_16_24 := 0
  final_clk_24_32 := 0
  final_clk_32_48 := 0
  final_pc0 := 4
  final_pc1 := 1
  final_pc2 := 0
  exit_code := 0
  is_execution_shard := 1
  committed_value_digest := Vector.replicate 32 0

private def nativeVerifierLedger (pi : SP1PublicIO Fp) :=
  let env := Environment.fromInput pi (fun _ _ => #[])
  (Soundness.NativeCore.ensemble image).verifierOperations.interactions.map
    (AbstractInteraction.eval env)

private def checkedVerifierRow (ledger : List (Interaction Fp)) (checkName name : String) :
    Bool × List (List Fp × Fp) :=
  let bytes := ledger.all fun interaction =>
    interaction.channel.name != "SP1Byte" || byteValid interaction.msg.toList
  let checks := ledger.filter fun interaction => interaction.channel.name == checkName
  let checked := decide (checks.length < SP1Prime) && checks.all fun interaction =>
    ((checks.filter (fun other => other.msg == interaction.msg)).map (·.mult)).sum == 0
  (bytes && checked, (ledger.filter (fun interaction => interaction.channel.name == name)).map
    (fun interaction => (interaction.msg.toList, interaction.mult)))

private def nativeVerifierRow (pi : SP1PublicIO Fp) (name : String) :
    Bool × List (List Fp × Fp) :=
  checkedVerifierRow (nativeVerifierLedger pi)
    (Soundness.NativeCore.bootChannel (p := SP1Prime) image).name name

/-- The installed verifier retains all 19 source occurrences and all ten boot-check occurrences,
including zero-valued checks. It adds no committed table. -/
theorem nativeVerifierInventory :
    (Soundness.NativeCore.ensemble (p := SP1Prime) image).tables.length = 60 ∧
    (nativeVerifierLedger bootPublic).length = 29 ∧
    ((nativeVerifierLedger bootPublic).filter fun interaction =>
      interaction.channel.name == (Soundness.NativeCore.bootChannel (p := SP1Prime) image).name).length = 10 := by
  native_decide

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (Soundness.NativeCore.verifier (p := SP1Prime) image)

/-- The installed public verifier emits both fixed control boundaries while enforcing the boot
fields through its assertion channel and retaining the original Byte requirements. -/
theorem nativeVerifierEndpoints :
    nativeVerifierRow bootPublic OrderedInitialProvider.channelName = verifierRow ∧
    nativeVerifierRow bootPublic OrderedFinalProvider.channelName = finalVerifierRow := by
  native_decide

/-- Wrong boot PC/time and a field-wrapping alternative clock encoding are rejected by the
installed public verifier and its Byte requirements. A matching folded clock alone is insufficient. -/
theorem rejectsForgedBoot :
    [nativeVerifierRow { bootPublic with init_clk_0_16 := 0 } OrderedInitialProvider.channelName,
     nativeVerifierRow { bootPublic with init_clk_24_32 := 1 } OrderedInitialProvider.channelName,
     nativeVerifierRow { bootPublic with init_pc0 := 4 } OrderedInitialProvider.channelName,
     nativeVerifierRow { bootPublic with init_pc1 := 0 } OrderedInitialProvider.channelName,
     nativeVerifierRow { bootPublic with init_clk_0_16 := 65537, init_clk_16_24 := -1 }
       OrderedInitialProvider.channelName].map Prod.fst = [false, false, false, false, false] := by
  native_decide

/-- Both private inventories close using the one composed verifier. Omitting either terminal
or duplicating an initial record fails its actual control ledger. -/
theorem nativeBoundaryInventories :
    let initial := nativeVerifierRow bootPublic OrderedInitialProvider.channelName
    let final := nativeVerifierRow bootPublic OrderedFinalProvider.channelName
    [controlValid [initial, initRegisterRow 0 0, terminalRow 1],
     controlValid [final, finalRegisterRow 0 0, finalTerminalRow 1],
     controlValid [initial, initRegisterRow 0 0],
     controlValid [final, finalRegisterRow 0 0],
     controlValid [initial, initRegisterRow 0 0, initRegisterRow 0 0, terminalRow 1]] =
      [true, true, false, false, false] := by native_decide

private def source : ExecutionSnapshot where
  sail := { registers := (configuredState 65536).regs, memory := image.initialMemory }
  host := {}
  clock := 17

private def localPublic : SP1PublicIO Fp :=
  { bootPublic with init_clk_0_16 := 17, final_clk_0_16 := 25 }

private def localVerifierLedger (snapshot : ExecutionSnapshot) (pi : SP1PublicIO Fp) :=
  let env := Environment.fromInput pi (fun _ _ => #[])
  (Soundness.LocalCore.ensemble image snapshot).verifierOperations.interactions.map
    (AbstractInteraction.eval env)

private def localVerifierRow (snapshot : ExecutionSnapshot) (pi : SP1PublicIO Fp) :
    Bool × List (List Fp × Fp) :=
  checkedVerifierRow (localVerifierLedger snapshot pi)
    (Soundness.LocalCore.sourceChannel (p := SP1Prime) image snapshot).name
    Soundness.SnapshotMemoryEnsemble.channelName

/-- All eight checks survive installation, including zero-valued checks; the 61 committed
tables and the original 19 verifier occurrences remain intact. -/
theorem localVerifierInventory :
    (Soundness.LocalCore.ensemble (p := SP1Prime) image source).tables.length = 61 ∧
    (localVerifierLedger source localPublic).length = 35 ∧
    ((localVerifierLedger source localPublic).filter fun interaction => interaction.channel.name ==
      (Soundness.LocalCore.sourceChannel (p := SP1Prime) image source).name).length = 16 := by
  native_decide

/-- Nonzero-clock continuations and stopped identity segments pass the installed public checks.
A stopped source cannot advance the final clock. -/
theorem localVerifierStoppedClock :
    [(localVerifierRow source localPublic).1,
     (localVerifierRow { source with host.exitCode := some 0 }
       { localPublic with final_clk_0_16 := 17 }).1,
     (localVerifierRow { source with host.exitCode := some 0 } localPublic).1] =
      [true, true, false] := by native_decide

/-- Wrong PC/time, noncanonical clock limbs, unsupported platform mode, and corrupt source ROM
are rejected by the actual installed verifier, independently of the touched Memory inventory. -/
theorem localVerifierRejectsForgedSource :
    [(localVerifierRow source { localPublic with init_clk_0_16 := 18 }).1,
     (localVerifierRow source { localPublic with init_clk_24_32 := 1 }).1,
     (localVerifierRow source { localPublic with init_pc0 := 4 }).1,
     (localVerifierRow source { localPublic with init_pc1 := 0 }).1,
     (localVerifierRow source { localPublic with init_clk_0_16 := 65553, init_clk_16_24 := -1 }).1,
     (localVerifierRow { source with sail.registers := source.sail.registers.insert .misa 4100 }
       localPublic).1,
     (localVerifierRow { source with sail.memory := source.sail.memory.write 65536 0 } localPublic).1] =
      [false, false, false, false, false, false, false] := by native_decide

end SP1CleanTest.Core.MemoryBoundary
