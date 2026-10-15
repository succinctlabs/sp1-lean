import SP1Clean.Native.Operations.FinalRegisterValue
import SP1Clean.Native.Operations.FinalRamValue
import SP1Clean.Native.Operations.FinalMemoryReceipt
import SP1Clean.Native.Operations.FinalRegisterCheck
import SP1Clean.Native.Operations.FinalRamCheck
import SP1Clean.Native.Operations.FinalMemoryChangeBoundary
import SP1Clean.Proofs.Chips.OrderedFinalProvider
import SP1Clean.Model.SP1Field
import Clean.Circuit.WitnessExport
import SP1CleanTest.Core.StaticMembership

/-! # Native target-value checks and complete-record handoff

These run the actual witness programs, assertions, fixed register membership, target RAM
lookups, and Byte semantics.
Receipt balance includes clocks and all value limbs. The original Memory and ordering ledgers
remain available to the enclosing machine; this fixture does not claim a complete mixed AIR.
-/

namespace SP1CleanTest.Core.FinalMemoryValue

open Circuit SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target

private abbrev Fp := ZMod SP1Prime

private def target : MemorySnapshot where
  registers := (Vector.replicate 32 0).set 1 123 |>.set 31 0xffffffffffffffff
  memory := ⟨[(65536, 9), (65539, 0), (65543, 17), (65539, 99), (2 ^ 48 - 1, 255)]⟩

private instance byteDecidable (op : ByteOpcode) (a b c : Fp) : Decidable (op.constrain a b c) := by
  cases op <;> unfold ByteOpcode.constrain <;> infer_instance

private def byteValid (values : List Fp) : Bool :=
  match values with
  | [opcode, a, b, c] =>
    [ByteOpcode.AND, .OR, .XOR, .U8Range, .LTU, .MSB, .Range].any fun op =>
      opcode == (op.idx : Fp) && decide (op.constrain a b c)
  | _ => false

private def localConstraints (snapshot : MemorySnapshot) (env : Environment Fp)
    (operations : List (FlatOperation Fp)) : Bool :=
  operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup lookup =>
      if arity : lookup.table.arity = size MemoryIntervalRow then
        lookup.table.name == "sp1.native.target_memory" && (snapshot.memory.intervals (2 ^ 48)).any fun interval =>
          toElements (interval.encode (p := SP1Prime)) == arity ▸ lookup.entry.map env
      else false
    | .witness .. | .interact .. => true

private def evaluate {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (snapshot : MemorySnapshot) (circuit : GeneralFormalCircuit Fp Input Output) (input : Input Fp) :
    Bool × List (String × List Fp × Fp) :=
  let program := circuit.main (varFromOffset Input 0)
  let env := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  let operations := (program.operations (size Input)).toFlat
  let interactions := FlatOperation.interactions operations
  let bytes := interactions.all fun interaction =>
    interaction.channel.name != "SP1Byte" || env interaction.mult == 0 ||
      byteValid (interaction.msg.map env).toList
  let membership := StaticMembership.check (FinalRegisterValue.membership snapshot)
    (interactions.map fun interaction =>
      (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult))
  (localConstraints snapshot env operations && bytes && membership,
    (interactions.filter fun interaction =>
      interaction.channel.name == "SP1FinalRegisterValue" || interaction.channel.name == "SP1FinalRamValue" ||
        interaction.channel.name == "SP1FinalMemoryChange").map
      fun interaction => (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult))

private def balanced (rows : List (Bool × List (String × List Fp × Fp))) : Bool :=
  let interactions := rows.flatMap Prod.snd
  rows.all Prod.fst && decide (interactions.length < SP1Prime) &&
    interactions.all fun (channel, message, _) =>
      ((interactions.filter fun entry => entry.1 == channel && entry.2.1 == message).map (·.2.2)).sum == 0

private def word (value : ℕ) : Word Fp := bitVecToWord (BitVec.ofNat 64 value)

private def record (address value clock : ℕ) : Channels.MemoryMsg Fp :=
  ⟨((clock / 2 ^ 24 : ℕ) : Fp), ((clock % 2 ^ 24 : ℕ) : Fp), (word address)[0], (word address)[1],
    (word address)[2], word value⟩

private def register : Channels.MemoryMsg Fp := record 1 123 (2 ^ 24 + 8)
private def ram : Channels.MemoryMsg Fp := record 65536 (target.memory.readWord 65536).toNat 264

private def registerRow (value : Channels.MemoryMsg Fp) := evaluate target (FinalRegisterValue.circuit target) value

private def ramRow (snapshot : MemorySnapshot) (value : Channels.MemoryMsg Fp) :=
  evaluate snapshot (FinalRamValue.circuit snapshot) value

private def registerReceipt := evaluate target
  (FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit)
  (OrderedMemoryProvider.populate register 0 1)

private def ramReceipt := evaluate target
  (FinalMemoryReceipt.circuit true OrderedFinalProvider.ramCircuit)
  (OrderedMemoryProvider.populate ram 2 65536)

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (FinalRegisterValue.circuit (p := SP1Prime) target)

/-- info: exportable ✓ (740 witness cells) -/
#guard_msgs in
#assert_exportable (FinalRamValue.circuit (p := SP1Prime) target)

/-- info: exportable ✓ (133 witness cells) -/
#guard_msgs in
#assert_exportable (FinalMemoryReceipt.circuit (p := SP1Prime) false OrderedFinalProvider.registerCircuit)

/-- info: exportable ✓ (196 witness cells) -/
#guard_msgs in
#assert_exportable (FinalMemoryReceipt.circuit (p := SP1Prime) true OrderedFinalProvider.ramCircuit)

/-- Constructors cover nonzero registers, sparse zero gaps, partial words, and the last native word. -/
theorem constructedRows :
    [0, 1, 31].all (fun index =>
      ((FinalRegisterValue.populate? target (record index (target.registers[index % 32]).toNat 17)).map
        fun input => (registerRow input).1).getD false) &&
    [65536, 65544, 2 ^ 48 - 8].all (fun address =>
      ((FinalRamValue.populate? target (record address (target.memory.readWord address).toNat 264)).map
        fun input => (evaluate target (FinalRamValue.circuit target) input).1).getD false) = true := by
  native_decide

/-- Directly forged inputs fail the actual AIR, independently of constructor rejection. -/
theorem rejectsForgedValues :
    [(registerRow { register with value := word 124 }).1,
     (registerRow { register with addr1 := 1 }).1,
     (registerRow { register with addr0 := 32 }).1,
     (ramRow target { ram with value := word 9 }).1,
     (ramRow target { ram with addr0 := 8 }).1,
     (ramRow { target with memory := target.memory.write 65543 18 } ram).1,
     (ramRow target (record (2 ^ 48 - 7) 0 264)).1] =
      [false, false, false, false, false, false, false] := by native_decide

/-- Full-record accounting rejects missing, duplicate, wrong-clock, and wrong-kind consumers. -/
theorem receiptAccounting :
    [balanced [ramRow target ram, registerReceipt, ramReceipt, registerRow register],
     balanced [registerReceipt],
     balanced [registerReceipt, registerRow register, registerRow register],
     balanced [registerReceipt, registerRow { register with clk_low := 9 }],
     balanced [ramReceipt, registerRow register], balanced []] =
      [true, false, false, false, false, true] := by native_decide

private def source : MemorySnapshot :=
  { target with registers := target.registers.set 1 17, memory := target.memory.write 65536 10 }

private def registerCheck (value : Channels.MemoryMsg Fp) (selected : Fp) :=
  evaluate target (FinalRegisterCheck.circuit target) ⟨value, selected⟩

private def ramCheck (value : Channels.MemoryMsg Fp) (selected : Fp) :=
  evaluate target (FinalRamCheck.circuit target)
    ⟨value, selected⟩

private def changes (before after : MemorySnapshot) :=
  evaluate after (FinalMemoryChangeBoundary.closed (p := SP1Prime) before after).circuit ()

/-- All three accounting channels are checked on real rows, including the verifier-owned
complete change demand. Omission, duplication, and unrelated target changes cannot balance. -/
theorem changeCoverage :
    [balanced [registerReceipt, ramReceipt, registerCheck register 1, ramCheck ram 1, changes source target],
     balanced [registerReceipt, ramReceipt, registerCheck register 1, ramCheck ram 0, changes source target],
     balanced [registerReceipt, ramReceipt, registerCheck register 0, ramCheck ram 1, changes source target],
     balanced [registerReceipt, ramReceipt, registerCheck register 1, ramCheck ram 1,
       changes source target, changes source target],
     balanced [registerReceipt, ramReceipt, registerCheck register 1, ramCheck ram 1,
       changes source { target with registers := target.registers.set 2 1 }],
     balanced [registerReceipt, ramReceipt, registerCheck register 0, ramCheck ram 0, changes target target],
     balanced [registerReceipt, ramReceipt, registerCheck register 1, ramCheck ram 0, changes target target],
     balanced [changes target target]] =
      [true, false, false, false, false, true, false, true] := by native_decide

/-- Disabled selectors still validate target bytes and leave their zero-multiplicity
occurrences in the physical ledger. Non-Boolean selectors fail the actual assertions. -/
theorem selectorDiscipline :
    [(registerCheck { register with value := word 124 } 0).1,
     (ramCheck { ram with value := word 9 } 0).1,
     (registerCheck register 2).1,
     (ramCheck ram 2).1] = [false, false, false, false] ∧
      (registerCheck register 0).2.length = 2 ∧
      (ramCheck ram 0).2.length = 2 := by native_decide

/-- A register at numeric address zero cannot supply a changed low-RAM key at address zero. -/
theorem lowRamIsDistinct :
    let value := record 0 0 8
    let receipt := evaluate target
      (FinalMemoryReceipt.circuit false OrderedFinalProvider.registerCircuit)
      (OrderedMemoryProvider.populate value 0 0)
    balanced [receipt, registerCheck value 1,
      changes target { target with memory := target.memory.write 0 1 }] = false := by native_decide

/-- Constructors retain complete target receipts and select exactly the computed change keys. -/
theorem changeConstructors :
    ((FinalRegisterCheck.populate? source target register).map fun input =>
      input.selected == 1 && (evaluate target (FinalRegisterCheck.circuit target) input).1).getD false = true ∧
    ((FinalRamCheck.populate? source target ram).map fun input =>
      input.selected == 1 && (evaluate target (FinalRamCheck.circuit target) input).1).getD false = true := by
  native_decide

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (FinalRegisterCheck.circuit (p := SP1Prime) target)

/-- info: exportable ✓ (740 witness cells) -/
#guard_msgs in
#assert_exportable (FinalRamCheck.circuit (p := SP1Prime) target)

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (FinalMemoryChangeBoundary.closed (p := SP1Prime) source target).circuit

end SP1CleanTest.Core.FinalMemoryValue
