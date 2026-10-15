import SP1Clean.Proofs.Chips.HostRamAccessChip.Ledger
import SP1Clean.Proofs.Chips.HostRamAccessChip.Populate
import SP1Clean.Model.Semantics.Decode
import SP1Clean.Model.SP1Field
import Clean.Circuit.WitnessExport

/-! # Executed host RAM access regressions

Run the actual witness program, assertions, and Byte and Memory pull guarantees. These local
tests retain both ledgers; they do not assert whole-ensemble balance or host-call authorization.
-/

namespace SP1CleanTest.Core.HostRamAccess

open Circuit SP1Clean SP1Clean.HostRamAccessChip SP1Clean.Soundness.Target

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

private def evaluate (input : Inputs Fp) : Bool × List (String × List Fp × Fp) :=
  let program := HostRamAccessChip.main (varFromOffset Inputs 0)
  let env := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  let operations := (program.operations (size Inputs)).toFlat
  let valid := operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup _ => false
    | .witness .. => true
    | .interact interaction =>
      if env interaction.mult == 0 then true
      else if interaction.channel.name == "SP1Byte" then byteValid (interaction.msg.map env).toList
      else if interaction.channel.name == "SP1Memory" then memoryValid (interaction.msg.map env).toList
      else interaction.channel.name == "sp1.native.host_ram_access"
  (valid, ((FlatOperation.interactions operations).filter fun interaction =>
    interaction.channel.name != "SP1Byte").map fun interaction =>
      (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult))

private def row (address : ℕ) (previousHigh previousLow high low0 low1 : Fp) : Inputs Fp :=
  let key : Word Fp := bitVecToWord (BitVec.ofNat 64 address)
  populate ⟨previousHigh, previousLow, key[0], key[1], key[2], #v[1, 2, 3, 4]⟩
    high low0 low1 #v[5, 6, 7, 8]

/-- Valid RAM words include limb boundaries and the final cell; both timestamp branches run. -/
theorem validTransfers :
    [row 65536 0 0 0 1 0, row 65544 4 16777215 5 1 0,
      { (row 65536 0 0 0 1 0) with new_value := #v[1, 2, 3, 4] },
      row 131072 5 65535 5 1 1,
      row (2 ^ 48 - 8) 16777215 16777208 16777215 65529 255].all
      (fun input => (evaluate input).1) = true := by native_decide

/-- Address and word checks reject aliases, misalignment, and either malformed word. -/
theorem rejectsMalformedWords :
    [row 32 0 0 0 1 0, row 65537 0 0 0 1 0,
      { (row 65536 0 0 0 1 0) with addr2 := 65536 },
      { (row 65536 0 0 0 1 0) with new_value := #v[65536, 0, 0, 0] },
      { (row 65536 0 0 0 1 0) with
        access := ⟨#v[65536, 0, 0, 0], ⟨0, 0, 1, 1, 0⟩⟩ }].all
      (fun input => !(evaluate input).1) = true := by native_decide

/-- Equal/reversed clocks, field-underflow aliases, and noncanonical current clocks fail. -/
theorem rejectsMalformedTimes :
    [row 65536 0 2 0 1 0, row 65536 0 3 0 1 0,
      row 65536 (-1) 0 0 1 0, row 65536 0 16777216 1 1 0,
      row 65536 0 0 16777216 1 0, row 65536 0 0 0 2 0, row 65536 0 0 0 1 256,
      { (row 65536 0 0 0 1 0) with access := ⟨#v[1, 2, 3, 4], ⟨0, -1, 1, 2, 0⟩⟩ },
      { (row 65536 0 0 0 1 0) with access := ⟨#v[1, 2, 3, 4], ⟨0, 0, 2, 1, 0⟩⟩ }].all
      (fun input => !(evaluate input).1) = true := by native_decide

/-- The host record uses the event clock; Memory uses the prior clock and event clock plus one. -/
theorem retainedLedgers : (evaluate (row 65536 0 0 0 1 0)).2 =
    [("SP1Memory", [0, 0, 0, 1, 0, 1, 2, 3, 4], -1),
     ("SP1Memory", [0, 2, 0, 1, 0, 5, 6, 7, 8], 1),
     ("sp1.native.host_ram_access", [0, 1, 0, 1, 0, 1, 2, 3, 4, 5, 6, 7, 8], 1)] := by
  native_decide

/-- info: exportable ✓ (201 witness cells) -/
#guard_msgs in
#assert_exportable (HostRamAccessChip.circuit (p := SP1Prime))

end SP1CleanTest.Core.HostRamAccess
