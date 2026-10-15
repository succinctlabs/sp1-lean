import SP1Clean.Proofs.Chips.HostCallChip.Populate
import SP1Clean.Model.SP1Field
import SP1Clean.Math.Address
import ToClean.Air.FiniteLookup

/-! # Executing native host-circuit regressions

Evaluate complete witness programs, local assertions, and the fixed syscall lookup. Byte and
Memory and host-read guarantees are checked directly; Program messages must be the fixture's canonical ECALL
at the supplied address (default `2^16`). Structural-channel messages are retained for each test's ledger assertions.
These fixture checks do not assert whole-machine balance or authentic boot-memory contents.
-/

namespace SP1CleanTest.Core.HostChecks

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core

private abbrev Fp := ZMod SP1Prime
abbrev Ledger := List (String × List Fp × Fp)

private instance byteDecidable (op : ByteOpcode) (a b c : Fp) : Decidable (op.constrain a b c) := by
  cases op <;> unfold ByteOpcode.constrain <;> infer_instance

private def byteValid (values : List Fp) : Bool :=
  match values with
  | [opcode, a, b, c] =>
    [ByteOpcode.AND, .OR, .XOR, .U8Range, .LTU, .MSB, .Range].any fun op =>
      opcode == (op.idx : Fp) && decide (op.constrain a b c)
  | _ => false

def evaluateProgram (program : Circuit Fp Unit) (inputs : List Fp)
    (corrupt : Option ℕ := none) (lookups : List (FiniteLookup Fp) := [])
    (programAddress : ℕ := 2 ^ 16) : Bool × Ledger :=
  let honest := (program.proverEnvironment (ProverHint.empty Fp) inputs).toEnvironment
  let env : Environment Fp := { honest with get := fun i =>
    if corrupt == (some (i - inputs.length)) && inputs.length ≤ i then honest.get i + 1 else honest.get i }
  let operations := (program.operations inputs.length).toFlat
  let fixed := FiniteLookup.ofStatic (SyscallKind.fixedTable (p := SP1Prime))
  let valid := operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup lookup => (fixed :: lookups).any fun table => lookup.table.name == table.table.name &&
      table.rows.any (fun row => row.toArray == (lookup.entry.map env).toArray)
    | .witness .. => true
    | .interact interaction =>
      if env interaction.mult == 0 then true
      else if interaction.channel.name == "SP1Byte" then byteValid (interaction.msg.map env).toList
      else if interaction.channel.name == "SP1Memory" then
        match (interaction.msg.map env).toList with
        | [_, low, _, _, _, a, b, c, d] =>
          low.val < 2 ^ 24 && [a, b, c, d].all (fun limb => limb.val < 65536)
        | _ => false
      else if interaction.channel.name == "SP1Program" then
        (interaction.msg.map env).toList ==
          (Address.ofNat programAddress).toList ++ [50, 5, 10, 0, 0, 0, 11, 0, 0, 0, 0, 0, 0]
      else if interaction.channel.name == "sp1.native.host_ram_read" then
        match (interaction.msg.map env).toList with
        | [_, _, addr0, addr1, addr2, a, b, c, d] =>
          let address := addr0.val + addr1.val * 65536 + addr2.val * 65536 ^ 2
          [addr0, addr1, addr2, a, b, c, d].all (fun limb => limb.val < 65536) &&
            65536 ≤ address && address < 2 ^ 48 && address % 8 == 0
        | _ => false
      else if interaction.channel.name == "sp1.native.host_buffer32" then
        match (interaction.msg.map env).toList with
        | _ :: _ :: a :: b :: c :: d :: bytes =>
          let address := a.val + b.val * 65536 + c.val * 65536 ^ 2 + d.val * 65536 ^ 3
          [a, b, c, d].all (fun limb => limb.val < 65536) &&
            65536 ≤ address && address + 32 ≤ 2 ^ 48 && bytes.length == 32 &&
            bytes.all (fun byte => byte.val < 256)
        | _ => false
      else if interaction.channel.name == "sp1.native.hint_node" then
        match (interaction.msg.map env).toList with
        | [a, b, c, d, e, f, w, x, y, z] =>
          [a, b, c, d, e, f, w, x, y, z].all (fun limb => limb.val < 65536) &&
            d.val + e.val * 65536 + f.val * 65536 ^ 2 <
              a.val + b.val * 65536 + c.val * 65536 ^ 2
        | _ => false
      else if interaction.channel.name == "sp1.native.hint_word" then
        match (interaction.msg.map env).toList with
        | [a, b, c, d, e, f, w, x, y, z, last] =>
          [a, b, c, d, e, f, w, x, y, z].all (fun limb => limb.val < 65536) &&
            0 < a.val + b.val * 65536 + c.val * 65536 ^ 2 && (last == 0 || last == 1)
        | _ => false
      else ["sp1.native.hint_queue_state", "sp1.native.hint_read_state", "SP1WritePermission",
        "SP1State", "SP1Exit", "SP1HostExit", "SP1Syscall", "SP1PublicValues", "sp1.native.host_call",
        "sp1.native.commit_state", "sp1.native.deferred_state", "sp1.native.host_ram_access",
        "SP1OrdinaryStateReceipt", "SP1OrdinaryObservation"].contains
          interaction.channel.name
  (valid, (FlatOperation.interactions operations).filterMap fun interaction =>
    if env interaction.mult == 0 then none else
      some (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult))
end SP1CleanTest.Core.HostChecks
