import SP1CleanTest.Alignment.Audit.OneAddNativePremises
import SP1Clean.Soundness.ProtectedLocalCore
import SP1Clean.Model.Core.SyscallTable
import ToClean.Air.FiniteLookup
import SP1CleanTest.Core.StaticMembership

/-! # Shared ADD fixture and actual AIR evaluator

Test support for local-core regressions, host extensions, and the talk runner. All assertions,
fixed lookups, and interaction messages come from the actual component programs.
-/

namespace SP1CleanTest.Core.LocalCore.Fixture

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core SP1Clean.Soundness SP1Clean.Soundness.Target

abbrev Fp := ZMod SP1Prime
abbrev Row := ℕ × List Fp
abbrev Ledger := List (String × List Fp × Fp)

def image : ProgramImage := ⟨[(65536, 0x003100b3)], 65536, []⟩

def source : ExecutionSnapshot where
  sail := { registers := ((configuredState 65536).regs.insert .x2 100).insert .x3 23
            memory := image.initialMemory }
  host := {}
  clock := 9

def snapshot : MemorySnapshot := source.sail.memorySnapshot

def publicInput : SP1PublicIO Fp where
  init_clk_0_16 := 9
  init_clk_16_24 := 0
  init_clk_24_32 := 0
  init_clk_32_48 := 0
  init_pc0 := 0
  init_pc1 := 1
  init_pc2 := 0
  final_clk_0_16 := 17
  final_clk_16_24 := 0
  final_clk_24_32 := 0
  final_clk_32_48 := 0
  final_pc0 := 4
  final_pc1 := 1
  final_pc2 := 0
  exit_code := 0
  is_execution_shard := 1
  committed_value_digest := Vector.replicate 32 0

def word (value : ℕ) : Word Fp := bitVecToWord (BitVec.ofNat 64 value)

def sourceRegister (previous index : ℕ) : Row :=
  (0, (toElements (OrderedSnapshotProvider.populate
    (SnapshotRegisterProvider.populate snapshot (BitVec.ofNat 5 index)) previous index)).toList)

def sourceRam : Row :=
  (1, (toElements (OrderedSnapshotProvider.populate
    (word 65536) 4 65536)).toList)

def terminal (table previous : ℕ) : Row :=
  (table, (toElements (OrderedBoundaryEnd.populate (word previous)
    (OrderedMemoryEnsemble.endKey (p := SP1Prime)))).toList)

def finalRecord (previous address clock value : ℕ) (epoch : ℕ := 0) : List Fp :=
  (toElements (OrderedMemoryProvider.populate
    (⟨epoch, clock, (word address)[0], (word address)[1], (word address)[2], word value⟩ : Channels.MemoryMsg Fp)
    previous address)).toList

def programRow : Row :=
  (6, ((DecodedProgramProvider.populate? (p := SP1Prime) image (65536, 0x003100b3) 1).map
    (fun input => (toElements input).toList)).getD [])

def baseRows : List Row :=
  [sourceRegister 0 1, sourceRegister 2 2, sourceRegister 3 3, sourceRam, terminal 2 65537,
    (3, finalRecord 0 1 13 123), (3, finalRecord 2 2 12 100), (3, finalRecord 3 3 11 23),
    (4, finalRecord 4 65536 0 (snapshot.memory.readWord 65536).toNat), terminal 5 65537,
    programRow, (7, Audit.OneAddNativePremises.inputs),
    (57, List.replicate (size HaltChip.Inputs) 0)]

def withoutRam : List Row :=
  baseRows.filter (fun row => !([1, 2, 4, 5].contains row.1)) ++ [terminal 2 4, terminal 5 4]

def evaluate (image : ProgramImage) (_source : ExecutionSnapshot) (component : Component Fp) (inputs : List Fp)
    (extraLookups : List (FiniteLookup Fp) := []) : Bool × Ledger :=
  let program := component.circuit.main component.rowInputVar
  let env := (program.proverEnvironment (ProverHint.empty Fp) inputs).toEnvironment
  let operations := (program.operations component.rowOffset).toFlat
  let fixed := [FiniteLookup.ofStatic (image.programTable (p := SP1Prime)),
    FiniteLookup.ofStatic (image.writePermissionTable (p := SP1Prime)),
    FiniteLookup.ofStatic (SyscallKind.fixedTable (p := SP1Prime))] ++ extraLookups
  let valid := inputs.length == component.rowOffset && operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup lookup => fixed.any fun table => lookup.table.name == table.table.name &&
        table.rows.any (fun row => row.toArray == (lookup.entry.map env).toArray)
    | .witness .. | .interact .. => true
  (valid, (FlatOperation.interactions operations).map fun interaction =>
    (interaction.channel.name, (interaction.msg.map env).toList, env interaction.mult))

/-- One real provider row for each Byte demand. Provider input shapes are checked at their actual
table indices; unused families are empty. The fixture needs U8Range, LTU, MSB, and fixed Range. -/
def byteProvider (entry : String × List Fp × Fp) : Option Row :=
  if entry.1 != "SP1Byte" || entry.2.2 == 0 then none else
  match entry.2.1 with
  | [opcode, a, b, c] =>
    if opcode == 3 then some (32, [b, c, -entry.2.2])
    else if opcode == 4 then some (37, [b, c, -entry.2.2])
    else if opcode == 5 then some (33, [b, -entry.2.2])
    else if opcode == 6 && b.val < 17 then some (38 + b.val, [a, -entry.2.2])
    else some (60, [])
  | _ => some (60, [])

end SP1CleanTest.Core.LocalCore.Fixture
