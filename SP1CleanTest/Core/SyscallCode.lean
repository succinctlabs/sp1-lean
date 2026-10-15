import SP1Clean.Proofs.Chips.CoreSyscallChip.Formal
import SP1Clean.Model.SP1Field
import ToClean.Air.FiniteLookup
import Clean.Circuit.WitnessExport

/-! # Native syscall profile and finite-lookup regressions

Run the guard's actual flattened assertions and its canonical finite lookup realization.
The whole-chip lookup is checked separately to catch wiring mistakes in the composition.
These local checks make no claim about host effects or whole-ensemble balance.
-/

namespace SP1CleanTest.Core.SyscallCode

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core

private abbrev Fp := ZMod SP1Prime

private def fixed : FiniteLookup Fp := FiniteLookup.ofStatic SyscallKind.fixedTable

private def contains (lookup : Lookup Fp) (env : Environment Fp) : Bool :=
  lookup.table.name == fixed.table.name && lookup.table.arity == fixed.table.arity &&
    fixed.rows.any (fun row => row.toArray == (lookup.entry.map env).toArray)

private def accepts (input : SyscallCodeGuard.Inputs Fp) : Bool :=
  let program := SyscallCodeGuard.main (varFromOffset SyscallCodeGuard.Inputs 0)
  let env := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  (program.operations (size SyscallCodeGuard.Inputs)).toFlat.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .lookup lookup => contains lookup env
    | .witness .. | .interact .. => true

/-- The exported fixed rows are exactly the eight canonical full words, in profile order. -/
theorem exportedInventory :
    fixed.rows.map (fun row => row.toArray.map (·.val)) =
      [#[0, 0, 0, 0], #[2, 0, 0, 0], #[3, 0, 0, 0], #[16, 0, 0, 0],
       #[26, 0, 0, 0], #[27, 0, 0, 0], #[240, 0, 0, 0], #[241, 0, 0, 0]] := by native_decide

/-- Every supported full code is accepted; selection is independent of witness-supplied tables. -/
theorem supportedCodes :
    SyscallKind.all.all (fun kind => accepts ⟨kind.encode, 1⟩) = true := by native_decide

/-- Unsupported low codes, dispatched-to-core codes, upper-limb aliases, and nonboolean gates fail. -/
theorem rejectedCodes :
    ([1, 4, 5, 0x01010005, 0x100000002, 0x100000003, 0x1000000f1, 0x100000000000002] :
      List (BitVec 64)).all (fun code => !accepts ⟨Soundness.Target.bitVecToWord code, 1⟩) = true ∧
    accepts ⟨#v[2, 0, 0, 0], 2⟩ = false ∧
    accepts ⟨#v[2, 65536, 0, 0], 1⟩ = false := by native_decide

/-- Padding imposes no code bound, but still checks that its gate is boolean. -/
theorem padding : accepts ⟨#v[65536, 91, 123, 90000], 0⟩ = true := by native_decide

private def chipLookupsAccept (code : Word Fp) : Bool :=
  let input : SyscallInstrsChip.Inputs Fp :=
    { (fromElements (Vector.replicate (size SyscallInstrsChip.Inputs) 0)) with
      op_a_memory := ⟨code, ⟨0, 0⟩⟩, is_real := 1 }
  let program := CoreSyscallChip.circuit.main (varFromOffset SyscallInstrsChip.Inputs 0)
  let env := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  let lookups := (program.operations (size SyscallInstrsChip.Inputs)).lookups
  lookups.length == 1 && lookups.all (fun lookup => contains lookup env)

/-- The complete chip wires its one fixed lookup to the prior x5 word, across all four limbs.
The synthetic rows here test lookup wiring only, not the other instruction constraints. -/
theorem chipProfileWiring :
    SyscallKind.all.all (fun kind => chipLookupsAccept kind.encode) = true ∧
    chipLookupsAccept #v[3, 0, 1, 0] = false ∧
    chipLookupsAccept #v[4, 0, 0, 0] = false := by native_decide

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (SyscallCodeGuard.circuit (p := SP1Prime))

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (CoreSyscallChip.circuit (p := SP1Prime))

end SP1CleanTest.Core.SyscallCode
