import SP1Clean.Native.Operations.InitialMemoryRead
import SP1CleanTest.Core.InitialMemoryLookup

/-! # Whole-word initial-memory AIR regressions

The checked words cross sparse-image gaps and a 16-bit address-limb boundary. Invalid byte-row
routing is tested against the actual flattened addition constraints, even though each byte row
individually authenticates a real initial-memory byte.
-/

namespace SP1CleanTest.Core.InitialMemoryRead

open Circuit SP1Clean SP1Clean.Model.Core SP1Clean.InitialMemoryRead

private abbrev Fp := ZMod SP1Clean.SP1Prime

private def memory : ByteMemory := ⟨[(7, 42), (0, 13), (65535, 255), (65536, 17)]⟩

/-- info: exportable ✓ (740 witness cells) -/
#guard_msgs in
#assert_exportable (circuit (p := SP1Clean.SP1Prime) memory)

private def evaluate (address : ℕ) (wrongOffset : Bool := false) : Bool × BitVec 64 :=
  let input : Word Fp := SP1Clean.Soundness.Target.bitVecToWord (BitVec.ofNat 64 address)
  let vars := varFromOffset Word 0
  let program := main memory vars
  let honest := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  -- Clone the first byte's address and complete witness into the second byte's slots.
  -- Its membership and containment remain valid, but the base+1 addition must fail.
  let byteWidth := size Word +
    (SP1Clean.InitialMemoryLookup.circuit (p := SP1Clean.SP1Prime) memory (2 ^ 48) (by norm_num)).localLength vars
  let replacement (i : ℕ) :=
    if wrongOffset && byteWidth ≤ i && i < 2 * byteWidth then honest.get (i - byteWidth)
    else honest.get i
  let env : Environment Fp := { honest with get := replacement }
  (InitialMemoryLookup.localConstraints memory (2 ^ 48) env (program.operations (size Word)).toFlat,
    SP1Clean.Word.toBitVec64 (ProvableType.eval env (program.output (size Word))))

/-- The circuit-generated words pass the AIR checks and equal the independently defined memory read. -/
theorem constructedWordRows : [0, 1, 7, 65532, 2 ^ 48 - 8].all (fun address =>
    evaluate address == (true, memory.readWord address)) = true := by
  native_decide

/-- Reusing a valid byte at the wrong position fails the circuit's address-link constraints. -/
theorem rejectsWrongOffset : (evaluate 0 true).1 = false := by native_decide

/-- The final complete word is accepted; crossing the address limit fails the actual constraints. -/
theorem wordFootprint : [2 ^ 48 - 8, 2 ^ 48 - 7, 2 ^ 48].map (fun address =>
    (evaluate address).1) = [true, false, false] := by native_decide

example : [2 ^ 48 - 8, 2 ^ 48 - 7, 2 ^ 48].map (fun address =>
    (populate? (p := SP1Clean.SP1Prime) address).isSome) = [true, false, false] := by
  native_decide

end SP1CleanTest.Core.InitialMemoryRead
