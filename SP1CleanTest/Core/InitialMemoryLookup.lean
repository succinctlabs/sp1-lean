import SP1Clean.Native.Operations.InitialMemoryLookup
import SP1Clean.Model.SP1Field
import Clean.Circuit.WitnessExport

/-! # Initial-memory AIR regressions

These checks run the circuit's witness program and evaluate its actual flattened assertions and
membership pulls. Interaction balance belongs to the ensemble tests. The negative cases distinguish
fixed-row authentication from address containment: either can fail while the other still holds.
-/

namespace SP1CleanTest.Core.InitialMemoryLookup

open Circuit SP1Clean SP1Clean.Model.Core SP1Clean.InitialMemoryLookup
open SP1Clean.Soundness.Target

private abbrev Fp := ZMod SP1Clean.SP1Prime

private def memory : ByteMemory := ⟨[(7, 42), (0, 13), (7, 9), (15, 255)]⟩

/-- info: exportable ✓ (89 witness cells) -/
#guard_msgs in
#assert_exportable (circuit (p := SP1Clean.SP1Prime) memory 16 (by norm_num))

/-- Evaluate flattened assertions and concrete initial-memory membership; balance is checked separately. -/
def localConstraints (memory : ByteMemory) (limit : ℕ) (env : Environment Fp)
    (operations : List (FlatOperation Fp)) : Bool :=
  operations.all fun operation =>
    match operation with
    | .assert expression => env expression == 0
    | .interact interaction =>
      if interaction.channel.name == "sp1.native.initial_memory" then
        (memory.intervals limit).any fun interval =>
          (toElements (interval.encode (p := SP1Clean.SP1Prime))).toList ++ [1] ==
            (interaction.msg.map env).toList
      else true
    | .lookup .. => false
    | .witness .. => true

/-- Mutations replace the selected interval and recompute honest comparison columns. This lets
containment failures remain distinct from forged fixed-row payloads. -/
private def check (image : ByteMemory) (limit address : ℕ)
    (replacement : Option MemoryInterval := none) : Bool × Fp :=
  let input : Word Fp := bitVecToWord (BitVec.ofNat 64 address)
  let vars : Var Word Fp := varFromOffset Word 0
  let program := main image limit vars
  let start := size Word
  let honest := (program.proverEnvironment (ProverHint.empty Fp) (toElements input).toList).toEnvironment
  let changes : List (ℕ × Fp) := match replacement with
    | none => []
    | some interval =>
      let row : MemoryIntervalRow Fp := interval.encode
      let lowerStart := start + size MemoryIntervalRow + WordRangeCheck.circuit.localLength vars
      (toElements row).toList.zipIdx start |>.map Prod.swap |>.append
        (((toElements (LtOperationUnsigned.populate input row.lower)).toList.zipIdx lowerStart).map Prod.swap) |>.append
        (((toElements (LtOperationUnsigned.populate input row.upper)).toList.zipIdx
          (lowerStart + size Circuits.Types.LtOperationUnsigned)).map Prod.swap)
  let env : Environment Fp := { honest with get := fun i => (changes.lookup i).getD (honest.get i) }
  (localConstraints image limit env (program.operations start).toFlat, env (program.output start))

/-- Every bounded input constructs a valid row and returns the expected sparse-memory byte. -/
theorem constructedRows :
    (List.range 16).map (fun address =>
      let result := check memory 16 address
      (result.1, result.2.val)) =
    [(true, 13), (true, 0), (true, 0), (true, 0), (true, 0), (true, 0), (true, 0), (true, 42),
     (true, 0), (true, 0), (true, 0), (true, 0), (true, 0), (true, 0), (true, 0), (true, 255)] := by
  native_decide

/-- A forged byte, a genuine but non-containing interval, and its exclusive upper endpoint fail. -/
theorem rejectsForgedRows :
    [(check memory 16 7 (some ⟨7, 8, 99⟩)).1,
      (check memory 16 6 (some ⟨7, 8, 42⟩)).1,
      (check memory 16 8 (some ⟨7, 8, 42⟩)).1] = [false, false, false] := by
  native_decide

example : (check memory 16 16).1 = false := by native_decide

example : (check memory (2 ^ 48) (2 ^ 48 - 1)).1 = true ∧
    (check memory (2 ^ 48) (2 ^ 48 - 1)).2 = 0 := by native_decide

example : (check memory (2 ^ 48) (2 ^ 48)).1 = false := by native_decide

end SP1CleanTest.Core.InitialMemoryLookup
