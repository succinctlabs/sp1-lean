import Clean.Circuit.WitnessExport
import SP1CleanTest.Core.HintReadFixtures
/-! # Executed physical hint word coverage

Run the real consumer, fixed source-word lookup, and fixed writable-interval provider. Boundary
fixtures supply a call's cursor endpoints and Memory records from the independent padded write.
Their complete non-Byte ledgers must balance; Byte guarantees are checked on every actual pull.
This exercises the word subsystem, not instruction/queue authorization or mixed-AIR installation.
-/

namespace SP1CleanTest.Core.HintReadWord

open Circuit Air.Flat SP1Clean Model.Core HintQueue HostChecks HintReadFixtures

/-- Empty, partial, and aligned hints balance every physical word and padding transfer. -/
theorem completeWrites : (List.range 18).all (fun length =>
    let actual := bytes length
    check image 65536 actual (rows 65536 actual)) = true := by native_decide

/-- Consumer tables may be reordered; omission or repetition changes the exact cursor inventory. -/
theorem coverageTampering :
    let actual := bytes 16
    let compiled := rows 65536 actual
    check image 65536 actual compiled.reverse = true ∧
      check image 65536 actual (compiled.drop 1) = false ∧
      check image 65536 actual (compiled.take 2) = false ∧
      check image 65536 actual (compiled ++ compiled.take 1) = false := by native_decide

/-- The final complete cell is legal even though its one-past address is outside the key encoding. -/
theorem finalCell : [0, 7, 8, 15, 16].all (fun length =>
    let actual := bytes length
    let address := 2 ^ 48 - 8 * wordCount actual
    check image address actual (rows address actual)) = true := by native_decide

/-- A locally valid row cannot change call clock or node identity along the balanced cursor. -/
theorem callIdentity :
    let actual := bytes 8
    let input := row 65536 actual 0
    let ram := { input.2.ram with
      clk_0_16 := 9
      access := { input.2.ram.access with access_timestamp :=
        { input.2.ram.access.access_timestamp with diff_low_limb := 9 } } }
    let clock := (input.1, { input.2 with ram })
    (checked clock).1 = true ∧ check image 65536 actual (clock :: (rows 65536 actual).drop 1) = false ∧
      check image 65536 actual ((input.1, { input.2 with pointer := Address.ofNat 2 }) ::
        (rows 65536 actual).drop 1) = false := by native_decide

/-- Source authentication rejects forged content and either incorrect end-marker variant. -/
theorem wordTampering :
    let actual := bytes 8
    let first := row 65536 actual 0
    let final := row 65536 actual 1
    let early := (true, HintReadWordChip.populate true first.2.ram first.2.pointer first.2.index)
    let continued := (false, HintReadWordChip.populate false final.2.ram final.2.pointer final.2.index)
    check image 65536 actual [(first.1, { first.2 with ram := { first.2.ram with new_value := 0 } }), final] = false ∧
      (checked early).1 = true ∧ (source actual (early.2.step true).word).1 = false ∧
      (checked continued).1 = true ∧ (source actual (continued.2.step false).word).1 = false ∧
      check image 65536 actual [early, final] = false ∧
      check image 65536 actual [first, continued] = false := by native_decide

/-- Every padding byte requires permission, even when its resulting value is zero. -/
theorem paddingPermission :
    let actual := bytes 8
    let protectedImage : ProgramImage := ⟨[(65544, 0x00000073)], 65544, []⟩
    check protectedImage 65536 actual (rows 65536 actual) = false ∧
      check image 65536 actual (rows 65536 actual) (some 65551) = false := by native_decide

/-- Counter jumps and computed-witness corruption fail local constraints. -/
theorem localTampering :
    let input := row 65536 (bytes 8) 0
    (checked (input.1, { input.2 with nextIndex := Address.ofNat 2 })).1 = false ∧
      (checked (input.1, { input.2 with nextAddress := Address.ofNat 65552 })).1 = false ∧
      [0, 63, 64, 127, 128, 199, 200, 201, 264].all (fun index => !(checked input (some index)).1) = true := by
  native_decide

/-- info: exportable ✓ (265 witness cells) -/
#guard_msgs in
#assert_exportable (HintReadWordChip.circuit (p := SP1Prime) false)

/-- info: exportable ✓ (265 witness cells) -/
#guard_msgs in
#assert_exportable (HintReadWordChip.circuit (p := SP1Prime) true)

end SP1CleanTest.Core.HintReadWord
