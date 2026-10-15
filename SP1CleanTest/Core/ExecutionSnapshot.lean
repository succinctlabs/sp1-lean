import SP1Clean.Model.Core.HostSnapshot
import SP1Clean.Model.SP1Field

/-! # Complete finite-boundary and host-execution regressions

The comparisons reject changes outside the GPR/RAM projection, including nextPC, retirement
bookkeeping, runtime output, and host state. The active finite interpreter performs a padded
HINT_READ and preserves those full-state fields. No dense Sail memory is evaluated by a test.
-/

namespace SP1CleanTest.Core.ExecutionSnapshot

open SP1Clean SP1Clean.Model.Core SP1Clean.Soundness.Target SP1Clean.Machine LeanRV64D.Defs

private def policy : HostPolicy := ⟨⟨fun _ => false, NativeLayout.guestMemory⟩, SP1Prime⟩

private def program : GuestProgram where
  rom := [(65536, 0x73)]
  pc_start := 65536
  memImage := []
  rom_nodup := by decide
  rom_aligned := by simp
  rom_in_window := by simp
  rom_full_width := by simp

private def source : ExecutionSnapshot where
  sail := {
    registers := ((((((∅ : SailRegisterFile.Map).insert Register.PC 65536).insert
      Register.x5 241).insert Register.x10 70000).insert Register.x11 8).insert
      Register.nextPC 80000).insert Register.minstret 19
    memory := ⟨[(70008, 99), (80000, 42), (65536, 0x73)]⟩
    cycleCount := 29
    output := #["earlier Sail output"] }
  host := { io := ⟨[[1, 2, 3, 4, 5, 6, 7, 8], [9]], [10]⟩, stdout := [11] }
  clock := 1000

private def expected : ExecutionSnapshot :=
  { source with
    sail := { source.sail with
      registers := (source.sail.registers.insert Register.x5 241).insert Register.PC 65540
      memory := source.sail.memory.writeBytes 70000
        ([1, 2, 3, 4, 5, 6, 7, 8] ++ List.replicate 8 0) }
    host := { source.host with io := { source.host.io with hints := [[9]] } }
    clock := 1264 }

/-- All Sail bookkeeping remains significant even when the GPR/RAM projection is unchanged. -/
theorem rejectsBookkeepingChanges :
    ([(Register.nextPC, 80001), (Register.minstret, 20), (Register.PC, 65540)].map
      (fun (reg, value) => match reg with
        | .nextPC => source.equivalent { source with sail.registers := source.sail.registers.insert .nextPC value }
        | .minstret => source.equivalent { source with sail.registers := source.sail.registers.insert .minstret value }
        | _ => source.equivalent { source with sail.registers := source.sail.registers.insert .PC value })) =
      [false, false, false] := by native_decide

theorem rejectsRuntimeAndHostChanges :
    [source.equivalent { source with sail.cycleCount := 30 },
     source.equivalent { source with sail.output := #["forged"] },
     source.equivalent { source with host.io.hints := [] },
     source.equivalent { source with host.stdout := [] },
     source.equivalent { source with clock := 1001 },
     source.equivalent { source with host.exitCode := some 0 }] =
      [false, false, false, false, false, false] := by native_decide

/-- Equal current bytes ignore overwritten history; an untouched-byte mutation remains visible. -/
theorem comparesCompleteMemory :
    source.equivalent { source with sail.memory.entries := source.sail.memory.entries ++ [(80000, 17)] } = true ∧
    source.equivalent { source with sail.memory := source.sail.memory.write 80000 17 } = false ∧
    source.equivalent { source with sail.memory := source.sail.memory.write 90000 17 } = false := by
  native_decide

/-- Missing registers differ from present zero registers, including an otherwise unused CSR. -/
theorem comparesMissingKeys :
    source.equivalent { source with sail.registers := source.sail.registers.insert Register.mcycle 0 } = false := by
  native_decide

/-- The exact eight-byte hint writes an additional eight zero padding bytes, consumes one hint,
and retains nextPC, minstret, the runtime counter/output, and the untouched byte at 80000. -/
theorem executesPaddedHint :
    ((source.hostStep? policy program).map (fun result =>
      result.1.equivalent expected && decide (result.2.rawCode = 241) &&
        decide (result.1.sail.memory.read 70008 = 0) &&
        decide (result.1.sail.memory.read 80000 = 42))).getD false = true := by
  native_decide

/-- An otherwise valid host request cannot bypass a mismatch in any of the four code bytes.
Sparse omitted bytes denote present zeros in the realized memory, so the positive fixture above
needs only the nonzero opcode byte; changing one of its zero bytes must still fail. -/
theorem rejectsCodeMemoryMismatch :
    (source.host.run policy source.sail.readContext).isSome = true ∧
      ((List.range 4).map fun offset =>
        ({ source with sail.memory := (source.sail.memory.write (65536 + offset)
          (if offset = 0 then 0 else 1)) }.hostStep? policy program).isNone) =
        [true, true, true, true] := by
  native_decide

/-- The executable check reaches the official full-state host semantics through the general
commuting theorem; this conclusion never evaluates the dense Sail memory realization. -/
theorem paddedHint_semanticStep :
    ∃ event, ExecutionStep policy program source.realize (.syscall event) expected.realize := by
  have checked := executesPaddedHint
  cases found : source.hostStep? policy program with
  | none => simp only [found, Option.map_none, Option.getD_none, Bool.false_eq_true] at checked
  | some result =>
      simp only [found, Option.map_some, Option.getD_some, Bool.and_eq_true] at checked
      have same := (ExecutionSnapshot.equivalent_iff result.1 expected).mp checked.1.1.1
      have step := ExecutionSnapshot.hostStep?_sound (by rfl : policy.memory.upper = 2 ^ 48) found
      rw [same] at step
      exact ⟨result.2, step⟩

/-- A recorded HALT prevents the sparse interpreter from executing any further host call. -/
theorem rejectsAfterHalt :
    ({ source with host.exitCode := some 0 }.hostStep? policy program).isNone = true := by
  native_decide

end SP1CleanTest.Core.ExecutionSnapshot
