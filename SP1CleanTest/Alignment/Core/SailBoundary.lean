import SP1Clean.Soundness.HostSailBoundary
import SP1CleanTest.Alignment.Support.LocalCoreFixture

/-! # Target Sail fields checked by the real verifier subcircuit

The ADD fixture supplies a complete initialized source. These checks execute the new circuit's
assertions, including its actual public-field equations. Missing zero-valued GPRs are kept distinct
from their Memory projection, and range tests precede field conversion.
-/

namespace SP1CleanTest.Alignment.Core.SailBoundary

open Circuit Air.Flat SP1Clean SP1Clean.Model.Core LeanRV64D.Defs

private abbrev Fp := ZMod SP1Prime
private def image := SP1CleanTest.Core.LocalCore.Fixture.image
private def source := SP1CleanTest.Core.LocalCore.Fixture.source
private def header := SP1CleanTest.Core.LocalCore.Fixture.publicInput

private def target : ExecutionSnapshot :=
  { source with
    sail := { source.sail with registers := (source.sail.registers.insert .x1 123).insert .PC 65540 }
    clock := 17 }

private def check (target : ExecutionSnapshot) (input : SP1PublicIO Fp := header) : Bool :=
  (SP1CleanTest.Core.LocalCore.Fixture.evaluate image source
    { circuit := SP1Clean.SailBoundary.circuit source target } (toElements input).toList []).1

/-- The outgoing ADD state supplies the existing header's real PC/clock and preserves its frame. -/
theorem activeAcceptance : check target = true := by native_decide

/-- An empty segment preserves arbitrary initialized register/runtime values. -/
theorem identityAcceptance : check source { header with final_clk_0_16 := 9, final_pc0 := 0 } = true := by
  native_decide

private def missingZero : ExecutionSnapshot :=
  { target with sail := { target.sail with registers := target.sail.registers.erase .x31 } }

/-- The missing zero-valued GPR is invisible to the Memory projection but rejected by this circuit. -/
theorem missingPresence :
    missingZero.sail.memorySnapshot.registers = target.sail.memorySnapshot.registers ∧
      check missingZero = false := by native_decide

/-- Preserved CSRs, key presence, runtime, canonical endpoints and pre-field bounds are enforced. -/
theorem mutations :
    [check missingZero,
     check { target with sail := { target.sail with registers := target.sail.registers.erase .mtvec } },
     check { target with sail := { target.sail with registers := target.sail.registers.erase .PC } },
     check { target with sail := { target.sail with registers := target.sail.registers.insert .mcountinhibit 1 } },
     check { target with sail := { target.sail with cycleCount := target.sail.cycleCount + 1 } },
     check { target with sail := { target.sail with output := target.sail.output.push "changed" } },
     check { target with clock := 18 },
     check { target with sail := { target.sail with registers := target.sail.registers.insert .PC 65544 } },
     check { target with sail := { target.sail with registers := target.sail.registers.insert .PC (65540 + 2 ^ 48) } },
     check { target with clock := target.clock + SP1Prime * 2 ^ 24 }] = List.replicate 10 false := by
  native_decide

end SP1CleanTest.Alignment.Core.SailBoundary
