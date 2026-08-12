import SP1CleanTest.NonVacuityReal

/-! # Independent-audit regression: one committed-window ADD row

The general real-row battery proves each chip's local constraint system satisfiable, but its
representative program counters predate the committed guest-program window. This audit anchor uses
the retained `ADD x1, x2, x3` example at `0x10000`, proves the full native Add circuit constraints,
and freezes the complete evaluated interaction list across all four buses.

This deliberately does **not** claim a witness of `SupportedCoreNativeRelation`. Closing that joint
claim additionally requires the Program provider's `decodedInROM` fact, whose concrete
`LeanRV64D.ext_decode` witness was retired during the Sail-v5 migration. The exact interaction list
below makes the remaining provider/boundary work visible without disguising that decode seam.
-/

namespace SP1Clean.Audit.OneAddNativePremises

open Air.Flat Circuit
open SP1Clean.NonVacuityRealTests SP1Clean.TraceGenTests
open LeanRV64D.Defs

/-- `ADD x1, x2, x3` at the first legal committed code address. The source values are `100` and
`23`; the destination receives `123`. -/
def event : AluEventRec :=
  { clk := 9, pc := 0x10000, a := 123, b := 100, c := 23, opA := 1, opB := 2, opC := 3,
    tsA := 13, prevTsA := 0, prevA := 0, tsB := 12, prevTsB := 0, tsC := 11, prevTsC := 0 }

def inputs : List (ZMod SP1Prime) := rTypeEventInputs event

def environment : Environment (ZMod SP1Prime) :=
  chipEnvironment AddChip.Inputs AddChip.main inputs

def operations : Operations (ZMod SP1Prime) :=
  chipOperations AddChip.Inputs AddChip.main inputs

/-- A stable, decidable projection of Clean's heterogeneous evaluated interaction. -/
def interactionView (interaction : Interaction (ZMod SP1Prime)) : String × Nat × List Nat :=
  (interaction.channel.name, interaction.mult.val, interaction.msg.toList.map ZMod.val)

def interactionViews : List (String × Nat × List Nat) :=
  (operations.interactionValues environment).map interactionView

/-- The committed-window row still satisfies every flattened Add-chip constraint, including its
true Clean subcircuits. -/
theorem constraints_hold : operations.ConstraintsHold environment :=
  constraintsHold_of_check (by native_decide)

/-- The exact four-bus footprint of the row. Multiplicity `SP1Prime - 1` is field `-1` (a pull),
and multiplicity `1` is a push. Besides guarding interaction layout, this records the finite
provider rows that a future joint non-vacuity witness must balance. -/
theorem interactions_exact :
    interactionViews =
      [ ("SP1Byte", SP1Prime - 1, [6, 1, 13, 0]),
        ("SP1Byte", SP1Prime - 1, [3, 0, 0, 0]),
        ("SP1State", SP1Prime - 1, [0, 9, 0, 1, 0]),
        ("SP1State", 1, [0, 17, 4, 1, 0]),
        ("SP1Byte", SP1Prime - 1, [6, 123, 16, 0]),
        ("SP1Byte", SP1Prime - 1, [6, 0, 16, 0]),
        ("SP1Byte", SP1Prime - 1, [6, 0, 16, 0]),
        ("SP1Byte", SP1Prime - 1, [6, 0, 16, 0]),
        ("SP1Byte", SP1Prime - 1, [6, 12, 16, 0]),
        ("SP1Byte", SP1Prime - 1, [3, 0, 0, 0]),
        ("SP1Byte", SP1Prime - 1, [6, 11, 16, 0]),
        ("SP1Byte", SP1Prime - 1, [3, 0, 0, 0]),
        ("SP1Byte", SP1Prime - 1, [6, 10, 16, 0]),
        ("SP1Byte", SP1Prime - 1, [3, 0, 0, 0]),
        ("SP1Program", SP1Prime - 1, [0, 1, 0, 0, 1, 2, 0, 0, 0, 3, 0, 0, 0, 0, 0, 0]),
        ("SP1Memory", SP1Prime - 1, [0, 0, 1, 0, 0, 0, 0, 0, 0]),
        ("SP1Memory", SP1Prime - 1, [0, 0, 2, 0, 0, 100, 0, 0, 0]),
        ("SP1Memory", 1, [0, 12, 2, 0, 0, 100, 0, 0, 0]),
        ("SP1Memory", SP1Prime - 1, [0, 0, 3, 0, 0, 23, 0, 0, 0]),
        ("SP1Memory", 1, [0, 11, 3, 0, 0, 23, 0, 0, 0]),
        ("SP1Memory", 1, [0, 13, 1, 0, 0, 123, 0, 0, 0]) ] := by
  native_decide

/-- The retained semantic projection agrees with the fetched Program-bus row. Consequently the
remaining concrete Program-provider seam is specifically evaluation of the generated official
decoder on `0x003100B3`, rather than an SP1 opcode/operand projection mismatch. -/
theorem program_projection :
    Soundness.Target.instrToProgramRow' (p := SP1Prime) #v[0, 1, 0]
        (.RTYPE (.Regidx 3#5, .Regidx 2#5, .Regidx 1#5, .ADD)) =
      some (Soundness.Target.addRow (p := SP1Prime)) := by
  rfl

end SP1Clean.Audit.OneAddNativePremises
