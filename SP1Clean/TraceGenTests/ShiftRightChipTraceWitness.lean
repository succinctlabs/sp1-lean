import SP1Clean.Chips.ShiftRightChip.Defs
import SP1Clean.TraceGenTests.TraceGenerator
import SP1Clean.TraceGenTests.ShiftRightChipTraceVectors

/-! # Whole-trace conformance anchor for `ShiftRightChip` — hint-driven flags, unmasked.

As `ShiftLeftChipTraceWitness`, for the four-variant right-shift chip: the per-event
`"shift_right_flags"` hint is built from the dumped executor opcode (SRL = 7, SRA = 8, SRLW = 22,
SRAW = 23). The battery cycles all four variants × {register-`c`, immediate-`c`} with the shift
amount swept, and the comparison is **unmasked** (all 69 columns) — including the inverted `v_*`
powers, the `e14`-gated top-limb splits (word variants zero them), the `b_msb`/`srw_msb`/
`sra_msb_v0123` sign witnesses, and the `sraFill`/`bmsbFill`/`srwFill` result placement.

SP1's right-shift padding template sets `v_01 = 16, v_012 = 256, v_0123 = 65536`; the derived
zero-input/empty-hint row reproduces it (`2^(4-0), 2^(8-0), 2^(16-0)`). -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- Per-event flag hint: the `"shift_right_flags"` one-hot from the dumped executor opcode. -/
def shiftRightHint (op : ℕ) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "shift_right_flags", 4 =>
    #[#v[if op = 7 then 1 else 0, if op = 8 then 1 else 0,
         if op = 22 then 1 else 0, if op = 23 then 1 else 0]]
  | _, _ => #[]

/-- The derived padding row: the circuit's witness closures on all-zero inputs with the empty hint
(= SP1's `padded_row_template`, `v_* = 16/256/65536`). -/
def shiftRightPadRow : List (ZMod SP1Prime) :=
  circuitTraceRow ShiftRightChip.Inputs (ShiftRightChip.main (p := SP1Prime))
    (List.replicate 33 0)

/-- The `ShiftRightChip` trace derived from the circuit: one `circuitTraceRow` per dumped event
(flag hint from the event's opcode), template padding to SP1's height. -/
def shiftRightChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e =>
      circuitTraceRow ShiftRightChip.Inputs (ShiftRightChip.main (p := SP1Prime))
        (aluTypeOpEventInputs e) (shiftRightHint e.opcode))
    ShiftRightChipTraceEvents ShiftRightChipTraceHeight 69 shiftRightPadRow

theorem shiftrightchip_trace_conforms :
    (shiftRightChipDerivedTrace
      == ShiftRightChipTraceRows.map (fun r => r.toList.map toField)) = true := by
  native_decide

end SP1Clean.TraceGenTests
