import SP1Clean.Chips.ShiftLeftChip.Defs
import SP1Clean.TraceGenTests.TraceGenerator
import SP1Clean.TraceGenTests.ShiftLeftChipTraceVectors

/-! # Whole-trace conformance anchor for `ShiftLeftChip` — hint-driven flags, unmasked.

The first **hint-driven** trace anchor: the chip's variant flags are not constant witnesses but
come from the `"shift_left_flags"` `ProverHint` (`Chips/ShiftLeftChip/Populate.lean`), so the
derivation builds a per-event hint from the dumped executor opcode (`shiftLeftHint`, SLL = 6 /
SLLW = 21 — the same discriminants the circuit's flag-weighted opcode expression uses). The
battery covers both variants × {register-`c`, immediate-`c`} with the shift amount swept over all
byte/bit shifts, and the comparison is **unmasked** (all 65 columns): every honest witness closure
— `c_bits`, the `v_*` powers, `shift_u16`, the limb bit-splits, `limb_result`, the SLLW MSB, the
placed result `a`, and the flags — is checked cell-for-cell against SP1's real `generate_trace`.

SP1 pads shift traces with a non-zero `padded_row_template` (`v_01 = v_012 = v_0123 = 1` — the
`v_*` constraints are ungated, so all-zero rows would violate them). The derived padding row is
the circuit's own zero-input/empty-hint row, which reproduces the template because the `v_*`
closures compute `2^(0 mod k) = 1` ungated — so SP1's padding behavior is itself conformance-checked. -/

namespace SP1Clean.TraceGenTests

open SP1Clean

/-- Per-event flag hint: the `"shift_left_flags"` one-hot from the dumped executor opcode. -/
def shiftLeftHint (op : ℕ) : ProverHint (ZMod SP1Prime) := fun key n =>
  match key, n with
  | "shift_left_flags", 2 => #[#v[if op = 6 then 1 else 0, if op = 21 then 1 else 0]]
  | _, _ => #[]

/-- The derived padding row: the circuit's witness closures on all-zero inputs with the empty hint
(= SP1's `padded_row_template`). -/
def shiftLeftPadRow : List (ZMod SP1Prime) :=
  circuitTraceRow ShiftLeftChip.Inputs (ShiftLeftChip.main (p := SP1Prime))
    (List.replicate 33 0)

/-- The `ShiftLeftChip` trace derived from the circuit: one `circuitTraceRow` per dumped event
(flag hint from the event's opcode), template padding to SP1's height. -/
def shiftLeftChipDerivedTrace : List (List (ZMod SP1Prime)) :=
  generateTrace
    (fun e =>
      circuitTraceRow ShiftLeftChip.Inputs (ShiftLeftChip.main (p := SP1Prime))
        (aluTypeOpEventInputs e) (shiftLeftHint e.opcode))
    ShiftLeftChipTraceEvents ShiftLeftChipTraceHeight 65 shiftLeftPadRow

theorem shiftleftchip_trace_conforms :
    (shiftLeftChipDerivedTrace
      == ShiftLeftChipTraceRows.map (fun r => r.toList.map toField)) = true := by
  native_decide

end SP1Clean.TraceGenTests
