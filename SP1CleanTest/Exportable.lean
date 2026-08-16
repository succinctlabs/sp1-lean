import SP1Clean
import Clean.Circuit.WitnessExport

/-! # Witness-generator exportability

The point of moving chip witness generation off Lean closures and onto Clean's witness IR is that
the generator becomes *data* — serializable, so a Rust prover can run it. `#assert_exportable` is the
check that this actually happened: it walks a circuit's flattened operations and fails, naming the
flat indices of the offending witnesses, if any of them is still a `WitgenIR.native` closure. On
success it prints the circuit's witness cell count.

That makes this file the thing that keeps "we removed the closures" honest. `scripts/check_no_witness_native.sh`
greps for the tokens; this evaluates the circuits.

**Coverage is the converted set, and grows one wave at a time.** A chip is listed here exactly when
its `main` is closure-free, so adding a line is the last step of converting a chip and the line fails
loudly if a conversion regresses. The chips *not* listed are not an oversight — they are the
remaining waves, and each would fail today:

* `ShiftLeft`, `ShiftRight` build a raw `.witness n (.native …)` prefix;
* `DivRem` reads its flag hint through a closure and is simply the largest port (30 sites, 217
  cells); its signed division is the sign/magnitude construction over the unsigned ops the IR
  already has (`srem_eq_bvAbs` proved half the reduction — see the withdrawn U6 entry in
  `docs/agents/clean-upstream.md`).

The nine memory chips appear here without ever having been converted individually: their only
witnesses come from the `AddressOperation` subcircuit, so converting that one operation cleared all
of them at once.

These are `#eval`-backed commands rather than proofs, so they contribute no axioms — but they do run
compiled code, which is why they live in the test library. -/

namespace SP1Clean.ExportableTests

open SP1Clean

/-- SP1's field is KoalaBear, `2^31 - 2^24 + 1`; the circuits are field-generic, and this is where
SP1's prover actually runs. -/
abbrev SP1Prime : ℕ := 2130706433

instance instFactSP1Prime : Fact (Nat.Prime SP1Prime) := ⟨by native_decide⟩
instance instFact2pow17SP1Prime : Fact (2 ^ 17 < SP1Prime) := ⟨by norm_num [SP1Prime]⟩
instance instFact2pow24SP1Prime : Fact (2 ^ 24 < SP1Prime) := ⟨by norm_num [SP1Prime]⟩

/-! ## ALU and control flow (waves W1–W2) -/

/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (AddChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (AddiChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (SubChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (3 witness cells) -/
#guard_msgs in
#assert_exportable (AddwChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (3 witness cells) -/
#guard_msgs in
#assert_exportable (SubwChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (7 witness cells) -/
#guard_msgs in
#assert_exportable (UTypeChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (8 witness cells) -/
#guard_msgs in
#assert_exportable (JalChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (9 witness cells) -/
#guard_msgs in
#assert_exportable (JalrChip.circuit (p := SP1Prime))

/-! ## Memory (wave W3) — cleared wholesale by the `AddressOperation` conversion -/

/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (LoadByteChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (LoadHalfChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (LoadWordChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (LoadDoubleChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (LoadX0Chip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (StoreByteChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (StoreHalfChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (StoreWordChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (4 witness cells) -/
#guard_msgs in
#assert_exportable (StoreDoubleChip.circuit (p := SP1Prime))

/-! ## Hint-driven ALU (wave W4) — flags through `FExpr.hintGet` -/

/-- info: exportable ✓ (19 witness cells) -/
#guard_msgs in
#assert_exportable (BitwiseChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (12 witness cells) -/
#guard_msgs in
#assert_exportable (LtChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (20 witness cells) -/
#guard_msgs in
#assert_exportable (BranchChip.circuit (p := SP1Prime))
/-- info: exportable ✓ (54 witness cells) -/
#guard_msgs in
#assert_exportable (MulChip.circuit (p := SP1Prime))

/-! ## Chips that witness nothing at all -/

/-- info: exportable ✓ (0 witness cells) -/
#guard_msgs in
#assert_exportable (AluX0Chip.circuit (p := SP1Prime))

end SP1Clean.ExportableTests
