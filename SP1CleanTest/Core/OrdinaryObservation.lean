import SP1CleanTest.Core.HostChecks
import Clean.Circuit.WitnessExport
import SP1Clean.Proofs.Operations.OrdinaryObservation

/-! # Executed ordinary retirement observations

These fixtures evaluate the actual composed program, including its Byte obligations. Explicit
observation endpoints test the subsystem ledger, without claiming their mixed-ensemble binding.
-/

namespace SP1CleanTest.Core.OrdinaryObservation

open Circuit Air.Flat SP1Clean SP1Clean.OrdinaryObservation HostChecks

private abbrev Fp := ZMod SP1Prime

private def word (value : ℕ) : Word Fp :=
  Soundness.Target.bitVecToWord (BitVec.ofNat 64 value)

private def initial (value : ℕ) : State Fp := ⟨0, 0, word value, #v[13, 7, 0]⟩

private def receipt (high low : Fp) : Channels.StateMsg Fp := ⟨high, low, 65536, 1, 0⟩

private def evaluate (enabled : Bool) (input : Inputs Fp) (corrupt : Option ℕ := none) :=
  evaluateProgram (main enabled (varFromOffset Inputs 0)) (toElements input).toList corrupt

private def first (enabled : Bool) (counter : ℕ) : Inputs Fp :=
  populate enabled (initial counter) (receipt 0 17)

/-- Enabled/inhibited retirement, each carry boundary and full u64 wrap use the real program. -/
theorem counters : [false, true].all (fun enabled =>
    [0, 65535, 2 ^ 32 - 1, 2 ^ 48 - 1, 2 ^ 64 - 1].all fun counter =>
      (evaluate enabled (first enabled counter)).1 &&
        Word.toBitVec64 (first enabled counter).counter ==
          BitVec.ofNat 64 (counter + if enabled then 1 else 0)) = true := by native_decide

/-- Clock ordering uses the recovered source, so successor overflow and refresh remain legal.
The raw PC limb 65536 is intentionally retained rather than spuriously range-checked. -/
theorem clockCrossings :
    (evaluate true (populate true (initial 0) (receipt 0 (2 ^ 24 + 1)))).1 = true ∧
    (evaluate true (populate true
      ⟨0, 2 ^ 24 - 7, word 1, #v[65536, 1, 0]⟩ (receipt 1 9))).1 = true := by native_decide

/-- Equal/reversed/wrapped source clocks, forged counters and corrupt gadget witnesses fail. -/
theorem rejectsMalformed :
    [populate true (initial 0) (receipt 0 8),
     populate true { initial 0 with clkLow := 10 } (receipt 0 17),
     populate true (initial 0) (receipt 0 0),
     populate true (initial 0) (receipt (2 ^ 24) 9),
     populate true (initial 0) (receipt 0 (2 ^ 24 + 8)),
     { first true 0 with counter := word 2 },
     { first true 0 with counter := #v[65536, 0, 0, 0] }].all
      (fun input => !(evaluate true input).1) = true ∧
    (evaluate false { first false 7 with counter := word 8 }).1 = false ∧
    [0, 24, 48, 72, 97, 98, 121, 122, 185].all (fun index =>
      !(evaluate true (first true 0) (some index)).1) = true := by native_decide

private def balance (ledger : Ledger) : Bool :=
  ledger.all fun key =>
    ((ledger.filter (fun item => item.1 == key.1 && item.2.1 == key.2.1)).map (·.2.2)).sum == 0

private def accepts (enabled : Bool) (start finish : State Fp) (inputs : List (Inputs Fp)) : Bool :=
  let evaluated := inputs.map (evaluate enabled ·)
  let ledger := (evaluated.flatMap (·.2)).filter (fun item => item.1 == "SP1OrdinaryObservation")
  evaluated.all (·.1) && balance (ledger ++
    [("SP1OrdinaryObservation", (toElements start).toList, 1),
     ("SP1OrdinaryObservation", (toElements finish).toList, -1)])

/-- Physical table order is irrelevant; balance authenticates the chronological counter and PC.
Empty inventories preserve the complete initial observation. -/
theorem histories : [false, true].all (fun enabled =>
    let a := first enabled (2 ^ 64 - 1)
    let b := populate enabled a.next ⟨0, 33, 0x2010, 0, 0⟩
    accepts enabled a.previous b.next [b, a] &&
    accepts enabled a.previous a.previous [] &&
    !accepts enabled a.previous b.next [] &&
    !accepts enabled a.previous b.next [a] &&
    !accepts enabled a.previous b.next [a, a, b] &&
    !accepts enabled a.previous { b.next with pc := #v[0x2011, 0, 0] } [a, b] &&
    !accepts enabled a.previous { b.next with counter := word 17 } [a, b] &&
    !accepts enabled a.previous b.next [a, populate enabled a.previous b.receipt]) = true := by native_decide

/-- Exact physical cost is independent of the retirement enable bit. -/
theorem cost : [false, true].all (fun enabled =>
    let evaluated := evaluate enabled (first enabled 0)
    evaluated.2.length == 7 &&
      (evaluated.2.filter (fun item => item.1 == "SP1Byte")).length == 4 &&
      (evaluated.2.filter (fun item => item.1 == "SP1OrdinaryStateReceipt")).length == 1 &&
      (evaluated.2.filter (fun item => item.1 == "SP1OrdinaryObservation")).length == 2) = true := by native_decide

/-- info: exportable ✓ (186 witness cells) -/
#guard_msgs in
#assert_exportable (circuit (p := SP1Prime) false)

/-- info: exportable ✓ (186 witness cells) -/
#guard_msgs in
#assert_exportable (circuit (p := SP1Prime) true)

end SP1CleanTest.Core.OrdinaryObservation
