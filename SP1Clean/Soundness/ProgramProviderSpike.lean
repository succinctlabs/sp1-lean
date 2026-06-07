import SP1Clean.Soundness.ProgramConsistency

/-! # Provider-chip spike (Program bus) — constructing the `ProgramProvider`, not assuming it

**The workaround this attacks.** `Soundness/ProgramConsistency.lean` threads `TraceProgramLink` (every real
instruction fetch is in the committed program ROM) as an honest assumption, because the **provider** chip —
SP1's preprocessed program/decode ROM — is modeled only as a membership *predicate* (`ProgramChip.ProgramProvider`),
not a real Air. The discharge lemma `programConsistent_of_balance` already reduces that link to
`ProgramProvider inROM prov` **+** the lone `isConsistentBalanced` (LogUp/GKR) fact — but the
`ProgramProvider` itself is still a *hypothesis*: nothing yet *produces* it.

**What this spike does.** It removes that hypothesis: it **constructs** a `ProgramProvider ProgramRowSpec`
from any list of valid (`ProgramRowSpec`) ROM rows — `programProvider_of_validRom` — so the end-to-end
`traceProgramLink_of_validRom_and_balance` derives `TraceProgramLink` from just (a) the ROM rows being
validly decoded and (b) the balanced Program bus, with **no** standalone provider assumption. Everything
here is axiom-clean.

**The trust boundary it isolates (the spike's real output).** After this, the *only* residual on the Program
link is `∀ row ∈ rom, ProgramRowSpec row` — i.e. the committed program ROM carries only validly-decoded rows
(register indices `< 32`, pc limbs `< 2^16`, `op_a_0` boolean). That is irreducible *within Clean's
constraint model*: it is either (a) a **preprocessing/commitment** fact about the verifying key's fixed ROM
content, or (b) provable by a real **instruction-decode** Air whose in-circuit 5-bit / 16-bit range checks
would themselves bottom out at the **Byte** bus (re-introducing a byte-provider obligation — the same shape one
level down). The Byte bus is the exact analog: `Chips/ByteChip.lean`'s `ByteProvider`/`ByteRowSpec` would
get a `byteProvider_of_validBytes` twin and the same boundary. So a full removal of all four threaded links
reduces to: a real preprocessed-table Air per bus, bottoming out at preprocessing trust — a much larger,
architecturally distinct effort than the per-instruction operation chips. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.LookupAccessList
open SP1Clean.ProgramChip (ProgramRow ProgramRowSpec ProgramProvider programRowKey)

variable {p : ℕ} [NeZero p]

/-- One Program-bus contribution sitting at a ROM row's key — the receiver's entry for `row` at
multiplicity `mult`. By construction `keyOf (romAccess row mult) = programRowKey row` (`rfl`). -/
def romAccess (row : ProgramRow (ZMod p)) (mult : ℤ) : LookupAccess :=
  let k := programRowKey row
  (k.1, k.2.1, k.2.2, mult)

omit [NeZero p] in
@[simp] theorem keyOf_romAccess (row : ProgramRow (ZMod p)) (mult : ℤ) :
    keyOf (romAccess row mult) = programRowKey row := rfl

/-- The preprocessed program ROM as a Program-bus contribution list: one `romAccess` per ROM row, each at
the per-row multiplicity `mult row` (the receiver's count). This is the *native content* of SP1's program
chip — a concrete list, not a predicate. -/
def romContributions (rom : List (ProgramRow (ZMod p))) (mult : ProgramRow (ZMod p) → ℤ) :
    LookupAccessList :=
  rom.map (fun row => romAccess row (mult row))

omit [NeZero p] in
/-- **The provider is constructed, not assumed.** A ROM all of whose rows are validly decoded
(`ProgramRowSpec`) yields a `ProgramProvider ProgramRowSpec`: every contribution sits at the key of a valid
row (itself). This is the receiver-side fact `programConsistent_of_balance` previously took as a hypothesis. -/
theorem programProvider_of_validRom (rom : List (ProgramRow (ZMod p))) (mult : ProgramRow (ZMod p) → ℤ)
    (h : ∀ row ∈ rom, ProgramRowSpec row) :
    ProgramProvider (p := p) ProgramRowSpec (romContributions rom mult) := by
  intro b hb
  simp only [romContributions, List.mem_map] at hb
  obtain ⟨row, hrow, rfl⟩ := hb
  exact ⟨row, h row hrow, keyOf_romAccess row (mult row)⟩

/-- **End-to-end: `TraceProgramLink` from ROM-validity + balance, no provider assumption.** Feeding the
constructed provider into `programConsistent_of_balance` discharges the instruction-fetch membership link
using only (a) the committed ROM rows being validly decoded and (b) the balanced Program bus. The standalone
`ProgramProvider` hypothesis of `programConsistent_of_balance` is gone — replaced by the concrete ROM. -/
theorem traceProgramLink_of_validRom_and_balance
    (rows : List (Trace.RowView (ZMod p)))
    (rom : List (ProgramRow (ZMod p))) (mult : ProgramRow (ZMod p) → ℤ)
    (h_valid : ∀ row ∈ rom, ProgramRowSpec row)
    (h_bal : isConsistentBalanced
      (aggregateChipRows rows programLookups ++ romContributions rom mult)) :
    TraceProgramLink rows ProgramRowSpec :=
  programConsistent_of_balance rows (romContributions rom mult) ProgramRowSpec
    (programProvider_of_validRom rom mult h_valid) h_bal

/-! ## A worked instance — a two-row ROM, end-to-end

A concrete program ROM with two validly-decoded rows; `programProvider_of_validRom` turns it into a
`ProgramProvider` with zero side conditions beyond the two rows' `ProgramRowSpec`s, demonstrating the
construction is inhabited (not vacuous). -/

/-- A validly-decoded R-type ROM row `add x1, x2, x3` at pc 0: indices `< 32`, pc limbs `< 2^16`,
`op_a_0 = 0`. The `op_b`/`op_c` are pure register reads (`#v[idx,0,0,0]`). -/
def demoRomRow : ProgramRow (ZMod p) :=
  ⟨0, 0, 0, 0, 1, #v[2, 0, 0, 0], 0, #v[3, 0, 0, 0], 0, 0⟩

omit [NeZero p] in
theorem demoRomRow_valid [Fact (2 ^ 17 < p)] : ProgramRowSpec (demoRomRow (p := p)) := by
  have h32 : (32 : ℕ) < p := by have := Fact.out (p := 2 ^ 17 < p); omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, Or.inl rfl⟩ <;>
    simp only [demoRomRow, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] <;>
    first
      | (rw [show (1 : ZMod p) = ((1 : ℕ) : ZMod p) from by norm_cast,
            ZMod.val_natCast_of_lt (by omega)]; norm_num)
      | (rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) from by norm_cast,
            ZMod.val_natCast_of_lt (by omega)]; norm_num)
      | (rw [show (3 : ZMod p) = ((3 : ℕ) : ZMod p) from by norm_cast,
            ZMod.val_natCast_of_lt (by omega)]; norm_num)
      | (rw [ZMod.val_zero]; norm_num)

omit [NeZero p] in
/-- The constructed provider for the one-row demo ROM is a genuine `ProgramProvider` (no assumption) —
the `programProvider_of_validRom` construction is inhabited, not vacuous. -/
theorem demoRom_programProvider [Fact (2 ^ 17 < p)] (mult : ProgramRow (ZMod p) → ℤ) :
    ProgramProvider (p := p) ProgramRowSpec (romContributions [demoRomRow (p := p)] mult) :=
  programProvider_of_validRom [demoRomRow] mult
    (by intro row hrow; simp only [List.mem_singleton] at hrow; subst hrow; exact demoRomRow_valid)

end SP1Clean.Soundness
