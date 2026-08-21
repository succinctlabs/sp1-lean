import SP1Clean.FormalModel.TraceGen.Events
import SP1Clean.FormalModel.Contracts.Chips

/-! # Trace generation — events to typed chip inputs

The **builder**: the total function taking one `RTypeEvent` to the typed input row a chip circuit
consumes. It is a transcription of SP1's adapter `populate` functions (read-only references,
paths relative to the sibling `sp1` checkout):

- `cpuStateCols` ← `CPUState::populate` (`crates/core/machine/src/adapter/state.rs`): the clock
  split as `clk >>> 24` / `(clk >>> 16) % 256` / `clk % 2^16`, the pc as three u16 limbs;
- `registerAccessCols` ← `RegisterAccessCols::populate` + `RegisterAccessTimestamp::
  populate_timestamp` (`crates/core/machine/src/memory/consistency/trace.rs`): the previous value
  as four u16 limbs, then `prev_low` (the previous access clock, *zeroed* when it belongs to an
  earlier 24-bit window) and `diff_low_limb` (the low 16 bits of the difference to this access);
- `rTypeReaderCols` ← `RTypeReader::populate` (`crates/core/machine/src/adapter/register/
  r_type.rs`): the three indices, the three access blocks — `op_a` a **write** (whose
  `prev_value` is the displaced content), `op_b`/`op_c` **reads** (whose `prev_value` is the value
  read) — and the `op_a_0` flag.

Everything here is a plain total function: no `Classical.choice`, no hint, no environment. The
*typed* output is the point — `SP1CleanTest/TraceGenTests/EventPopulate.lean` mirrors the same
populate functions as flat `List F` cell lists for the test library's compiled-evaluation
conformance battery, which cannot carry a proof obligation; these typed blocks are what the
reader-contract lemmas of `Readers.lean` are stated over.

The per-chip assembly at the bottom is deliberately trivial (three fields): the two adapter
blocks, which is where all the content lives, are shared by the whole family, so rolling a new
R-type chip into this layer costs one `def` here and one `ProverAssumptions` lemma in its
`Complete.lean`.

**Field bound.** This layer carries `Fact (2 ^ 24 < p)` (which supplies the project-standard
`Fact (2 ^ 17 < p)` through `SP1Clean.instFact_2_17_of_2_24`): the 24-bit clock arithmetic the
timestamp columns perform has to be non-wrapping in the field, which a `2 ^ 17` bound does not
give. SP1's own prime is 31-bit, and the grounding engine already carries `Fact (2 ^ 25 < p)`. -/

namespace SP1Clean.TraceGen

-- The builders are pure column arithmetic: they need no field bound at all (only `Readers.lean`,
-- which proves things *about* them, carries `Fact p.Prime` + `Fact (2 ^ 24 < p)`).
variable {p : ℕ}

/-! ## Column blocks -/

/-- The four little-endian u16 limbs of a natural number, as field elements — the committed form
of every 64-bit value in a row.

(A duplicate of `SP1Clean.DivRemChip.wordOfNat`, which is chip-scoped and sits three layers above
this one. The shared home for both is `Math/Word.lean`; hoisting it there is a follow-up, since
that file is imported by essentially the whole project.) -/
def wordOfNat (n : ℕ) : Word (ZMod p) :=
  #v[((n % 2 ^ 16 : ℕ) : ZMod p), ((n / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p),
     ((n / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p), ((n / 2 ^ 48 % 2 ^ 16 : ℕ) : ZMod p)]

/-- SP1's `CPUState::populate`: the clock as `clk_high`/`clk_16_24`/`clk_0_16` and the program
counter as three u16 limbs. -/
def cpuStateCols (clk pc : ℕ) : Extracted.CPUState (ZMod p) where
  clk_high := ((clk >>> 24 : ℕ) : ZMod p)
  clk_16_24 := ((clk >>> 16 % 256 : ℕ) : ZMod p)
  clk_0_16 := ((clk % 2 ^ 16 : ℕ) : ZMod p)
  pc := #v[((pc % 2 ^ 16 : ℕ) : ZMod p), ((pc >>> 16 % 2 ^ 16 : ℕ) : ZMod p),
           ((pc >>> 32 % 2 ^ 16 : ℕ) : ZMod p)]

-- The projection lemmas below are deliberately **not** `@[simp]`: a built row is a large value,
-- and the whole point of stating the reader contracts over the folded builders is that no proof
-- ever normalizes one. Cite them explicitly where a projection really has to be taken.
lemma cpuStateCols_clk_high (clk pc : ℕ) :
    (cpuStateCols (p := p) clk pc).clk_high = ((clk >>> 24 : ℕ) : ZMod p) := rfl

lemma cpuStateCols_clk_16_24 (clk pc : ℕ) :
    (cpuStateCols (p := p) clk pc).clk_16_24 = ((clk >>> 16 % 256 : ℕ) : ZMod p) := rfl

lemma cpuStateCols_clk_0_16 (clk pc : ℕ) :
    (cpuStateCols (p := p) clk pc).clk_0_16 = ((clk % 2 ^ 16 : ℕ) : ZMod p) := rfl

lemma cpuStateCols_pc_zero (clk pc : ℕ) :
    (cpuStateCols (p := p) clk pc).pc[0] = ((pc % 2 ^ 16 : ℕ) : ZMod p) := rfl

lemma cpuStateCols_pc_one (clk pc : ℕ) :
    (cpuStateCols (p := p) clk pc).pc[1] = ((pc >>> 16 % 2 ^ 16 : ℕ) : ZMod p) := rfl

lemma cpuStateCols_pc_two (clk pc : ℕ) :
    (cpuStateCols (p := p) clk pc).pc[2] = ((pc >>> 32 % 2 ^ 16 : ℕ) : ZMod p) := rfl

/-- SP1's `populate_timestamp` previous-access clock: the previous access's low 24 bits when it
happened in the same 24-bit window as this access, and `0` otherwise (a cross-window previous
access is not comparable to this one, and the memory argument carries the window in `clk_high`
instead). -/
def prevLowOf (prevTs currTs : ℕ) : ℕ :=
  if prevTs >>> 24 = currTs >>> 24 then prevTs % 2 ^ 24 else 0

/-- SP1's `populate_timestamp` low difference limb: the low 16 bits of `currTs - prevLow - 1`,
the strictly-positive gap between the previous access and this one. -/
def diffLowOf (prevTs currTs : ℕ) : ℕ :=
  (currTs % 2 ^ 24 - prevLowOf prevTs currTs - 1) % 2 ^ 16

/-- SP1's `RegisterAccessCols::populate`: the previous value of the register as a committed word,
plus the previous-access timestamp block. `currTs` is the clock of *this* row's access to the
register (`clk + 4` for the `op_a` write, `clk + 3` / `clk + 2` for the `op_b` / `op_c` reads). -/
def registerAccessCols (value prevTs currTs : ℕ) : Extracted.RegisterAccessCols (ZMod p) where
  prev_value := wordOfNat value
  access_timestamp :=
    { prev_low := ((prevLowOf prevTs currTs : ℕ) : ZMod p)
      diff_low_limb := ((diffLowOf prevTs currTs : ℕ) : ZMod p) }

lemma registerAccessCols_prev_value (value prevTs currTs : ℕ) :
    (registerAccessCols (p := p) value prevTs currTs).prev_value = wordOfNat value := rfl

lemma registerAccessCols_prev_low (value prevTs currTs : ℕ) :
    (registerAccessCols (p := p) value prevTs currTs).access_timestamp.prev_low
      = ((prevLowOf prevTs currTs : ℕ) : ZMod p) := rfl

lemma registerAccessCols_diff_low_limb (value prevTs currTs : ℕ) :
    (registerAccessCols (p := p) value prevTs currTs).access_timestamp.diff_low_limb
      = ((diffLowOf prevTs currTs : ℕ) : ZMod p) := rfl

/-- SP1's `RTypeReader::populate`: the three register indices, their access blocks at the
`MemoryAccessPosition` offsets `A = 4` / `B = 3` / `C = 2`, and the `rd = x0` flag. -/
def rTypeReaderCols (e : RTypeEvent) : Extracted.RTypeReader (ZMod p) where
  op_a := ((e.opA : ℕ) : ZMod p)
  op_a_memory := registerAccessCols e.prevA e.prevTsA (e.clk + 4)
  op_a_0 := if e.opA = 0 then 1 else 0
  op_b := ((e.opB : ℕ) : ZMod p)
  op_b_memory := registerAccessCols e.b e.prevTsB (e.clk + 3)
  op_c := ((e.opC : ℕ) : ZMod p)
  op_c_memory := registerAccessCols e.c e.prevTsC (e.clk + 2)

lemma rTypeReaderCols_op_a (e : RTypeEvent) :
    (rTypeReaderCols (p := p) e).op_a = ((e.opA : ℕ) : ZMod p) := rfl

lemma rTypeReaderCols_op_a_0 (e : RTypeEvent) :
    (rTypeReaderCols (p := p) e).op_a_0 = if e.opA = 0 then 1 else 0 := rfl

lemma rTypeReaderCols_op_a_memory (e : RTypeEvent) :
    (rTypeReaderCols (p := p) e).op_a_memory
      = registerAccessCols e.prevA e.prevTsA (e.clk + 4) := rfl

lemma rTypeReaderCols_op_b_memory (e : RTypeEvent) :
    (rTypeReaderCols (p := p) e).op_b_memory = registerAccessCols e.b e.prevTsB (e.clk + 3) := rfl

lemma rTypeReaderCols_op_c_memory (e : RTypeEvent) :
    (rTypeReaderCols (p := p) e).op_c_memory = registerAccessCols e.c e.prevTsC (e.clk + 2) := rfl

/-! ## Per-chip assembly

One `def` per chip of the family. The chip's `Inputs` is the `is_real` selector plus the two
shared blocks, so there is nothing chip-specific to build. -/

/-- The `Add` chip's committed input row for one event — a **real** row (`is_real = 1`). -/
def RTypeEvent.toAddInputs (e : RTypeEvent) : AddChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := rTypeReaderCols e

lemma RTypeEvent.toAddInputs_is_real (e : RTypeEvent) :
    (e.toAddInputs (p := p)).is_real = 1 := rfl

lemma RTypeEvent.toAddInputs_state (e : RTypeEvent) :
    (e.toAddInputs (p := p)).state = cpuStateCols e.clk e.pc := rfl

lemma RTypeEvent.toAddInputs_adapter (e : RTypeEvent) :
    (e.toAddInputs (p := p)).adapter = rTypeReaderCols e := rfl

/-! ## Padding

SP1 pads every chip's trace to a power-of-two height with **zero** rows
(`RowMajorMatrix::pad_to_height`); the AIR gates every semantic constraint on `is_real`, so a zero
row carries almost no obligation. It is a separate builder rather than an event, because a padding
row corresponds to no execution step. -/

/-- The all-zero register-access block of a padding row. -/
def zeroAccessCols : Extracted.RegisterAccessCols (ZMod p) where
  prev_value := #v[0, 0, 0, 0]
  access_timestamp := { prev_low := 0, diff_low_limb := 0 }

/-- The all-zero R-type adapter block of a padding row. -/
def zeroRTypeReaderCols : Extracted.RTypeReader (ZMod p) where
  op_a := 0
  op_a_memory := zeroAccessCols
  op_a_0 := 0
  op_b := 0
  op_b_memory := zeroAccessCols
  op_c := 0
  op_c_memory := zeroAccessCols

/-- The `Add` chip's padding row: every column zero, `is_real = 0`. -/
def addPaddingInputs : AddChip.Inputs (ZMod p) where
  is_real := 0
  state := { clk_high := 0, clk_16_24 := 0, clk_0_16 := 0, pc := #v[0, 0, 0] }
  adapter := zeroRTypeReaderCols

end SP1Clean.TraceGen
