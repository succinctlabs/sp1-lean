import SP1Clean.FormalModel.TraceGen.Events
import SP1Clean.FormalModel.Contracts.Chips
import SP1Clean.Extracted.MemoryAccess

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
  read) — and the `op_a_0` flag;
- `iTypeReaderCols` / `aluTypeReaderCols` / `jTypeReaderCols` ← the sibling `populate`s in
  `i_type.rs` / `alu_type.rs` / `j_type.rs`: the same `op_a` write block throughout, with the
  `op_c` slot replaced by a committed immediate word (`ITypeReader`, `JTypeReader`) or by a word
  *plus* an access block selected by `imm_c` (`ALUTypeReader`), and with `op_b` dropped entirely
  in the J-type case.

Everything here is a plain total function: no `Classical.choice`, no hint, no environment. The
*typed* output is the point — `SP1CleanTest/TraceGenTests/EventPopulate.lean` mirrors the same
populate functions as flat `List F` cell lists for the test library's compiled-evaluation
conformance battery, which cannot carry a proof obligation; these typed blocks are what the
reader-contract lemmas of `Readers.lean` are stated over.

The per-chip assembly at the bottom is deliberately trivial (three or four fields): the two
adapter blocks, which is where all the content lives, are shared by the whole family, so rolling a
new chip into this layer costs one `def` here and one `ProverAssumptions` lemma in its
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

-- The four limb projections, as `rfl`-lemmas. Deliberately not `@[simp]`, for the same reason the
-- block projections below are not: the memory chips read individual RAM limbs out of a built word
-- (the sub-word selection gates), and they should do so by citing one of these rather than by
-- normalizing the word.
lemma wordOfNat_zero (n : ℕ) : (wordOfNat (p := p) n)[0] = ((n % 2 ^ 16 : ℕ) : ZMod p) := rfl

lemma wordOfNat_one (n : ℕ) :
    (wordOfNat (p := p) n)[1] = ((n / 2 ^ 16 % 2 ^ 16 : ℕ) : ZMod p) := rfl

lemma wordOfNat_two (n : ℕ) :
    (wordOfNat (p := p) n)[2] = ((n / 2 ^ 32 % 2 ^ 16 : ℕ) : ZMod p) := rfl

lemma wordOfNat_three (n : ℕ) :
    (wordOfNat (p := p) n)[3] = ((n / 2 ^ 48 % 2 ^ 16 : ℕ) : ZMod p) := rfl

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

/-! ## The RAM access block

`MemoryAccessCols::populate` (same file as `RegisterAccessCols::populate`) differs from the
register block in exactly one way, and it is the interesting one: a RAM access commits **both**
halves of the previous timestamp (`prev_high` and `prev_low`) and a `compare_low` flag saying which
half the monotonicity argument compares, where a register access commits only `prev_low` and zeroes
it across a window boundary. That is why the memory family's event owes a bound on the clock and
the register families do not — the cross-window branch really does subtract high limbs. -/

/-- SP1's `populate_timestamp` comparison selector: `1` when the previous access happened in the
same 24-bit clock window as this one (so the *low* halves are compared), `0` when it did not (so
the *high* halves are). -/
def memCompareLow (prevTs currTs : ℕ) : ℕ :=
  if prevTs >>> 24 = currTs >>> 24 then 1 else 0

/-- SP1's `populate_timestamp` gap `current_time_value - prev_time_value - 1`, at whichever of the
two comparison halves `memCompareLow` selects. Committed as the limb pair
`diff_low_limb + diff_high_limb · 2^16`. -/
def memDiffOf (prevTs currTs : ℕ) : ℕ :=
  if prevTs >>> 24 = currTs >>> 24 then currTs % 2 ^ 24 - prevTs % 2 ^ 24 - 1
  else currTs >>> 24 - prevTs >>> 24 - 1

/-- SP1's `MemoryAccessCols::populate`: the cell's previous value as a committed word, the previous
access's two clock halves, the comparison selector, and the gap's two limbs. `currTs` is this row's
RAM access clock (`clk + 1`, `MemoryAccessPosition::Memory = 1`). -/
def memoryAccessCols (value prevTs currTs : ℕ) : Extracted.MemoryAccessCols (ZMod p) where
  prev_value := wordOfNat value
  access_timestamp :=
    { prev_high := ((prevTs >>> 24 : ℕ) : ZMod p)
      prev_low := ((prevTs % 2 ^ 24 : ℕ) : ZMod p)
      compare_low := ((memCompareLow prevTs currTs : ℕ) : ZMod p)
      diff_low_limb := ((memDiffOf prevTs currTs % 2 ^ 16 : ℕ) : ZMod p)
      diff_high_limb := ((memDiffOf prevTs currTs / 2 ^ 16 : ℕ) : ZMod p) }

lemma memoryAccessCols_prev_value (value prevTs currTs : ℕ) :
    (memoryAccessCols (p := p) value prevTs currTs).prev_value = wordOfNat value := rfl

lemma memoryAccessCols_prev_high (value prevTs currTs : ℕ) :
    (memoryAccessCols (p := p) value prevTs currTs).access_timestamp.prev_high
      = ((prevTs >>> 24 : ℕ) : ZMod p) := rfl

lemma memoryAccessCols_prev_low (value prevTs currTs : ℕ) :
    (memoryAccessCols (p := p) value prevTs currTs).access_timestamp.prev_low
      = ((prevTs % 2 ^ 24 : ℕ) : ZMod p) := rfl

lemma memoryAccessCols_compare_low (value prevTs currTs : ℕ) :
    (memoryAccessCols (p := p) value prevTs currTs).access_timestamp.compare_low
      = ((memCompareLow prevTs currTs : ℕ) : ZMod p) := rfl

lemma memoryAccessCols_diff_low_limb (value prevTs currTs : ℕ) :
    (memoryAccessCols (p := p) value prevTs currTs).access_timestamp.diff_low_limb
      = ((memDiffOf prevTs currTs % 2 ^ 16 : ℕ) : ZMod p) := rfl

lemma memoryAccessCols_diff_high_limb (value prevTs currTs : ℕ) :
    (memoryAccessCols (p := p) value prevTs currTs).access_timestamp.diff_high_limb
      = ((memDiffOf prevTs currTs / 2 ^ 16 : ℕ) : ZMod p) := rfl

/-- The all-zero RAM access block of a padding row. -/
def zeroMemoryAccessCols : Extracted.MemoryAccessCols (ZMod p) where
  prev_value := #v[0, 0, 0, 0]
  access_timestamp :=
    { prev_high := 0, prev_low := 0, compare_low := 0, diff_low_limb := 0, diff_high_limb := 0 }

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

/-! ## The `ITypeReader` block -/

/-- SP1's `ITypeReader::populate`: the two register indices and their access blocks at the
`MemoryAccessPosition` offsets `A = 4` / `B = 3`, the `rd = x0` flag, and the decoded immediate as
a committed word (`self.op_c_imm = Word::from(record.op_c)`) — no `op_c` register access. -/
def iTypeReaderCols (e : ITypeEvent) : Extracted.ITypeReader (ZMod p) where
  op_a := ((e.opA : ℕ) : ZMod p)
  op_a_memory := registerAccessCols e.prevA e.prevTsA (e.clk + 4)
  op_a_0 := if e.opA = 0 then 1 else 0
  op_b := ((e.opB : ℕ) : ZMod p)
  op_b_memory := registerAccessCols e.b e.prevTsB (e.clk + 3)
  op_c_imm := wordOfNat e.imm

lemma iTypeReaderCols_op_a (e : ITypeEvent) :
    (iTypeReaderCols (p := p) e).op_a = ((e.opA : ℕ) : ZMod p) := rfl

lemma iTypeReaderCols_op_a_0 (e : ITypeEvent) :
    (iTypeReaderCols (p := p) e).op_a_0 = if e.opA = 0 then 1 else 0 := rfl

lemma iTypeReaderCols_op_a_memory (e : ITypeEvent) :
    (iTypeReaderCols (p := p) e).op_a_memory
      = registerAccessCols e.prevA e.prevTsA (e.clk + 4) := rfl

lemma iTypeReaderCols_op_b_memory (e : ITypeEvent) :
    (iTypeReaderCols (p := p) e).op_b_memory = registerAccessCols e.b e.prevTsB (e.clk + 3) := rfl

lemma iTypeReaderCols_op_c_imm (e : ITypeEvent) :
    (iTypeReaderCols (p := p) e).op_c_imm = wordOfNat e.imm := rfl

/-! ## The `ALUTypeReader` block -/

/-- SP1's `ALUTypeReader::populate` for the `op_c` slot — the one **row-dependent** block in this
file. On an immediate row (`imm_c = 1`) the populate copies the committed `op_c` word into
`prev_value` and zeroes both timestamp columns; on a register row it fills the block from the
`rs2` read record at `MemoryAccessPosition::C = 2`, exactly as the R-type adapter does. -/
def aluTypeOpCCols (e : ALUTypeEvent) : Extracted.RegisterAccessCols (ZMod p) :=
  if e.immC = 1 then
    { prev_value := wordOfNat e.opC, access_timestamp := { prev_low := 0, diff_low_limb := 0 } }
  else registerAccessCols e.c e.prevTsC (e.clk + 2)

/-- On a register row the `op_c` block is the ordinary `rs2` read block, so every R-type lemma
about `registerAccessCols` applies to it verbatim. -/
lemma aluTypeOpCCols_of_reg {e : ALUTypeEvent} (h : e.immC = 0) :
    aluTypeOpCCols (p := p) e = registerAccessCols e.c e.prevTsC (e.clk + 2) := by
  rw [aluTypeOpCCols, if_neg (by omega)]

/-- SP1's `ALUTypeReader::populate`: as the R-type block, but the `op_c` slot is the committed
word `Word::from(record.op_c)` plus the row-dependent access block above, and the row commits the
`imm_c` flag. -/
def aluTypeReaderCols (e : ALUTypeEvent) : Extracted.ALUTypeReader (ZMod p) where
  op_a := ((e.opA : ℕ) : ZMod p)
  op_a_memory := registerAccessCols e.prevA e.prevTsA (e.clk + 4)
  op_a_0 := if e.opA = 0 then 1 else 0
  op_b := ((e.opB : ℕ) : ZMod p)
  op_b_memory := registerAccessCols e.b e.prevTsB (e.clk + 3)
  op_c := wordOfNat e.opC
  op_c_memory := aluTypeOpCCols e
  imm_c := ((e.immC : ℕ) : ZMod p)

lemma aluTypeReaderCols_op_a (e : ALUTypeEvent) :
    (aluTypeReaderCols (p := p) e).op_a = ((e.opA : ℕ) : ZMod p) := rfl

lemma aluTypeReaderCols_op_a_0 (e : ALUTypeEvent) :
    (aluTypeReaderCols (p := p) e).op_a_0 = if e.opA = 0 then 1 else 0 := rfl

lemma aluTypeReaderCols_op_a_memory (e : ALUTypeEvent) :
    (aluTypeReaderCols (p := p) e).op_a_memory
      = registerAccessCols e.prevA e.prevTsA (e.clk + 4) := rfl

lemma aluTypeReaderCols_op_b_memory (e : ALUTypeEvent) :
    (aluTypeReaderCols (p := p) e).op_b_memory
      = registerAccessCols e.b e.prevTsB (e.clk + 3) := rfl

lemma aluTypeReaderCols_op_c (e : ALUTypeEvent) :
    (aluTypeReaderCols (p := p) e).op_c = wordOfNat e.opC := rfl

lemma aluTypeReaderCols_op_c_memory (e : ALUTypeEvent) :
    (aluTypeReaderCols (p := p) e).op_c_memory = aluTypeOpCCols e := rfl

lemma aluTypeReaderCols_imm_c (e : ALUTypeEvent) :
    (aluTypeReaderCols (p := p) e).imm_c = ((e.immC : ℕ) : ZMod p) := rfl

/-! ## The `JTypeReader` block -/

/-- SP1's `JTypeReader::populate`: the destination index, its write access block at
`MemoryAccessPosition::A = 4`, the `rd = x0` flag, and the two decoded immediates as committed
words — a J-type row makes no other register access. -/
def jTypeReaderCols (e : JTypeEvent) : Extracted.JTypeReader (ZMod p) where
  op_a := ((e.opA : ℕ) : ZMod p)
  op_a_memory := registerAccessCols e.prevA e.prevTsA (e.clk + 4)
  op_a_0 := if e.opA = 0 then 1 else 0
  op_b_imm := wordOfNat e.immB
  op_c_imm := wordOfNat e.immC

lemma jTypeReaderCols_op_a (e : JTypeEvent) :
    (jTypeReaderCols (p := p) e).op_a = ((e.opA : ℕ) : ZMod p) := rfl

lemma jTypeReaderCols_op_a_0 (e : JTypeEvent) :
    (jTypeReaderCols (p := p) e).op_a_0 = if e.opA = 0 then 1 else 0 := rfl

lemma jTypeReaderCols_op_a_memory (e : JTypeEvent) :
    (jTypeReaderCols (p := p) e).op_a_memory
      = registerAccessCols e.prevA e.prevTsA (e.clk + 4) := rfl

lemma jTypeReaderCols_op_b_imm (e : JTypeEvent) :
    (jTypeReaderCols (p := p) e).op_b_imm = wordOfNat e.immB := rfl

/-! ## Per-chip assembly

One `def` per chip. The chip's `Inputs` is the `is_real` selector plus the shared `state` and
adapter blocks (and, for `UType`, the variant flag), so there is nothing chip-specific to build. -/

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

/-- The `Sub` chip's committed input row for one event — a **real** row (`is_real = 1`). -/
def RTypeEvent.toSubInputs (e : RTypeEvent) : SubChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := rTypeReaderCols e

/-- The `Subw` chip's committed input row for one event — a **real** row (`is_real = 1`). -/
def RTypeEvent.toSubwInputs (e : RTypeEvent) : SubwChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := rTypeReaderCols e

/-- The `Addi` chip's committed input row for one event — a **real** row (`is_real = 1`). -/
def ITypeEvent.toAddiInputs (e : ITypeEvent) : AddiChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e

/-- The `Addw` chip's committed input row for one event — a **real** row (`is_real = 1`). -/
def ALUTypeEvent.toAddwInputs (e : ALUTypeEvent) : AddwChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := aluTypeReaderCols e

lemma ALUTypeEvent.toAddwInputs_adapter (e : ALUTypeEvent) :
    (e.toAddwInputs (p := p)).adapter = aluTypeReaderCols e := rfl

/-- The `UType` chip's committed input row for one event — a **real** row (`is_real = 1`). The
extra committed column beyond the two shared blocks is the variant selector, read off the event's
own opcode discriminant (`Opcode::AUIPC = 48`, `Opcode::LUI = 49`; the chip's `Spec` recombines it
as `is_auipc * 48 + (1 - is_auipc) * 49`). -/
def JTypeEvent.toUTypeInputs (e : JTypeEvent) : UTypeChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := jTypeReaderCols e
  is_auipc := if e.opcode = 48 then 1 else 0

/-- The `Jal` chip's committed input row for one event — a **real** row (`is_real = 1`). Same three
fields as `UType`'s, minus the variant selector: the two chips share the whole `JTypeReader` block
and differ only in what the immediates mean. -/
def JTypeEvent.toJalInputs (e : JTypeEvent) : JalChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := jTypeReaderCols e

lemma JTypeEvent.toJalInputs_state (e : JTypeEvent) :
    (e.toJalInputs (p := p)).state = cpuStateCols e.clk e.pc := rfl

lemma JTypeEvent.toJalInputs_adapter (e : JTypeEvent) :
    (e.toJalInputs (p := p)).adapter = jTypeReaderCols e := rfl

/-- The `Jalr` chip's committed input row for one event — a **real** row (`is_real = 1`). The
`ITypeReader` block is the very one `Addi` and the memory chips build; `Jalr`'s jump base is the
`op_b` register read carried inside it. -/
def ITypeEvent.toJalrInputs (e : ITypeEvent) : JalrChip.Inputs (ZMod p) where
  is_real := 1
  state := cpuStateCols e.clk e.pc
  adapter := iTypeReaderCols e

lemma ITypeEvent.toJalrInputs_state (e : ITypeEvent) :
    (e.toJalrInputs (p := p)).state = cpuStateCols e.clk e.pc := rfl

lemma ITypeEvent.toJalrInputs_adapter (e : ITypeEvent) :
    (e.toJalrInputs (p := p)).adapter = iTypeReaderCols e := rfl

lemma JTypeEvent.toUTypeInputs_is_auipc (e : JTypeEvent) :
    (e.toUTypeInputs (p := p)).is_auipc = if e.opcode = 48 then 1 else 0 := rfl

lemma JTypeEvent.toUTypeInputs_adapter (e : JTypeEvent) :
    (e.toUTypeInputs (p := p)).adapter = jTypeReaderCols e := rfl

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

/-- The all-zero I-type adapter block of a padding row. -/
def zeroITypeReaderCols : Extracted.ITypeReader (ZMod p) where
  op_a := 0
  op_a_memory := zeroAccessCols
  op_a_0 := 0
  op_b := 0
  op_b_memory := zeroAccessCols
  op_c_imm := #v[0, 0, 0, 0]

/-- The all-zero ALU-type adapter block of a padding row. -/
def zeroALUTypeReaderCols : Extracted.ALUTypeReader (ZMod p) where
  op_a := 0
  op_a_memory := zeroAccessCols
  op_a_0 := 0
  op_b := 0
  op_b_memory := zeroAccessCols
  op_c := #v[0, 0, 0, 0]
  op_c_memory := zeroAccessCols
  imm_c := 0

/-- The all-zero J-type adapter block of a padding row. -/
def zeroJTypeReaderCols : Extracted.JTypeReader (ZMod p) where
  op_a := 0
  op_a_memory := zeroAccessCols
  op_a_0 := 0
  op_b_imm := #v[0, 0, 0, 0]
  op_c_imm := #v[0, 0, 0, 0]

/-- The all-zero `CPUState` block of a padding row. -/
def zeroCPUStateCols : Extracted.CPUState (ZMod p) where
  clk_high := 0
  clk_16_24 := 0
  clk_0_16 := 0
  pc := #v[0, 0, 0]

/-- The `Add` chip's padding row: every column zero, `is_real = 0`. -/
def addPaddingInputs : AddChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroRTypeReaderCols

/-- The `Sub` chip's padding row: every column zero, `is_real = 0`. -/
def subPaddingInputs : SubChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroRTypeReaderCols

/-- The `Subw` chip's padding row: every column zero, `is_real = 0`. -/
def subwPaddingInputs : SubwChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroRTypeReaderCols

/-- The `Addi` chip's padding row: every column zero, `is_real = 0`. -/
def addiPaddingInputs : AddiChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroITypeReaderCols

/-- The `Addw` chip's padding row: every column zero, `is_real = 0` (and `imm_c = 0`, the
register-row form the chip's `ProverAssumptions` asks for). -/
def addwPaddingInputs : AddwChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroALUTypeReaderCols

/-- The `Jal` chip's padding row: every column zero, `is_real = 0`. The two `value[3] = 0` conjuncts
the chip carries **ungated** hold on it, since a zero row's two `AddOperation` results are `0 + 0`
and `0 + 4`. -/
def jalPaddingInputs : JalChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroJTypeReaderCols

/-- The `Jalr` chip's padding row: every column zero, `is_real = 0` (same two ungated
`value[3] = 0` conjuncts as `Jal`). -/
def jalrPaddingInputs : JalrChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroITypeReaderCols

/-- The `UType` chip's padding row: every column zero, `is_real = 0` (so `is_auipc = 0`, the LUI
form — and the decode relation the chip's `ProverAssumptions` carries **ungated** holds on it,
since `RV64.lui 0 = 0` is the zero word's value). -/
def uTypePaddingInputs : UTypeChip.Inputs (ZMod p) where
  is_real := 0
  state := zeroCPUStateCols
  adapter := zeroJTypeReaderCols
  is_auipc := 0

end SP1Clean.TraceGen
