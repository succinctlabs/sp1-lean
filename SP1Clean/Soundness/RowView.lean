import SP1Clean.Extracted.ALUTypeReader
import SP1Clean.Extracted.JTypeReader
import SP1Clean.Extracted.ITypeReader
import SP1Clean.Extracted.CPUState
import SP1Clean.Model.ProgramChip

/-! # Row-view adapter infrastructure (the chip-agnostic trace row)

The chip-agnostic per-row view the multi-chip soundness capstone is built on. A heterogeneous trace
mixing rows of different chips materialises one *homogeneous* `List RowView`, over which the State and
Program access projections are defined once and shared across chips.

`AdapterView` is the reader-agnostic register-adapter shape: the superset every reader
(`RTypeReader`/`ALUTypeReader`/`JTypeReader`/`ITypeReader`) projects into via its `toAdapterView`,
so the State/Program/Memory/Byte bus machinery never needs to know a row's reader type. `RowView`
bundles that adapter with the CPUState, the committed `next_pc`, the `is_real` selector, the rd
write value, and the Program-bus opcode. Each chip maps its `(inputs, cols)` to a `RowView` in its
`ChipKind.view` (`Soundness/ChipRow.lean`). The live normalized access vocabulary is kept beside the
view below: `StateAccess`/`stateAccess` and `ProgramAccess`/`programAccess`/`ProgramAccess.toRow`. -/

namespace SP1Clean.Trace

/-- The **reader-agnostic register adapter** the Memory/Program/Byte bus projections read. SP1 (and
the extraction) model the register adapter as *two distinct* column structs —
`Extracted.RTypeReader` (scalar `op_c`) and `Extracted.ALUTypeReader` (`Word`-typed `op_c` + an
`imm_c` immediate flag) — but a single heterogeneous trace materialises one *homogeneous*
`List RowView`, so `RowView.adapter` must be a single concrete type. `AdapterView` is that type: the
superset shape (`op_b op_c : Word`, `imm_b imm_c : F`) every reader projects into via its
`toAdapterView`. A pure R-type reader projects `op_b := #v[op_b, 0, 0, 0]`,
`op_c := #v[op_c, 0, 0, 0]`, `imm_b := imm_c := 0`, which makes the `is_real * (1 - imm_b/c)`
operand gating and the `op_b/c[1..3]`/`imm_b/c` Program-bus slots degenerate to pure scalar
behaviour. A J-type reader (JAL/AUIPC) projects `op_b := op_b_imm` (a full immediate `Word`),
`imm_b := 1`, so the op_b register access is gated off on every row (`is_real * (1 - 1) = 0`),
faithful to SP1 emitting no op_b memory interaction for an immediate operand. -/
structure AdapterView (F : Type) where
  op_a : F
  op_a_memory : Extracted.RegisterAccessCols F
  op_a_0 : F
  op_b : Word F
  op_b_memory : Extracted.RegisterAccessCols F
  imm_b : F
  op_c : Word F
  op_c_memory : Extracted.RegisterAccessCols F
  imm_c : F

/-- The chip-independent physical view of one generic RAM `MemoryAccess` block. The address is the
aligned three-limb key actually placed on SP1's Memory bus; `prev*` and `diff*` are the committed
timestamp columns, and `priorValue`/`newValue` are the pull/push cell words. Current clock limbs and
the activity gate come from the enclosing `RowView`.

This is deliberately a projection of the real chip row, not a second memory semantics. It exists so
the whole-machine grounding layer can state one load/store interaction and timestamp contract while
the chip-level `interactionsWith_memory_eq` theorem remains the authority for actual emissions. -/
structure RamAccessView (F : Type) where
  compareLow : F
  prevHigh : F
  prevLow : F
  diffLow : F
  diffHigh : F
  address : Vector F 3
  priorValue : Word F
  newValue : Word F

/-- The `RTypeReader` (scalar `op_c`, no immediate) projection: widen `op_c` to `#v[op_c, 0, 0, 0]`
and pin `imm_c := 0`. The op_c gating `is_real - imm_c` and the `op_c[1..3]`/`imm_c` Program slots
then collapse to the scalar R-type behaviour. -/
def _root_.SP1Clean.Extracted.RTypeReader.toAdapterView {F : Type} [Zero F]
    (c : Extracted.RTypeReader F) : AdapterView F :=
  { op_a := c.op_a, op_a_memory := c.op_a_memory, op_a_0 := c.op_a_0,
    op_b := #v[c.op_b, 0, 0, 0], op_b_memory := c.op_b_memory, imm_b := 0,
    op_c := #v[c.op_c, 0, 0, 0], op_c_memory := c.op_c_memory, imm_c := 0 }

/-- The `ALUTypeReader` (immediate-capable, `Word`-typed `op_c`) projection: op_b is still a scalar
register read (`#v[op_b, 0, 0, 0]`, `imm_b := 0`); op_c/imm_c are identity. -/
def _root_.SP1Clean.Extracted.ALUTypeReader.toAdapterView {F : Type} [Zero F]
    (c : Extracted.ALUTypeReader F) : AdapterView F :=
  { op_a := c.op_a, op_a_memory := c.op_a_memory, op_a_0 := c.op_a_0,
    op_b := #v[c.op_b, 0, 0, 0], op_b_memory := c.op_b_memory, imm_b := 0,
    op_c := c.op_c, op_c_memory := c.op_c_memory, imm_c := c.imm_c }

/-- The `JTypeReader` (JAL/AUIPC) projection: op_a is the rd register write; **both** op_b and op_c
are immediate `Word`s (`imm_b := imm_c := 1`), so their register accesses are gated off on every
row. J-type has no op_b/op_c memory columns, so the (gated-to-zero) memory slots reuse
`op_a_memory` as a harmless placeholder. -/
def _root_.SP1Clean.Extracted.JTypeReader.toAdapterView {F : Type} [Zero F] [One F]
    (c : Extracted.JTypeReader F) : AdapterView F :=
  { op_a := c.op_a, op_a_memory := c.op_a_memory, op_a_0 := c.op_a_0,
    op_b := c.op_b_imm, op_b_memory := c.op_a_memory, imm_b := 1,
    op_c := c.op_c_imm, op_c_memory := c.op_a_memory, imm_c := 1 }

/-- The `ITypeReader` (JALR / loads) projection: op_a is the rd register write, op_b is a scalar
register read (rs1, `#v[op_b, 0, 0, 0]`, `imm_b := 0`), and op_c is the **immediate** `op_c_imm`
(`imm_c := 1`), so the op_c register access is gated off on every row. I-type has no op_c memory
column, so the (gated-to-zero) op_c memory slot reuses `op_b_memory` as a harmless placeholder. -/
def _root_.SP1Clean.Extracted.ITypeReader.toAdapterView {F : Type} [Zero F] [One F]
    (c : Extracted.ITypeReader F) : AdapterView F :=
  { op_a := c.op_a, op_a_memory := c.op_a_memory, op_a_0 := c.op_a_0,
    op_b := #v[c.op_b, 0, 0, 0], op_b_memory := c.op_b_memory, imm_b := 0,
    op_c := c.op_c_imm, op_c_memory := c.op_b_memory, imm_c := 1 }

/-- **One committed contiguous memory write** (a store): `width` little-endian bytes of `value`
written at the byte address recombined from the three `AddressOperation` limbs
(`addrNat = a0 + a1·2^16 + a2·2^32`). The write-side projection of the Memory-bus `MemEvent`;
carried on a store `RowView`. Only the low `width` bytes of `value` are written — the high bytes of
SP1's read-modify-write `store_value` are irrelevant. -/
structure MemWrite (F : Type) where
  addr : Vector F 3
  value : Word F
  width : Nat

/-- **The two orthogonal write axes** a committed row may perform (the PC transition is always
committed, so it is not represented here): an optional **register write** — gated by `writesReg`,
the existing `op_a := rdWrite` — and an optional contiguous **memory write** (`some` only for
stores). This mirrors the Sail `SequentialState`'s split `regs`/`mem`: the real RISC-V mental model
is "each instruction transitions the PC, writes ≤ 1 register, and writes ≤ 1 contiguous memory
range." `writesReg` is exactly the (currently hardcoded-`true`) `opAEvent.is_write`. A hypothetical
reg+mem instruction (an atomic AMO) is expressible with both axes active — the two-axis model is the
long-term-viable generalization. -/
structure CommitEffect (F : Type) where
  writesReg : Bool
  memWrite : Option (MemWrite F)

namespace CommitEffect
/-- The common case — ALU / jump / normal load: write `op_a := rdWrite`, no memory write. -/
def regWrite {F : Type} : CommitEffect F := ⟨true, none⟩
/-- No register write, no memory write — Branch (`op_a = rs1` source), AluX0 / LoadX0
(`op_a = x0`). -/
def noWrite {F : Type} : CommitEffect F := ⟨false, none⟩
/-- A destination-writing reader whose table also accepts `rd = x0`.  SP1's canonical Program row
uses `op_a_0 = 0` exactly for a nonzero destination and `op_a_0 = 1` for `x0`; the Program-grounding
premise establishes that provenance before the effect is consumed.  JAL, JALR, and U-type share one
physical table across both cases, so their architectural effect is selected here rather than by
inventing separate chip kinds. -/
def destination {F : Type} [DecidableEq F] [Zero F] (opA0 : F) : CommitEffect F :=
  if opA0 = 0 then regWrite else noWrite
/-- No register write, one contiguous memory write — the stores (`op_a = rs2` is a read-back
self-write). -/
def store {F : Type} (mw : MemWrite F) : CommitEffect F := ⟨false, some mw⟩
end CommitEffect

/-- The **chip-agnostic** per-row columns the four interaction-bus projections read: the CPUState
and the reader-agnostic `AdapterView` blocks, the `is_real` selector, the rd write-back value (the
ALU result the Memory bus carries for the `op_a` write), and the Program-bus opcode. Every chip maps
to this via `ChipRow.view` (R-type readers through `RTypeReader.toAdapterView`, ALU readers through
`ALUTypeReader.toAdapterView`), so the machine grounding and execution layers share one normalized
view across chips. -/
structure RowView (F : Type) where
  state : Extracted.CPUState F
  /-- The committed `next_pc` (3 u16 limbs) the chip passes to `CPUState::eval` — the chip-agnostic
  trace shadow of SP1's dedicated `next_pc` column block (e.g. the Branch oracle row). For a
  straight-line chip it is `#v[pc[0]+4, pc[1], pc[2]]`; for a control-flow chip it is the
  data-dependent branch/jump target. Read abstractly through `Soundness.stateAccess`. -/
  next_pc : Vector F 3
  adapter : AdapterView F
  is_real : F
  rdWrite : Word F
  opcode : F
  /-- **The committed architectural write effect** (SC Phase 4): the register-write gate + the
  optional memory write. `.regWrite` for the register-writing chips (the common case), `.noWrite`
  for Branch / AluX0 / LoadX0, `.store ⟨…⟩` for the stores. Read only by the target-execution
  refinement layer (`Soundness/RowEffectDefs.lean` `replayVal`/`memReplayVal`/`RowEffect`); the bus
  projections ignore it. -/
  commit : CommitEffect F

end SP1Clean.Trace

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.ProgramChip (ProgramRow)

variable {p : ℕ}

/-! ## Live State and Program access views

These are semantic projections of `Trace.RowView`, not a second interaction ledger. The machine
grounding and Sail bridge layers use them to read the current/next PC and the committed instruction
row uniformly across all instruction chips. -/

/-- Per-row State access: clock components, current and committed next PC, clock advance, and the
activity gate. All currently supported instruction chips advance the SP1 clock by eight ticks. -/
structure StateAccess (F : Type) where
  clk_high : F
  clk_low : F
  pc : Vector F 3
  next_pc : Vector F 3
  clk_inc : F
  is_real : F

/-- Project a chip-independent row view to the State access consumed by the execution layer. -/
def stateAccess (r : Trace.RowView (ZMod p)) : StateAccess (ZMod p) :=
  { clk_high := r.state.clk_high
    clk_low := r.state.clk_0_16 + r.state.clk_16_24 * 65536
    pc := r.state.pc
    next_pc := r.next_pc
    clk_inc := 8
    is_real := r.is_real }

/-- Per-row Program access: the committed instruction-fetch fields plus the activity gate. -/
structure ProgramAccess (F : Type) where
  pc : Vector F 3
  opcode : F
  op_a : F
  op_b : Word F
  imm_b : F
  op_c : Word F
  op_a_0 : F
  imm_c : F
  is_real : F

/-- Project a chip-independent row view to the Program access consumed by decode grounding. -/
def programAccess (r : Trace.RowView (ZMod p)) : ProgramAccess (ZMod p) :=
  { pc := r.state.pc
    opcode := r.opcode
    op_a := r.adapter.op_a
    op_b := r.adapter.op_b
    imm_b := r.adapter.imm_b
    op_c := r.adapter.op_c
    op_a_0 := r.adapter.op_a_0
    imm_c := r.adapter.imm_c
    is_real := r.is_real }

/-- Drop the activity gate to obtain the canonical Program-table row. -/
def ProgramAccess.toRow (pa : ProgramAccess (ZMod p)) : ProgramRow (ZMod p) :=
  { pc0 := pa.pc[0]
    pc1 := pa.pc[1]
    pc2 := pa.pc[2]
    opcode := pa.opcode
    op_a := pa.op_a
    op_b := pa.op_b
    imm_b := pa.imm_b
    op_c := pa.op_c
    op_a_0 := pa.op_a_0
    imm_c := pa.imm_c }

end SP1Clean.Soundness
