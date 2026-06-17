import SP1Clean.Soundness.TargetVm
import SP1Clean.Soundness.ProgramConsistency
import SP1Clean.Soundness.Opcode

/-! # W3 — the decode half of `OperandsBound` (trusted Program path)

The decode component of the target theorem's `OperandsBound` (`Soundness/TargetVm.lean`): each real
row's committed Program-bus operand columns are the **decode of the instruction word at its pc**, built
on the official LeanRV64D decoder (`ext_decode`/`encdec_backwards`) so fetch-decode coherence with
`try_step` holds by construction.

* `instrToProgramRow` projects a decoded LeanRV64D `instruction` to the committed Program-bus column
  shape (`ProgramChip.ProgramRow`), mirroring `Channels.ProgramMsg` / `ProgramConsistency.programAccess`
  (R-type arm first; the other opcode families follow the same convention).
* `DecodeOperandsBound prog` is the concrete decode conjunct of `OperandsBound`.
* `decodedInROM prog` is the "committed program table = decode of the guest ROM" membership predicate —
  the trusted-path instantiation of `ProgramConsistency.inROM` connecting the *encoded* `GuestProgram.rom`
  to the *decoded* committed columns.
* `decode_bound` derives `DecodeOperandsBound` for every real walk row from the (threaded) Program-bus
  consistency `TraceProgramValid rows (decodedInROM prog)` — the decode half of `TargetObligations.bound`.

The full discharge of the threaded consistency from bus balance (a `ProgramProvider (decodedInROM prog)`
via `programConsistent_of_balance`) and the W7 `try_step` decode-stage reduction that *consumes* this
predicate are tracked separately (roadmap W3 discharge / W7). -/

namespace SP1Clean.Soundness.Target

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.ProgramChip (ProgramRow)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 24 < p); omega⟩

/-! ## The decode projection: LeanRV64D `instruction` → committed Program-bus columns -/

/-- A register index as the field element committed on the Program bus (its 5-bit value, `0..31`). -/
def regidxVal (r : regidx) : ZMod p := match r with | .Regidx b => (b.toNat : ZMod p)

/-- A 64-bit value as the committed `Word` (four little-endian 16-bit limbs as field elements) — the
inverse of `Word.toBitVec64`, matching SP1's `Word::from_le_bits` for a (sign-extended) immediate. -/
def bitVecToWord (v : BitVec 64) : Word (ZMod p) :=
  #v[((BitVec.extractLsb' 0 16 v).toNat : ZMod p),
     ((BitVec.extractLsb' 16 16 v).toNat : ZMod p),
     ((BitVec.extractLsb' 32 16 v).toNat : ZMod p),
     ((BitVec.extractLsb' 48 16 v).toNat : ZMod p)]

/-- LeanRV64D R-type op → SP1 `Opcode` (the committed `opcode` discriminant via `Opcode.toNat`).
The 32-bit-word arms (`ADDW`…) are a distinct AST constructor (`RTYPEW`/`ropw`), handled separately. -/
def ropToOpcode : rop → Opcode
  | .ADD => .ADD | .SUB => .SUB | .SLL => .SLL | .SLT => .SLT | .SLTU => .SLTU
  | .XOR => .XOR | .SRL => .SRL | .SRA => .SRA | .OR => .OR | .AND => .AND

/-- LeanRV64D I-type op → SP1 `Opcode`. Only `ADDI` is its own opcode; the rest commit their R-type
opcode distinguished by `imm_c = 1` (SP1's `disassembler/rrs.rs`: `XORI → XOR`, `ORI → OR`,
`ANDI → AND`, `SLTI → SLT`, `SLTIU → SLTU`). -/
def iopToOpcode : iop → Opcode
  | .ADDI => .ADDI | .SLTI => .SLT | .SLTIU => .SLTU
  | .XORI => .XOR | .ORI => .OR | .ANDI => .AND

/-- U-type op → SP1 `Opcode` (`LUI`/`AUIPC` are their own opcodes). -/
def uopToOpcode : uop → Opcode | .LUI => .LUI | .AUIPC => .AUIPC

/-- Branch op → SP1 `Opcode`. -/
def bopToOpcode : bop → Opcode
  | .BEQ => .BEQ | .BNE => .BNE | .BLT => .BLT | .BGE => .BGE | .BLTU => .BLTU | .BGEU => .BGEU

/-- Load op → SP1 `Opcode`, keyed on byte-width (`word_width` is the byte count `1/2/4/8`) and the
unsigned flag (`disassembler/rrs.rs`: `LB/LBU/LH/LHU/LW/LWU/LD`). -/
def loadOpcode (width : word_width) (isU : Bool) : Opcode :=
  if width == 1 then (if isU then .LBU else .LB)
  else if width == 2 then (if isU then .LHU else .LH)
  else if width == 4 then (if isU then .LWU else .LW)
  else .LD

/-- Store op → SP1 `Opcode`, keyed on byte-width (`SB/SH/SW/SD`). -/
def storeOpcode (width : word_width) : Opcode :=
  if width == 1 then .SB else if width == 2 then .SH else if width == 4 then .SW else .SD

/-- Shift-immediate op → SP1 `Opcode` (shifts share the R-type shift opcode, `imm_c = 1`). -/
def sopToOpcode : sop → Opcode | .SLLI => .SLL | .SRLI => .SRL | .SRAI => .SRA

/-- Word shift-immediate op → SP1 `Opcode`. -/
def sopwToOpcode : sopw → Opcode | .SLLIW => .SLLW | .SRLIW => .SRLW | .SRAIW => .SRAW

/-- RV64 word R-type op → SP1 `Opcode`. -/
def ropwToOpcode : ropw → Opcode
  | .ADDW => .ADDW | .SUBW => .SUBW | .SLLW => .SLLW | .SRLW => .SRLW | .SRAW => .SRAW

/-- M-extension multiply descriptor → SP1 `Opcode`: `result_part = Low` is `MUL`; the high-half forms
split on operand signedness (`MULH` signed×signed, `MULHU` unsigned×unsigned, `MULHSU` signed×unsigned).
The `High, Unsigned, Signed` combination is not a RISC-V instruction (defaulted, unreachable in decode). -/
def mulOpToOpcode (m : mul_op) : Opcode :=
  match m.result_part, m.signed_rs1, m.signed_rs2 with
  | .Low, _, _ => .MUL
  | .High, .Signed, .Signed => .MULH
  | .High, .Unsigned, .Unsigned => .MULHU
  | .High, .Signed, .Unsigned => .MULHSU
  | .High, .Unsigned, .Signed => .MULHSU

/-- Project a decoded LeanRV64D `instruction` (at a given pc) to the committed Program-bus row. R-type:
`RTYPE (rs2, rs1, rd, op)` (the LeanRV64D tuple order, matching `AddSail.spec_add`/`execute_RTYPE`) maps
to `op_a := rd`, `op_b := #v[rs1,0,0,0]`, `op_c := #v[rs2,0,0,0]`, `imm_b = imm_c = 0`,
`op_a_0 := (rd == x0)`. Other opcode families are `none` here (slice 2). -/
def instrToProgramRow (pc : Vector (ZMod p) 3) : instruction → Option (ProgramRow (ZMod p))
  | .RTYPE (rs2, rs1, rd, op) =>
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((ropToOpcode op).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := #v[regidxVal rs2, 0, 0, 0],
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 0 }
  | .ITYPE (imm, rs1, rd, op) =>
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((iopToOpcode op).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := bitVecToWord (imm.signExtend 64),
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 1 }
  | .UTYPE (imm, rd, op) =>
      -- LUI/AUIPC: op_b = op_c = sign-extended (imm << 12); both immediates.
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((uopToOpcode op).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := bitVecToWord ((imm.signExtend 64) <<< 12),
             imm_b := 1,
             op_c := bitVecToWord ((imm.signExtend 64) <<< 12),
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 1 }
  | .JAL (imm, rd) =>
      -- JAL: op_a = rd, op_b = sign-extended jump offset (immediate), op_c = 0.
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((Opcode.JAL).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := bitVecToWord (imm.signExtend 64),
             imm_b := 1,
             op_c := #v[0, 0, 0, 0],
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 1 }
  | .JALR (imm, rs1, rd) =>
      -- JALR: I-type-shaped — op_a = rd, op_b = rs1 (register), op_c = sign-extended immediate.
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((Opcode.JALR).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := bitVecToWord (imm.signExtend 64),
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 1 }
  | .BTYPE (imm, rs2, rs1, op) =>
      -- Branches have no destination: op_a = rs1 (source), op_b = rs2 (source), op_c = offset.
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((bopToOpcode op).toNat : ZMod p),
             op_a := regidxVal rs1,
             op_b := #v[regidxVal rs2, 0, 0, 0],
             imm_b := 0,
             op_c := bitVecToWord (imm.signExtend 64),
             op_a_0 := if regidxVal (p := p) rs1 = 0 then 1 else 0,
             imm_c := 1 }
  | .LOAD (imm, rs1, rd, isU, width) =>
      -- Loads: op_a = rd, op_b = rs1 (base register), op_c = sign-extended offset.
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((loadOpcode width isU).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := bitVecToWord (imm.signExtend 64),
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 1 }
  | .STORE (imm, rs2, rs1, width) =>
      -- Stores have no destination: op_a = rs2 (value source), op_b = rs1 (base), op_c = offset.
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((storeOpcode width).toNat : ZMod p),
             op_a := regidxVal rs2,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := bitVecToWord (imm.signExtend 64),
             op_a_0 := if regidxVal (p := p) rs2 = 0 then 1 else 0,
             imm_c := 1 }
  | .SHIFTIOP (shamt, rs1, rd, op) =>
      -- SLLI/SRLI/SRAI: I-type shape, op_c = zero-extended shift amount.
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((sopToOpcode op).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := bitVecToWord (shamt.setWidth 64),
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 1 }
  | .SHIFTIWOP (shamt, rs1, rd, op) =>
      -- SLLIW/SRLIW/SRAIW: I-type shape, op_c = zero-extended (5-bit) shift amount.
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((sopwToOpcode op).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := bitVecToWord (shamt.setWidth 64),
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 1 }
  | .ADDIW (imm, rs1, rd) =>
      -- ADDIW: no own opcode — commits ADDW with imm_c = 1 (I-type shape).
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((Opcode.ADDW).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := bitVecToWord (imm.signExtend 64),
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 1 }
  | .RTYPEW (rs2, rs1, rd, op) =>
      -- ADDW/SUBW/SLLW/SRLW/SRAW: R-type shape.
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((ropwToOpcode op).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := #v[regidxVal rs2, 0, 0, 0],
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 0 }
  | .MUL (rs2, rs1, rd, m) =>
      -- MUL/MULH/MULHU/MULHSU: R-type shape, opcode from the multiply descriptor.
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((mulOpToOpcode m).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := #v[regidxVal rs2, 0, 0, 0],
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 0 }
  | .MULW (rs2, rs1, rd) =>
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((Opcode.MULW).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := #v[regidxVal rs2, 0, 0, 0],
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 0 }
  | .DIV (rs2, rs1, rd, isU) =>
      -- DIV/DIVU: R-type shape, opcode by signedness.
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := (((if isU then Opcode.DIVU else Opcode.DIV)).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := #v[regidxVal rs2, 0, 0, 0],
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 0 }
  | .DIVW (rs2, rs1, rd, isU) =>
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := (((if isU then Opcode.DIVUW else Opcode.DIVW)).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := #v[regidxVal rs2, 0, 0, 0],
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 0 }
  | .REM (rs2, rs1, rd, isU) =>
      -- REM/REMU: R-type shape, opcode by signedness.
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := (((if isU then Opcode.REMU else Opcode.REM)).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := #v[regidxVal rs2, 0, 0, 0],
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 0 }
  | .REMW (rs2, rs1, rd, isU) =>
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := (((if isU then Opcode.REMUW else Opcode.REMW)).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := #v[regidxVal rs2, 0, 0, 0],
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 0 }
  | _ => none

omit [Fact (2 ^ 24 < p)] in
/-- The R-type projection, unfolded — the committed Program-bus column shape an `RTYPE` decode produces
(`op_a = rd`, `op_b[0] = rs1`, `op_c[0] = rs2`, high limbs and immediate flags `0`, opcode the SP1
discriminant). The definitional spec of `instrToProgramRow` on R-type, the anchor a W7 `try_step` decode
reduction lands against. -/
theorem instrToProgramRow_rtype (pc : Vector (ZMod p) 3) (rs2 rs1 rd : regidx) (op : rop) :
    instrToProgramRow pc (.RTYPE (rs2, rs1, rd, op)) =
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((ropToOpcode op).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := #v[regidxVal rs2, 0, 0, 0],
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 0 } := rfl

omit [Fact (2 ^ 24 < p)] in
/-- The I-type projection, unfolded — `op_a = rd`, `op_b[0] = rs1`, `op_c = sign-extended immediate`
(as little-endian limbs), `imm_c = 1`, opcode the SP1 discriminant (`ADDI` its own; the rest the R-type
opcode, per `iopToOpcode`). -/
theorem instrToProgramRow_itype (pc : Vector (ZMod p) 3) (imm : BitVec 12) (rs1 rd : regidx) (op : iop) :
    instrToProgramRow pc (.ITYPE (imm, rs1, rd, op)) =
      some { pc0 := pc[0], pc1 := pc[1], pc2 := pc[2],
             opcode := ((iopToOpcode op).toNat : ZMod p),
             op_a := regidxVal rd,
             op_b := #v[regidxVal rs1, 0, 0, 0],
             imm_b := 0,
             op_c := bitVecToWord (imm.signExtend 64),
             op_a_0 := if regidxVal (p := p) rd = 0 then 1 else 0,
             imm_c := 1 } := rfl

/-- The pc-limb vector of a program row. -/
def rowPcVec (row : ProgramRow (ZMod p)) : Vector (ZMod p) 3 := #v[row.pc0, row.pc1, row.pc2]

/-- The 64-bit pc a program row's limbs reassemble to (the `fetchWord` key). -/
def pcBitsOfRow (row : ProgramRow (ZMod p)) : BitVec 64 :=
  pcBitsOfVals row.pc0.val row.pc1.val row.pc2.val

/-! ## The decode conjunct of `OperandsBound` and the program-ROM membership -/

/-- **The decode component of `OperandsBound`.** In a configured state, the word fetched at the row's pc
decodes (via the official `ext_decode`) to an instruction whose projection equals the row's committed
Program-bus columns. Built on `ext_decode` so a W7 `try_step` decode-stage reduction sees the same
function. -/
def DecodeOperandsBound (prog : GuestProgram) (r : Trace.RowView (ZMod p)) (s : SailState) : Prop :=
  SailConfigured s → ∀ w, prog.fetchWord (rcvPcOf (stateAccess r)) = some w →
    ∃ i s', (ext_decode w).run s = .ok i s' ∧
      instrToProgramRow r.state.pc i = some (programAccess r).toRow

/-- **The trusted program table = decode of the guest ROM.** The `inROM` membership predicate for a
`GuestProgram`: a row is valid iff it is the decode of the instruction word the guest ROM holds at the
row's pc. Instantiating `ProgramConsistency`'s `inROM` with this connects the encoded `GuestProgram.rom`
to the decoded committed columns. (Discharged from bus balance via a `ProgramProvider (decodedInROM prog)`
— tracked separately.) -/
def decodedInROM (prog : GuestProgram) (row : ProgramRow (ZMod p)) : Prop :=
  ∃ w, prog.fetchWord (pcBitsOfRow row) = some w ∧
    ∀ s, SailConfigured s → ∃ i s', (ext_decode w).run s = .ok i s' ∧
      instrToProgramRow (rowPcVec row) i = some row

/-! ## The decode half of `TargetObligations.bound` -/

/-- **The decode half of `TargetObligations.bound`.** Every real walk row satisfies the decode conjunct
of `OperandsBound`, derived from the (threaded) Program-bus consistency that the committed program table
is the decode of the guest ROM (`decodedInROM`). The `WalkOf` trail consists of real rows
(`trail_rows_real`), each a row of the trace, so program consistency hands it its `decodedInROM` fact —
which is exactly `DecodeOperandsBound` at the row's pc. -/
theorem decode_bound (prog : GuestProgram) {pi : SP1PublicIO (ZMod p)}
    {rows : List (ChipRow p)} {path : List (Trace.RowView (ZMod p))}
    (h_link : TraceProgramValid (rows.map ChipRow.view) (decodedInROM prog))
    (hw : WalkOf pi rows path) {i : ℕ} (hi : i < path.length) (s : SailState) :
    DecodeOperandsBound prog (path[i]'hi) s := by
  intro hcfg w hfetch
  set r := path[i]'hi with hr_def
  have hr_path : r ∈ path := List.getElem_mem hi
  -- the walk row is a real row of the trace
  have hmem : r ∈ realRowEdges (rows.map ChipRow.view) :=
    Multiset.mem_of_le hw.2 (Multiset.mem_coe.mpr hr_path)
  rw [realRowEdges, Multiset.mem_filter] at hmem
  obtain ⟨hr_coe, h_real⟩ := hmem
  have hr_rows : r ∈ rows.map ChipRow.view := Multiset.mem_coe.mp hr_coe
  -- its committed program columns lie in the decoded ROM
  have ha_mem : programAccess r ∈ aggregateProgramAccesses (rows.map ChipRow.view) := by
    simp only [aggregateProgramAccesses]; exact List.mem_map_of_mem hr_rows
  have h_real' : (programAccess r).is_real ≠ 0 := by
    simpa only [programAccess, stateAccess] using h_real
  obtain ⟨w₀, hfetch₀, hdec⟩ := h_link.rom_holds (programAccess r) ha_mem h_real'
  -- the fetched words agree (same pc key)
  have hpc : pcBitsOfRow (programAccess r).toRow = rcvPcOf (stateAccess r) := by
    simp only [pcBitsOfRow, rcvPcOf, programAccess, ProgramAccess.toRow, stateAccess]
  rw [hpc, hfetch] at hfetch₀
  obtain rfl : w = w₀ := Option.some.inj hfetch₀
  -- the pc vectors agree, so the projection's target is the committed row
  have hpcvec : rowPcVec (programAccess r).toRow = r.state.pc := by
    simp only [rowPcVec, programAccess, ProgramAccess.toRow]
    apply Vector.ext; intro j hj
    interval_cases j <;> simp
  obtain ⟨ii, s', hrun, hproj⟩ := hdec s hcfg
  exact ⟨ii, s', hrun, by rw [hpcvec] at hproj; exact hproj⟩

/-! ## Wiring the decode predicate into `TargetObligations` -/

/-- **The `TargetObligations.bound` field, discharged by decode.** Exactly the shape of the `bound`
field of `TargetVm.TargetObligations` instantiated at `OperandsBound := DecodeOperandsBound prog`,
proved from the threaded Program-bus consistency via `decode_bound`. This is the decode seam closed at
the obligation level. -/
theorem decode_targetBound (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (rows : List (ChipRow p))
    (h_link : TraceProgramValid (rows.map ChipRow.view) (decodedInROM prog)) :
    ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ i (hi : i < path.length) s, RefinesAt prog s0 path i s →
        DecodeOperandsBound prog (path[i]'hi) s := by
  intro s0 path _h0 hw i hi s _href
  exact decode_bound prog h_link hw hi s

/-- **`DecodeOperandsBound` is a valid `OperandsBound` for the target theorem.** Assemble a full
`TargetObligations` for `OperandsBound := DecodeOperandsBound prog`: the `bound` field is discharged by
`decode_targetBound` (from the threaded Program-bus consistency), and `lift`/`halt`/`halt_nonempty` are
taken as the remaining named seams (W7 step-lift, W5 ECALL/HALT). Feeding the result into
`Target.sp1_target_execution` yields the machine-level theorem with the *concrete* decode-derived
`OperandsBound`, with exactly the W7/W5 obligations open. -/
def targetObligations_of_decode (prog : GuestProgram) (pi : SP1TargetPublicIO (ZMod p))
    (rows : List (ChipRow p))
    (h_link : TraceProgramValid (rows.map ChipRow.view) (decodedInROM prog))
    (h_lift : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ i (hi : i + 1 < path.length) s,
        RefinesAt prog s0 path i s → DecodeOperandsBound prog (path[i]'(by omega)) s →
        ∃ s', SailStep s s' ∧ RowEffect prog (path[i]'(by omega)) s s')
    (h_halt_nonempty : ∀ path, WalkOf pi.toLegacy rows path → path ≠ [])
    (h_halt : ∀ s0 path, IsInitialState prog s0 → WalkOf pi.toLegacy rows path →
      ∀ (hne : path ≠ []) s,
        RefinesAt prog s0 path (path.length - 1) s →
        DecodeOperandsBound prog (path[path.length - 1]'(by
          have := List.length_pos_of_ne_nil hne; omega)) s →
        SP1Halted prog (exitOf pi.exit_code) s) :
    TargetObligations prog pi rows (DecodeOperandsBound prog) where
  bound := decode_targetBound prog pi rows h_link
  lift := h_lift
  halt_nonempty := h_halt_nonempty
  halt := h_halt

end SP1Clean.Soundness.Target
