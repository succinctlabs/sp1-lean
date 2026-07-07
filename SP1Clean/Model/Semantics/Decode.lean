import SP1Clean.Model.Opcode
import SP1Clean.Model.ProgramChip
import SP1Clean.Model.Semantics.GuestProgram
import SP1Clean.Model.SailDecode
import SP1Clean.Math.Word

/-! # Decode core — LeanRV64D `instruction` → committed Program-bus columns (`Model/Semantics/`)

The decode projection `instrToProgramRow` and the ROM-membership predicate `decodedInROM`, relocated
DOWN to `Model/Semantics/` (from `Soundness/Decode.lean`) so the Program channel's semantic guarantee
`ProgTruth` (`Model/Semantics/Truth.lean`) can reference `decodedInROM`. Built on the official
`ext_decode`/`encdec_backwards` decoder so fetch-decode coherence with `try_step` holds by construction.
The `RowView`/`TargetObligations`-coupled theorems (`DecodeOperandsBound`, `decode_bound`, …) stay in
`Soundness/Decode.lean`, which imports this core. Namespace `SP1Clean.Soundness.Target` is unchanged
(decoupled from path), so every `instrToProgramRow`/`decodedInROM` reference resolves as before. -/

namespace SP1Clean.Soundness.Target

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.ProgramChip (ProgramRow)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

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

omit [Fact (2 ^ 17 < p)] in
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

omit [Fact (2 ^ 17 < p)] in
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

/-! ## Decode inversion — the committed row's `(opcode, imm_c)` pins the R-type instruction (W7) -/

/-- Every SP1 opcode discriminant is `< 53` — so it casts injectively into `ZMod p` (`2^17 < p`). -/
theorem opcode_toNat_lt (o : Opcode) : o.toNat < 53 := by cases o <;> decide

/-- **Opcode cast reflection (generic).** In `ZMod p` (`2^17 < p`), two opcode discriminants equal as
field elements are equal in `ℕ` — the injectivity of `Nat.cast` on the opcode range (`< 53`) the whole
decode-inversion family rides. -/
theorem opcodeCast_inj {o o' : Opcode} (h : (o.toNat : ZMod p) = (o'.toNat : ZMod p)) :
    o.toNat = o'.toNat := by
  have hp : (2:ℕ) ^ 17 < p := Fact.out
  have h1 := opcode_toNat_lt o
  have h1' := opcode_toNat_lt o'
  have h2 := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt (by omega), ZMod.val_natCast_of_lt (by omega)] at h2

/-- **`regidxVal` is injective on the register-index range.** Two 5-bit register indices with equal
committed field values (`(·.toNat : ZMod p)`) are equal — the indices are `< 32 < 2^17 < p`, so `Nat.cast`
does not collide. The pinning fact the ∀-state decode uniqueness (`decodesRType`) rides. -/
theorem regidx_bv_inj {x y : BitVec 5} (h : (x.toNat : ZMod p) = (y.toNat : ZMod p)) : x = y := by
  have hp : (2 : ℕ) ^ 17 < p := Fact.out
  have hxy : x.toNat = y.toNat := by
    have hh := congrArg ZMod.val h
    rwa [ZMod.val_natCast_of_lt (by have := x.isLt; omega),
      ZMod.val_natCast_of_lt (by have := y.isLt; omega)] at hh
  exact BitVec.eq_of_toNat_eq hxy

/-- **The R-type decode inversion (W7), generic over the op.** If a decoded instruction `i` projects
(`instrToProgramRow`) to a committed row whose opcode is `op`'s and whose `imm_c = 0`, then `i` *is*
`RTYPE (rs2, rs1, rd, op)`, with the row's operand columns exactly the `regidxVal` of those registers. The
`imm_c = 0` rules out every immediate-typed arm (`imm_c = 1`); the opcode column rules out the other
R-shaped arms (RTYPEW / MUL / MULW / DIV* / REM*, whose discriminants are distinct from every `ropToOpcode`)
and — via `opcodeCast_inj` + `ropToOpcode` injectivity — pins the op within the RTYPE arm. Keyed on the
committed columns via `split` over the projection's match arms — no full case over `instruction`'s ~300
constructors. **Serves the whole R-type family** (Add/Sub/Bitwise/Lt/Shift/Mul/DivRem — one `op`). -/
theorem instrToProgramRow_inv_rtype {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (op : rop) (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = ((ropToOpcode op).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx, i = .RTYPE (rs2, rs1, rd, op) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] := by
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm one_ne_zero))
  · rename_i rs2 rs1 rd op'
    have hz : (ropToOpcode op').toNat = (ropToOpcode op).toNat := opcodeCast_inj hop
    obtain rfl : op' = op := by cases op' <;> cases op <;> first | rfl | (exact absurd hz (by decide))
    exact ⟨rs2, rs1, rd, rfl, rfl, rfl, rfl⟩
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i rs2 rs1 rd m
    exact absurd (opcodeCast_inj hop)
      (by rcases m with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> cases op <;> decide)
  · rename_i rs2 rs1 rd
    exact absurd (opcodeCast_inj hop) (by cases op <;> decide)
  · rename_i rs2 rs1 rd isU
    exact absurd (opcodeCast_inj hop) (by cases isU <;> cases op <;> decide)
  · rename_i rs2 rs1 rd isU
    exact absurd (opcodeCast_inj hop) (by cases isU <;> cases op <;> decide)
  · rename_i rs2 rs1 rd isU
    exact absurd (opcodeCast_inj hop) (by cases isU <;> cases op <;> decide)
  · rename_i rs2 rs1 rd isU
    exact absurd (opcodeCast_inj hop) (by cases isU <;> cases op <;> decide)

/-- **The RTYPEW decode inversion (W7), generic over the W-op.** The `execute_RTYPEW` twin of
`instrToProgramRow_inv_rtype`: if a decoded `i` projects to a committed row whose opcode is `op`'s
(`ropwToOpcode`, image `{19..23}`) and whose `imm_c = 0`, then `i` *is* `RTYPEW (rs2, rs1, rd, op)`. Same
shape as the R-type arm (the RTYPEW projection differs only in the opcode); `imm_c = 0` kills the
immediate-typed arms, and the opcode column — disjoint from `ropToOpcode` (`0..10`) and from MUL/MULW/DIV*/REM*
— rules out the other R-shaped arms and pins the op within RTYPEW. **Serves Addw/Subw + the `*W` variants of
Shift** (SLLW/SRLW/SRAW). -/
theorem instrToProgramRow_inv_rtypew {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (op : ropw) (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = ((ropwToOpcode op).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx, i = .RTYPEW (rs2, rs1, rd, op) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] := by
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm one_ne_zero))
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i rs2 rs1 rd op'
    have hz : (ropwToOpcode op').toNat = (ropwToOpcode op).toNat := opcodeCast_inj hop
    obtain rfl : op' = op := by cases op' <;> cases op <;> first | rfl | (exact absurd hz (by decide))
    exact ⟨rs2, rs1, rd, rfl, rfl, rfl, rfl⟩
  · rename_i rs2 rs1 rd m
    exact absurd (opcodeCast_inj hop)
      (by rcases m with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> cases op <;> decide)
  · rename_i rs2 rs1 rd
    exact absurd (opcodeCast_inj hop) (by cases op <;> decide)
  · rename_i rs2 rs1 rd isU
    exact absurd (opcodeCast_inj hop) (by cases isU <;> cases op <;> decide)
  · rename_i rs2 rs1 rd isU
    exact absurd (opcodeCast_inj hop) (by cases isU <;> cases op <;> decide)
  · rename_i rs2 rs1 rd isU
    exact absurd (opcodeCast_inj hop) (by cases isU <;> cases op <;> decide)
  · rename_i rs2 rs1 rd isU
    exact absurd (opcodeCast_inj hop) (by cases isU <;> cases op <;> decide)

/-- The pc-limb vector of a program row. -/
def rowPcVec (row : ProgramRow (ZMod p)) : Vector (ZMod p) 3 := #v[row.pc0, row.pc1, row.pc2]

/-- Reassemble three 16-bit PC limb values into the Sail 64-bit PC. (Relocated here with `pcBitsOfRow`
from `Soundness/TargetVm.lean` — the decode core's `fetchWord` key needs it at the Model layer.) -/
def pcBitsOfVals (a b c : ℕ) : BitVec 64 := BitVec.ofNat 64 (a + b * 2 ^ 16 + c * 2 ^ 32)

/-- The 64-bit pc a program row's limbs reassemble to (the `fetchWord` key). -/
def pcBitsOfRow (row : ProgramRow (ZMod p)) : BitVec 64 :=
  pcBitsOfVals row.pc0.val row.pc1.val row.pc2.val

/-- **The trusted program table = decode of the guest ROM.** The `inROM` membership predicate for a
`GuestProgram`: a row is valid iff it is the decode of the instruction word the guest ROM holds at the
row's pc. Instantiating `ProgramConsistency`'s `inROM` with this connects the encoded `GuestProgram.rom`
to the decoded committed columns. (Discharged from bus balance via a `ProgramProvider (decodedInROM prog)`
— tracked separately.) -/
def decodedInROM (prog : GuestProgram) (row : ProgramRow (ZMod p)) : Prop :=
  ∃ w, prog.fetchWord (pcBitsOfRow row) = some w ∧
    ∀ s, SailConfigured s → ∃ i, (ext_decode w).run s = .ok i s ∧
      instrToProgramRow (rowPcVec row) i = some row

set_option linter.unusedSectionVars false in
/-- **RV64 decode accessor.** Unpacks `decodedInROM` to the official LeanRV64D `ext_decode` result (the
generated RV64 `encdec_backwards` decoder): the fetched ROM word `w` and, for any configured Sail state,
the decoded `instruction` `i` with its `ext_decode` run and the `instrToProgramRow` projection back to the
row. This is the callable RV64 surface the Phase-4 `advance`/`try_step` reduction consumes from a fetch's
`ProgTruth` — making the LeanRV64D decoder an explicit, reusable lemma rather than a buried existential. -/
theorem decodedInROM.decodes {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (h : decodedInROM prog row) (s : SailState) (hs : SailConfigured s) :
    ∃ w i, prog.fetchWord (pcBitsOfRow row) = some w ∧
      (ext_decode w).run s = .ok i s ∧ instrToProgramRow (rowPcVec row) i = some row := by
  obtain ⟨w, hfetch, hbody⟩ := h
  obtain ⟨i, hrun, hrow⟩ := hbody s hs
  exact ⟨w, i, hfetch, hrun, hrow⟩

/-- **The I-type decode inversion (W7), generic over the op.** The I-type twin of
`instrToProgramRow_inv_rtype`: if a decoded `i` projects to a committed row whose opcode is `op`'s
(`iopToOpcode`) and whose `imm_c = 1`, then `i` *is* `ITYPE (imm, rs1, rd, op)`, with the operand columns
the `regidxVal`s and `op_c` the sign-extended immediate word. `imm_c = 1` rules out the R-shaped arms
(`imm_c = 0`); the opcode column rules out the other immediate-shaped arms (UTYPE/JAL/JALR/BTYPE/LOAD/STORE/
SHIFTI(W)OP/ADDIW — opcodes disjoint from `iopToOpcode`'s image `{1,3,4,5,9,10}`). `word_width` is a Sail
`Int`, so the LOAD/STORE arms close via `split_ifs <;> decide` on `loadOpcode`/`storeOpcode`, not `cases`.
**Serves ADDI + the immediate ALU forms** (SLTI/XORI/…, which share their register opcode). -/
theorem instrToProgramRow_inv_itype {pc : Vector (ZMod p) 3} {i : instruction}
    {row : ProgramRow (ZMod p)} (op : iop)
    (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = ((iopToOpcode op).toNat : ZMod p))
    (himm : row.imm_c = (1 : ZMod p)) :
    ∃ (imm : BitVec 12) (rs1 rd : regidx), i = .ITYPE (imm, rs1, rd, op) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = bitVecToWord (imm.signExtend 64) := by
  have honezero : (1 : ZMod p) ≠ 0 := by
    have : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    exact one_ne_zero
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm.symm honezero))
  · rename_i imm rs1 rd op'
    have hz : (iopToOpcode op').toNat = (iopToOpcode op).toNat := opcodeCast_inj hop
    obtain rfl : op' = op := by cases op' <;> cases op <;> first | rfl | (exact absurd hz (by decide))
    exact ⟨imm, rs1, rd, rfl, rfl, rfl, rfl⟩
  · rename_i imm rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i imm rd
    exact absurd (opcodeCast_inj hop) (by cases op <;> decide)
  · rename_i imm rs1 rd
    exact absurd (opcodeCast_inj hop) (by cases op <;> decide)
  · rename_i imm rs2 rs1 op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i imm rs1 rd isU width
    exact absurd (opcodeCast_inj hop)
      (by cases isU <;> cases op <;> (simp only [loadOpcode, iopToOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rs2 rs1 width
    exact absurd (opcodeCast_inj hop)
      (by cases op <;> (simp only [storeOpcode, iopToOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i shamt rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i shamt rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i imm rs1 rd
    exact absurd (opcodeCast_inj hop) (by cases op <;> decide)

/-- **The ADDIW decode inversion (W7).** ADDIW has no own opcode — it commits the ADDW opcode (`19`) with
`imm_c = 1` (I-type shape), so it is pinned by `(opcode = ADDW, imm_c = 1)`: `imm_c = 1` kills the
`imm_c = 0` arms, and opcode `ADDW` (disjoint from every `iopToOpcode`/UTYPE/JAL/JALR/BTYPE/LOAD/STORE/SHIFT
image) rules out the other immediate-shaped arms — leaving the `.ADDIW` arm. The I-type-W twin of
`instrToProgramRow_inv_itype` (no `op` parameter). -/
theorem instrToProgramRow_inv_addiw {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = ((Opcode.ADDW).toNat : ZMod p))
    (himm : row.imm_c = (1 : ZMod p)) :
    ∃ (imm : BitVec 12) (rs1 rd : regidx), i = .ADDIW (imm, rs1, rd) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = bitVecToWord (imm.signExtend 64) := by
  have honezero : (1 : ZMod p) ≠ 0 := by
    have : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    exact one_ne_zero
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm.symm honezero))
  · rename_i imm rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> decide)
  · rename_i imm rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> decide)
  · rename_i imm rd
    exact absurd (opcodeCast_inj hop) (by decide)
  · rename_i imm rs1 rd
    exact absurd (opcodeCast_inj hop) (by decide)
  · rename_i imm rs2 rs1 op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> decide)
  · rename_i imm rs1 rd isU width
    exact absurd (opcodeCast_inj hop)
      (by cases isU <;> (simp only [loadOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rs2 rs1 width
    exact absurd (opcodeCast_inj hop)
      (by simp only [storeOpcode, Opcode.toNat]; split_ifs <;> decide)
  · rename_i shamt rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> decide)
  · rename_i shamt rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> decide)
  · rename_i imm rs1 rd
    exact ⟨imm, rs1, rd, rfl, rfl, rfl, rfl⟩

/-- **The ∀-configured-state `RTYPE(op)` decode from a row's `ProgTruth` membership.** From
`decodedInROM prog row` on a row whose committed opcode is `op`'s and whose `imm_c = 0`, the fetched ROM
word `w` decodes — **in every configured Sail state** — to `RTYPE (rs2, rs1, rd, op)` with the register
indices pinned to the row's committed operand columns. A configured witness `s0` instantiates the
`decodedInROM` body; `regidx_bv_inj` pins the (per-state existential) decode to the single instruction the
row's columns determine, lifting it to the uniform ∀-state form the Phase-4 `advance` consumes. Generic
over `op` via `instrToProgramRow_inv_rtype` — **the whole R-type family's decode producer**. -/
theorem decodesRType {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : rop)
    (h : decodedInROM prog row)
    (hop : row.opcode = ((ropToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 0)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (rs2 rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.RTYPE (.Regidx rs2, .Regidx rs1, .Regidx rd, op)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨rs2r, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_rtype op hrow0 hop himm
  obtain ⟨rs2⟩ := rs2r; obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, rs2, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨rs2', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_rtype op hrow2 hop himm
  obtain ⟨rs2'⟩ := rs2'; obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e2 : rs2' = rs2 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hc.symm.trans hc')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h
    exact h.symm)
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h
    exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'
    simp only [regidxVal] at h
    exact h.symm)
  subst e2 e1 e0; rw [hi2] at hrun2; exact hrun2

/-- **The ∀-configured-state RTYPEW decode producer** — the `execute_RTYPEW` twin of `decodesRType`. From the
Program-bus `decodedInROM` + the committed `(opcode, imm_c=0)`, recover the fetched word `w` and the register
indices `rs2/rs1/rd`, with the decode `ext_decode w = RTYPEW(rs2,rs1,rd,op)` holding in **every** configured
state (the register indices pinned by `regidx_bv_inj`). What `advance_of_rtypew` consumes. -/
theorem decodesRTypew {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : ropw)
    (h : decodedInROM prog row)
    (hop : row.opcode = ((ropwToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 0)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (rs2 rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.RTYPEW (.Regidx rs2, .Regidx rs1, .Regidx rd, op)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨rs2r, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_rtypew op hrow0 hop himm
  obtain ⟨rs2⟩ := rs2r; obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, rs2, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨rs2', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_rtypew op hrow2 hop himm
  obtain ⟨rs2'⟩ := rs2'; obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e2 : rs2' = rs2 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hc.symm.trans hc')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h
    exact h.symm)
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h
    exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'
    simp only [regidxVal] at h
    exact h.symm)
  subst e2 e1 e0; rw [hi2] at hrun2; exact hrun2

/-- **`bitVecToWord` is a right inverse of `toBitVec64`.** Reassembling the four little-endian 16-bit
limb-extracts of a 64-bit value recovers it. Gives both the I-type immediate binding
(`toBitVec64 op_c = signExtend imm`) and `bitVecToWord` injectivity (the imm-uniqueness `decodesIType` rides). -/
theorem toBitVec64_bitVecToWord (v : BitVec 64) : Word.toBitVec64 (bitVecToWord (p := p) v) = v := by
  have hp : (2:ℕ) ^ 17 < p := Fact.out
  have hlt : ∀ i, (BitVec.extractLsb' i 16 v).toNat < 2 ^ 16 := fun i => (BitVec.extractLsb' i 16 v).isLt
  have hltp : ∀ i, (BitVec.extractLsb' i 16 v).toNat < p := fun i => by have := hlt i; omega
  have hRU : Word.isU64 (bitVecToWord (p := p) v) := by
    refine Word.isU64_of_cases ?_ ?_ ?_ ?_ <;>
      (simp only [bitVecToWord, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
        List.getElem_cons_succ]; rw [ZMod.val_natCast_of_lt (hltp _)]; exact hlt _)
  rw [← BitVec.toNat_inj, Word.toBitVec64_toNat hRU, Word.toNat]
  simp only [bitVecToWord, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero,
    List.getElem_cons_succ]
  rw [ZMod.val_natCast_of_lt (hltp 0), ZMod.val_natCast_of_lt (hltp 16), ZMod.val_natCast_of_lt (hltp 32),
    ZMod.val_natCast_of_lt (hltp 48), BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat,
    BitVec.extractLsb'_toNat, BitVec.extractLsb'_toNat]
  simp only [Nat.shiftRight_eq_div_pow]
  have := v.isLt
  omega

/-- The 12→64 sign-extension is injective (it preserves the low 12 bits). -/
theorem sext12_inj {a b : BitVec 12} (h : a.signExtend 64 = b.signExtend 64) : a = b := by
  have h12 : ∀ x : BitVec 12, (x.signExtend 64).setWidth 12 = x := fun x => by bv_decide
  rw [← h12 a, ← h12 b, h]

/-- **The ∀-configured-state `ITYPE(op)` decode from a row's `ProgTruth` membership.** The I-type twin of
`decodesRType`: the register indices are pinned by `regidx_bv_inj`, and the immediate `imm` by the `op_c`
column via `toBitVec64_bitVecToWord` + `sext12_inj`. The Phase-4 I-type `advance`'s decode producer. -/
theorem decodesIType {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : iop)
    (h : decodedInROM prog row)
    (hop : row.opcode = ((iopToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 1)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (imm : BitVec 12) (rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.ITYPE (imm, .Regidx rs1, .Regidx rd, op)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = bitVecToWord (imm.signExtend 64) := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨imm, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_itype op hrow0 hop himm
  obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, imm, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨imm', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_itype op hrow2 hop himm
  obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h
    exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'
    simp only [regidxVal] at h
    exact h.symm)
  have eimm : imm' = imm := by
    have e := congrArg (Word.toBitVec64 (p := p)) (hc.symm.trans hc')
    rw [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at e
    exact (sext12_inj e).symm
  subst e1 e0 eimm
  rw [hi2] at hrun2
  exact hrun2

/-- **The ∀-configured-state ADDIW decode producer** — the `.ADDIW` twin of `decodesIType`, keyed on the
committed `(opcode = ADDW, imm_c = 1)`. Recovers `w` + `imm/rs1/rd` with the decode holding in every
configured state (register indices pinned by `regidx_bv_inj`, the immediate by `sext12_inj` on the `op_c`
column). What `advance_of_addiw` consumes. -/
theorem decodesADDIW {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (h : decodedInROM prog row)
    (hop : row.opcode = ((Opcode.ADDW).toNat : ZMod p)) (himm : row.imm_c = 1)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (imm : BitVec 12) (rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.ADDIW (imm, .Regidx rs1, .Regidx rd)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = bitVecToWord (imm.signExtend 64) := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨imm, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_addiw hrow0 hop himm
  obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, imm, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨imm', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_addiw hrow2 hop himm
  obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h
    exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'
    simp only [regidxVal] at h
    exact h.symm)
  have eimm : imm' = imm := by
    have e := congrArg (Word.toBitVec64 (p := p)) (hc.symm.trans hc')
    rw [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at e
    exact (sext12_inj e).symm
  subst e1 e0 eimm
  rw [hi2] at hrun2
  exact hrun2

end SP1Clean.Soundness.Target
