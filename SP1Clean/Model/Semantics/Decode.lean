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

open LeanRV64D.Defs
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

/-! ## Move-1 image guards (folded from the former `DecodeGuards.lean`). The row projection
`instrToProgramRow` is total, so its `.MUL`/`.LOAD`/`.STORE` arms admit *phantom* records the real
decoder never emits (non-canonical `mul_op`, the width-8 unsigned load). `instrToProgramRow'` guards
those arms to the decoder's canonical image — **definitionally a guard wrapper** around
`instrToProgramRow` — on which the projection is injective. This is the guarded projection the
`decodedInROM` hoist (below) and the collapsed MUL/LOAD/STORE producers consume. -/

/-- The 4 canonical `mul_op` records — exactly the image of `encdec_mul_op_backwards`:
(Low,S,S) = MUL, (High,S,S) = MULH, (High,S,U) = MULHSU, (High,U,U) = MULHU. The 4 others (incl.
(High,U,S), the phantom MULHSU alias with a different product) are never decoded. -/
def mulOpCanonical (m : mul_op) : Bool :=
  match m.result_part, m.signed_rs1, m.signed_rs2 with
  | .Low, .Signed, .Signed => true
  | .High, .Signed, .Signed => true
  | .High, .Signed, .Unsigned => true
  | .High, .Unsigned, .Unsigned => true
  | _, _, _ => false

/-- The LOAD widths the decoder can emit (`valid_load_encdec`, RV64 `xlen_bytes = 8`):
width ∈ {1,2,4} any sign, width 8 only signed (no LDU). -/
def loadWidthOK (width : word_width) (isU : Bool) : Bool :=
  width == 1 || width == 2 || width == 4 || (width == 8 && !isU)

/-- The STORE widths the decoder can emit (`width_enc_backwards` image): {1,2,4,8}. -/
def storeWidthOK (width : word_width) : Bool :=
  width == 1 || width == 2 || width == 4 || width == 8

/-- `instrToProgramRow` with the MUL/LOAD/STORE arms image-guarded (a guard wrapper, definitionally
equal to inlining the guards into the three arms). -/
def instrToProgramRow' (pc : Vector (ZMod p) 3) : instruction → Option (ProgramRow (ZMod p))
  | .MUL (rs2, rs1, rd, m) =>
      if mulOpCanonical m then instrToProgramRow pc (.MUL (rs2, rs1, rd, m)) else none
  | .LOAD (imm, rs1, rd, isU, width) =>
      if loadWidthOK width isU then instrToProgramRow pc (.LOAD (imm, rs1, rd, isU, width)) else none
  | .STORE (imm, rs2, rs1, width) =>
      if storeWidthOK width then instrToProgramRow pc (.STORE (imm, rs2, rs1, width)) else none
  | i => instrToProgramRow pc i

omit [Fact (2 ^ 17 < p)] in
/-- The guards only restrict: a primed projection is an unprimed one. -/
theorem instrToProgramRow'_some {pc : Vector (ZMod p) 3} {i : instruction}
    {row : ProgramRow (ZMod p)}
    (h : instrToProgramRow' pc i = some row) : instrToProgramRow pc i = some row := by
  unfold instrToProgramRow' at h
  split at h
  · split at h
    · exact h
    · exact absurd h (by simp)
  · split at h
    · exact h
    · exact absurd h (by simp)
  · split at h
    · exact h
    · exact absurd h (by simp)
  · exact h

omit [Fact (2 ^ 17 < p)] in
/-- Guard extraction at the MUL arm: a primed projection of a `.MUL` forces canonicity. -/
theorem instrToProgramRow'_mul_canonical {pc : Vector (ZMod p) 3} {rs2 rs1 rd : regidx}
    {m : mul_op} {row : ProgramRow (ZMod p)}
    (h : instrToProgramRow' pc (.MUL (rs2, rs1, rd, m)) = some row) :
    mulOpCanonical m = true := by
  cases hcm : mulOpCanonical m with
  | true => rfl
  | false =>
    rw [instrToProgramRow'] at h
    rw [hcm] at h
    simp at h

omit [Fact (2 ^ 17 < p)] in
/-- On concrete constructors the primed projection is unguarded (default arm). -/
theorem instrToProgramRow'_rtype (pc : Vector (ZMod p) 3) (t : regidx × regidx × regidx × rop) :
    instrToProgramRow' pc (.RTYPE t) = instrToProgramRow pc (.RTYPE t) := rfl

/-- **The trusted program table = decode of the guest ROM.** The `inROM` membership predicate for a
`GuestProgram`: a row is valid iff it is the decode of the instruction word the guest ROM holds at the
row's pc. Instantiating `ProgramConsistency`'s `inROM` with this connects the encoded `GuestProgram.rom`
to the decoded committed columns. (Discharged from bus balance via a `ProgramProvider (decodedInROM prog)`
— tracked separately.)

**Shape (C1/Move-2):** the decoded instruction `I` is hoisted **out** of the state quantifier (∃I∀s, not
∀s∃i) over the **guarded** projection `instrToProgramRow'`. Fixing `I` across all configured states is what
lets every `decodes<T>` consumer invert *once* (no cross-state `regidx_bv_inj` pinning), and the guarded
projection is what lets the MUL/LOAD/STORE consumers drop their `hpin` side-conditions. This strengthens the
predicate; it is a sound, derivable strengthening (see `decodedInROM_*_hoist` below — ∃I∀s follows from the
weak guarded ∀s form for real decodes). -/
def decodedInROM (prog : GuestProgram) (row : ProgramRow (ZMod p)) : Prop :=
  ∃ (w : BitVec 32) (I : instruction),
    prog.fetchWord (pcBitsOfRow row) = some w ∧
    (∀ s, SailConfigured s → (ext_decode w).run s = .ok I s) ∧
    instrToProgramRow' (rowPcVec row) I = some row

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
  obtain ⟨w, I, hfetch, hrun, hrow⟩ := h
  exact ⟨w, I, hfetch, hrun s hs, instrToProgramRow'_some hrow⟩

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

/-- **The U-type decode inversion (W7).** LUI/AUIPC are their own opcodes (`uopToOpcode`, image `{48,49}`),
committed with `imm_c = 1` and `op_b = op_c = bitVecToWord ((imm.signExtend 64) <<< 12)` (both immediates). So
`(opcode, imm_c = 1)` pins the `.UTYPE` arm: `imm_c = 1` kills the R-shaped arms, and opcode `LUI`/`AUIPC`
(disjoint from every other immediate-shaped arm's opcode) rules out the rest. Returns the shifted-immediate
`op_b` encoding (which `immOf`/`decodesUType` invert). -/
theorem instrToProgramRow_inv_utype {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (op : uop) (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = ((uopToOpcode op).toNat : ZMod p))
    (himm : row.imm_c = (1 : ZMod p)) :
    ∃ (imm : BitVec 20) (rd : regidx), i = .UTYPE (imm, rd, op) ∧
      row.op_a = regidxVal rd ∧ row.op_b = bitVecToWord ((imm.signExtend 64) <<< 12) := by
  have honezero : (1 : ZMod p) ≠ 0 := by
    have : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    exact one_ne_zero
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm.symm honezero))
  · rename_i imm rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i imm rd op'
    have hz : (uopToOpcode op').toNat = (uopToOpcode op).toNat := opcodeCast_inj hop
    obtain rfl : op' = op := by cases op' <;> cases op <;> first | rfl | (exact absurd hz (by decide))
    exact ⟨imm, rd, rfl, rfl, rfl⟩
  · rename_i imm rd
    exact absurd (opcodeCast_inj hop) (by cases op <;> decide)
  · rename_i imm rs1 rd
    exact absurd (opcodeCast_inj hop) (by cases op <;> decide)
  · rename_i imm rs2 rs1 op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i imm rs1 rd isU width
    exact absurd (opcodeCast_inj hop)
      (by cases isU <;> cases op <;> (simp only [loadOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rs2 rs1 width
    exact absurd (opcodeCast_inj hop)
      (by cases op <;> (simp only [storeOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i shamt rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i shamt rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i imm rs1 rd
    exact absurd (opcodeCast_inj hop) (by cases op <;> decide)

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

/-- **The 20-bit U-immediate encoding is injective.** Two U-immediates whose `op_b` limb-encodings
(`bitVecToWord ((·.signExtend 64) <<< 12)`) agree are equal — the low-4/high-16 limb split
(`limb.toNat / 4096 + limb.toNat * 16`) recovers the immediate exactly (axiom-clean via `omega`, no
`bv_decide`). The U-type twin of `sext12_inj`; the imm-uniqueness `decodesUType` rides. -/
theorem sext20shl12_word_inj (a b : BitVec 20)
    (h : bitVecToWord ((a.signExtend 64) <<< 12)
      = bitVecToWord ((b.signExtend 64) <<< 12 : BitVec 64) (p := p)) :
    a = b := by
  have hp : (2:ℕ) ^ 17 < p := Fact.out
  have hval16 : ∀ w : BitVec 16, ((w.toNat : ZMod p)).val = w.toNat := fun w => by
    rw [ZMod.val_natCast_of_lt]; exact lt_trans w.isLt (by omega)
  have keyf : ∀ x : BitVec 20,
      (BitVec.extractLsb' 0 16 ((x.signExtend 64) <<< 12)).toNat / 4096 +
      (BitVec.extractLsb' 16 16 ((x.signExtend 64) <<< 12)).toNat * 16 = x.toNat := fun x => by
    have hx : x.toNat < 2 ^ 20 := x.isLt
    simp only [BitVec.extractLsb'_toNat, BitVec.toNat_shiftLeft, BitVec.toNat_signExtend,
      BitVec.toNat_setWidth, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow]
    split <;> omega
  have h0 : (BitVec.extractLsb' 0 16 ((a.signExtend 64) <<< 12)).toNat
      = (BitVec.extractLsb' 0 16 ((b.signExtend 64) <<< 12)).toNat := by
    have e := congrArg (fun w => (w[0]'(by omega)).val) h
    simp only [bitVecToWord, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at e
    rw [hval16, hval16] at e; exact e
  have h1 : (BitVec.extractLsb' 16 16 ((a.signExtend 64) <<< 12)).toNat
      = (BitVec.extractLsb' 16 16 ((b.signExtend 64) <<< 12)).toNat := by
    have e := congrArg (fun w => (w[1]'(by omega)).val) h
    simp only [bitVecToWord, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_succ,
      List.getElem_cons_zero] at e
    rw [hval16, hval16] at e; exact e
  apply BitVec.eq_of_toNat_eq
  rw [← keyf a, ← keyf b, h0, h1]

/-- **The ∀-configured-state U-type decode producer** — the `.UTYPE` twin of `decodesIType`, keyed on the
committed `(opcode ∈ {LUI,AUIPC}, imm_c = 1)`. Recovers `w` + `imm/rd` with the decode holding in every
configured state (register `rd` pinned by `regidx_bv_inj`, the 20-bit immediate by `sext20shl12_word_inj` on
the `op_b` column). Returns `op_b = bitVecToWord ((imm.signExtend 64) <<< 12)` — which the chip's `immOf`
inverts. What `advance_of_utype` consumes. -/
theorem decodesUType {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : uop)
    (h : decodedInROM prog row)
    (hop : row.opcode = ((uopToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 1)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (imm : BitVec 20) (rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.UTYPE (imm, .Regidx rd, op)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = bitVecToWord ((imm.signExtend 64) <<< 12) := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨imm, rdr, hi0, ha, hb⟩ := instrToProgramRow_inv_utype op hrow0 hop himm
  obtain ⟨rd⟩ := rdr
  refine ⟨w, imm, rd, hfetch, ?_, ha, hb⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨imm', rd', hi2, ha', hb'⟩ := instrToProgramRow_inv_utype op hrow2 hop himm
  obtain ⟨rd'⟩ := rd'
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'; simp only [regidxVal] at h; exact h.symm)
  have eimm : imm' = imm := sext20shl12_word_inj imm' imm (hb'.symm.trans hb)
  subst e0 eimm; rw [hi2] at hrun2; exact hrun2

/-- **The JAL decode inversion (W7).** JAL is its own opcode (`Opcode.JAL` = 46) committed with `imm_c = 1`,
`op_a = rd`, `op_b = bitVecToWord (imm.signExtend 64)` (the 21-bit jump offset sign-extended), `op_c = 0`. So
`(opcode = JAL, imm_c = 1)` pins the `.JAL` arm. The immediate-shaped twin of `inv_addiw` (JAL is one of the
`imm_c = 1` bullets). -/
theorem instrToProgramRow_inv_jal {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = ((Opcode.JAL).toNat : ZMod p))
    (himm : row.imm_c = (1 : ZMod p)) :
    ∃ (imm : BitVec 21) (rd : regidx), i = .JAL (imm, rd) ∧
      row.op_a = regidxVal rd ∧ row.op_b = bitVecToWord (imm.signExtend 64)
      ∧ row.op_c = #v[0, 0, 0, 0] := by
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
    exact ⟨imm, rd, rfl, rfl, rfl, rfl⟩
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
    exact absurd (opcodeCast_inj hop) (by decide)

/-- **The 21-bit JAL offset sign-extension is injective** (clean, no `bv_decide`): recover `x` as the low 21
bits of `x.signExtend 64` via `getLsbD`. The imm-uniqueness `decodesJal` rides. -/
theorem sext21_inj {a b : BitVec 21} (h : a.signExtend 64 = b.signExtend 64) : a = b := by
  have key : ∀ x : BitVec 21, (x.signExtend 64).setWidth 21 = x := fun x => by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi]
    have h64 : i < 64 := by omega
    simp [hi, h64]
  rw [← key a, ← key b, h]

/-- **The ∀-configured-state JAL decode producer** — the `.JAL` twin of `decodesADDIW`, keyed on the committed
`(opcode = JAL, imm_c = 1)`. Recovers `w` + `imm/rd` with the decode holding in every configured state (`rd`
by `regidx_bv_inj`, the 21-bit offset by `sext21_inj` on `op_b`). What `advance_of_jal` consumes. -/
theorem decodesJal {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (h : decodedInROM prog row)
    (hop : row.opcode = ((Opcode.JAL).toNat : ZMod p)) (himm : row.imm_c = 1)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (imm : BitVec 21) (rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.JAL (imm, .Regidx rd)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = bitVecToWord (imm.signExtend 64) ∧
      row.op_c = #v[0, 0, 0, 0] := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨imm, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_jal hrow0 hop himm
  obtain ⟨rd⟩ := rdr
  refine ⟨w, imm, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨imm', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_jal hrow2 hop himm
  obtain ⟨rd'⟩ := rd'
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'; simp only [regidxVal] at h; exact h.symm)
  have eimm : imm' = imm := by
    have e := congrArg (Word.toBitVec64 (p := p)) (hb.symm.trans hb')
    rw [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at e
    exact (sext21_inj e).symm
  subst e0 eimm; rw [hi2] at hrun2; exact hrun2

/-- **The JALR decode inversion (W7).** JALR is I-type-shaped (its own opcode `Opcode.JALR` = 47, `imm_c = 1`,
`op_a = rd`, `op_b = #v[regidxVal rs1, 0, 0, 0]` the rs1 register, `op_c = bitVecToWord (imm.signExtend 64)`
the 12-bit immediate). The `.JALR` twin of `instrToProgramRow_inv_addiw` (JALR is one of the `imm_c = 1`
bullets). -/
theorem instrToProgramRow_inv_jalr {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = ((Opcode.JALR).toNat : ZMod p))
    (himm : row.imm_c = (1 : ZMod p)) :
    ∃ (imm : BitVec 12) (rs1 rd : regidx), i = .JALR (imm, rs1, rd) ∧
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
    exact ⟨imm, rs1, rd, rfl, rfl, rfl, rfl⟩
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
    exact absurd (opcodeCast_inj hop) (by decide)

/-- **The ∀-configured-state JALR decode producer** — the `.JALR` twin of `decodesADDIW`, keyed on
`(opcode = JALR, imm_c = 1)`. Recovers `w` + `imm/rs1/rd` (`rs1` in `op_b`, the 12-bit immediate in `op_c`
pinned by `sext12_inj`). What `advance_of_jalr` consumes. -/
theorem decodesJalr {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (h : decodedInROM prog row)
    (hop : row.opcode = ((Opcode.JALR).toNat : ZMod p)) (himm : row.imm_c = 1)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (imm : BitVec 12) (rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.JALR (imm, .Regidx rs1, .Regidx rd)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = bitVecToWord (imm.signExtend 64) := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨imm, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_jalr hrow0 hop himm
  obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, imm, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨imm', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_jalr hrow2 hop himm
  obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h
    exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'; simp only [regidxVal] at h; exact h.symm)
  have eimm : imm' = imm := by
    have e := congrArg (Word.toBitVec64 (p := p)) (hc.symm.trans hc')
    rw [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at e
    exact (sext12_inj e).symm
  subst e1 e0 eimm; rw [hi2] at hrun2; exact hrun2


/-! ## DivRem (DIV/DIVU/REM/REMU/DIVW/DIVUW/REMW/REMUW) decode inversions + producers (SC Phase 4) -/

/-- The DIV/DIVU decode inversion (R-type shape, opcode `if isU then DIVU else DIV`, imm_c = 0). -/
theorem instrToProgramRow_inv_div {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (isU : Bool) (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = (((if isU then Opcode.DIVU else Opcode.DIV)).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx, i = .DIV (rs2, rs1, rd, isU) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] := by
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm one_ne_zero))
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd m
    exact absurd (opcodeCast_inj hop)
      (by rcases m with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd
    exact absurd (opcodeCast_inj hop) (by cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    obtain rfl : isU' = isU := by
      have hz := opcodeCast_inj hop
      cases isU' <;> cases isU <;> first | rfl | (exact absurd hz (by decide))
    exact ⟨rs2, rs1, rd, rfl, rfl, rfl, rfl⟩
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> cases isU <;> decide)

/-- The REM/REMU decode inversion (R-type shape, opcode `if isU then REMU else REM`, imm_c = 0). -/
theorem instrToProgramRow_inv_rem {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (isU : Bool) (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = (((if isU then Opcode.REMU else Opcode.REM)).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx, i = .REM (rs2, rs1, rd, isU) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] := by
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm one_ne_zero))
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd m
    exact absurd (opcodeCast_inj hop)
      (by rcases m with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd
    exact absurd (opcodeCast_inj hop) (by cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    obtain rfl : isU' = isU := by
      have hz := opcodeCast_inj hop
      cases isU' <;> cases isU <;> first | rfl | (exact absurd hz (by decide))
    exact ⟨rs2, rs1, rd, rfl, rfl, rfl, rfl⟩
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> cases isU <;> decide)

/-- The DIVW/DIVUW decode inversion (R-type shape, opcode `if isU then DIVUW else DIVW`, imm_c = 0). -/
theorem instrToProgramRow_inv_divw {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (isU : Bool) (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = (((if isU then Opcode.DIVUW else Opcode.DIVW)).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx, i = .DIVW (rs2, rs1, rd, isU) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] := by
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm one_ne_zero))
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd m
    exact absurd (opcodeCast_inj hop)
      (by rcases m with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd
    exact absurd (opcodeCast_inj hop) (by cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    obtain rfl : isU' = isU := by
      have hz := opcodeCast_inj hop
      cases isU' <;> cases isU <;> first | rfl | (exact absurd hz (by decide))
    exact ⟨rs2, rs1, rd, rfl, rfl, rfl, rfl⟩
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> cases isU <;> decide)

/-- The REMW/REMUW decode inversion (R-type shape, opcode `if isU then REMUW else REMW`, imm_c = 0). -/
theorem instrToProgramRow_inv_remw {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (isU : Bool) (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = (((if isU then Opcode.REMUW else Opcode.REMW)).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx, i = .REMW (rs2, rs1, rd, isU) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] := by
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm one_ne_zero))
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd m
    exact absurd (opcodeCast_inj hop)
      (by rcases m with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd
    exact absurd (opcodeCast_inj hop) (by cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> cases isU <;> decide)
  · rename_i rs2 rs1 rd isU'
    obtain rfl : isU' = isU := by
      have hz := opcodeCast_inj hop
      cases isU' <;> cases isU <;> first | rfl | (exact absurd hz (by decide))
    exact ⟨rs2, rs1, rd, rfl, rfl, rfl, rfl⟩

/-- ∀-configured-state DIV/DIVU decode producer (mirrors `decodesRType`). -/
theorem decodesDiv {prog : GuestProgram} {row : ProgramRow (ZMod p)} (isU : Bool)
    (h : decodedInROM prog row)
    (hop : row.opcode = (((if isU then Opcode.DIVU else Opcode.DIV)).toNat : ZMod p)) (himm : row.imm_c = 0)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (rs2 rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.DIV (.Regidx rs2, .Regidx rs1, .Regidx rd, isU)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨rs2r, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_div isU hrow0 hop himm
  obtain ⟨rs2⟩ := rs2r; obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, rs2, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨rs2', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_div isU hrow2 hop himm
  obtain ⟨rs2'⟩ := rs2'; obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e2 : rs2' = rs2 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hc.symm.trans hc')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h; exact h.symm)
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h; exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'; simp only [regidxVal] at h; exact h.symm)
  subst e2 e1 e0; rw [hi2] at hrun2; exact hrun2

/-- ∀-configured-state REM/REMU decode producer. -/
theorem decodesRem {prog : GuestProgram} {row : ProgramRow (ZMod p)} (isU : Bool)
    (h : decodedInROM prog row)
    (hop : row.opcode = (((if isU then Opcode.REMU else Opcode.REM)).toNat : ZMod p)) (himm : row.imm_c = 0)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (rs2 rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.REM (.Regidx rs2, .Regidx rs1, .Regidx rd, isU)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨rs2r, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_rem isU hrow0 hop himm
  obtain ⟨rs2⟩ := rs2r; obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, rs2, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨rs2', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_rem isU hrow2 hop himm
  obtain ⟨rs2'⟩ := rs2'; obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e2 : rs2' = rs2 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hc.symm.trans hc')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h; exact h.symm)
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h; exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'; simp only [regidxVal] at h; exact h.symm)
  subst e2 e1 e0; rw [hi2] at hrun2; exact hrun2

/-- ∀-configured-state DIVW/DIVUW decode producer. -/
theorem decodesDivw {prog : GuestProgram} {row : ProgramRow (ZMod p)} (isU : Bool)
    (h : decodedInROM prog row)
    (hop : row.opcode = (((if isU then Opcode.DIVUW else Opcode.DIVW)).toNat : ZMod p)) (himm : row.imm_c = 0)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (rs2 rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.DIVW (.Regidx rs2, .Regidx rs1, .Regidx rd, isU)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨rs2r, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_divw isU hrow0 hop himm
  obtain ⟨rs2⟩ := rs2r; obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, rs2, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨rs2', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_divw isU hrow2 hop himm
  obtain ⟨rs2'⟩ := rs2'; obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e2 : rs2' = rs2 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hc.symm.trans hc')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h; exact h.symm)
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h; exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'; simp only [regidxVal] at h; exact h.symm)
  subst e2 e1 e0; rw [hi2] at hrun2; exact hrun2

/-- ∀-configured-state REMW/REMUW decode producer. -/
theorem decodesRemw {prog : GuestProgram} {row : ProgramRow (ZMod p)} (isU : Bool)
    (h : decodedInROM prog row)
    (hop : row.opcode = (((if isU then Opcode.REMUW else Opcode.REMW)).toNat : ZMod p)) (himm : row.imm_c = 0)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (rs2 rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.REMW (.Regidx rs2, .Regidx rs1, .Regidx rd, isU)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨rs2r, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_remw isU hrow0 hop himm
  obtain ⟨rs2⟩ := rs2r; obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, rs2, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨rs2', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_remw isU hrow2 hop himm
  obtain ⟨rs2'⟩ := rs2'; obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e2 : rs2' = rs2 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hc.symm.trans hc')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h; exact h.symm)
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h; exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'; simp only [regidxVal] at h; exact h.symm)
  subst e2 e1 e0; rw [hi2] at hrun2; exact hrun2

/-! ## MUL/MULW decode inversions + producers (SC Phase 4)

Unlike DIV/REM (opcode ↔ signedness is injective), `mulOpToOpcode` is **not** injective at the
MUL opcode (`.Low, _, _ => .MUL`, four preimages) nor at MULHSU (two).  So `instrToProgramRow_inv_mul`
takes an explicit `hpin` pinning the `mul_op` from the opcode — provable (`by decide`) only for MULH
and MULHU.  MUL and MULHSU remain decoder seams (would need `ext_decode` output-determinism). -/

/-- The MUL/MULH/MULHU/MULHSU decode inversion (R-type shape, opcode `mulOpToOpcode op`, imm_c = 0),
generic over `op : mul_op` with the opcode-pin `hpin` (the `storeOpcode_pin_one` move: the split lands
on `.MUL(rs2,rs1,rd,op')`, `hpin` forces `op' = op`). -/
theorem instrToProgramRow_inv_mul {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (op : mul_op) (hpin : ∀ op' : mul_op, (mulOpToOpcode op').toNat = (mulOpToOpcode op).toNat → op' = op)
    (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = ((mulOpToOpcode op).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx, i = .MUL (rs2, rs1, rd, op) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] := by
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm one_ne_zero))
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd m
    obtain rfl : m = op := hpin m (opcodeCast_inj hop)
    exact ⟨rs2, rs1, rd, rfl, rfl, rfl, rfl⟩
  · rename_i rs2 rs1 rd
    exact absurd (opcodeCast_inj hop)
      (by rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop)
      (by cases isU' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop)
      (by cases isU' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop)
      (by cases isU' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop)
      (by cases isU' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))

/-- The MULW decode inversion (R-type shape, opcode `MULW`, imm_c = 0).  No `mul_op`, so the
instruction is fully fixed (no pin needed). -/
theorem instrToProgramRow_inv_mulw {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = ((Opcode.MULW).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx, i = .MULW (rs2, rs1, rd) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] := by
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm one_ne_zero))
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> decide)
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> decide)
  · rename_i rs2 rs1 rd m
    exact absurd (opcodeCast_inj hop)
      (by rcases m with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide)
  · rename_i rs2 rs1 rd
    exact ⟨rs2, rs1, rd, rfl, rfl, rfl, rfl⟩
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop) (by cases isU' <;> decide)

/-! ## Move-1 MUL-arm guarded inversion (folded from the former `DecodeGuards.lean`; the `hpin`-free
MUL inversion the collapsed `decodesMul` consumes). -/

/-- `mulOpToOpcode` is injective **on the canonical records** (globally 4-to-1 at MUL, 2-to-1 at
MULHSU — this is the fact the guard buys). -/
theorem mulOp_canonical_inj (m op : mul_op) (hm : mulOpCanonical m = true)
    (hop : mulOpCanonical op = true)
    (h : (mulOpToOpcode m).toNat = (mulOpToOpcode op).toNat) : m = op := by
  rcases m with ⟨a, b, c⟩; rcases op with ⟨a', b', c'⟩
  cases a <;> cases b <;> cases c <;> cases a' <;> cases b' <;> cases c' <;>
    first
      | rfl
      | (exact absurd hm (by decide))
      | (exact absurd hop (by decide))
      | (exact absurd h (by decide))

/-- **The MUL inversion WITHOUT `hpin`.** From the *guarded* projection, the opcode column pins the
whole `mul_op` record for any canonical `op` (in particular MUL and MULHSU, the two `hpin`-unprovable
cases): the guard on the projection side supplies the record's canonicity, and `mulOp_canonical_inj`
finishes. `hcanon` is `by decide`/`rfl` at each concrete opcode. -/
theorem instrToProgramRow_inv_mul' {pc : Vector (ZMod p) 3} {i : instruction}
    {row : ProgramRow (ZMod p)}
    (op : mul_op) (hcanon : mulOpCanonical op = true)
    (h : instrToProgramRow' pc i = some row)
    (hop : row.opcode = ((mulOpToOpcode op).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx, i = .MUL (rs2, rs1, rd, op) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] := by
  have h0 : instrToProgramRow pc i = some row := instrToProgramRow'_some h
  simp only [instrToProgramRow] at h0
  split at h0
  all_goals first | contradiction | (rw [Option.some.injEq] at h0; subst h0)
  all_goals (try (exact absurd himm one_ne_zero))
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd m
    have hg : mulOpCanonical m = true := instrToProgramRow'_mul_canonical h
    obtain rfl : m = op := mulOp_canonical_inj m op hg hcanon (opcodeCast_inj hop)
    exact ⟨rs2, rs1, rd, rfl, rfl, rfl, rfl⟩
  · rename_i rs2 rs1 rd
    exact absurd (opcodeCast_inj hop)
      (by rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide)
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop)
      (by cases isU' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop)
      (by cases isU' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop)
      (by cases isU' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))
  · rename_i rs2 rs1 rd isU'
    exact absurd (opcodeCast_inj hop)
      (by cases isU' <;> (rcases op with ⟨a, b, c⟩; cases a <;> cases b <;> cases c <;> decide))

/-- The MULHSU corollary — the previously-blocked case, zero side conditions beyond the columns. -/
theorem instrToProgramRow_inv_mulhsu {pc : Vector (ZMod p) 3} {i : instruction}
    {row : ProgramRow (ZMod p)}
    (h : instrToProgramRow' pc i = some row)
    (hop : row.opcode = ((Opcode.MULHSU).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx,
      i = .MUL (rs2, rs1, rd, ⟨.High, .Signed, .Unsigned⟩) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] :=
  instrToProgramRow_inv_mul' ⟨.High, .Signed, .Unsigned⟩ rfl h hop himm

/-- The plain-MUL corollary — the 4-preimage case, also unblocked. -/
theorem instrToProgramRow_inv_mul_low {pc : Vector (ZMod p) 3} {i : instruction}
    {row : ProgramRow (ZMod p)}
    (h : instrToProgramRow' pc i = some row)
    (hop : row.opcode = ((Opcode.MUL).toNat : ZMod p))
    (himm : row.imm_c = (0 : ZMod p)) :
    ∃ rs2 rs1 rd : regidx,
      i = .MUL (rs2, rs1, rd, ⟨.Low, .Signed, .Signed⟩) ∧
      row.op_a = regidxVal rd ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = #v[regidxVal rs2, 0, 0, 0] :=
  instrToProgramRow_inv_mul' ⟨.Low, .Signed, .Signed⟩ rfl h hop himm

/-- ∀-configured-state MUL/MULH/MULHU/MULHSU decode producer (mirrors `decodesDiv`), threading `hpin`. -/
theorem decodesMul {prog : GuestProgram} {row : ProgramRow (ZMod p)} (op : mul_op)
    (hpin : ∀ op' : mul_op, (mulOpToOpcode op').toNat = (mulOpToOpcode op).toNat → op' = op)
    (h : decodedInROM prog row)
    (hop : row.opcode = ((mulOpToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 0)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (rs2 rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.MUL (.Regidx rs2, .Regidx rs1, .Regidx rd, op)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨rs2r, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_mul op hpin hrow0 hop himm
  obtain ⟨rs2⟩ := rs2r; obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, rs2, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨rs2', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_mul op hpin hrow2 hop himm
  obtain ⟨rs2'⟩ := rs2'; obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e2 : rs2' = rs2 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hc.symm.trans hc')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h; exact h.symm)
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h; exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'; simp only [regidxVal] at h; exact h.symm)
  subst e2 e1 e0; rw [hi2] at hrun2; exact hrun2

/-- ∀-configured-state MULW decode producer (mirrors `decodesDivw`; no `mul_op`). -/
theorem decodesMulw {prog : GuestProgram} {row : ProgramRow (ZMod p)}
    (h : decodedInROM prog row)
    (hop : row.opcode = ((Opcode.MULW).toNat : ZMod p)) (himm : row.imm_c = 0)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (rs2 rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.MULW (.Regidx rs2, .Regidx rs1, .Regidx rd)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = #v[(rs2.toNat : ZMod p), 0, 0, 0] := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨rs2r, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_mulw hrow0 hop himm
  obtain ⟨rs2⟩ := rs2r; obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, rs2, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨rs2', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_mulw hrow2 hop himm
  obtain ⟨rs2'⟩ := rs2'; obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e2 : rs2' = rs2 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hc.symm.trans hc')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h; exact h.symm)
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h; exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'; simp only [regidxVal] at h; exact h.symm)
  subst e2 e1 e0; rw [hi2] at hrun2; exact hrun2

/-! ## BTYPE (branches) decode inversion + producer (SC Phase 4 · Phase 3a) -/

/-- **The 13-bit B-immediate sign-extension is injective** (clean, no `bv_decide`): recover `x` as the low
13 bits of `x.signExtend 64` via `getLsbD`. The imm-uniqueness `decodesBType` rides. -/
theorem sext13_inj {a b : BitVec 13} (h : a.signExtend 64 = b.signExtend 64) : a = b := by
  have key : ∀ x : BitVec 13, (x.signExtend 64).setWidth 13 = x := fun x => by
    apply BitVec.eq_of_getLsbD_eq; intro i hi
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_signExtend, hi]
    have h64 : i < 64 := by omega
    simp [hi, h64]
  rw [← key a, ← key b, h]

/-- **The BTYPE decode inversion (W7), generic over the branch op.** If a decoded `i` projects to a
committed row whose opcode is `op`'s (`bopToOpcode`, image `{40..45}`) and whose `imm_c = 1`, then `i` *is*
`BTYPE (imm, rs2, rs1, op)`, with `op_a = rs1` (SOURCE), `op_b = rs2` (source), `op_c = signExtended imm`.
`imm_c = 1` kills the R-shaped arms; the opcode column rules out the other immediate-shaped arms and pins
`op` within BTYPE. The immediate-shaped twin of `instrToProgramRow_inv_jalr`. -/
theorem instrToProgramRow_inv_btype {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramChip.ProgramRow (ZMod p)}
    (op : bop) (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = ((bopToOpcode op).toNat : ZMod p))
    (himm : row.imm_c = (1 : ZMod p)) :
    ∃ (imm : BitVec 13) (rs2 rs1 : regidx), i = .BTYPE (imm, rs2, rs1, op) ∧
      row.op_a = regidxVal rs1 ∧ row.op_b = #v[regidxVal rs2, 0, 0, 0]
      ∧ row.op_c = bitVecToWord (imm.signExtend 64) := by
  have honezero : (1 : ZMod p) ≠ 0 := by
    have : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    exact one_ne_zero
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm.symm honezero))
  · rename_i imm rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i imm rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i imm rd
    exact absurd (opcodeCast_inj hop) (by cases op <;> decide)
  · rename_i imm rs1 rd
    exact absurd (opcodeCast_inj hop) (by cases op <;> decide)
  · rename_i imm rs2 rs1 op'
    have hz : (bopToOpcode op').toNat = (bopToOpcode op).toNat := opcodeCast_inj hop
    obtain rfl : op' = op := by cases op' <;> cases op <;> first | rfl | (exact absurd hz (by decide))
    exact ⟨imm, rs2, rs1, rfl, rfl, rfl, rfl⟩
  · rename_i imm rs1 rd isU width
    exact absurd (opcodeCast_inj hop)
      (by cases isU <;> cases op <;> (simp only [loadOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rs2 rs1 width
    exact absurd (opcodeCast_inj hop)
      (by cases op <;> (simp only [storeOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i shamt rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i shamt rs1 rd op'
    exact absurd (opcodeCast_inj hop) (by cases op' <;> cases op <;> decide)
  · rename_i imm rs1 rd
    exact absurd (opcodeCast_inj hop) (by cases op <;> decide)

/-- **The ∀-configured-state BTYPE decode producer** — the `.BTYPE` twin of `decodesJalr`, keyed on the
committed `(opcode ∈ {BEQ..BGEU}, imm_c = 1)`. Recovers `w` + `imm/rs2/rs1` with the decode holding in every
configured state (`rs1` from `op_a` and `rs2` from `op_b` pinned by `regidx_bv_inj`, the 13-bit offset by
`sext13_inj` on `op_c`). What `BranchChip.advance` consumes. -/
theorem decodesBType {prog : GuestProgram} {row : ProgramChip.ProgramRow (ZMod p)} (op : bop)
    (h : decodedInROM prog row)
    (hop : row.opcode = ((bopToOpcode op).toNat : ZMod p)) (himm : row.imm_c = 1)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (imm : BitVec 13) (rs2 rs1 : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.BTYPE (imm, .Regidx rs2, .Regidx rs1, op)) sc) ∧
      row.op_a = (rs1.toNat : ZMod p) ∧
      row.op_b = #v[(rs2.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = bitVecToWord (imm.signExtend 64) := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨imm, rs2r, rs1r, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_btype op hrow0 hop himm
  obtain ⟨rs2⟩ := rs2r; obtain ⟨rs1⟩ := rs1r
  refine ⟨w, imm, rs2, rs1, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨imm', rs2', rs1', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_btype op hrow2 hop himm
  obtain ⟨rs2'⟩ := rs2'; obtain ⟨rs1'⟩ := rs1'
  have e2 : rs2' = rs2 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h
    exact h.symm)
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := ha.symm.trans ha'; simp only [regidxVal] at h; exact h.symm)
  have eimm : imm' = imm := by
    have e := congrArg (Word.toBitVec64 (p := p)) (hc.symm.trans hc')
    rw [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at e
    exact (sext13_inj e).symm
  subst e2 e1 eimm; rw [hi2] at hrun2; exact hrun2

/-! ## LOAD decode inversion + producer (SC Phase 4 · Phase 3b) -/

/-- **The LOAD decode inversion (W7).** LOAD is I-type-shaped (`op_a = rd`, `op_b = rs1`, `op_c =
signExtended offset`, `imm_c = 1`), opcode `loadOpcode width isU`. Because `loadOpcode` is not globally
injective (width 8 / `LD` is the `else` branch), the caller supplies the width-specific injectivity `hpin`
(discharged by `decide` for a concrete width, e.g. width 1 → {LB, LBU}). The other immediate-shaped arms are
ruled out by opcode disjointness (`split_ifs` over `loadOpcode`, then `decide`); the `imm_c = 0` arms by
`himm`. The load twin of `instrToProgramRow_inv_jalr`. -/
theorem instrToProgramRow_inv_load {pc : Vector (ZMod p) 3} {i : instruction} {row : ProgramRow (ZMod p)}
    (width : word_width) (isU : Bool)
    (hpin : ∀ (w' : word_width) (u' : Bool),
      (loadOpcode w' u').toNat = (loadOpcode width isU).toNat → w' = width ∧ u' = isU)
    (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = ((loadOpcode width isU).toNat : ZMod p))
    (himm : row.imm_c = (1 : ZMod p)) :
    ∃ (imm : BitVec 12) (rs1 rd : regidx), i = .LOAD (imm, rs1, rd, isU, width) ∧
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
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (simp only [iopToOpcode, loadOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (simp only [uopToOpcode, loadOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rd
    exact absurd (opcodeCast_inj hop)
      (by simp only [loadOpcode, Opcode.toNat]; split_ifs <;> decide)
  · rename_i imm rs1 rd
    exact absurd (opcodeCast_inj hop)
      (by simp only [loadOpcode, Opcode.toNat]; split_ifs <;> decide)
  · rename_i imm rs2 rs1 op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (simp only [bopToOpcode, loadOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rs1 rd isU' width'
    obtain ⟨rfl, rfl⟩ := hpin width' isU' (opcodeCast_inj hop)
    exact ⟨imm, rs1, rd, rfl, rfl, rfl, rfl⟩
  · rename_i imm rs2 rs1 width'
    exact absurd (opcodeCast_inj hop)
      (by simp only [storeOpcode, loadOpcode, Opcode.toNat]; split_ifs <;> decide)
  · rename_i shamt rs1 rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (simp only [sopToOpcode, loadOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i shamt rs1 rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (simp only [sopwToOpcode, loadOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rs1 rd
    exact absurd (opcodeCast_inj hop)
      (by simp only [loadOpcode, Opcode.toNat]; split_ifs <;> decide)

/-! ## Move-1 LOAD-opcode injectivity (folded from the former `DecodeGuards.lean`). -/

theorem loadOpcode_one (isU : Bool) :
    loadOpcode (1 : word_width) isU = if isU then Opcode.LBU else Opcode.LB := by
  unfold loadOpcode; rw [if_pos (beq_self_eq_true (1 : word_width))]

theorem loadOpcode_two (isU : Bool) :
    loadOpcode (2 : word_width) isU = if isU then Opcode.LHU else Opcode.LH := by
  unfold loadOpcode
  rw [if_neg (by decide), if_pos (beq_self_eq_true (2 : word_width))]

theorem loadOpcode_four (isU : Bool) :
    loadOpcode (4 : word_width) isU = if isU then Opcode.LWU else Opcode.LW := by
  unfold loadOpcode
  rw [if_neg (by decide), if_neg (by decide), if_pos (beq_self_eq_true (4 : word_width))]

theorem loadOpcode_eight (isU : Bool) : loadOpcode (8 : word_width) isU = Opcode.LD := by
  unfold loadOpcode
  rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]

/-- **`loadOpcode` is injective on the decoder image** {(1,*),(2,*),(4,*),(8,false)}. -/
theorem loadOpcode_inj_on_valid (w w' : word_width) (u u' : Bool)
    (hw : loadWidthOK w u = true) (hw' : loadWidthOK w' u' = true)
    (h : (loadOpcode w u).toNat = (loadOpcode w' u').toNat) : w = w' ∧ u = u' := by
  have hc : w = 1 ∨ w = 2 ∨ w = 4 ∨ (w = 8 ∧ u = false) := by
    simp only [loadWidthOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      Bool.not_eq_true'] at hw
    tauto
  have hc' : w' = 1 ∨ w' = 2 ∨ w' = 4 ∨ (w' = 8 ∧ u' = false) := by
    simp only [loadWidthOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true,
      Bool.not_eq_true'] at hw'
    tauto
  rcases hc with rfl | rfl | rfl | ⟨rfl, rfl⟩ <;>
    rcases hc' with rfl | rfl | rfl | ⟨rfl, rfl⟩ <;>
    simp only [loadOpcode_one, loadOpcode_two, loadOpcode_four, loadOpcode_eight] at h <;>
    (try cases u) <;> (try cases u') <;>
    (try simp at h) <;>
    first
      | exact ⟨rfl, rfl⟩
      | exact absurd h (by decide)

/-- **The ∀-configured-state LOAD decode producer** — the `.LOAD` twin of `decodesJalr`, keyed on the
committed `(opcode = loadOpcode width isU, imm_c = 1)` + the width-specific injectivity `hpin`. Recovers `w`
+ `imm/rs1/rd` with the decode holding in every configured state (`rs1`/`rd` pinned by `regidx_bv_inj`, the
12-bit offset by `sext12_inj` on `op_c`). What `advance_of_load_width1` consumes. -/
theorem decodesLoad {prog : GuestProgram} {row : ProgramRow (ZMod p)} (width : word_width) (isU : Bool)
    (hpin : ∀ (w' : word_width) (u' : Bool),
      (loadOpcode w' u').toNat = (loadOpcode width isU).toNat → w' = width ∧ u' = isU)
    (h : decodedInROM prog row)
    (hop : row.opcode = ((loadOpcode width isU).toNat : ZMod p)) (himm : row.imm_c = 1)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (imm : BitVec 12) (rs1 rd : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.LOAD (imm, .Regidx rs1, .Regidx rd, isU, width)) sc) ∧
      row.op_a = (rd.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = bitVecToWord (imm.signExtend 64) := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨imm, rs1r, rdr, hi0, ha, hb, hc⟩ := instrToProgramRow_inv_load width isU hpin hrow0 hop himm
  obtain ⟨rs1⟩ := rs1r; obtain ⟨rd⟩ := rdr
  refine ⟨w, imm, rs1, rd, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨imm', rs1', rd', hi2, ha', hb', hc'⟩ := instrToProgramRow_inv_load width isU hpin hrow2 hop himm
  obtain ⟨rs1'⟩ := rs1'; obtain ⟨rd'⟩ := rd'
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have h := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at h
    exact h.symm)
  have e0 : rd' = rd := regidx_bv_inj (by
    have h := ha.symm.trans ha'; simp only [regidxVal] at h; exact h.symm)
  have eimm : imm' = imm := by
    have e := congrArg (Word.toBitVec64 (p := p)) (hc.symm.trans hc')
    rw [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at e
    exact (sext12_inj e).symm
  subst e1 e0 eimm; rw [hi2] at hrun2; exact hrun2


/-! ## STORE decode inversion + producer (SC Phase 4 · Phase 3b) -/

-- impossible forward reference. Both are general `storeOpcode` facts and belong beside `storeOpcode`.

/-- `(storeOpcode 1).toNat = 36` (SB). Proven via `beq_self_eq_true` (NOT `rfl`/`decide`) so the
kernel never deep-reduces the `word_width = Int` comparison; the `SB.toNat = 36` tail is a small
enum `rfl`. Isolates the one Int-literal reduction the store adapter needs. -/
theorem storeOpcode_one_toNat : (storeOpcode (1 : word_width)).toNat = 36 := by
  have hsb : storeOpcode (1 : word_width) = Opcode.SB := by
    unfold storeOpcode; rw [if_pos (beq_self_eq_true (1 : word_width))]
  rw [hsb]; rfl

/-- **The width pin for SB.** `storeOpcode` is non-injective at `.SD` (maps everything ∉{1,2,4}
there), but injective at SB/SH/SW: `(storeOpcode w').toNat = (storeOpcode 1).toNat → w' = 1`. Feeds
`decodesStore`'s `hpin` for StoreByte. (For StoreDouble, the analogous pin needs the `ext_decode`
`width ∈ {1,2,4,8}` fact, since `storeOpcode 8 = .SD` collides with any other w' ∉ {1,2,4}.) -/
theorem storeOpcode_pin_one (w' : word_width)
    (h : (storeOpcode w').toNat = (storeOpcode (1 : word_width)).toNat) : w' = 1 := by
  rw [storeOpcode_one_toNat] at h; simp only [storeOpcode] at h
  split_ifs at h with h1 h2 h3
  · exact by simpa using h1
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- `(storeOpcode 2).toNat = 37` (SH). Same `beq_self_eq_true` discipline as width 1 — no kernel
deep-reduction of the `word_width = Int` comparison. -/
theorem storeOpcode_two_toNat : (storeOpcode (2 : word_width)).toNat = 37 := by
  have hsh : storeOpcode (2 : word_width) = Opcode.SH := by
    unfold storeOpcode; rw [if_neg (by decide), if_pos (beq_self_eq_true (2 : word_width))]
  rw [hsh]; rfl

/-- `(storeOpcode 4).toNat = 38` (SW). -/
theorem storeOpcode_four_toNat : (storeOpcode (4 : word_width)).toNat = 38 := by
  have hsw : storeOpcode (4 : word_width) = Opcode.SW := by
    unfold storeOpcode; rw [if_neg (by decide), if_neg (by decide),
      if_pos (beq_self_eq_true (4 : word_width))]
  rw [hsw]; rfl

/-- **The width pin for SH.** `storeOpcode` is injective at SB/SH/SW:
`(storeOpcode w').toNat = (storeOpcode 2).toNat → w' = 2`. Feeds `decodesStore`'s `hpin` for StoreHalf. -/
theorem storeOpcode_pin_two (w' : word_width)
    (h : (storeOpcode w').toNat = (storeOpcode (2 : word_width)).toNat) : w' = 2 := by
  rw [storeOpcode_two_toNat] at h; simp only [storeOpcode] at h
  split_ifs at h with h1 h2 h3
  · exact absurd h (by decide)
  · exact by simpa using h2
  · exact absurd h (by decide)
  · exact absurd h (by decide)

/-- **The width pin for SW.** `(storeOpcode w').toNat = (storeOpcode 4).toNat → w' = 4`. -/
theorem storeOpcode_pin_four (w' : word_width)
    (h : (storeOpcode w').toNat = (storeOpcode (4 : word_width)).toNat) : w' = 4 := by
  rw [storeOpcode_four_toNat] at h; simp only [storeOpcode] at h
  split_ifs at h with h1 h2 h3
  · exact absurd h (by decide)
  · exact absurd h (by decide)
  · exact by simpa using h3
  · exact absurd h (by decide)

/-- **The STORE decode inversion (W7), keyed on byte-width.** S-type shaped: if a decoded `i` projects
to a committed row whose opcode is `storeOpcode width`'s and whose `imm_c = 1`, then `i` *is*
`STORE (imm, rs2, rs1, width')` with `op_a = rs2` (the value SOURCE), `op_b = rs1` (base source),
`op_c = signExtended imm`. Because `word_width = Int` and `storeOpcode` is non-injective at `.SD`, the
recovered `width'` is returned with only `(storeOpcode width').toNat = (storeOpcode width).toNat`; the
caller pins it (via `storeOpcode_pin_one` for SB). `imm_c = 1` kills the R-shaped arms; the opcode
column (image {36,37,38,39}) rules out the other immediate-shaped arms. The `.STORE` twin of
`instrToProgramRow_inv_btype`. -/
theorem instrToProgramRow_inv_store {pc : Vector (ZMod p) 3} {i : instruction}
    {row : ProgramChip.ProgramRow (ZMod p)}
    (width : word_width) (h : instrToProgramRow pc i = some row)
    (hop : row.opcode = ((storeOpcode width).toNat : ZMod p))
    (himm : row.imm_c = (1 : ZMod p)) :
    ∃ (imm : BitVec 12) (rs2 rs1 : regidx) (width' : word_width),
      i = .STORE (imm, rs2, rs1, width') ∧
      (storeOpcode width').toNat = (storeOpcode width).toNat ∧
      row.op_a = regidxVal rs2 ∧ row.op_b = #v[regidxVal rs1, 0, 0, 0]
      ∧ row.op_c = bitVecToWord (imm.signExtend 64) := by
  have honezero : (1 : ZMod p) ≠ 0 := by
    have : Fact (1 < p) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
    exact one_ne_zero
  simp only [instrToProgramRow] at h
  split at h
  all_goals first | contradiction | (rw [Option.some.injEq] at h; subst h)
  all_goals (try (exact absurd himm.symm honezero))
  · rename_i imm rs1 rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (simp only [storeOpcode, iopToOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (simp only [storeOpcode, uopToOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rd
    exact absurd (opcodeCast_inj hop) (by simp only [storeOpcode, Opcode.toNat]; split_ifs <;> decide)
  · rename_i imm rs1 rd
    exact absurd (opcodeCast_inj hop) (by simp only [storeOpcode, Opcode.toNat]; split_ifs <;> decide)
  · rename_i imm rs2 rs1 op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (simp only [storeOpcode, bopToOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rs1 rd isU width2
    exact absurd (opcodeCast_inj hop)
      (by cases isU <;> (simp only [storeOpcode, loadOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rs2 rs1 width'
    exact ⟨imm, rs2, rs1, width', rfl, opcodeCast_inj hop, rfl, rfl, rfl⟩
  · rename_i shamt rs1 rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (simp only [storeOpcode, sopToOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i shamt rs1 rd op'
    exact absurd (opcodeCast_inj hop)
      (by cases op' <;> (simp only [storeOpcode, sopwToOpcode, Opcode.toNat]; split_ifs <;> decide))
  · rename_i imm rs1 rd
    exact absurd (opcodeCast_inj hop) (by simp only [storeOpcode, Opcode.toNat]; split_ifs <;> decide)

/-! ## Move-1 STORE-opcode injectivity (folded from the former `DecodeGuards.lean`; placed after the
`storeOpcode_*_toNat` pin family it consumes). -/

/-- `(storeOpcode 8).toNat = 39` (SD) — completing the existing 1/2/4 pin family. -/
theorem storeOpcode_eight_toNat : (storeOpcode (8 : word_width)).toNat = 39 := by
  have hsd : storeOpcode (8 : word_width) = Opcode.SD := by
    unfold storeOpcode
    rw [if_neg (by decide), if_neg (by decide), if_neg (by decide)]
  rw [hsd]; rfl

/-- **`storeOpcode` injective on the guarded widths** — including the previously un-pinnable SD case. -/
theorem storeOpcode_inj_on_valid (w w' : word_width)
    (hw : storeWidthOK w = true) (hw' : storeWidthOK w' = true)
    (h : (storeOpcode w).toNat = (storeOpcode w').toNat) : w = w' := by
  have hc : w = 1 ∨ w = 2 ∨ w = 4 ∨ w = 8 := by
    simp only [storeWidthOK, Bool.or_eq_true, beq_iff_eq] at hw; tauto
  have hc' : w' = 1 ∨ w' = 2 ∨ w' = 4 ∨ w' = 8 := by
    simp only [storeWidthOK, Bool.or_eq_true, beq_iff_eq] at hw'; tauto
  rcases hc with rfl | rfl | rfl | rfl <;> rcases hc' with rfl | rfl | rfl | rfl <;>
    simp only [storeOpcode_one_toNat, storeOpcode_two_toNat, storeOpcode_four_toNat,
      storeOpcode_eight_toNat] at h <;>
    first
      | rfl
      | exact absurd h (by decide)

/-- The SD pin — impossible without the guard. -/
theorem storeOpcode_pin_eight (w' : word_width) (hw' : storeWidthOK w' = true)
    (h : (storeOpcode w').toNat = (storeOpcode (8 : word_width)).toNat) : w' = 8 :=
  storeOpcode_inj_on_valid w' 8 hw' (by decide) h

/-- **The ∀-configured-state STORE decode producer** — the `.STORE` twin of `decodesBType`, keyed on
`(opcode = storeOpcode width, imm_c = 1)`. Recovers `w` + `imm/rs2/rs1` with the decode holding in
every configured state (`rs2` from `op_a`, `rs1` from `op_b` pinned by `regidx_bv_inj`; the 12-bit
offset by `sext12_inj` on `op_c`; the width by the caller's `hpin`). What `StoreByteChip.advance`
consumes. -/
theorem decodesStore {prog : GuestProgram} {row : ProgramChip.ProgramRow (ZMod p)} (width : word_width)
    (h : decodedInROM prog row)
    (hop : row.opcode = ((storeOpcode width).toNat : ZMod p)) (himm : row.imm_c = 1)
    (hpin : ∀ w' : word_width, (storeOpcode w').toNat = (storeOpcode width).toNat → w' = width)
    {s0 : SailState} (hs0 : SailConfigured s0) :
    ∃ (w : BitVec 32) (imm : BitVec 12) (rs2 rs1 : BitVec 5),
      prog.fetchWord (pcBitsOfRow row) = some w ∧
      (∀ sc, SailConfigured sc → (ext_decode w).run sc
        = .ok (instruction.STORE (imm, .Regidx rs2, .Regidx rs1, width)) sc) ∧
      row.op_a = (rs2.toNat : ZMod p) ∧
      row.op_b = #v[(rs1.toNat : ZMod p), 0, 0, 0] ∧
      row.op_c = bitVecToWord (imm.signExtend 64) := by
  obtain ⟨w, i0, hfetch, hrun0, hrow0⟩ := h.decodes s0 hs0
  obtain ⟨imm, rs2r, rs1r, width', hi0, hwop, ha, hb, hc⟩ :=
    instrToProgramRow_inv_store width hrow0 hop himm
  obtain ⟨rs2⟩ := rs2r; obtain ⟨rs1⟩ := rs1r
  refine ⟨w, imm, rs2, rs1, hfetch, ?_, ha, hb, hc⟩
  intro sc hsc
  obtain ⟨w2, i2, hfetch2, hrun2, hrow2⟩ := h.decodes sc hsc
  obtain rfl : w2 = w := (Option.some.injEq _ _).mp (hfetch2 ▸ hfetch)
  obtain ⟨imm', rs2', rs1', width'2, hi2, hwop2, ha', hb', hc'⟩ :=
    instrToProgramRow_inv_store width hrow2 hop himm
  have hpw2 : width'2 = width := hpin width'2 hwop2
  obtain ⟨rs2'⟩ := rs2'; obtain ⟨rs1'⟩ := rs1'
  have e2 : rs2' = rs2 := regidx_bv_inj (by
    have hh := ha.symm.trans ha'; simp only [regidxVal] at hh; exact hh.symm)
  have e1 : rs1' = rs1 := regidx_bv_inj (by
    have hh := congrArg (fun v => v[0]) (hb.symm.trans hb')
    simp only [regidxVal, Vector.getElem_mk, List.getElem_toArray, List.getElem_cons_zero] at hh
    exact hh.symm)
  have eimm : imm' = imm := by
    have e := congrArg (Word.toBitVec64 (p := p)) (hc.symm.trans hc')
    rw [toBitVec64_bitVecToWord, toBitVec64_bitVecToWord] at e
    exact (sext12_inj e).symm
  rw [e2, e1, eimm, hpw2] at hi2
  rw [hi2] at hrun2; exact hrun2


end SP1Clean.Soundness.Target
