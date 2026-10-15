module

public import Mathlib.Data.BitVec
/-!
# RV64 reference semantics

The bit-vector reference functions the chip `Spec`s are stated against: one pure function per
RV64IM operation the supported instruction set uses, on 64-bit operands. They are the project's own
reading of the RISC-V unprivileged ISA (RV64I integer register-register/upper-immediate operations
and the "M" multiplication/division extension), in the shape the chip proofs unfold — the low
32-bit projections of the `*w` forms are `extractLsb 31 0`, the shift amounts are the low
five/six bits of `rs2`, and division by zero / signed overflow follow the ISA's fixed results.

**Operand order is `rs2` then `rs1`**, matching the Sail model's `execute_* rs2 rs1 rd` argument
order so that a bridge lemma reads `SailRV64.op rs2 rs1 = RV64.op rs2 rs1` without swapping. The
Sail-side counterparts live in `Model/SailPure.lean`; the equalities between the two are proved
in `Proofs/Sail/RV64Bridge.lean`.

This module replaces the former `riscv-lean` dependency, whose only role here was to supply
these definitions and the same bridge lemmas.
-/

@[expose] public section

namespace SP1Clean.RV64

/-! ## RV64I -/

/-- `LUI`: the 20-bit immediate placed in bits 31..12, sign-extended to 64 bits. -/
def lui (imm : BitVec 20) : BitVec 64 :=
  BitVec.signExtend 64 (imm ++ (0x0 : BitVec 12))

/-- `AUIPC`: the sign-extended 32-bit offset `imm << 12` added to the `pc`. -/
def auipc (imm : BitVec 20) (pc : BitVec 64) : BitVec 64 :=
  BitVec.add (BitVec.signExtend 64 (BitVec.append imm (0x0 : BitVec 12))) pc

/-- `ADD`: wrapping 64-bit addition. -/
def add (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val + rs2_val

/-- `SUB`: wrapping 64-bit subtraction. -/
def sub (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val - rs2_val

/-- `SLL`: logical left shift of `rs1` by the low six bits of `rs2`. -/
def sll (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let shamt := (BitVec.extractLsb 5 0 rs2_val);
  rs1_val <<< shamt

/-- `SLT`: `1` iff `rs1 < rs2` as signed integers. -/
def slt (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.ofBool (BitVec.slt rs1_val rs2_val))

/-- `SLTU`: `1` iff `rs1 < rs2` as unsigned integers. -/
def sltu (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.setWidth 64 (BitVec.ofBool (BitVec.ult rs1_val rs2_val))

/-- `XOR`. -/
def xor (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val ^^^ rs2_val

/-- `SRL`: logical right shift of `rs1` by the low six bits of `rs2`. -/
def srl (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let shamt := (BitVec.extractLsb 5 0 rs2_val)
  rs1_val >>> shamt

/-- `SRA`: arithmetic right shift of `rs1` by the low six bits of `rs2`. -/
def sra (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.sshiftRight' rs1_val (BitVec.extractLsb 5 0 rs2_val)

/-- `OR`. -/
def or (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val ||| rs2_val

/-- `AND`. -/
def and (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val &&& rs2_val

/-- `ADDW`: 32-bit wrapping addition of the low words, sign-extended. -/
def addw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb' 0 32 rs1_val
  let rs2 := BitVec.extractLsb' 0 32 rs2_val
  BitVec.signExtend 64 (BitVec.add rs1 rs2)

/-- `SUBW`: 32-bit wrapping subtraction of the low words, sign-extended. -/
def subw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb' 0 32 rs1_val
  let rs2 := BitVec.extractLsb' 0 32 rs2_val
  BitVec.signExtend 64 (BitVec.sub rs1 rs2)

/-- `SLLW`: logical left shift of the low word of `rs1` by the low five bits of `rs2`,
sign-extended. -/
def sllw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb' 0 32 rs1_val;
  let rs2 := BitVec.extractLsb' 0 32 rs2_val;
  let shamt := BitVec.extractLsb' 0 5 rs2;
  BitVec.signExtend 64 (rs1 <<< shamt)

/-- `SRLW`: logical right shift of the low word of `rs1` by the low five bits of `rs2`,
sign-extended. -/
def srlw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb' 0 32 rs1_val;
  let rs2 := BitVec.extractLsb' 0 32 rs2_val;
  let shamt := BitVec.extractLsb' 0 5 rs2;
  BitVec.signExtend 64 (rs1 >>> shamt)

/-- `SRAW`: arithmetic right shift of the low word of `rs1` by the low five bits of `rs2`,
sign-extended. -/
def sraw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb 31 0 rs1_val
  let rs2 := BitVec.extractLsb 4 0 rs2_val
  BitVec.signExtend 64 (BitVec.sshiftRight' rs1 rs2)

/-! ## "M" extension -/

/-- `REM`: signed remainder, truncating toward zero; `rs1` when `rs2 = 0`. -/
def rem (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val.srem rs2_val

/-- `REMU`: unsigned remainder; `rs1` when `rs2 = 0`. -/
def remu (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs1_val.umod rs2_val

/-- `REMW`: signed 32-bit remainder of the low words, sign-extended. -/
def remw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb 31 0 rs1_val
  let rs2 := BitVec.extractLsb 31 0 rs2_val
  BitVec.signExtend 64 (rs1.srem rs2)

/-- `REMUW`: unsigned 32-bit remainder of the low words, sign-extended. -/
def remuw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb 31 0 rs1_val
  let rs2 := BitVec.extractLsb 31 0 rs2_val
  BitVec.signExtend 64 (rs1.umod rs2)

/-- `MUL`: the low 64 bits of the product. -/
def mul (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 := rs2_val * rs1_val

/-- `MULH`: the high 64 bits of the signed × signed product. -/
def mulh (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 ((BitVec.signExtend 129 rs1_val) * (BitVec.signExtend 129 rs2_val))

/-- `MULHU`: the high 64 bits of the unsigned × unsigned product. -/
def mulhu (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
   BitVec.extractLsb 127 64
    (BitVec.extractLsb' 0 128 ((BitVec.zeroExtend 128 rs1_val) * (BitVec.zeroExtend 128 rs2_val)))

/-- `MULHSU`: the high 64 bits of the signed `rs1` × unsigned `rs2` product. -/
def mulhsu (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.extractLsb 127 64 (((BitVec.signExtend 129 rs1_val) * (BitVec.zeroExtend 129 rs2_val)))

/-- `MULW`: the low 32 bits of the product of the low words, sign-extended. -/
def mulw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  BitVec.signExtend 64
    (((BitVec.extractLsb 31 0 rs1_val) * (BitVec.extractLsb 31 0 rs2_val)))

/-- `DIV`: signed division truncating toward zero; `-1` when `rs2 = 0`, and the ISA's wrap on
`MIN / -1` (carried by `BitVec.sdiv`). -/
def div (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  if rs2_val = 0#64 then
    -1#64
  else
    rs1_val.sdiv rs2_val

/-- `DIVW`: signed 32-bit division of the low words, sign-extended; `-1` when the low word of
`rs2` is zero. -/
def divw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb 31 0 rs1_val
  let rs2 := BitVec.extractLsb 31 0 rs2_val
  BitVec.signExtend 64 (if rs2 = 0#32 then  -1#32 else rs1.sdiv rs2)

/-- `DIVU`: unsigned division; all ones when `rs2 = 0`. -/
def divu (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  if rs2_val = 0#64 then  (-1)  else rs1_val.udiv rs2_val

/-- `DIVUW`: unsigned 32-bit division of the low words, sign-extended; all ones when the low
word of `rs2` is zero. -/
def divuw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1 := BitVec.extractLsb 31 0 rs1_val
  let rs2 := BitVec.extractLsb 31 0 rs2_val
  BitVec.signExtend 64 (if rs2 = 0#32 then -1#32 else rs1.udiv rs2)

end SP1Clean.RV64
