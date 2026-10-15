import SP1Clean.Model.SailWrap
/-!
# Monad-free Sail "M"-extension semantics

The pure write value of each generated `execute_MUL`/`execute_MULW`/`execute_DIV`/`execute_DIVW`/
`execute_REM`/`execute_REMW` clause of the pinned `LeanRV64D` model, factored out of the `SailM`
plumbing exactly as `Model/SailWrap.lean` does for `execute_RTYPE`/`execute_RTYPEW`
(`execute_RTYPE_pure`): every clause is `skeleton_binary rs2 rs1 rd f` — read `rs1`, read `rs2`,
write `f rs1 rs2` to `rd`, retire — and the `execute_*_eq` lemmas below hold by `rfl` because the
bodies are the generated ones with the register reads lifted out. The bit-vector-only equalities
between these and the `RV64` reference functions are in `Proofs/Sail/RV64Bridge.lean`.

Argument conventions follow the generated clauses: `rs2` before `rs1`; the `div`/`divw`/`mul`
family takes its mode flag last and `rem`/`remw` take it first.

This module replaces the former `riscv-lean` dependency's `SailPure`/`Skeleton`/`SailToRV64` role.
-/

open LeanRV64D.Defs

namespace SP1Clean.SailRV64

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

/-- The shape of every binary register-register clause: read `rs1` and `rs2`, write
`execute_func rs1 rs2` to `rd`, retire successfully. -/
def skeleton_binary (rs2 : regidx) (rs1 : regidx) (rd : regidx)
    (execute_func : BitVec 64 → BitVec 64 → BitVec 64) : SailM ExecutionResult := do
  let rs1_val ← rX_bits rs1
  let rs2_val ← rX_bits rs2
  let result := execute_func rs1_val rs2_val
  wX_bits rd result
  pure RETIRE_SUCCESS

/-- `execute_REM`'s write value: the truncating remainder of the two operands read as unsigned or
signed integers, `rs1` when the divisor is zero. -/
def rem (is_unsigned : Bool) (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_int : Int := if is_unsigned then BitVec.toNatInt rs1_val else BitVec.toInt rs1_val
  let rs2_int : Int := if is_unsigned then BitVec.toNatInt rs2_val else BitVec.toInt rs2_val
  let remainder := if ((rs2_int == 0) : Bool) then rs1_int else (Int.tmod rs1_int rs2_int)
  to_bits_truncate (l := 64) remainder

/-- `execute_REMW`'s write value: the 32-bit truncating remainder of the low words, sign-extended. -/
def remw (is_unsigned : Bool) (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb rs1_val 31 0
  let rs2_val32 := Sail.BitVec.extractLsb rs2_val 31 0
  let rs1_int : Int := if is_unsigned then BitVec.toNatInt rs1_val32 else BitVec.toInt rs1_val32
  let rs2_int : Int := if is_unsigned then BitVec.toNatInt rs2_val32 else BitVec.toInt rs2_val32
  let remainder := if ((rs2_int == 0) : Bool) then rs1_int else (Int.tmod rs1_int rs2_int)
  sign_extend (m := 64) (to_bits_truncate (l := 32) remainder)

/-- `execute_MULW`'s write value: the truncated 32-bit product of the low words, sign-extended. -/
def mulw (rs2_val : BitVec 64) (rs1_val : BitVec 64) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb rs1_val 31 0
  let rs2_val32 := Sail.BitVec.extractLsb rs2_val 31 0
  let rs1_int : Int := BitVec.toInt rs1_val32
  let rs2_int : Int := BitVec.toInt rs2_val32
  let result32 : BitVec 32 := to_bits_truncate (l := 32) (rs1_int *i rs2_int)
  sign_extend (m := 64) result32

/-- `execute_MUL`'s write value: the model's `mult_to_bits_half` selected by the `mul_op`
signedness/half flags. -/
def mul (rs2_val : BitVec 64) (rs1_val : BitVec 64) (mul_op : mul_op) : BitVec 64 :=
  mult_to_bits_half (l := 64) mul_op.signed_rs1 mul_op.signed_rs2 rs1_val rs2_val
    mul_op.result_part

/-- `execute_DIV`'s write value: the truncating quotient with the ISA's zero-divisor and signed
overflow results. -/
def div (rs2_val : BitVec 64) (rs1_val : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_int : Int := if is_unsigned then BitVec.toNatInt rs1_val else BitVec.toInt rs1_val
  let rs2_int : Int := if is_unsigned then BitVec.toNatInt rs2_val else BitVec.toInt rs2_val
  let quotient : Int :=
    if ((rs2_int == 0) : Bool) then (Neg.neg 1) else (Int.tdiv rs1_int rs2_int)
  let quotient : Int :=
    if (((LeanRV64D.Functions.not is_unsigned)
          && (quotient ≥b (2 ^i (LeanRV64D.Functions.xlen -i 1)))) : Bool)
      then (Neg.neg (2 ^i (LeanRV64D.Functions.xlen -i 1)))
    else quotient
  to_bits_truncate (l := 64) quotient

/-- `execute_DIVW`'s write value: the 32-bit truncating quotient of the low words,
sign-extended. -/
def divw (rs2_val : BitVec 64) (rs1_val : BitVec 64) (is_unsigned : Bool) : BitVec 64 :=
  let rs1_val32 := Sail.BitVec.extractLsb rs1_val 31 0
  let rs2_val32 := Sail.BitVec.extractLsb rs2_val 31 0
  let rs1_int : Int := if is_unsigned then BitVec.toNatInt rs1_val32 else BitVec.toInt rs1_val32
  let rs2_int : Int := if is_unsigned then BitVec.toNatInt rs2_val32 else BitVec.toInt rs2_val32
  let quotient : Int :=
    if ((rs2_int == 0) : Bool) then (Neg.neg 1) else (Int.tdiv rs1_int rs2_int)
  let quotient : Int :=
    if (((LeanRV64D.Functions.not is_unsigned) && (quotient ≥b (2 ^i 31))) : Bool)
      then (Neg.neg (2 ^i 31))
    else quotient
  sign_extend (m := 64) (to_bits_truncate (l := 32) quotient)

/-! ## The generated clauses are their skeletons -/

theorem execute_MUL_eq (rs2 rs1 rd : regidx) (op : mul_op) :
    execute_MUL rs2 rs1 rd op
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => mul val2 val1 op) := rfl

theorem execute_MULW_eq (rs2 rs1 rd : regidx) :
    execute_MULW rs2 rs1 rd = skeleton_binary rs2 rs1 rd (fun val1 val2 => mulw val2 val1) := rfl

theorem execute_DIV_eq (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIV rs2 rs1 rd is_unsigned
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => div val2 val1 is_unsigned) := rfl

theorem execute_DIVW_eq (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_DIVW rs2 rs1 rd is_unsigned
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => divw val2 val1 is_unsigned) := rfl

theorem execute_REM_eq (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REM rs2 rs1 rd is_unsigned
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => rem is_unsigned val2 val1) := rfl

theorem execute_REMW_eq (rs2 rs1 rd : regidx) (is_unsigned : Bool) :
    execute_REMW rs2 rs1 rd is_unsigned
      = skeleton_binary rs2 rs1 rd (fun val1 val2 => remw is_unsigned val2 val1) := rfl

end SP1Clean.SailRV64
