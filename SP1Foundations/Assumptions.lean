import SP1Foundations.SailM
import SP1Foundations.Opcode

open LeanRV64D.Functions Sail SailState

/-
i type
imm_b = 0, imm_c = 1 is correct
op_b < 32 is correct since it's a register
op_c being 12-bit sign-extension is correct

shift i type
imm_b = 0, imm_c = 1, op_b < 32 is correct
op_c < 2^6 is not sure, probably not needed :eyes:
in that case probably can just remove shift i type assumption and use I type
w shift i type
imm_b = 0, imm_c = 1, op_b < 32 is correct
op_c < 2^5 is not sure, probably not needed  :eyes:
in that case probably can just remove shift i type assumption and use I type
r type
imm_b = 0, imm_c = 0 is correct
op_b, op_c < 32 is correct since they are registers
b type
imm_b = 0, imm_c = 1 is correct
op_b < 32 is correct since its register
op_c being 13-bit sign extended is right
not sure if op_c % 4 == 0 is necessarily true?  :eyes:
I know that op_c % 2 == 0 is true though
(edited)
:eyes:
1

Also sent as direct message


Min
  Oct 8th at 6:53 PM
trusted_instr_state :eyes:
as mentioned, the (op_b + op_c) % 4 == 0 is now in constraints
so maybe it's possible to just fully remove trusted_instr_state
(edited)
Also sent as direct message


Min
  Oct 8th at 7:23 PM
trusted_instr
ADD/SUB/SUBW -> RType (true)
ADDI / JALR -> IType (true)
AND/OR/XOR/SLT/SLTU/ADDW
these are between R / I (true)
so imm_c = 0 -> RType, and imm_c = 1 -> IType
BEQ | BNE | BLT | BGE | BLTU | BGEU -> BType (true)
SLL | SRL | SRA
these are between R & shift-I (true)
so imm_c = 0 -> RType, and imm_c = 1 -> shiftIType
LUI | AUIPC
these are U type, so imm_b = imm_c = 1 is true
not sure op_b_0 >= 2^12 is true? it's a multiple of 2^12 probably, but it can be zero I think? :eyes:
the sign extension is correct (2^12 * 20bit = 32 bit -> sign extended to 64 bit)
JAL
this is J type, so imm_b = imm_c = 1 is true
21-bit sign extension is correct since its J type
technically we only know op_b % 2 == 0 I think?  :eyes:
also here we do constrain (pc + op_b) % 4 == 0 directly as well
so you don't need to assume op_b % 4 == 0 here
LOAD & STORE
these are all I types
to be exact, STORE is S type, but the immediate is 12-bit sign extended
SLLW / SRLW / SRAW
these are between R & w-shift-I (true)
so imm_c = 0 -> RType, and imm_c = 1 -> w-shiftIType
MUL & DIV
these are R type (true)
-/

section reader_constraints

@[simp] def i_type_constraints
    (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin KB) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 12 op_c_0)

@[simp] def shift_i_type_constraints
    (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin KB) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)

@[simp]
def w_shift_i_type_constraints
    (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin KB) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)

@[simp] def r_type_constraints
    (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin KB) : Prop :=
  (imm_b = 0 ∧ imm_c = 0)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ op_c_0 < 32 ∧ op_c_1 = 0 ∧ op_c_2 = 0 ∧ op_c_3 = 0

@[simp]
def b_type_constraints (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin KB) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 13 op_c_0)
  ∧ (Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] % 4#64 = 0)

end reader_constraints

namespace Opcode

/-- Assumptions we make about the inputs to instructions. -/
@[simp] def trusted_instr (opcode : Opcode)
  (op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin KB) : Prop :=
  match opcode with
  | ADD | SUB | SUBW =>
      r_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | ADDI | JALR =>
      i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | AND | OR | XOR | SLT | SLTU | ADDW =>
      (imm_c = 0 → r_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
      ∧ (imm_c = 1 → i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
  | BEQ | BNE | BLT | BGE | BLTU | BGEU =>
      b_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | SLL | SRL | SRA =>
      (imm_c = 0 → r_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
      ∧ (imm_c = 1 → shift_i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
  | LUI | AUIPC =>
      (imm_b = 1 ∧ imm_c = 1)
      ∧ op_b_0 >= 2^12
      ∧ BitVec.signExtend 64 (BitVec.ofNat 32 (op_b_0.val + op_b_1.val * 65536)) = Word.toBitVec64 #v[op_b_0, op_b_1, op_b_2, op_b_3]
  | JAL =>
      (imm_b = 1 ∧ imm_c = 1) ∧
      Word.toBitVec64 #v[op_b_0, op_b_1, op_b_2, op_b_3] = BitVec.signExtend 64 (BitVec.ofNat 21 (op_b_0.val + op_b_1.val * 65536)) ∧
      (Word.toBitVec64 #v[op_b_0, op_b_1, op_b_2, op_b_3]) % 4#64 = 0
  | LB | LH | LW | LD | LBU | LHU | LWU =>
      i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | SB | SH | SW | SD =>
      i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | SLLW | SRLW | SRAW =>
      (imm_c = 0 → r_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
      ∧ (imm_c = 1 → w_shift_i_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
  | MUL | MULW | MULH | MULHU | MULHSU | DIV | DIVU | DIVW | DIVUW | REM | REMU | REMW | REMUW =>
      r_type_constraints op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | UNIMP | ECALL | EBREAK => True

end Opcode

section SailState

/-- Class specifying a number of register values that are expected to be true in the SP1 VM.
Note: it should be shown inductively that SP1 will preserve these values given the constrains. -/
class SailState.SP1Config (s : SailState) where
  is_mem_regs (reg : Register) : reg ∈ s.regs
  -- dt: we should have a more natural way to express this
  h_mprv_disabled : BitVec.ofNat 1 (BitVec.toNat (s.regs.get Register.mstatus (is_mem_regs _)) >>> 17) = 0#1
  h_cur_privilege : s.regs.get Register.cur_privilege (is_mem_regs _) = Privilege.Machine
  h_clint_base : s.regs.get Register.plat_clint_base (is_mem_regs _) = 0
  h_clint_size : s.regs.get Register.plat_clint_size (is_mem_regs _) = 0
  h_plat_rom_base : s.regs.get Register.plat_rom_base (is_mem_regs _) = 0
  h_plat_ram_base : s.regs.get Register.plat_ram_base (is_mem_regs _) = 2^16
  h_plat_ram_size : s.regs.get Register.plat_ram_size (is_mem_regs _) = 2^48 - 2^16 - 1

end SailState

section public_values

/-- Mock function that the constraint extractor uses to print public values. -/
opaque public_value : Unit → ℕ → Fin KB := fun _ => 0

/-- Assume mprotect is globally disabled in SP1 via a public value. -/
@[simp] axiom mprotect_disabled : public_value () 151 = 0

end public_values

section pmp_check

/-- We can't prove this directly because the loop in `pmpCheck` doesn't unfold.
Adding this is at least consistent, since the left-hand side has no actual value. -/
axiom pmp_check_machine (reg_val : BitVec 64) (offset : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (width : ℕ) :
    EStateM.run (pmpCheck (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0)))
      width (AccessType.Write Data) Privilege.Machine) s = EStateM.Result.ok none s

/-- We can't prove this directly because the loop in `pmpCheck` doesn't unfold.
Adding this is at least consistent, since the left-hand side has no actual value. -/
axiom pmp_check_machine' (reg_val : BitVec 64) (offset : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (width : ℕ) :
    EStateM.run (pmpCheck (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0)))
      width (AccessType.Read ()) Privilege.Machine) s = EStateM.Result.ok none s

end pmp_check
