import SP1Foundations.SailM
import SP1Foundations.Opcode

set_option linter.style.setOption false
set_option linter.style.longLine false

open LeanRV64D.Functions Sail SailState

section isValidMemConfig

/-- `plat_have_clint` is manually set in our fork of sail in the `PlatformConfig.lean` file. -/
@[simp] lemma plat_have_clint_eq_false : plat_have_clint = false := rfl

/-- `plat_have_sig` is manually set in our fork of sail in the `PlatformConfig.lean` file. -/
@[simp] lemma plat_have_sig_eq_false : plat_have_sig = false := rfl

/-- `sys_pmp_count` is manually set to zero in our fork in the `PmpRegs.lean` file. -/
@[simp] lemma sys_pmp_count_eq_zero : sys_pmp_count = 0 := rfl

/-- Memory access setting for all of memory in our model. -/
@[reducible]
def SP1_PMA : PMA where
  mem_type := MemoryRegionType.MainMemory
  cacheable := false
  coherent := true
  executable := true
  readable := true
  writable := true
  read_idempotent := false
  write_idempotent := false
  misaligned_exceptions := {
    load_store := none
    vector := none
    amo := .AlignmentException
  }
  atomic_support := AtomicSupport.AMONone
  reservability := Reservability.RsrvNone
  supports_cbo_zero := false
  supports_pte_read := false
  supports_pte_write := false

/-- Single memory region with uniform access across all memory. -/
@[reducible]
def SP1_PMA_Region : PMA_Region where
  base := 2 ^ 16
  size := 2 ^ 48 - 2 ^ 16
  attributes := SP1_PMA
  include_in_device_tree := false

/-- All the registers needed for memory ops are set appropriately. -/
structure SailState.isValidMemConfig (s : SailState) (hs : SailState.isInitialized s) where
  h_cur_privilege : s.regs.get Register.cur_privilege (hs _) = Privilege.Machine
  h_mprv_disabled : BitVec.ofNat 1 ((s.regs.get Register.mstatus (hs _)).toNat >>> 17) = 0#1
  h_mseccfg_disabled : BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs _)).toNat >>> 10) = 0#1
  h_htif_disabled : s.regs.get Register.htif_tohost_base (hs _) = none
  h_pma_regions : s.regs.get Register.pma_regions (hs _) = [SP1_PMA_Region]

end isValidMemConfig

/-! ### Polymorphic `*_type_constraints_poly` over `ZMod p`

Reader-type assumptions parametric over a prime field `ZMod p`. Used by
`Opcode.trusted_instr_poly` and `SP1Constraint.toProp`. -/
section reader_constraints_poly

variable {p : ℕ} [NeZero p]

@[simp] def i_type_constraints_poly
    (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : ZMod p) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 12 op_c_0.val)

@[simp] def shift_i_type_constraints_poly
    (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : ZMod p) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ op_c_0 < 2^6 ∧ op_c_1 = 0 ∧ op_c_2 = 0 ∧ op_c_3 = 0

@[simp]
def w_shift_i_type_constraints_poly
    (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : ZMod p) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ op_c_0 < 2^5 ∧ op_c_1 = 0 ∧ op_c_2 = 0 ∧ op_c_3 = 0

@[simp] def r_type_constraints_poly
    (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : ZMod p) : Prop :=
  (imm_b = 0 ∧ imm_c = 0)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ op_c_0 < 32 ∧ op_c_1 = 0 ∧ op_c_2 = 0 ∧ op_c_3 = 0

@[simp]
def b_type_constraints_poly (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : ZMod p) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 13 op_c_0.val)
  ∧ (Word.toBitVec64 #v[op_c_0, op_c_1, op_c_2, op_c_3] % 4#64 = 0)

end reader_constraints_poly

namespace Opcode

/-- Assumptions we make about the inputs to instructions, over `ZMod p`. -/
@[simp] def trusted_instr_poly {p : ℕ} [NeZero p] (opcode : Opcode)
  (op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : ZMod p) : Prop :=
  match opcode with
  | ADD | SUB | SUBW =>
      r_type_constraints_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | ADDI | JALR =>
      i_type_constraints_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | AND | OR | XOR | SLT | SLTU | ADDW =>
      (imm_c = 0 → r_type_constraints_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
      ∧ (imm_c = 1 → i_type_constraints_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
  | BEQ | BNE | BLT | BGE | BLTU | BGEU =>
      b_type_constraints_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | SLL | SRL | SRA =>
      (imm_c = 0 → r_type_constraints_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
      ∧ (imm_c = 1 → shift_i_type_constraints_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
  | LUI | AUIPC =>
      (imm_b = 1 ∧ imm_c = 1)
      ∧ op_b_0.val % 2 ^ 12 = 0
      ∧ BitVec.signExtend 64 (BitVec.ofNat 32 (op_b_0.val + op_b_1.val * 65536)) = Word.toBitVec64 #v[op_b_0, op_b_1, op_b_2, op_b_3]
  | JAL =>
      (imm_b = 1 ∧ imm_c = 1) ∧
      Word.toBitVec64 #v[op_b_0, op_b_1, op_b_2, op_b_3] = BitVec.signExtend 64 (BitVec.ofNat 21 (op_b_0.val + op_b_1.val * 65536)) ∧
      (Word.toBitVec64 #v[op_b_0, op_b_1, op_b_2, op_b_3]) % 4#64 = 0
  | LB | LH | LW | LD | LBU | LHU | LWU =>
      i_type_constraints_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | SB | SH | SW | SD =>
      i_type_constraints_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | SLLW | SRLW | SRAW =>
      (imm_c = 0 → r_type_constraints_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
      ∧ (imm_c = 1 → w_shift_i_type_constraints_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c)
  | MUL | MULW | MULH | MULHU | MULHSU | DIV | DIVU | DIVW | DIVUW | REM | REMU | REMW | REMUW =>
      r_type_constraints_poly op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c
  | UNIMP | ECALL | EBREAK => True

end Opcode
