import SP1Foundations.SailM
import SP1Foundations.Opcode

open LeanRV64D.Functions Sail SailState

section isValidMemConfig

/-- `plat_have_clint` is manually set in our fork of sail in the `PlatformConfig.lean` file. -/
@[simp] lemma plat_have_clint_eq_false : plat_have_clint = false := rfl

/-- `plat_have_sig` is manually set in our fork of sail in the `PlatformConfig.lean` file. -/
@[simp] lemma plat_have_sig_eq_false : plat_have_sig = false := rfl

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
  ∧ op_c_0 < 2^6 ∧ op_c_1 = 0 ∧ op_c_2 = 0 ∧ op_c_3 = 0

@[simp]
def w_shift_i_type_constraints
    (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : Fin KB) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ op_c_0 < 2^5 ∧ op_c_1 = 0 ∧ op_c_2 = 0 ∧ op_c_3 = 0

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

/-! ### Polymorphic `*_type_constraints_poly` over `ZMod p`

Mirror the `Fin KB` versions above but parametric over a prime field
`ZMod p`. Used by `Opcode.trusted_instr_poly` and
`SP1Constraint.toProp_poly`. The existing `Fin KB` versions stay
load-bearing for chip code; these `_poly` variants exist so the
operation iff lemmas and the polymorphic `toProp` body can refer to
generic-field constraints. -/
section reader_constraints_poly

variable {p : ℕ} [NeZero p]

@[simp] def i_type_constraints_poly
    (_op_a op_b_0 op_b_1 op_b_2 op_b_3 op_c_0 op_c_1 op_c_2 op_c_3 imm_b imm_c : ZMod p) : Prop :=
  (imm_b = 0 ∧ imm_c = 1)
  ∧ (op_b_0 < 32 ∧ op_b_1 = 0 ∧ op_b_2 = 0 ∧ op_b_3 = 0)
  ∧ Word.toBitVec64_poly #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 12 op_c_0.val)

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
  ∧ Word.toBitVec64_poly #v[op_c_0, op_c_1, op_c_2, op_c_3] = BitVec.signExtend 64 (BitVec.ofNat 13 op_c_0.val)
  ∧ (Word.toBitVec64_poly #v[op_c_0, op_c_1, op_c_2, op_c_3] % 4#64 = 0)

end reader_constraints_poly

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
      ∧ op_b_0.val % 2 ^ 12 = 0
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

/-- Polymorphic counterpart of `trusted_instr` over `ZMod p`. Used by
`SP1Constraint.toProp_poly`. -/
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
      ∧ BitVec.signExtend 64 (BitVec.ofNat 32 (op_b_0.val + op_b_1.val * 65536)) = Word.toBitVec64_poly #v[op_b_0, op_b_1, op_b_2, op_b_3]
  | JAL =>
      (imm_b = 1 ∧ imm_c = 1) ∧
      Word.toBitVec64_poly #v[op_b_0, op_b_1, op_b_2, op_b_3] = BitVec.signExtend 64 (BitVec.ofNat 21 (op_b_0.val + op_b_1.val * 65536)) ∧
      (Word.toBitVec64_poly #v[op_b_0, op_b_1, op_b_2, op_b_3]) % 4#64 = 0
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

section pmp_check

/-- Store-side PMP check is a no-op under SP1's kernel configuration.
Used by: `MemChecks.lean` (4 sites, byte/half/word/double widths).
Reason axiomatised: `pmpCheck` walks `for i in [0..sys_pmp_count) ... readReg pmpaddr_n / pmpcfg_n`
and dispatches on per-entry attributes; the loop doesn't reduce without per-entry facts about
each `pmpaddr` / `pmpcfg` register.
Discharge condition: add a `SailState.isValidPmpConfig` precondition (e.g. all `pmpcfg_n` A-fields
= OFF) and unfold the bounded loop.
Consistent because: SP1 is configured with no PMP entries enabled, so the LHS denotes a fixed
"allow" outcome regardless of how the unmodelled platform state is filled in. -/
axiom pmp_check_machine (reg_val : BitVec 64) (offset : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (width : ℕ) :
    (pmpCheck (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0)))
      width (MemoryAccessType.Store mem_payload.Data) Privilege.Machine).run s =
        EStateM.Result.ok none s

/-- Load counterpart of `pmp_check_machine`. Same justification.
Used by: `MemChecks.lean` (4 sites, byte/half/word/double widths). -/
axiom pmp_check_machine' (reg_val : BitVec 64) (offset : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (width : ℕ) :
    (pmpCheck (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0)))
      width (MemoryAccessType.Load mem_payload.Data) Privilege.Machine).run s =
        EStateM.Result.ok none s

-- /-- Store-side PMA check is a no-op under SP1's kernel configuration.
-- Used by: `MemChecks.lean` (4 sites, byte/half/word/double widths).
-- Reason axiomatised: `pmaCheck` calls `matching_pma_region (← readReg pma_regions)` and dispatches
-- on per-region attributes; nothing in `SailState.isInitialized` constrains `pma_regions`.
-- Discharge condition: add a `SailState.isValidPmaConfig` precondition (e.g. `pma_regions = []`).
-- Consistent because: SP1 has no PMA regions configured, so the LHS denotes a fixed "allow" outcome. -/
-- axiom pma_check_machine (reg_val : BitVec 64) (offset : BitVec 64)
--     (s : SailState) (hs : SailState.isInitialized s) (width : ℕ)
--     (pbmt : page_based_mem_type) (res_or_con : Bool) :
--     (pmaCheck (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0)))
--       width (MemoryAccessType.Store mem_payload.Data) pbmt res_or_con).run s =
--         EStateM.Result.ok none s

-- /-- Load counterpart of `pma_check_machine`. Same justification.
-- Used by: `MemChecks.lean` (4 sites, byte/half/word/double widths). -/
-- axiom pma_check_machine' (reg_val : BitVec 64) (offset : BitVec 64)
--     (s : SailState) (hs : SailState.isInitialized s) (width : ℕ)
--     (pbmt : page_based_mem_type) (res_or_con : Bool) :
--     (pmaCheck (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0)))
--       width (MemoryAccessType.Load mem_payload.Data) pbmt res_or_con).run s =
--         EStateM.Result.ok none s

end pmp_check
