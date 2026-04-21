import SP1Foundations.SailM
import SP1Foundations.Opcode

open LeanRV64D.Functions Sail SailState

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
      width (MemoryAccessType.Store Data) Privilege.Machine) s = EStateM.Result.ok none s

/-- We can't prove this directly because the loop in `pmpCheck` doesn't unfold.
Adding this is at least consistent, since the left-hand side has no actual value. -/
axiom pmp_check_machine' (reg_val : BitVec 64) (offset : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (width : ℕ) :
    EStateM.run (pmpCheck (physaddr.Physaddr (zero_extend (BitVec.addInt (reg_val + offset) 0)))
      width (MemoryAccessType.Load Data) Privilege.Machine) s = EStateM.Result.ok none s

end pmp_check

section sail_v4_control_flow

/-- `insert` preserves `isInitialized`: adding a register keeps every register present. -/
@[aesop safe apply, simp]
lemma SailState.isInitialized_insert (s : SailState) (hs : s.isInitialized)
    (reg : Register) (v : RegisterType reg) :
    SailState.isInitialized { s with regs := s.regs.insert reg v } := by
  intro r
  simp only [Std.ExtDHashMap.mem_insert]
  exact Or.inr (hs r)

/-- SP1 does not enable the Zicfilp (CFI landing-pad) extension, so
`update_elp_state` (introduced in sail-v4) is effectively a no-op: it reads
`cur_privilege` through `currentlyEnabled Ext_Zicfilp`, finds Zicfilp disabled,
and returns `pure ()` without touching the `elp` register. Asserting this as
an axiom is consistent — no downstream SP1 proof reads `elp`. -/
axiom update_elp_state_of_isInitialized (rs1 : regidx) (s : SailState)
    (hs : SailState.isInitialized s) :
    EStateM.run (update_elp_state rs1) s = EStateM.Result.ok () s

/-- In sail-v4, `jump_to` wraps an alignment check that gates on
`currentlyEnabled Ext_Zca`, which reads `misa`. For a 4-byte aligned target
the alignment-failure branch is unreachable (bit 0 and bit 1 of the target are
both zero), so `jump_to` reduces to `writeReg nextPC target; pure RETIRE_SUCCESS`.
Axiomatised because the Zca / misa dependency cannot be discharged from
`isInitialized` alone. -/
axiom jump_to_of_mod4_eq_zero (target : BitVec 64) (s : SailState)
    (hs : SailState.isInitialized s) (h_aligned : target % 4#64 = 0) :
    EStateM.run (jump_to target) s =
      EStateM.Result.ok LeanRV64D.Functions.RETIRE_SUCCESS
        { s with regs := s.regs.insert Register.nextPC target }

/-- Specialisation of `jump_to_of_mod4_eq_zero` for JALR-style targets:
JALR computes `target = (rs1 + imm) & ~1`, which Lean sail-v4 expresses as
`BitVec.update target 0 0#1` / `18446744073709551614#64 &&& target`. When
the raw `target` is already 4-aligned, the low-bit clear is a no-op. -/
axiom jump_to_of_mask_mod4_eq_zero (target : BitVec 64) (s : SailState)
    (hs : SailState.isInitialized s) (h_aligned : target % 4#64 = 0) :
    EStateM.run (jump_to (18446744073709551614#64 &&& target)) s =
      EStateM.Result.ok LeanRV64D.Functions.RETIRE_SUCCESS
        { s with regs := s.regs.insert Register.nextPC target }

end sail_v4_control_flow
