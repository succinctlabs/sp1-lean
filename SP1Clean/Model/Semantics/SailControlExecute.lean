import SP1Clean.Model.Semantics.SailRetirement

/-! # Official Sail control-flow execute stages

Circuit-independent execute results for JAL, JALR and BTYPE. The existing chip bridges consume
these same lemmas, while semantic fixtures and frame proofs can use them without chip rows.
-/

namespace SP1Clean.Advance
open SP1Clean Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Defs LeanRV64D.Functions
open SP1Clean.Soundness.Target SP1Clean.TryStepReduction SP1Clean.SailMem

/-- **The JAL execute stage reaches `Retire_Success`.** `execute (.JAL …)` reads the staged `nextPC` (the
link `pc+4`), then `jump_to (pc + signExtend imm)` **overwrites** `nextPC` with the (4-aligned) target, then
writes the link `pc+4` to `rd`. Unlike the straight-line family, the execute *changes* `nextPC` — hence the
jump core below. -/
theorem execute_JAL_reaches (imm : BitVec 21) (rd_idx : BitVec 5) (pc : BitVec 64) (t : SailState)
    (hs : t.isInitialized)
    (hpc : t.regs.get? Register.PC = some pc)
    (hnpc : t.regs.get? Register.nextPC = some (pc + 4#64))
    (halign : (pc + sign_extend (m := 64) imm) % 4#64 = 0) :
    (execute (.JAL (imm, .Regidx rd_idx))).run t
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then
            {t with regs := t.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)}
          else
            {t with regs := ((t.regs.insert Register.nextPC (pc + sign_extend (m := 64) imm)).insert
              (reg_idx_to_Register rd_idx) (bitVecToRegidxVal rd_idx (pc + 4#64)))}) := by
  have hget_npc : t.regs.get Register.nextPC (hs _) = pc + 4#64 := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at hnpc; exact hnpc
  have hget_pc : t.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at hpc; exact hpc
  simp only [execute, execute_JAL, get_next_pc]
  rw [run_readReg_bind_of_isInitialized t Register.nextPC hs, hget_npc]
  rw [run_readReg_bind_of_isInitialized t Register.PC hs, hget_pc]
  rw [run_bind_of_run' t _ (jump_to (pc + sign_extend (m := 64) imm))
    (ExecutionResult.Retire_Success ()) (jump_to_of_mod4_eq_zero _ t hs halign)]
  simp only [run_bind_of_run' _ _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  split <;> simp_all

/-- **The JALR execute stage reaches `Retire_Success`.** Like `execute_JAL_reaches` but JALR (a) has an
`update_elp_state rs1` prefix (a no-op under `isValidMemConfig`), (b) reads `rs1` (not the pc), and (c)
jumps to the **LSB-cleared** target `(rs1_val + signExtend imm) &&& ~~~1` (`BitVec.update … 0 0#1`). -/
theorem execute_JALR_reaches (imm : BitVec 12) (rs1_idx rd_idx : BitVec 5) (pc rs1_val : BitVec 64)
    (t : SailState) (hs : t.isInitialized) (hconfig : SailState.isValidMemConfig t hs)
    (hnpc : t.regs.get? Register.nextPC = some (pc + 4#64))
    (h_rs1 : SailState.get_reg? t rs1_idx = some rs1_val)
    (halign : (BitVec.update (rs1_val + sign_extend (m := 64) imm) 0 0#1) % 4#64 = 0) :
    (execute (.JALR (imm, .Regidx rs1_idx, .Regidx rd_idx))).run t
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then
            {t with regs := (t.regs.insert Register.nextPC
              (BitVec.update (rs1_val + sign_extend (m := 64) imm) 0 0#1))}
          else
            {t with regs := ((t.regs.insert Register.nextPC
              (BitVec.update (rs1_val + sign_extend (m := 64) imm) 0 0#1)).insert
              (reg_idx_to_Register rd_idx) (bitVecToRegidxVal rd_idx (pc + 4#64)))}) := by
  have hget_npc : t.regs.get Register.nextPC (hs _) = pc + 4#64 := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at hnpc; exact hnpc
  have hupd : (update_elp_state (.Regidx rs1_idx)).run t = .ok () t :=
    update_elp_state_of_isInitialized _ t hs hconfig
  simp only [execute, execute_JALR, get_next_pc_eq]
  rw [run_bind_of_run' t _ _ () hupd]
  rw [run_readReg_bind_of_isInitialized t Register.nextPC hs, hget_npc]
  rw [run_bind_of_run t _ rs1_val (by rw [run_rX_bits, h_rs1])]
  simp only [pure_bind]
  rw [run_bind_of_run' t _ _ (ExecutionResult.Retire_Success ())
    (jump_to_of_mod4_eq_zero _ t hs halign)]
  simp only [run_bind_of_run' _ _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  split <;> simp_all

/-- The Sail-computed branch-taken predicate for a `bop`, keyed exactly on `execute_BTYPE`'s inner
`match op` (BEQ/BNE via `==`/`!=`, the four ordering forms via the Sail `zopz0z*` comparison fns).
The BranchChip adapter connects this predicate to its semantic branch condition. -/
def btypeTaken (op : bop) (x y : BitVec 64) : Bool :=
  match op with
  | .BEQ => x == y
  | .BNE => x != y
  | .BLT => zopz0zI_s x y
  | .BGE => zopz0zKzJ_s x y
  | .BLTU => zopz0zI_u x y
  | .BGEU => zopz0zKzJ_u x y

/-- **The BTYPE execute stage reaches `Retire_Success`.** On a state `t` whose `rs1`/`rs2` reads and
staged `nextPC = pc + 4` are known, `execute (.BTYPE …)` runs to `Retire_Success` committing
`nextPC := target` (only): the **taken** arm's `jump_to` overwrites `nextPC ← target = pc + signExtend imm`
(4-aligned via `jump_to_of_mod4_eq_zero`); the **not-taken** arm leaves the staged `pc+4` untouched, so the
result equals `{t with regs.insert nextPC target}` (target = pc+4) by the idempotent re-insert of the already
staged `nextPC`. The `hexec` the control-flow core (`advance_of_ctrl`) needs — the branch twin of the
straight-line `*_execute_reaches`, but the execute *changes* `nextPC` (no `rd` write). -/
theorem execute_BTYPE_reaches (imm : BitVec 13) (rs1_idx rs2_idx : BitVec 5) (op : bop)
    (pc target rs1_val rs2_val : BitVec 64) (t : SailState) (hs : t.isInitialized)
    (hpc : t.regs.get? Register.PC = some pc)
    (hnpc : t.regs.get? Register.nextPC = some (pc + 4#64))
    (h_rs1 : SailState.get_reg? t rs1_idx = some rs1_val)
    (h_rs2 : SailState.get_reg? t rs2_idx = some rs2_val)
    (h_taken : btypeTaken op rs1_val rs2_val = true → target = pc + sign_extend (m := 64) imm)
    (h_not_taken : btypeTaken op rs1_val rs2_val = false → target = pc + 4#64)
    (h_align : target.toNat % 4 = 0) :
    (execute (.BTYPE (imm, .Regidx rs2_idx, .Regidx rs1_idx, op))).run t
      = .ok (ExecutionResult.Retire_Success ())
          {t with regs := t.regs.insert Register.nextPC target} := by
  have hpc_get : t.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at hpc; exact hpc
  by_cases hc : btypeTaken op rs1_val rs2_val = true
  · have hnpc_t := h_taken hc
    have htgt4 : (pc + sign_extend (m := 64) imm) % 4#64 = 0 := by
      rw [← hnpc_t]; apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_umod]; simpa using h_align
    have hjump := jump_to_of_mod4_eq_zero (pc + sign_extend (m := 64) imm) t hs htgt4
    cases op <;> simp only [btypeTaken, beq_iff_eq, bne_iff_ne] at hc <;>
      simp [execute, execute_BTYPE, run_rX_bits, h_rs1, h_rs2,
        Sail.run_readReg_bind_of_isInitialized _ _ hs, hpc_get, RETIRE_SUCCESS, hjump, hnpc_t, hc]
  · simp only [Bool.not_eq_true] at hc
    have hnt := h_not_taken hc
    have hgtnpc : t.regs.get? Register.nextPC = some target := by rw [hnpc, hnt]
    have hidem : t.regs.insert Register.nextPC target = t.regs := by
      apply Std.ExtDHashMap.ext_get?; intro k; rw [Std.ExtDHashMap.get?_insert]
      split
      · rename_i hk; simp only [beq_iff_eq] at hk; subst hk; rw [hgtnpc]; rfl
      · rfl
    cases op <;> simp only [btypeTaken, beq_eq_false_iff_ne, bne_eq_false_iff_eq] at hc <;>
      simp [execute, execute_BTYPE, run_rX_bits, h_rs1, h_rs2, RETIRE_SUCCESS, hc, hidem]

end SP1Clean.Advance
