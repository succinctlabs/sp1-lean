import SP1Clean.Foundations.SailMemory
import SP1Clean.Foundations.SailWrap
import SP1Clean.Foundations.Word
import SP1Clean.Chips.LoadX0Chip.Formal
import SP1Clean.Soundness.ChipRow

/-! # Native Sail bridge for LoadX0 (loads into x0)

`LoadX0` is the fast path for loads whose destination register is `x0`. The memory read still happens
(for side effects / fault checking), but the loaded value is **discarded** — `wX_bits (.Regidx 0#5) v`
is a no-op on register state (`run_wX_bits` with `idx = 0#5` returns the state unchanged). So the RISC-V
Sail execution of any of the seven load opcodes into `x0` agrees with the SP1 emulation `sp1_loadX0`
(write `nextPC = pc + 4`, return `RETIRE_SUCCESS`).

Unlike the regular Load bridges, this needs **no** sign/zero-extension or byte-concatenation reasoning:
the read merely has to succeed (via `run_vmem_read_of_width_N'`), after which the `extend_value` and the
`wX_bits (.Regidx 0#5)` write collapse to nothing. Four width-core lemmas (1/2/4/8 bytes, each generic in
`is_unsigned`) feed the seven per-opcode theorems `correct_loadX0_{lb,lbu,lh,lhu,lw,lwu,ld}`. -/

namespace SP1Clean.LoadX0Sail

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The SP1 chip emulation: write `nextPC = pc + 4` and return `RETIRE_SUCCESS` — the loaded word is
discarded because the destination is `x0`. -/
def sp1_loadX0 (pc : BitVec 64) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC (pc + 4#64)
  pure RETIRE_SUCCESS

/-- The RISC-V spec for a load-into-`x0`: advance `nextPC`, then execute the Sail `LOAD` at the given
width / sign mode. Each named opcode spec is an instance of this. -/
noncomputable def specX0 (is_unsigned : Bool) (width : Nat)
    (imm : BitVec 12) (rs1 rd : BitVec 5) : SailM ExecutionResult := do
  Sail.writeReg Register.nextPC ((← Sail.readReg Register.PC) + 4#64)
  execute_LOAD imm (.Regidx rs1) (.Regidx rd) is_unsigned width

/-- The seven per-opcode specs, by width and sign mode. -/
noncomputable def spec_loadX0_lb  (imm : BitVec 12) (rs1 rd : BitVec 5) := specX0 false 1 imm rs1 rd
noncomputable def spec_loadX0_lbu (imm : BitVec 12) (rs1 rd : BitVec 5) := specX0 true  1 imm rs1 rd
noncomputable def spec_loadX0_lh  (imm : BitVec 12) (rs1 rd : BitVec 5) := specX0 false 2 imm rs1 rd
noncomputable def spec_loadX0_lhu (imm : BitVec 12) (rs1 rd : BitVec 5) := specX0 true  2 imm rs1 rd
noncomputable def spec_loadX0_lw  (imm : BitVec 12) (rs1 rd : BitVec 5) := specX0 false 4 imm rs1 rd
noncomputable def spec_loadX0_lwu (imm : BitVec 12) (rs1 rd : BitVec 5) := specX0 true  4 imm rs1 rd
noncomputable def spec_loadX0_ld  (imm : BitVec 12) (rs1 rd : BitVec 5) := specX0 true  8 imm rs1 rd

/-- Shared post-`nextPC`-write state bookkeeping: `isInitialized` / `isValidMemConfig` / the `rs1`
register read all survive the `nextPC` insert (it is none of the config registers). -/
private lemma persist_nextPC (rs1_idx : BitVec 5) (reg_val pc : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val) :
    let sp : SailState := { s with regs := s.regs.insert Register.nextPC (pc + 4#64) }
    ∃ (hsp_init : SailState.isInitialized sp),
      SailState.isValidMemConfig sp hsp_init ∧ sp.get_reg? rs1_idx = some reg_val ∧ sp.mem = s.mem := by
  intro sp
  have hsp_init : SailState.isInitialized sp :=
    SailState.isInitialized_insert s hs Register.nextPC (pc + 4#64)
  refine ⟨hsp_init, ?_, ?_, rfl⟩
  · obtain ⟨hcp, hmprv, hmsec, hhtif, hpma⟩ := hconfig
    have key : ∀ (reg : Register) (h : reg ∈ s.regs) (h' : reg ∈ sp.regs),
        reg ≠ Register.nextPC → sp.regs.get reg h' = s.regs.get reg h := by
      intro reg h h' hne
      show (s.regs.insert Register.nextPC (pc + 4#64)).get reg _ = _
      rw [Std.ExtDHashMap.get_insert]; simp [Ne.symm hne]
    exact
      { h_cur_privilege := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hcp
        h_mprv_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hmprv
        h_mseccfg_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hmsec
        h_htif_disabled := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hhtif
        h_pma_regions := by rw [key _ (hs _) (hsp_init _) (by decide)]; exact hpma }
  · rw [SailState.get_reg?_insert_nextPC]; exact h_rs1

/-! ## The four width-core lemmas

Each proves the read succeeds and the `x0` write is discarded, so `specX0 _ W imm rs1 0#5` reduces to
`sp1_loadX0 pc`. Generic in `is_unsigned` (the discarded `extend_value` mode). -/

set_option maxHeartbeats 10000000 in
omit [Fact (2 ^ 17 < p)] in
theorem loadX0_w1 (is_unsigned : Bool)
    (rs1_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64) (data₀ : BitVec 8)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 1 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀) :
    (specX0 is_unsigned 1 imm rs1_idx 0#5).run s = (sp1_loadX0 pc).run s := by
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc; exact h_pc
  set sp : SailState := { s with regs := s.regs.insert Register.nextPC (pc + 4#64) } with hsp
  obtain ⟨hsp_init, hsp_config, hsp_rs1, hmem_eq⟩ := persist_nextPC rs1_idx reg_val pc s hs hconfig h_rs1
  have hadd : (reg_val + BitVec.signExtend 64 imm).toNat
      = reg_val.toNat + (BitVec.signExtend 64 imm).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have hm₀ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat]? = some data₀ := by
    rw [hmem_eq, ← hadd]; exact hmem₀
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 1 = true := by
    rw [is_aligned_vaddr_iff_mod, hadd]; exact h_aligned
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 1) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 1 (by omega) h_lo (by rw [hadd]; exact h_hi)
  have hread := run_vmem_read_of_width_1' rs1_idx reg_val (BitVec.signExtend 64 imm) data₀
    sp hsp_init hsp_rs1 h_align' hsp_config h_fits h_in_range hm₀
  simp only at hread
  rw [hsp] at hread
  simp [specX0, sp1_loadX0, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, hpc_get, hse,
    LeanRV64D.Functions.xlen_bytes, Sail.assert, PreSail.assert, hread]

set_option maxHeartbeats 10000000 in
omit [Fact (2 ^ 17 < p)] in
theorem loadX0_w2 (is_unsigned : Bool)
    (rs1_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64) (data₀ data₁ : BitVec 8)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 2 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁) :
    (specX0 is_unsigned 2 imm rs1_idx 0#5).run s = (sp1_loadX0 pc).run s := by
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc; exact h_pc
  set sp : SailState := { s with regs := s.regs.insert Register.nextPC (pc + 4#64) } with hsp
  obtain ⟨hsp_init, hsp_config, hsp_rs1, hmem_eq⟩ := persist_nextPC rs1_idx reg_val pc s hs hconfig h_rs1
  have hadd : (reg_val + BitVec.signExtend 64 imm).toNat
      = reg_val.toNat + (BitVec.signExtend 64 imm).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have hm₀ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat]? = some data₀ := by
    rw [hmem_eq, ← hadd]; exact hmem₀
  have hm₁ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1]? = some data₁ := by
    rw [hmem_eq, ← hadd]; exact hmem₁
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 2 = true := by
    rw [is_aligned_vaddr_iff_mod, hadd]; exact h_aligned
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 2) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 2 (by omega) h_lo (by rw [hadd]; exact h_hi)
  have hread := run_vmem_read_of_width_2' rs1_idx reg_val (BitVec.signExtend 64 imm) data₀ data₁
    sp hsp_init hsp_rs1 h_align' hsp_config h_fits h_in_range hm₀ hm₁
  simp only at hread
  rw [hsp] at hread
  simp [specX0, sp1_loadX0, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, hpc_get, hse,
    LeanRV64D.Functions.xlen_bytes, Sail.assert, PreSail.assert, hread]

set_option maxHeartbeats 10000000 in
omit [Fact (2 ^ 17 < p)] in
theorem loadX0_w4 (is_unsigned : Bool)
    (rs1_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64)
    (data₀ data₁ data₂ data₃ : BitVec 8)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 4 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃) :
    (specX0 is_unsigned 4 imm rs1_idx 0#5).run s = (sp1_loadX0 pc).run s := by
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc; exact h_pc
  set sp : SailState := { s with regs := s.regs.insert Register.nextPC (pc + 4#64) } with hsp
  obtain ⟨hsp_init, hsp_config, hsp_rs1, hmem_eq⟩ := persist_nextPC rs1_idx reg_val pc s hs hconfig h_rs1
  have hadd : (reg_val + BitVec.signExtend 64 imm).toNat
      = reg_val.toNat + (BitVec.signExtend 64 imm).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have hm₀ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat]? = some data₀ := by
    rw [hmem_eq, ← hadd]; exact hmem₀
  have hm₁ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1]? = some data₁ := by
    rw [hmem_eq, ← hadd]; exact hmem₁
  have hm₂ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2]? = some data₂ := by
    rw [hmem_eq, ← hadd]; exact hmem₂
  have hm₃ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 3]? = some data₃ := by
    rw [hmem_eq, ← hadd]; exact hmem₃
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 4 = true := by
    rw [is_aligned_vaddr_iff_mod, hadd]; exact h_aligned
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 4) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 4 (by omega) h_lo (by rw [hadd]; exact h_hi)
  have hread := run_vmem_read_of_width_4' rs1_idx reg_val (BitVec.signExtend 64 imm)
    data₀ data₁ data₂ data₃
    sp hsp_init hsp_rs1 h_align' hsp_config h_fits h_in_range hm₀ hm₁ hm₂ hm₃
  simp only at hread
  rw [hsp] at hread
  simp [specX0, sp1_loadX0, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, hpc_get, hse,
    LeanRV64D.Functions.xlen_bytes, Sail.assert, PreSail.assert, hread]

set_option maxHeartbeats 10000000 in
omit [Fact (2 ^ 17 < p)] in
theorem loadX0_w8 (is_unsigned : Bool)
    (rs1_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64)
    (data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ : BitVec 8)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc)
    (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 8 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃)
    (hmem₄ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 4]? = some data₄)
    (hmem₅ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 5]? = some data₅)
    (hmem₆ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 6]? = some data₆)
    (hmem₇ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 7]? = some data₇) :
    (specX0 is_unsigned 8 imm rs1_idx 0#5).run s = (sp1_loadX0 pc).run s := by
  have hse : (sign_extend imm : BitVec 64) = BitVec.signExtend 64 imm := by simp [sign_extend]
  have hpc_get : s.regs.get Register.PC (hs _) = pc := by
    rw [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at h_pc; exact h_pc
  set sp : SailState := { s with regs := s.regs.insert Register.nextPC (pc + 4#64) } with hsp
  obtain ⟨hsp_init, hsp_config, hsp_rs1, hmem_eq⟩ := persist_nextPC rs1_idx reg_val pc s hs hconfig h_rs1
  have hadd : (reg_val + BitVec.signExtend 64 imm).toNat
      = reg_val.toNat + (BitVec.signExtend 64 imm).toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt]; omega
  have hm₀ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat]? = some data₀ := by
    rw [hmem_eq, ← hadd]; exact hmem₀
  have hm₁ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1]? = some data₁ := by
    rw [hmem_eq, ← hadd]; exact hmem₁
  have hm₂ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2]? = some data₂ := by
    rw [hmem_eq, ← hadd]; exact hmem₂
  have hm₃ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 3]? = some data₃ := by
    rw [hmem_eq, ← hadd]; exact hmem₃
  have hm₄ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4]? = some data₄ := by
    rw [hmem_eq, ← hadd]; exact hmem₄
  have hm₅ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 5]? = some data₅ := by
    rw [hmem_eq, ← hadd]; exact hmem₅
  have hm₆ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 6]? = some data₆ := by
    rw [hmem_eq, ← hadd]; exact hmem₆
  have hm₇ : sp.mem[reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 7]? = some data₇ := by
    rw [hmem_eq, ← hadd]; exact hmem₇
  have h_align' : is_aligned_vaddr (virtaddr.Virtaddr (reg_val + BitVec.signExtend 64 imm)) 8 = true := by
    rw [is_aligned_vaddr_iff_mod, hadd]; exact h_aligned
  have h_in_range :
      range_subset (zero_extend (BitVec.addInt (reg_val + BitVec.signExtend 64 imm) 0))
        (to_bits 8) (2#64 ^ 16) (2#64 ^ 48 - 2#64 ^ 16) = true :=
    range_subset_sp1_pma _ 8 (by omega) h_lo (by rw [hadd]; exact h_hi)
  have hread := run_vmem_read_of_width_8' rs1_idx reg_val (BitVec.signExtend 64 imm)
    data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇
    sp hsp_init hsp_rs1 h_align' hsp_config h_fits h_in_range hm₀ hm₁ hm₂ hm₃ hm₄ hm₅ hm₆ hm₇
  simp only at hread
  rw [hsp] at hread
  simp [specX0, sp1_loadX0, run_readReg_of_isInitialized _ _ hs,
    EStateM.Result.map, execute_LOAD, hpc_get, hse,
    LeanRV64D.Functions.xlen_bytes, Sail.assert, PreSail.assert, hread]

/-! ## The seven per-opcode correctness theorems

Each `correct_loadX0_<op>` instantiates the matching width-core lemma at its sign mode; the named spec
unfolds to `specX0` definitionally. -/

omit [Fact (2 ^ 17 < p)] in
theorem correct_loadX0_lb
    (rs1_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64) (data₀ : BitVec 8)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc) (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 1 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀) :
    (spec_loadX0_lb imm rs1_idx 0#5).run s = (sp1_loadX0 pc).run s :=
  loadX0_w1 false rs1_idx imm reg_val data₀ pc s hs hconfig h_pc h_rs1 h_aligned h_fits h_hi h_lo hmem₀

omit [Fact (2 ^ 17 < p)] in
theorem correct_loadX0_lbu
    (rs1_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64) (data₀ : BitVec 8)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc) (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 1 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀) :
    (spec_loadX0_lbu imm rs1_idx 0#5).run s = (sp1_loadX0 pc).run s :=
  loadX0_w1 true rs1_idx imm reg_val data₀ pc s hs hconfig h_pc h_rs1 h_aligned h_fits h_hi h_lo hmem₀

omit [Fact (2 ^ 17 < p)] in
theorem correct_loadX0_lh
    (rs1_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64) (data₀ data₁ : BitVec 8)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc) (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 2 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁) :
    (spec_loadX0_lh imm rs1_idx 0#5).run s = (sp1_loadX0 pc).run s :=
  loadX0_w2 false rs1_idx imm reg_val data₀ data₁ pc s hs hconfig h_pc h_rs1
    h_aligned h_fits h_hi h_lo hmem₀ hmem₁

omit [Fact (2 ^ 17 < p)] in
theorem correct_loadX0_lhu
    (rs1_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64) (data₀ data₁ : BitVec 8)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc) (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 2 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁) :
    (spec_loadX0_lhu imm rs1_idx 0#5).run s = (sp1_loadX0 pc).run s :=
  loadX0_w2 true rs1_idx imm reg_val data₀ data₁ pc s hs hconfig h_pc h_rs1
    h_aligned h_fits h_hi h_lo hmem₀ hmem₁

omit [Fact (2 ^ 17 < p)] in
theorem correct_loadX0_lw
    (rs1_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc) (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 4 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃) :
    (spec_loadX0_lw imm rs1_idx 0#5).run s = (sp1_loadX0 pc).run s :=
  loadX0_w4 false rs1_idx imm reg_val data₀ data₁ data₂ data₃ pc s hs hconfig h_pc h_rs1
    h_aligned h_fits h_hi h_lo hmem₀ hmem₁ hmem₂ hmem₃

omit [Fact (2 ^ 17 < p)] in
theorem correct_loadX0_lwu
    (rs1_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64) (data₀ data₁ data₂ data₃ : BitVec 8)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc) (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 4 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃) :
    (spec_loadX0_lwu imm rs1_idx 0#5).run s = (sp1_loadX0 pc).run s :=
  loadX0_w4 true rs1_idx imm reg_val data₀ data₁ data₂ data₃ pc s hs hconfig h_pc h_rs1
    h_aligned h_fits h_hi h_lo hmem₀ hmem₁ hmem₂ hmem₃

omit [Fact (2 ^ 17 < p)] in
theorem correct_loadX0_ld
    (rs1_idx : BitVec 5) (imm : BitVec 12) (reg_val : BitVec 64)
    (data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ : BitVec 8)
    (pc : BitVec 64) (s : SailState) (hs : SailState.isInitialized s)
    (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc) (h_rs1 : s.get_reg? rs1_idx = some reg_val)
    (h_aligned : (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 8 = 0)
    (h_fits : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 < 2 ^ 64)
    (h_hi : reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 ≤ 2 ^ 48)
    (h_lo : 2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat)
    (hmem₀ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀)
    (hmem₁ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁)
    (hmem₂ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂)
    (hmem₃ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃)
    (hmem₄ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 4]? = some data₄)
    (hmem₅ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 5]? = some data₅)
    (hmem₆ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 6]? = some data₆)
    (hmem₇ : s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 7]? = some data₇) :
    (spec_loadX0_ld imm rs1_idx 0#5).run s = (sp1_loadX0 pc).run s :=
  loadX0_w8 true rs1_idx imm reg_val data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ pc s hs hconfig
    h_pc h_rs1 h_aligned h_fits h_hi h_lo hmem₀ hmem₁ hmem₂ hmem₃ hmem₄ hmem₅ hmem₆ hmem₇

/-- **End-to-end composition for LoadX0.** A selector-gated 7-way conjunction: for whichever load opcode
is active (its selector `= 1`), the matching RISC-V Sail `LOAD`-into-`x0` agrees with the SP1 emulation
`sp1_loadX0` (advance `nextPC`, discard the read). Each conjunct quantifies that opcode's own
alignment/fits/range facts and selected memory bytes, and is discharged by the matching
`correct_loadX0_<op>`. The capstone-facing wrapper for `LoadX0Chip.kind`. -/
theorem loadX0_chip_reaches_sail
    (rs1 : BitVec 5) (imm : BitVec 12) (pc reg_val : BitVec 64)
    (s : SailState) (hs : SailState.isInitialized s) (hconfig : SailState.isValidMemConfig s hs)
    (h_pc : s.regs.get? Register.PC = some pc) (h_rs1 : s.get_reg? rs1 = some reg_val) :
    (∀ (data₀ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 1 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        (spec_loadX0_lb imm rs1 0#5).run s = (sp1_loadX0 pc).run s) ∧
    (∀ (data₀ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 1 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        (spec_loadX0_lbu imm rs1 0#5).run s = (sp1_loadX0 pc).run s) ∧
    (∀ (data₀ data₁ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 2 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁ →
        (spec_loadX0_lh imm rs1 0#5).run s = (sp1_loadX0 pc).run s) ∧
    (∀ (data₀ data₁ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 2 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁ →
        (spec_loadX0_lhu imm rs1 0#5).run s = (sp1_loadX0 pc).run s) ∧
    (∀ (data₀ data₁ data₂ data₃ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 4 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃ →
        (spec_loadX0_lw imm rs1 0#5).run s = (sp1_loadX0 pc).run s) ∧
    (∀ (data₀ data₁ data₂ data₃ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 4 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃ →
        (spec_loadX0_lwu imm rs1 0#5).run s = (sp1_loadX0 pc).run s) ∧
    (∀ (data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 8 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 4]? = some data₄ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 5]? = some data₅ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 6]? = some data₆ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 7]? = some data₇ →
        (spec_loadX0_ld imm rs1 0#5).run s = (sp1_loadX0 pc).run s) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro data₀ h_al h_fits h_hi h_lo hm0
    exact correct_loadX0_lb rs1 imm reg_val data₀ pc s hs hconfig h_pc h_rs1 h_al h_fits h_hi h_lo hm0
  · intro data₀ h_al h_fits h_hi h_lo hm0
    exact correct_loadX0_lbu rs1 imm reg_val data₀ pc s hs hconfig h_pc h_rs1 h_al h_fits h_hi h_lo hm0
  · intro data₀ data₁ h_al h_fits h_hi h_lo hm0 hm1
    exact correct_loadX0_lh rs1 imm reg_val data₀ data₁ pc s hs hconfig h_pc h_rs1 h_al h_fits h_hi h_lo
      hm0 hm1
  · intro data₀ data₁ h_al h_fits h_hi h_lo hm0 hm1
    exact correct_loadX0_lhu rs1 imm reg_val data₀ data₁ pc s hs hconfig h_pc h_rs1 h_al h_fits h_hi h_lo
      hm0 hm1
  · intro data₀ data₁ data₂ data₃ h_al h_fits h_hi h_lo hm0 hm1 hm2 hm3
    exact correct_loadX0_lw rs1 imm reg_val data₀ data₁ data₂ data₃ pc s hs hconfig h_pc h_rs1 h_al
      h_fits h_hi h_lo hm0 hm1 hm2 hm3
  · intro data₀ data₁ data₂ data₃ h_al h_fits h_hi h_lo hm0 hm1 hm2 hm3
    exact correct_loadX0_lwu rs1 imm reg_val data₀ data₁ data₂ data₃ pc s hs hconfig h_pc h_rs1 h_al
      h_fits h_hi h_lo hm0 hm1 hm2 hm3
  · intro data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ h_al h_fits h_hi h_lo hm0 hm1 hm2 hm3 hm4 hm5
      hm6 hm7
    exact correct_loadX0_ld rs1 imm reg_val data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ pc s hs
      hconfig h_pc h_rs1 h_al h_fits h_hi h_lo hm0 hm1 hm2 hm3 hm4 hm5 hm6 hm7

end SP1Clean.LoadX0Sail

namespace SP1Clean.LoadX0Chip

open SP1Clean.LoadX0Sail
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.SailMem

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- **LoadX0's `ChipKind` registration** — loads whose destination is `x0` (read discarded). Straight-line
`view`, I-type adapter, gating selector `is_real` (the sum of the seven opcode flags), opcode the weighted
selector sum `opcodeVal`; the loaded word is discarded so the rd write-back is the zero word. `sailEquiv`
quantifies the PC/rs1 reads and is the input-independent 7-way per-opcode correctness conjunction (each
`spec_loadX0_<op>` reduces to `sp1_loadX0`); `reaches_sail` is `loadX0_chip_reaches_sail`. -/
def kind : Soundness.ChipKind p where
  name := "LoadX0"
  Inputs := LoadX0Chip.Inputs
  Cols := Extracted.LoadX0Columns
  view := fun inp _cols => ⟨inp.state,
    #v[inp.state.pc[0] + 4, inp.state.pc[1], inp.state.pc[2]],
    inp.adapter.toAdapterView, LoadX0Chip.isReal inp,
    #v[(0 : ZMod p), 0, 0, 0], LoadX0Chip.opcodeVal inp⟩
  chipSpec := fun inp cols data => LoadX0Chip.Spec inp cols data
  sailEquiv := fun _inp _cols s => ∀ (rs1 : BitVec 5) (imm : BitVec 12) (pc reg_val : BitVec 64),
    (hs : SailState.isInitialized s) → SailState.isValidMemConfig s hs →
    s.regs.get? Register.PC = some pc → s.get_reg? rs1 = some reg_val →
    (∀ (data₀ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 1 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        (spec_loadX0_lb imm rs1 0#5).run s = (sp1_loadX0 pc).run s) ∧
    (∀ (data₀ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 1 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 1 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        (spec_loadX0_lbu imm rs1 0#5).run s = (sp1_loadX0 pc).run s) ∧
    (∀ (data₀ data₁ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 2 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁ →
        (spec_loadX0_lh imm rs1 0#5).run s = (sp1_loadX0 pc).run s) ∧
    (∀ (data₀ data₁ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 2 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 2 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁ →
        (spec_loadX0_lhu imm rs1 0#5).run s = (sp1_loadX0 pc).run s) ∧
    (∀ (data₀ data₁ data₂ data₃ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 4 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃ →
        (spec_loadX0_lw imm rs1 0#5).run s = (sp1_loadX0 pc).run s) ∧
    (∀ (data₀ data₁ data₂ data₃ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 4 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 4 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃ →
        (spec_loadX0_lwu imm rs1 0#5).run s = (sp1_loadX0 pc).run s) ∧
    (∀ (data₀ data₁ data₂ data₃ data₄ data₅ data₆ data₇ : BitVec 8),
        (reg_val.toNat + (BitVec.signExtend 64 imm).toNat) % 8 = 0 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 < 2 ^ 64 →
        reg_val.toNat + (BitVec.signExtend 64 imm).toNat + 8 ≤ 2 ^ 48 →
        2 ^ 16 ≤ (reg_val + BitVec.signExtend 64 imm).toNat →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat]? = some data₀ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 1]? = some data₁ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 2]? = some data₂ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 3]? = some data₃ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 4]? = some data₄ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 5]? = some data₅ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 6]? = some data₆ →
        s.mem[(reg_val + BitVec.signExtend 64 imm).toNat + 7]? = some data₇ →
        (spec_loadX0_ld imm rs1 0#5).run s = (sp1_loadX0 pc).run s)
  reaches_sail := fun _inp _cols _data s _h_real _h_chip rs1 imm pc reg_val hs hconfig h_pc h_rs1 =>
    loadX0_chip_reaches_sail rs1 imm pc reg_val s hs hconfig h_pc h_rs1

end SP1Clean.LoadX0Chip
