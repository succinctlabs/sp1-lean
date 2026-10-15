import SP1Clean.Model.Semantics.SailRetirement
import SP1Clean.Model.SailPure

/-! # Official Sail arithmetic execute stages

These circuit-independent reductions describe the actual register update of each arithmetic
family, including x0. The instruction bridges and semantic frame laws share these declarations.
-/

open LeanRV64D.Defs
namespace SP1Clean.Advance
open SP1Clean Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target SP1Clean.TryStepReduction SP1Clean.SailMem

/-- **The RTYPE execute stage reaches `Retire_Success`.** `execute (.RTYPE …)` on a state whose `rs1`/`rs2`
register reads are known runs to `Retire_Success` and writes only `rd` (via `wX_bits`, x0-uniform). This is
the `hexec` the ladder needs, for the whole R-type family (Add/Sub/Bitwise/Lt/Shift/… — one `op`). The
committed write value is `execute_RTYPE_pure op_b op_c op`; a chip's semantic `Spec` ties that to `rdWrite`. -/
theorem rtype_execute_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (op : rop)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b)
    (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.RTYPE (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_RTYPE_pure op_b op_c op)))}) := by
  simp only [execute, execute_RTYPE_eq_execute_RTYPE', execute_RTYPE']
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- **The RTYPEW execute stage reaches `Retire_Success`**, generic over the 32-bit W-op. `execute (.RTYPEW …)`
on a state whose `rs1`/`rs2` reads are known runs to `Retire_Success` writing only `rd` with
`execute_RTYPEW_pure op_b op_c op` (the low-32 result sign-extended to 64). The `hexec` the shared core needs
for the W-op family (Addw/Subw + SLLW/SRLW/SRAW); structurally the RTYPE twin (`execute_RTYPEW'` = two reads +
one write), so the proof is identical modulo `RTYPEW`. -/
theorem rtypew_execute_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (op : ropw)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b)
    (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.RTYPEW (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_RTYPEW_pure op_b op_c op)))}) := by
  simp only [execute, execute_RTYPEW_eq_execute_RTYPEW', execute_RTYPEW']
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- **`execute_ITYPE` pure part** — the I-type twin of `execute_RTYPE_pure` (op1 = the `rs1` read, `immext`
= the sign-extended immediate). Covers the ALU immediate ops ADDI/SLTI/SLTIU/ANDI/ORI/XORI, so one
`itype_execute_reaches` serves the whole immediate-ALU family (Addi + the immediate forms of Bitwise/Lt). -/
def execute_ITYPE_pure (op1 immext : BitVec 64) (op : iop) : BitVec 64 :=
  match op with
  | .ADDI => op1 + immext
  | .SLTI => zero_extend (m := 64) (bool_to_bit (zopz0zI_s op1 immext))
  | .SLTIU => zero_extend (m := 64) (bool_to_bit (zopz0zI_u op1 immext))
  | .ANDI => op1 &&& immext
  | .ORI => op1 ||| immext
  | .XORI => op1 ^^^ immext

/-- `execute_ITYPE` with the isolated pure part (the I-type twin of `execute_RTYPE'`). -/
def execute_ITYPE' (imm : BitVec 12) (rs1 rd : regidx) (op : iop) : SailM ExecutionResult := do
  let rs1_bits ← rX_bits rs1
  wX_bits rd (execute_ITYPE_pure rs1_bits (sign_extend (m := 64) imm) op)
  pure RETIRE_SUCCESS

@[simp] theorem execute_ITYPE_eq_execute_ITYPE' (imm : BitVec 12) (rs1 rd : regidx) (op : iop) :
    execute_ITYPE imm rs1 rd op = execute_ITYPE' imm rs1 rd op := by
  cases op <;> simp_all [execute_ITYPE', execute_ITYPE, execute_ITYPE_pure]

/-- **The ITYPE execute stage reaches `Retire_Success`**, generic over the ALU immediate op. `execute
(.ITYPE …)` on a state whose `rs1` read is known runs to `Retire_Success` writing only `rd` with
`execute_ITYPE_pure op_b (signExtend imm) op` — the I-type `hexec` the shared core needs (one read + the
immediate, no `rs2`). Serves the whole immediate-ALU family via `op`. -/
theorem itype_execute_reaches (imm : BitVec 12) (rs1_idx rd_idx : BitVec 5) (op : iop)
    (op_b : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) :
    (execute (.ITYPE (imm, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_ITYPE_pure op_b (sign_extend (m := 64) imm) op)))}) := by
  simp only [execute, execute_ITYPE_eq_execute_ITYPE', execute_ITYPE']
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The pure value written by a 64-bit shift-immediate instruction.  The shift amount is genuinely
six bits in RV64; keeping that width here covers shifts 32--63 rather than routing through the
older five-bit convenience lemmas. -/
def execute_SHIFTIOP_pure (op_b : BitVec 64) (shamt : BitVec 6) (op : sop) : BitVec 64 :=
  match op with
  | .SLLI => shift_bits_left op_b shamt
  | .SRLI => shift_bits_right op_b shamt
  | .SRAI => shift_bits_right_arith op_b shamt

/-- `execute_SHIFTIOP` with its register read separated from the pure shift. -/
def execute_SHIFTIOP' (shamt : BitVec 6) (rs1 rd : regidx) (op : sop) : SailM ExecutionResult := do
  let op_b ← rX_bits rs1
  wX_bits rd (execute_SHIFTIOP_pure op_b shamt op)
  pure RETIRE_SUCCESS

@[simp] theorem execute_SHIFTIOP_eq_execute_SHIFTIOP'
    (shamt : BitVec 6) (rs1 rd : regidx) (op : sop) :
    execute_SHIFTIOP shamt rs1 rd op = execute_SHIFTIOP' shamt rs1 rd op := by
  have hshamt : Sail.BitVec.extractLsb shamt 5 0 = shamt := by
    apply BitVec.eq_of_toNat_eq
    simp only [Sail.BitVec.extractLsb, BitVec.extractLsb_toNat, Nat.shiftRight_zero]
    rw [Nat.mod_eq_of_lt]
    exact shamt.isLt
  cases op <;>
    simp [execute_SHIFTIOP, execute_SHIFTIOP', execute_SHIFTIOP_pure,
      LeanRV64D.Functions.log2_xlen, hshamt]

/-- The 64-bit shift-immediate execute stage reaches `Retire_Success`, reading only `rs1` and
writing the result of the official six-bit shift operation to `rd`. -/
theorem shiftitype_execute_reaches (shamt : BitVec 6) (rs1_idx rd_idx : BitVec 5) (op : sop)
    (op_b : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) :
    (execute (.SHIFTIOP (shamt, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_SHIFTIOP_pure op_b shamt op)))}) := by
  simp only [execute, execute_SHIFTIOP_eq_execute_SHIFTIOP', execute_SHIFTIOP']
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The pure value written by a word shift-immediate instruction. -/
def execute_SHIFTIWOP_pure (op_b : BitVec 64) (shamt : BitVec 5) (op : sopw) : BitVec 64 :=
  let op_b32 := Sail.BitVec.extractLsb op_b 31 0
  let result : BitVec 32 :=
    match op with
    | .SLLIW => shift_bits_left op_b32 shamt
    | .SRLIW => shift_bits_right op_b32 shamt
    | .SRAIW => shift_bits_right_arith op_b32 shamt
  sign_extend (m := 64) result

/-- `execute_SHIFTIWOP` with its register read separated from the pure word shift. -/
def execute_SHIFTIWOP' (shamt : BitVec 5) (rs1 rd : regidx) (op : sopw) : SailM ExecutionResult := do
  let op_b ← rX_bits rs1
  wX_bits rd (execute_SHIFTIWOP_pure op_b shamt op)
  pure RETIRE_SUCCESS

@[simp] theorem execute_SHIFTIWOP_eq_execute_SHIFTIWOP'
    (shamt : BitVec 5) (rs1 rd : regidx) (op : sopw) :
    execute_SHIFTIWOP shamt rs1 rd op = execute_SHIFTIWOP' shamt rs1 rd op := by
  cases op <;> rfl

/-- The word shift-immediate execute stage reaches `Retire_Success`, reading only `rs1`. -/
theorem shiftiwtype_execute_reaches (shamt : BitVec 5) (rs1_idx rd_idx : BitVec 5) (op : sopw)
    (op_b : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) :
    (execute (.SHIFTIWOP (shamt, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_SHIFTIWOP_pure op_b shamt op)))}) := by
  simp only [execute, execute_SHIFTIWOP_eq_execute_SHIFTIWOP', execute_SHIFTIWOP']
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- **`execute_ADDIW` pure part** — `signExtend 64 (extractLsb (op_b + immext) 31 0)` (the low-32 sum
sign-extended). ADDIW is its own Sail AST arm (`execute_ADDIW`), not `execute_ITYPE .ADDI`, so it gets its
own pure part / reaches (the `execute_RTYPEW_pure`-analogue for the immediate-W form). -/
def execute_ADDIW_pure (op_b immext : BitVec 64) : BitVec 64 :=
  sign_extend (m := 64) (Sail.BitVec.extractLsb (op_b + immext) 31 0)

/-- **The ADDIW execute stage reaches `Retire_Success`.** `execute (.ADDIW …)` on a state whose `rs1` read is
known runs to `Retire_Success` writing only `rd` with `execute_ADDIW_pure op_b (signExtend imm)`. The
immediate-W `hexec` the shared core needs (one read + the immediate; the `let y ← pure …` intermediate folds
via `pure_bind`). -/
theorem execute_ADDIW_reaches (imm : BitVec 12) (rs1_idx rd_idx : BitVec 5)
    (op_b : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) :
    (execute (.ADDIW (imm, .Regidx rs1_idx, .Regidx rd_idx))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_ADDIW_pure op_b (sign_extend (m := 64) imm))))}) := by
  simp only [execute, execute_ADDIW, execute_ADDIW_pure, pure_bind]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- **`execute_UTYPE` pure part** — LUI writes `signExtend (imm ++ 0¹²)` (the immediate `<< 12`); AUIPC writes
`pc + signExtend (imm ++ 0¹²)` (pc-relative). The only `execute` value in the straight-line family that
*depends on the pc* — hence the pc-frame in `advance_write_core`'s `hexec`. -/
def execute_UTYPE_pure (op : uop) (pc : BitVec 64) (imm : BitVec 20) : BitVec 64 :=
  match op with
  | .LUI => sign_extend (m := 64) (imm +++ 0#12)
  | .AUIPC => pc + sign_extend (m := 64) (imm +++ 0#12)

/-- **The UTYPE execute stage reaches `Retire_Success`.** `execute (.UTYPE …)` on a state `t` whose pc is
`pc` runs to `Retire_Success` writing only `rd` with `execute_UTYPE_pure op pc imm` — no register reads, but
AUIPC reads the pc (`get_arch_pc = readReg PC`), threaded via `hpct`. -/
theorem execute_UTYPE_reaches (imm : BitVec 20) (rd_idx : BitVec 5) (op : uop) (pc : BitVec 64)
    (t : SailState) (hpct : t.regs.get? Register.PC = some pc) :
    (execute (.UTYPE (imm, .Regidx rd_idx, op))).run t
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then t
           else {t with regs := (t.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (execute_UTYPE_pure op pc imm)))}) := by
  have harchpc : (get_arch_pc ()).run t = .ok pc t := by
    simp [get_arch_pc, PreSail.readReg, hpct]
  cases op
  · simp only [execute, execute_UTYPE, execute_UTYPE_pure, pure_bind]
    rw [run_bind_of_run' t _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]; rfl
  · simp only [execute, execute_UTYPE, execute_UTYPE_pure]
    rw [run_bind_of_run t _ pc harchpc, pure_bind,
      run_bind_of_run' t _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]; rfl


/-- The DIV/DIVU execute stage reaches `Retire_Success` (write value `SailRV64.div op_c op_b isU`).
The div-by-zero/overflow special cases are fully inside `SailRV64.div`; `div_eq` reduces
`execute_DIV` to `SailRV64.skeleton_binary` by `rfl`, so this mirrors `rtype_execute_reaches` exactly. -/
theorem execute_DIV_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (isU : Bool)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.DIV (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, isU))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (SailRV64.div op_c op_b isU)))}) := by
  simp only [execute, SailRV64.execute_DIV_eq, SailRV64.skeleton_binary]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The REM/REMU execute stage reaches `Retire_Success` (write value `SailRV64.rem isU op_c op_b`).
`execute_REM` has only bool-specialized named lemmas, so the reduction to `SailRV64.skeleton_binary` is an
inline `show … from rfl` (holds for a variable `isU` — the body threads `is_unsigned` as a value). -/
theorem execute_REM_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (isU : Bool)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.REM (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, isU))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (SailRV64.rem isU op_c op_b)))}) := by
  simp only [execute, show execute_REM (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx) isU
    = SailRV64.skeleton_binary (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)
        (fun val1 val2 => SailRV64.rem isU val2 val1) from rfl, SailRV64.skeleton_binary]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The DIVW/DIVUW execute stage reaches `Retire_Success` (write value `SailRV64.divw op_c op_b isU`). -/
theorem execute_DIVW_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (isU : Bool)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.DIVW (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, isU))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (SailRV64.divw op_c op_b isU)))}) := by
  simp only [execute, SailRV64.execute_DIVW_eq, SailRV64.skeleton_binary]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The REMW/REMUW execute stage reaches `Retire_Success` (write value `SailRV64.remw isU op_c op_b`). -/
theorem execute_REMW_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (isU : Bool)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.REMW (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, isU))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (SailRV64.remw isU op_c op_b)))}) := by
  simp only [execute, show execute_REMW (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx) isU
    = SailRV64.skeleton_binary (.Regidx rs2_idx) (.Regidx rs1_idx) (.Regidx rd_idx)
        (fun val1 val2 => SailRV64.remw isU val2 val1) from rfl, SailRV64.skeleton_binary]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The MUL/MULH/MULHU/MULHSU execute stage reaches `Retire_Success` (write value
`SailRV64.mul op_c op_b op`).  Generic in `op : mul_op`; mirrors `execute_DIV_reaches`
via `SailRV64.execute_MUL_eq`/`SailRV64.skeleton_binary`. -/
theorem execute_MUL_reaches (rs2_idx rs1_idx rd_idx : BitVec 5) (op : mul_op)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.MUL (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx, op))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (SailRV64.mul op_c op_b op)))}) := by
  simp only [execute, SailRV64.execute_MUL_eq, SailRV64.skeleton_binary]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl

/-- The MULW execute stage reaches `Retire_Success` (write value `SailRV64.mulw op_c op_b`).
Mirrors `execute_DIVW_reaches` via `SailRV64.execute_MULW_eq`/`SailRV64.skeleton_binary`. -/
theorem execute_MULW_reaches (rs2_idx rs1_idx rd_idx : BitVec 5)
    (op_b op_c : BitVec 64) (s_a : SailState)
    (h_rs1 : s_a.get_reg? rs1_idx = some op_b) (h_rs2 : s_a.get_reg? rs2_idx = some op_c) :
    (execute (.MULW (.Regidx rs2_idx, .Regidx rs1_idx, .Regidx rd_idx))).run s_a
      = .ok (ExecutionResult.Retire_Success ())
          (if rd_idx = 0#5 then s_a
           else {s_a with regs := (s_a.regs.insert (reg_idx_to_Register rd_idx)
             (bitVecToRegidxVal rd_idx (SailRV64.mulw op_c op_b)))}) := by
  simp only [execute, SailRV64.execute_MULW_eq, SailRV64.skeleton_binary]
  rw [run_bind_of_run s_a _ op_b (by rw [run_rX_bits, h_rs1]),
    run_bind_of_run s_a _ op_c (by rw [run_rX_bits, h_rs2]),
    run_bind_of_run' s_a _ _ () (run_wX_bits (regidx.Regidx rd_idx) _)]
  rfl
end SP1Clean.Advance
