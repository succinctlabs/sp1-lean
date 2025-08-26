import SP1Foundations.BitVec
import SP1Foundations.Misc
import SP1Foundations.Register
import SP1Foundations.Word

open LeanRV64IM.Functions

set_option maxHeartbeats 10000000

attribute [local simp]
  regidxToRegister_inj
  nextPC_ne_reg_idx_toRegister
  PC_ne_reg_idx_toRegister
  Sail.readReg
  PreSail.readReg
  Std.ExtDHashMap.get?_insert
  Std.ExtDHashMap.get?_insert_self

attribute [local grind =]
  nextPC_ne_reg_idx_toRegister
  PC_ne_reg_idx_toRegister
  EStateM.run_pure
  EStateM.run_throw
  EStateM.run_modify

grind_pattern Std.ExtDHashMap.get?_insert_self => (m.insert k v).get? k
grind_pattern BitVec.ofNat_eq_ofNat => (@OfNat.ofNat.{0} (BitVec n) i (@BitVec.instOfNat n i))

section sailboats

namespace Option

/-- Version of `Option.getM` using `throw` instead of `failure`-/
def toSailM {α} (x : Option α) : SailM α :=
  Option.elim x (throw Sail.Error.Unreachable) pure

@[simp] lemma toSailM_none : toSailM (α := α) none = throw Sail.Error.Unreachable := rfl

@[simp] lemma toSailM_some (x : α) : toSailM (some x) = pure x := rfl

@[simp] lemma toSailM_map (f : α → β) (x : Option α) :
    (Option.map f x).toSailM = f <$> x.toSailM := match x with | none => rfl | some _ => rfl

end Option

namespace SailState

section get_reg?

/-- Read the value in the register corresponding to `idx`, giving an actual `BitVec 64`.
This avoids the issue of some (unused by us) registers having other length vectors. -/
@[grind] def get_reg? (s : SailState) (idx : BitVec 5) : Option (BitVec 64) :=
  if idx = 0 then some 0 else reg_idx_must_64 idx ▸ s.regs.get? (reg_idx_to_Register idx)

@[simp]
lemma get_reg?_insert_of_ne
  (h : reg ≠ reg_idx_to_Register idx) :
  SailState.get_reg? { s with regs := s.regs.insert reg v } idx =
  SailState.get_reg? s idx := by grind

@[simp]
lemma get_reg?_insert_self
  {s : SailState}
  (v : RegisterType (reg_idx_to_Register idx)) :
  let reg := reg_idx_to_Register idx
  SailState.get_reg? {s with regs := s.regs.insert reg v} idx =
  if idx = 0 then some 0 else reg_idx_must_64 idx ▸ some v := by grind

@[simp]
lemma get_reg?_insert_nextPC :
  SailState.get_reg? {s with regs := s.regs.insert Register.nextPC v} idx =
  SailState.get_reg? s idx := by aesop

@[simp]
lemma get_reg?_insert_PC :
  SailState.get_reg? {s with regs := s.regs.insert Register.PC v} idx =
  SailState.get_reg? s idx := by aesop

end get_reg?

end SailState

namespace Sail

@[simp low]
lemma run_dite (p : Prop) [Decidable p] (mx : p → SailM α) (mx' : ¬ p → SailM α) :
  (if h : p then mx h else mx' h).run = if h : p then (mx h).run else (mx' h).run :=
    apply_dite EStateM.run p mx mx'

@[simp low]
lemma run_ite (p : Prop) [Decidable p] (mx mx' : SailM α) :
  (if p then mx else mx').run = if p then mx.run else mx'.run :=
    apply_ite EStateM.run p mx mx'

section write_reg

/-- Alternative to `write_reg` that takes a `BitVec` rather than an explicit `Register`. -/
def write_reg (idx : BitVec 5) (val : BitVec 64) : SailM Unit := do
  let reg : Register := reg_idx_to_Register idx
  if idx != 0 then modify fun s =>
    { s with regs := s.regs.insert reg (reg_idx_must_64 idx ▸ val) }
  else if val ≠ 0 then throw Sail.Error.Unreachable

@[simp, grind =]
lemma run_write_reg :
    (write_reg idx val).run s =
      let reg : Register := reg_idx_to_Register idx
      if idx = 0 then if val = 0 then .ok () s else .error Sail.Error.Unreachable s
        else .ok () { s with regs := s.regs.insert reg (reg_idx_must_64 idx ▸ val) }
  := by unfold write_reg; aesop

@[simp]
lemma write_reg_write_reg_self :
    (do write_reg idx val; write_reg idx val') =
      if idx = 0 ∧ val ≠ 0 then throw .Unreachable else write_reg idx val'
:= by aesop

/-- Swap writes to two distinct registers, assuming only `0#5` written to the `0` register. -/
@[simp]
lemma write_reg_write_reg_comm
  (h : idx ≠ idx') (hval : idx = 0 → val = 0) (hval' : idx' = 0 → val' = 0) :
  (do write_reg idx val; write_reg idx' val') =
    (do write_reg idx' val'; write_reg idx val)
  := by aesop (add unsafe (by simp (disch := aesop)))

end write_reg

section write_reg'

/-- Version of `write_reg` that doesn't throw an error writing to the `0` register.
This matches more closely with the behavior of `wX_bits` -/
def write_reg' (idx : BitVec 5) (val : BitVec 64) : SailM Unit :=
  do if idx != 0 then modify fun s =>
    { s with regs := s.regs.insert (reg_idx_to_Register idx) (reg_idx_must_64 idx ▸ val) }

@[simp]
lemma run_write_reg' :
  (write_reg' idx val).run s =
    let reg : Register := reg_idx_to_Register idx
    .ok () (if idx = 0 then s
      else { s with regs := s.regs.insert reg (reg_idx_must_64 idx ▸ val) })
  := by unfold write_reg'; aesop

/-- `write_reg` and `write_reg'` align if not the `0` index of the value written is `0`. -/
@[simp]
lemma write_reg_eq_write_reg' (h : idx ≠ 0 ∨ val = 0) :
  write_reg idx val = write_reg' idx val := by unfold write_reg write_reg'; aesop

@[simp]
lemma write_reg'_write_reg'_self :
  (do write_reg' idx val; write_reg' idx val') = write_reg' idx val' := by aesop

/-- Swap writes to two distinct registers. -/
@[simp]
lemma write_reg'_write_reg'_comm (h : idx ≠ idx') :
  (do write_reg' idx val; write_reg' idx' val') =
    (do write_reg' idx' val'; write_reg' idx val)
  := by aesop (add unsafe (by simp (disch := aesop)))

end write_reg'

section writeReg

@[simp]
lemma run_writeReg :
  (Sail.writeReg reg v).run s =
    .ok PUnit.unit { s with regs := s.regs.insert reg v} := rfl

@[simp]
lemma run_writeReg_bind (mx : Unit → SailM α) :
  (Sail.writeReg reg v >>= mx).run s =
    (mx ()).run {s with regs := s.regs.insert reg v} := by aesop

@[simp]
lemma writeReg_writeReg_self :
  (do Sail.writeReg reg v; Sail.writeReg reg v') = Sail.writeReg reg v' := by aesop

/-- Swap writes to two different registers. -/
@[simp]
lemma writeReg_writeReg_comm (h : reg ≠ reg') :
  (do Sail.writeReg reg v; Sail.writeReg reg' v') =
    (do Sail.writeReg reg' v'; Sail.writeReg reg v)
  := by aesop (add unsafe (by simp (disch := aesop)))

end writeReg

section readReg

-- dt: why does simp not choose to apply this when it can?
@[simp]
lemma run_readReg (s : SailState) (reg : Register) :
  (Sail.readReg reg).run s = match s.regs.get? reg with
  | some v => .ok v s
  | none => .error Sail.Error.Unreachable s := by aesop

@[simp]
lemma run_readReg_insert_of_ne (s : SailState) (h : reg ≠ reg') :
  (Sail.readReg reg').run { s with regs := s.regs.insert reg v} =
    match s.regs.get? reg' with
    | some w => .ok w { s with regs := s.regs.insert reg v }
    | none => .error .Unreachable { s with regs := s.regs.insert reg v } := by aesop

@[simp]
lemma run_readReg_insert_self (s : SailState) :
  (Sail.readReg reg).run { s with regs := s.regs.insert reg v } =
    .ok v { s with regs := s.regs.insert reg v } := by aesop

@[simp]
lemma map_const_run_readReg
  (h : (s.regs.get? reg).isSome) :
  ((Sail.readReg reg).run s).map (fun _ => x) = .ok x s
    := by
  rw [Option.isSome_iff_exists] at h
  aesop

end readReg

section rX_bits

lemma rX_bits_eq_get_reg? {s : SailState} :
  (rX_bits (regidx.Regidx idx)).run s = (s.get_reg? idx).toSailM.run s := by
  fin_cases idx
  · aesop

  all_goals
    simp [Option.toSailM, SailState.get_reg?] at *
    simp [Option.elim, reg_idx_to_Register]
    simp [rX_bits, rX]
    aesop

@[simp high]
lemma run_rX_bits :
  (rX_bits (.Regidx idx)).run s =
  match SailState.get_reg? s idx with
  | some v => .ok v s
  | none => .error Sail.Error.Unreachable s
    := by
  rw [rX_bits_eq_get_reg?]; aesop

end rX_bits

section wX_bits

lemma wX_bits_eq_write_reg' (idx : BitVec 5) (val : BitVec 64) :
    wX_bits (.Regidx idx) val = write_reg' idx val := by
    symm
    simp [write_reg', wX_bits]
    by_cases x_is_31 : idx = 31#5
    · rw [x_is_31]
      simp
      simp [wX, Sail.writeReg, PreSail.writeReg, xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names, LeanRV64IM.Functions.not, regval_into_reg]
    fin_cases idx
    · simp [wX]
    all_goals
      simp [wX, Sail.writeReg, PreSail.writeReg, xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names, LeanRV64IM.Functions.not, regval_into_reg, reg_idx_to_Register]

@[simp high]
lemma run_wX_bits (reg : regidx) (data : BitVec 64) :
  (wX_bits reg data).run s = let .Regidx idx := reg
    .ok () (if idx = 0#5 then s else {s with
      regs := s.regs.insert (reg_idx_to_Register idx) (bitVecToRegidxVal idx data)}) := by
  let .Regidx idx := reg
  simp [wX_bits_eq_write_reg']
  fin_cases idx <;> simp [xreg_write_callback, reg_name_forwards, get_config_use_abi_names, LeanRV64IM.Functions.not] <;> rfl

@[simp high]
lemma wX_bits_eq_writeReg :
  wX_bits (.Regidx idx) val = if idx = 0#5 then pure () else
    Sail.writeReg (reg_idx_to_Register idx) (bitVecToRegidxVal idx val) := by aesop

end wX_bits

@[simp]
lemma run_bool_bit_backwards :
    (bool_bit_backwards b).run s = match b with
    | 1#1 => .ok true s
    | 0#1 => .ok false s := by
  simp [bool_bit_backwards]
  fin_cases b <;> rfl

@[simp]
lemma run_bit_to_bool :
    (bit_to_bool b).run s = match b with
    | 1#1 => .ok true s
    | 0#1 => .ok false s := by
  fin_cases b <;> rfl

section write_read_bind

/-- Reading a just written value looks like just using the written value. -/
@[simp]
lemma writeReg_readReg_bind
  (mx : RegisterType reg → SailM α) :
  (do Sail.writeReg reg v; let w ← Sail.readReg reg; mx w) =
    (do Sail.writeReg reg v; mx v) := by aesop

end write_read_bind

@[simp]
lemma writeReg_bind_map_readReg
  (f : RegisterType reg → α) :
  (do Sail.writeReg reg v; f <$> Sail.readReg reg) =
    (do Sail.writeReg reg v; return f v) := by aesop

/-- Writing a value overwrites the previous write. -/
@[simp]
lemma writeReg_wX_bits_writeReg :
  (do Sail.writeReg reg v; wX_bits typ_0 data; Sail.writeReg reg v') =
    (do wX_bits typ_0 data; Sail.writeReg reg v') := by aesop

section pc

@[simp] lemma set_next_pc_eq :
  set_next_pc pc = Sail.writeReg Register.nextPC pc := rfl

@[simp] lemma get_next_pc_eq :
  get_next_pc u = Sail.readReg Register.nextPC := rfl

@[simp] lemma tick_pc_eq :
  tick_pc u = (do Sail.writeReg Register.PC (← Sail.readReg Register.nextPC))
  := by unfold tick_pc; aesop

@[simp] lemma force_pc_eq :
  force_pc pc = Sail.writeReg Register.PC pc := rfl

end pc

end Sail

end sailboats

section execution

open PreSail
open LeanRV64IM.Functions

@[simp]
lemma bool_bits_forwards_to_if : bool_bits_forwards b = if b then 1#1 else 0#1 := by aesop

section RTYPE

/-- `execute_RTYPE` pure part -/
def execute_RTYPE_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : rop) :=
  match op with
  | .ADD => op1 + op2
  | .SLT => zero_extend (m := 64) (bool_to_bits (zopz0zI_s op1 op2))
  | .SLTU => zero_extend (m := 64) (bool_to_bits (zopz0zI_u op1 op2))
  | .AND => op1 &&& op2
  | .OR => op1 ||| op2
  | .XOR => op1 ^^^ op2
  | .SLL => Sail.shift_bits_left op1 (Sail.BitVec.extractLsb op2 (LeanRV64IM.Functions.log2_xlen -i 1) 0)
  | .SRL => Sail.shift_bits_right op1 (Sail.BitVec.extractLsb op2 (LeanRV64IM.Functions.log2_xlen -i 1) 0)
  | .SUB => op1 - op2
  | .SRA => shift_bits_right_arith op1 (Sail.BitVec.extractLsb op2 (LeanRV64IM.Functions.log2_xlen -i 1) 0)

/-- `execute_RTYPE` pure part for `Word` arguments -/
@[simp] def execute_RTYPE_pure_w (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : rop) :=
match op with
  | .ADD => op1.toBitVec64 + op2.toBitVec64
  | .SLT => if op1.toInt < op2.toInt then 1#64 else 0#64
  | .SLTU => if op1.toNat < op2.toNat then 1#64 else 0#64
  | .AND => op1.toBitVec64 &&& op2.toBitVec64
  | .OR => op1.toBitVec64 ||| op2.toBitVec64
  | .XOR => op1.toBitVec64 ^^^ op2.toBitVec64
  | .SLL => op1.toBitVec64 <<< (BitVec.setWidth 6 op2.toBitVec64)
  | .SRL => op1.toBitVec64 >>> (BitVec.setWidth 6 op2.toBitVec64)
  | .SUB => op1.toBitVec64 - op2.toBitVec64
  | .SRA => op1.toBitVec64.sshiftRight (BitVec.setWidth 6 op2.toBitVec64).toNat

/-- `execute_RTYPE` pure part for `BWord` arguments -/
@[simp] def execute_RTYPE_pure_bw (op1 : BWord (Fin BB)) (op2 : BWord (Fin BB)) (op : rop) :=
match op with
  | .ADD => op1.toBitVec64 + op2.toBitVec64
  | .SLT => if op1.toInt < op2.toInt then 1#64 else 0#64
  | .SLTU => if op1.toNat < op2.toNat then 1#64 else 0#64
  | .AND => op1.toBitVec64 &&& op2.toBitVec64
  | .OR => op1.toBitVec64 ||| op2.toBitVec64
  | .XOR => op1.toBitVec64 ^^^ op2.toBitVec64
  | .SLL => op1.toBitVec64 <<< (BitVec.setWidth 6 op2.toBitVec64)
  | .SRL => op1.toBitVec64 >>> (BitVec.setWidth 6 op2.toBitVec64)
  | .SUB => op1.toBitVec64 - op2.toBitVec64
  | .SRA => op1.toBitVec64.sshiftRight (BitVec.setWidth 6 op2.toBitVec64).toNat

lemma exec_RTYPE_pure_bv_to_w (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : rop) :
  op1.isU64 → op2.isU64 →
  execute_RTYPE_pure op1.toBitVec64 op2.toBitVec64 op = execute_RTYPE_pure_w op1 op2 op := by
  intro h_op1_isU64 h_op2_isU64
  cases op <;> simp [execute_RTYPE_pure, LeanRV64IM.Functions.log2_xlen]
  . rw [Sail.shift_bits_left]
    simp [Word.toBitVec64_toNat h_op2_isU64]
  . simp [zopz0zI_s, bool_to_bits]
    repeat rw [Word.toBitVec64_toInt (by assumption)]
    aesop
  . simp [zopz0zI_u, bool_to_bits]
    repeat rw [Word.toBitVec64_toNat (by assumption)]
    aesop
  . rw [Sail.shift_bits_right]
    simp [Word.toBitVec64_toNat h_op2_isU64]
  . have mod_lt_63 : (63 + (op2.toNat : ℤ) % 64).toNat = 63 + op2.toNat % 64 := by omega
    have mod_lt_64 : (64 + (op2.toNat : ℤ) % 64).toNat = 64 + op2.toNat % 64 := by omega
    simp [shift_bits_right_arith, shift_right_arith]
    rw [BitVec.toNat_setWidth, Word.toBitVec64_toNat (by assumption)]
    simp
    rw [mod_lt_63, mod_lt_64]
    symm; apply bitVec_sshiftright_eq

lemma exec_RTYPE_pure_bv_to_bw (op1 : BWord (Fin BB)) (op2 : BWord (Fin BB)) (op : rop) :
  op1.isU64 → op2.isU64 →
  execute_RTYPE_pure op1.toBitVec64 op2.toBitVec64 op = execute_RTYPE_pure_bw op1 op2 op := by
  intro h_op1_isU64 h_op2_isU64
  cases op <;> simp [execute_RTYPE_pure, LeanRV64IM.Functions.log2_xlen]
  . rw [Sail.shift_bits_left]
    simp [BWord.toBitVec64_toNat h_op2_isU64]
  . simp [zopz0zI_s, bool_to_bits]
    repeat rw [BWord.toBitVec64_toInt (by assumption)]
    aesop
  . simp [zopz0zI_u, bool_to_bits]
    repeat rw [BWord.toBitVec64_toNat (by assumption)]
    aesop
  . rw [Sail.shift_bits_right]
    simp [BWord.toBitVec64_toNat h_op2_isU64]
  . have mod_lt_63 : (63 + (op2.toNat : ℤ) % 64).toNat = 63 + op2.toNat % 64 := by omega
    have mod_lt_64 : (64 + (op2.toNat : ℤ) % 64).toNat = 64 + op2.toNat % 64 := by omega
    simp [shift_bits_right_arith, shift_right_arith]
    rw [BitVec.toNat_setWidth, BWord.toBitVec64_toNat (by assumption)]
    simp
    rw [mod_lt_63, mod_lt_64]
    symm; apply bitVec_sshiftright_eq

/-- `execute_RTYPE` with isolated pure part -/
def execute_RTYPE' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_RTYPE_pure rs1_bits rs2_bits op))
  (pure RETIRE_SUCCESS)

@[simp]
lemma execute_RTYPE_eq_execute_RTYPE' :
  execute_RTYPE rs2 rs1 rd op = execute_RTYPE' rs2 rs1 rd op
  := by cases op <;> simp_all [execute_RTYPE', execute_RTYPE, execute_RTYPE_pure, LeanRV64IM.Functions.xlen]

end RTYPE

section RTYPEW

/-- `execute_RTYPEW` pure part - 32-bit -/
@[simp] def execute_RTYPEW_pure_32 (op1 : BitVec 32) (op2 : BitVec 32) (op : ropw) :=
  match op with
  | .ADDW => op1 + op2
  | .SUBW => op1 - op2
  | .SLLW => Sail.shift_bits_left op1 (Sail.BitVec.extractLsb op2 4 0)
  | .SRLW => Sail.shift_bits_right op1 (Sail.BitVec.extractLsb op2 4 0)
  | .SRAW => shift_bits_right_arith op1 (Sail.BitVec.extractLsb op2 4 0)

/-- `execute_RTYPEW` pure part - 32-bit for `HWord` arguments -/
@[simp] def execute_RTYPEW_pure_32_w (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : ropw) :=
  let op1 := op1.low
  let op2 := op2.low
  match op with
  | .ADDW => op1.toBitVec32 + op2.toBitVec32
  | .SUBW => op1.toBitVec32 - op2.toBitVec32
  | .SLLW => op1.toBitVec32 <<< (BitVec.setWidth 5 op2.toBitVec32)
  | .SRLW => op1.toBitVec32 >>> (BitVec.setWidth 5 op2.toBitVec32)
  | .SRAW => op1.toBitVec32.sshiftRight (BitVec.setWidth 5 op2.toBitVec32).toNat

/-- `execute_RTYPEW` pure part - 64-bit -/
def execute_RTYPEW_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : ropw) :=
  let op1 := BitVec.setWidth 32 op1
  let op2 := BitVec.setWidth 32 op2
  sign_extend (m := 64) (execute_RTYPEW_pure_32 op1 op2 op)

/-- `execute_RTYPEW` pure part - 64-bit for `Word` arguments -/
@[simp] def execute_RTYPEW_pure_w (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : ropw) :=
  sign_extend (m := 64) (execute_RTYPEW_pure_32_w op1 op2 op)

lemma exec_RTYPEW_pure_bv_to_w (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : ropw) :
  op1.isU64 → op2.isU64 →
  execute_RTYPEW_pure op1.toBitVec64 op2.toBitVec64 op = execute_RTYPEW_pure_w op1 op2 op := by
  intro h_op1_isU64 h_op2_isU64
  have ha' := Word.lt_cases_of_isU64 h_op1_isU64
  have hb' := Word.lt_cases_of_isU64 h_op2_isU64
  cases op <;> simp [execute_RTYPEW_pure] <;> congr
  . apply Word.setWidth_eq_low h_op1_isU64
  . apply Word.setWidth_eq_low h_op2_isU64
  . apply Word.setWidth_eq_low h_op1_isU64
  . apply Word.setWidth_eq_low h_op2_isU64
  . rw [Sail.shift_bits_left]
    simp [Word.toBitVec64_toNat h_op2_isU64]
    rw [Word.setWidth_eq_low h_op1_isU64]
    congr 1
    simp [Word.toNat, Word.low, HWord.toBitVec32, HWord.toNat]
    omega
  . rw [Sail.shift_bits_right]
    simp [Word.toBitVec64_toNat h_op2_isU64]
    rw [Word.setWidth_eq_low h_op1_isU64]
    congr 1
    simp [Word.toNat, Word.low, HWord.toBitVec32, HWord.toNat]
    omega
  . have mod_lt_31: forall x : ℕ, (31 + (x : ℤ) % 32).toNat = 31 + x % 32 := by omega
    have mod_lt_32 : forall x : ℕ, (32 + (x : ℤ) % 32).toNat = 32 + x % 32 := by omega
    rw [Word.setWidth_eq_low h_op1_isU64]
    simp [bitVec_sshiftright_eq]
    simp [shift_bits_right_arith, shift_right_arith]
    (repeat rw [BitVec.toNat_ofNat]); simp
    have : op2.toBitVec64.toNat % 4294967296 % 32 = op2.toBitVec64.toNat % 32 := by omega
    rw [this]
    have : (op2.toBitVec64.toNat : ℤ) % 4294967296 % 32 = op2.toBitVec64.toNat % 32 := by omega
    rw [this, mod_lt_31, mod_lt_32]; simp
    have : op2.toBitVec64.toNat % 32 = op2.low.toBitVec32.toNat % 32 := by
      simp [Word.toBitVec64, Word.toNat, Word.low, HWord.toBitVec32, HWord.toNat]
      omega
    rw [this]

/-- `execute_RTYPEW` with isolated pure part -/
def execute_RTYPEW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_RTYPEW_pure rs1_bits rs2_bits op))
  (pure RETIRE_SUCCESS)

@[simp]
lemma execute_RTYPEW_eq_execute_RTYPEW' :
  execute_RTYPEW rs2 rs1 rd op = execute_RTYPEW' rs2 rs1 rd op
  := by
    simp_all [execute_RTYPEW, execute_RTYPEW', execute_RTYPEW_pure]
    aesop (add unsafe (by congr <;> simp [← BitVec.toNat_inj]))

end RTYPEW

section ITYPE

@[simp]
def rop_of_iop (op : iop) : rop :=
  match op with
  | .ADDI => .ADD
  | .SLTI => .SLT
  | .SLTIU => .SLTU
  | .ANDI => .AND
  | .ORI => .OR
  | .XORI => .XOR

/-- `execute_ITYPE` pure part -/
def execute_ITYPE_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : iop) :=
  execute_RTYPE_pure op1 op2 (rop_of_iop op)

/-- `execute_ITYPE` pure part for `Word` arguments -/
def execute_ITYPE_pure_w (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : iop) :=
  execute_RTYPE_pure_w op1 op2 (rop_of_iop op)

/-- `execute_ITYPE` pure part for `BWord` arguments -/
def execute_ITYPE_pure_bw (op1 : BWord (Fin BB)) (op2 : BWord (Fin BB)) (op : iop) :=
  execute_RTYPE_pure_bw op1 op2 (rop_of_iop op)

lemma exec_ITYPE_pure_bv_to_w (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : iop) :
  op1.isU64 → op2.isU64 →
  execute_ITYPE_pure op1.toBitVec64 op2.toBitVec64 op = execute_ITYPE_pure_w op1 op2 op := by
  intro h_op1_isU64 h_op2_isU64
  simp [execute_ITYPE_pure_w, execute_ITYPE_pure]
  cases op <;> simp <;> exact exec_RTYPE_pure_bv_to_w _ _ _ h_op1_isU64 h_op2_isU64

lemma exec_ITYPE_pure_bv_to_bw (op1 : BWord (Fin BB)) (op2 : BWord (Fin BB)) (op : iop) :
  op1.isU64 → op2.isU64 →
  execute_ITYPE_pure op1.toBitVec64 op2.toBitVec64 op = execute_ITYPE_pure_bw op1 op2 op := by
  intro h_op1_isU64 h_op2_isU64
  simp [execute_ITYPE_pure_bw, execute_ITYPE_pure]
  cases op <;> simp <;> exact exec_RTYPE_pure_bv_to_bw _ _ _ h_op1_isU64 h_op2_isU64

/-- `execute_RTYPE` with isolated pure part -/
def execute_ITYPE' (imm : BitVec 12) (rs1 : regidx) (rd : regidx) (op : iop) : SailM ExecutionResult := do
  let immext := sign_extend (m := 64) imm
  let rs1_bits ← do (rX_bits rs1)
  (wX_bits rd (execute_ITYPE_pure rs1_bits immext op))
  (pure RETIRE_SUCCESS)

@[simp]
lemma execute_ITYPE_eq_execute_ITYPE' :
  execute_ITYPE imm rs1 rd op = execute_ITYPE' imm rs1 rd op
  := by cases op <;> simp_all [execute_ITYPE', execute_ITYPE, execute_ITYPE_pure, execute_RTYPE_pure, LeanRV64IM.Functions.xlen]

end ITYPE

section ADDIW

def execute_ADDIW' (imm : BitVec 12) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  (wX_bits rd (execute_RTYPEW_pure rs1_bits (sign_extend (m := 64) imm) .ADDW))
  (pure RETIRE_SUCCESS)

@[simp]
lemma execute_ADDIW'_eq_execute_ADDIW' :
  execute_ADDIW imm rs1 rd = execute_ADDIW' imm rs1 rd
  := by
    simp_all [execute_ADDIW, execute_ADDIW', execute_RTYPEW_pure]
    aesop (add unsafe (by congr <;> bv_decide))

end ADDIW

section SHIFTIOP

@[simp]
def rop_of_sop (op : sop) : rop :=
  match op with
  | .SLLI => .SLL
  | .SRLI => .SRL
  | .SRAI => .SRA

@[simp] def execute_SHIFTIOP_pure_w (op1 : Word (Fin BB)) (shamt : BitVec 6) (op : sop) :=
  let shamtBB : Fin BB := ⟨ shamt.toNat, by omega ⟩
  execute_RTYPE_pure_w op1 #v[shamtBB, 0, 0, 0] (rop_of_sop op)

def execute_SHIFTIOP_pure (op1 : BitVec 64) (shamt : BitVec 6) (op : sop) :=
  let shamt64 : BitVec 64 := shamt
  execute_RTYPE_pure op1 shamt64 (rop_of_sop op)

lemma exec_SHIFTIOP_pure_bv_to_w (op1 : Word (Fin BB)) (shamt : BitVec 6) (op : sop) :
  op1.isU64 →
  execute_SHIFTIOP_pure op1.toBitVec64 shamt op = execute_SHIFTIOP_pure_w op1 shamt op := by
  intro h_op1_isU64
  have h_op2_isU64 : Word.isU64 #v[ ⟨ shamt.toNat, by omega ⟩ , 0, 0, 0 ] := by apply Word.isU64_of_cases <;> simp; omega
  simp only [execute_SHIFTIOP_pure_w, execute_SHIFTIOP_pure]
  rw [← exec_RTYPE_pure_bv_to_w _ _ _ h_op1_isU64 h_op2_isU64]
  suffices : (BitVec.setWidth 64 shamt) = Word.toBitVec64 #v[ ⟨ shamt.toNat, by omega ⟩, 0, 0, 0]
  . rw [this]
  . rw [← BitVec.toNat_inj]
    rw [Word.toBitVec64_toNat h_op2_isU64, Word.toNat]
    simp; omega

def execute_SHIFTIOP' (shamt : BitVec 6) (rs1 : regidx) (rd : regidx) (op : sop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  (wX_bits rd (execute_SHIFTIOP_pure rs1_bits shamt op))
  (pure RETIRE_SUCCESS)

@[simp]
lemma execute_SHIFTIOP_eq_execute_SHIFTIOP' :
  execute_SHIFTIOP shamt rs1 rd op = execute_SHIFTIOP' shamt rs1 rd op
  := by
    have h_eq_shamt : BitVec.ofNat 6 (shamt.toNat % 18446744073709551616) = shamt := by
      rw [Nat.mod_eq_of_lt (by omega)]; simp
    simp [execute_SHIFTIOP, execute_SHIFTIOP', execute_SHIFTIOP_pure, execute_RTYPE_pure, LeanRV64IM.Functions.log2_xlen]
    aesop

end SHIFTIOP

section SHIFTIWOP

@[simp]
def ropw_of_sopw (op : sopw) : ropw :=
  match op with
  | .SLLIW => .SLLW
  | .SRLIW => .SRLW
  | .SRAIW => .SRAW

@[simp] def execute_SHIFTIWOP_pure_w (op1 : Word (Fin BB)) (shamt : BitVec 5) (op : sopw) :=
  let shamtBB : Fin BB := ⟨ shamt.toNat, by omega ⟩
  execute_RTYPEW_pure_w op1 #v[shamtBB, 0, 0, 0] (ropw_of_sopw op)

def execute_SHIFTIWOP_pure (op1 : BitVec 64) (shamt : BitVec 5) (op : sopw) :=
  let shamt64 : BitVec 64 := shamt
  execute_RTYPEW_pure op1 shamt64 (ropw_of_sopw op)

lemma exec_SHIFTIWOP_pure_bv_to_w (op1 : Word (Fin BB)) (shamt : BitVec 5) (op : sopw) :
  op1.isU64 →
  execute_SHIFTIWOP_pure op1.toBitVec64 shamt op = execute_SHIFTIWOP_pure_w op1 shamt op := by
  intro h_op1_isU64
  have h_op2_isU64 : Word.isU64 #v[ ⟨ shamt.toNat, by omega ⟩ , 0, 0, 0 ] := by apply Word.isU64_of_cases <;> simp; omega
  simp only [execute_SHIFTIWOP_pure_w, execute_SHIFTIWOP_pure]
  rw [← exec_RTYPEW_pure_bv_to_w _ _ _ h_op1_isU64 h_op2_isU64]
  suffices : (BitVec.setWidth 64 shamt) = Word.toBitVec64 #v[ ⟨ shamt.toNat, by omega ⟩, 0, 0, 0]
  . rw [this]
  . rw [← BitVec.toNat_inj]
    rw [Word.toBitVec64_toNat h_op2_isU64, Word.toNat]
    simp; omega

def execute_SHIFTIWOP' (shamt : BitVec 5) (rs1 : regidx) (rd : regidx) (op : sopw) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  (wX_bits rd (execute_SHIFTIWOP_pure rs1_bits shamt op))
  (pure RETIRE_SUCCESS)

@[simp]
lemma execute_SHIFTIWOP_eq_execute_SHIFTIWOP' :
  execute_SHIFTIWOP shamt rs1 rd op = execute_SHIFTIWOP' shamt rs1 rd op
  := by
    have h_eq_shamt : BitVec.ofNat 5 (shamt.toNat % 4294967296) = shamt := by
      rw [Nat.mod_eq_of_lt (by omega)]; simp
    simp [execute_SHIFTIWOP, execute_SHIFTIWOP', execute_SHIFTIWOP_pure, execute_RTYPEW_pure, LeanRV64IM.Functions.log2_xlen]
    aesop

end SHIFTIWOP

section MUL

/-- Multiplication opcodes -/
inductive mop where | MUL | MULH | MULHU | MULHUS | MULHSU
  deriving BEq, DecidableEq, Inhabited, Repr

def mop_of_mul_op (m : mul_op) : mop :=
  match m with
  | { high := false, signed_rs1 := _, signed_rs2 := _ } => .MUL
  | { high := true, signed_rs1 := false, signed_rs2 := false } => .MULHU
  | { high := true, signed_rs1 := false, signed_rs2 := true } => .MULHUS
  | { high := true, signed_rs1 := true, signed_rs2 := false } => .MULHSU
  | { high := true, signed_rs1 := true, signed_rs2 := true } => .MULH

/-- execute_MUL pure part -/
def execute_MUL_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : mop) : BitVec 64 :=
  let rs1_ext : BitVec 128 := op1.extend 128 (op = .MULH ∨ op = .MULHSU)
  let rs2_ext : BitVec 128 := op2.extend 128 (op = .MULH ∨ op = .MULHUS)
  let result_wide := rs1_ext * rs2_ext
  (if (op = .MUL)
    then (Sail.BitVec.extractLsb result_wide 63 0)
    else (Sail.BitVec.extractLsb result_wide 127 64))

lemma combine_MUL_MULH {pl ph op1 op2: Word (Fin BB)}
  (isU64_pl : pl.isU64) (isU64_ph : ph.isU64)
  (isU64_op1 : op1.isU64) (isU64_op2 : op2.isU64) :
  Word.toBitVec64 pl = execute_MUL_pure op1.toBitVec64 op2.toBitVec64 .MUL →
  Word.toBitVec64 ph = execute_MUL_pure op1.toBitVec64 op2.toBitVec64 .MULH →
    DWord.toBitVec128 #v[pl[0], pl[1], pl[2], pl[3], ph[0], ph[1], ph[2], ph[3]] = (op1.extend true).toBitVec128 * (op2.extend true).toBitVec128
   := by
  iterate 2 rw [Word.extend_true_is_signExtend (by assumption)]
  simp [execute_MUL_pure, -BitVec.extractLsb]
  intro lo hi
  have : BitVec.extractLsb 63 0 (op1.toBitVec64.extend 128 False * op2.toBitVec64.extend 128 False) = BitVec.extractLsb 63 0 (op1.toBitVec64.extend 128 True * op2.toBitVec64.extend 128 True) := by simp [BitVec.extend, -BitVec.extractLsb]; bv_decide
  rw [this] at lo; clear this
  simp [BitVec.extend, -BitVec.extractLsb] at *
  set x := BitVec.signExtend 128 op1.toBitVec64 * BitVec.signExtend 128 op2.toBitVec64
  trans BitVec.extractLsb 63 0 x + (BitVec.setWidth 128 (BitVec.extractLsb 127 64 x) <<< 64)
  . rw [← lo, ← hi]
    rw [← BitVec.toNat_inj]
    rw [DWord.toBitVec128, DWord.toNat, Word.toBitVec64, Word.toBitVec64, Word.toNat, Word.toNat]
    repeat rw [BitVec.toNat_add]
    simp [Nat.shiftLeft_eq]
    apply Word.lt_cases_of_isU64 at isU64_pl
    apply Word.lt_cases_of_isU64 at isU64_ph
    iterate 2 rw [Nat.mod_eq_of_lt (b := 18446744073709551616) (by omega)]
    ring_nf
  . bv_decide

/-- execute_MUL pure part for BWord arguments -/
def execute_MUL_pure_bw (op1 : BWord (Fin BB)) (op2 : BWord (Fin BB)) (op : mop) : BitVec 64 :=
  let op1_ext := op1.extend (op = .MULH ∨ op = .MULHSU)
  let op2_ext := op2.extend (op = .MULH ∨ op = .MULHUS)
  let result_wide := op1_ext.toBitVec128 * op2_ext.toBitVec128
  (if (op = .MUL)
    then (Sail.BitVec.extractLsb result_wide 63 0)
    else (Sail.BitVec.extractLsb result_wide 127 64))

lemma exec_MUL_pure_bv_to_bw (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : mop) :
  op1.isU64 → op2.isU64 →
  execute_MUL_pure op1.toBitVec64 op2.toBitVec64 op = execute_MUL_pure_bw op1.toBWord op2.toBWord op := by
  intro is_U64_op1 is_U64_op2
  have := op1.toBWord_toU64 is_U64_op1
  have := op2.toBWord_toU64 is_U64_op2

  cases op <;> simp [execute_MUL_pure, execute_MUL_pure_bw, -BitVec.toNat_mul] <;>
  (repeat rw [BWord.extend_true_is_signExtend (by assumption)]) <;>
  (repeat rw [BWord.extend_false_is_setWidth (by assumption)]) <;>
  congr <;> simp [BitVec.extend] <;>
  rw [Word.toBitVec64_toBWord (by assumption)]

def execute_MUL' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (m : mop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_MUL_pure rs1_bits rs2_bits m))
  (pure RETIRE_SUCCESS)

@[simp]
lemma execute_MUL'_eq_execute_MUL :
  execute_MUL rs2 rs1 rd op = execute_MUL' rs2 rs1 rd (mop_of_mul_op op)
    := by
  have bounds_toInt_64 : forall (bv : BitVec 64), -2^63 ≤ bv.toInt ∧ bv.toInt < 2^63 := by
    simp [BitVec.toInt]; intros; split_ifs <;> omega
  have bounds_toNat_64 : forall (bv : BitVec 64), 0 ≤ bv.toNat ∧ bv.toNat < 2^64 := by omega

  rcases op with ⟨ high, sgn1, sgn2 ⟩
  rcases sgn2 with sgn2 | sgn2 <;> rcases sgn1 with sgn1 | sgn1 <;> rcases high with high | high

  all_goals
    simp_all [execute_MUL', execute_MUL, execute_MUL_pure, BitVec.extend, mop_of_mul_op, LeanRV64IM.Functions.xlen, to_bits_truncate, Sail.get_slice_int]
    refine bind_congr ?_; intro r1
    refine bind_congr ?_; intro r2
    ext s; simp_all; congr 4
    have mod_129_to_128 : forall (a : ℤ), (a % 680564733841876926926749214863536422912).toNat % 340282366920938463463374607431768211456 = (a % 340282366920938463463374607431768211456).toNat := by omega

  . rw [Int.toNat_emod (by nlinarith) (by simp)]
    rw [Int.toNat_mul (by simp) (by simp)]
    simp

  . rw [Int.toNat_emod (by nlinarith) (by simp)]
    rw [Int.toNat_mul (by simp) (by simp)]
    simp

  . unfold BitVec.toInt
    split_ifs <;> simp_all
    . rw [Int.toNat_emod (by nlinarith) (by simp)]
      simp; congr
    . simp [← BitVec.toNat_inj]
      trans (- (((18446744073709551616 : ℤ) - r1.toNat) * r2.toNat) % 340282366920938463463374607431768211456).toNat % 18446744073709551616
      . congr 3
        ring_nf
      . rw [Int.neg_emod_eq_sub_emod]
        have := bounds_toNat_64 r1
        have := bounds_toNat_64 r2
        rw [Int.toNat_emod (by nlinarith) (by simp)]
        rw [Int.toNat_sub'' (by simp) (by nlinarith)]
        simp only [Int.reduceToNat]
        rw [Int.toNat_mul (by omega) (by omega)]
        simp
        rw [Nat.mul_sub_right_distrib]
        rw [Nat.sub_sub_right _ (by nlinarith)]
        omega

  . congr 2
    rw [mod_129_to_128]
    apply BitVec.toInt_toNat_as_toNat_128

  . unfold BitVec.toInt
    split_ifs <;> simp_all
    . rw [Int.toNat_emod (by nlinarith) (by simp)]
      simp; congr
    . simp [← BitVec.toNat_inj]
      trans (- ((r1.toNat : ℤ) * ((18446744073709551616 : ℤ) - r2.toNat)) % 340282366920938463463374607431768211456).toNat % 18446744073709551616
      . congr 3
        ring_nf
      . rw [Int.neg_emod_eq_sub_emod]
        have := bounds_toNat_64 r1
        have := bounds_toNat_64 r2
        rw [Int.toNat_emod (by nlinarith) (by simp)]
        rw [Int.toNat_sub'' (by simp) (by nlinarith)]
        simp only [Int.reduceToNat]
        rw [Int.toNat_mul (by omega) (by omega)]
        simp
        rw [Nat.mul_sub_left_distrib]
        rw [Nat.sub_sub_right _ (by nlinarith)]
        omega

  . congr 2
    rw [mod_129_to_128]
    apply BitVec.toNat_toInt_as_toNat_128

  . unfold BitVec.toInt
    split_ifs <;> simp_all
    . rw [Int.toNat_emod (by nlinarith) (by simp)]
      simp; congr
    . simp [← BitVec.toNat_inj]
      trans (- ((r1.toNat : ℤ) * ((18446744073709551616 : ℤ) - r2.toNat)) % 340282366920938463463374607431768211456).toNat % 18446744073709551616
      . congr 3
        ring_nf
      . rw [Int.neg_emod_eq_sub_emod]
        have := bounds_toNat_64 r1
        have := bounds_toNat_64 r2
        rw [Int.toNat_emod (by nlinarith) (by simp)]
        rw [Int.toNat_sub'' (by simp) (by nlinarith)]
        simp only [Int.reduceToNat]
        rw [Int.toNat_mul (by omega) (by omega)]
        simp
        rw [Nat.mul_sub_left_distrib ]
        rw [Nat.sub_sub_right _ (by nlinarith)]
        omega
    . simp [← BitVec.toNat_inj]
      trans (- (((18446744073709551616 : ℤ) - r1.toNat) * r2.toNat) % 340282366920938463463374607431768211456).toNat % 18446744073709551616
      . congr 3
        ring_nf
      . rw [Int.neg_emod_eq_sub_emod]
        have := bounds_toNat_64 r1
        have := bounds_toNat_64 r2
        rw [Int.toNat_emod (by nlinarith) (by simp)]
        rw [Int.toNat_sub'' (by simp) (by nlinarith)]
        simp only [Int.reduceToNat]
        rw [Int.toNat_mul (by omega) (by omega)]
        simp
        rw [Nat.mul_sub_right_distrib]
        rw [Nat.sub_sub_right _ (by nlinarith)]
        omega
    . simp [← BitVec.toNat_inj]
      trans (((18446744073709551616 : ℤ) - r1.toNat) * (18446744073709551616 - r2.toNat) % 340282366920938463463374607431768211456).toNat % 18446744073709551616
      . congr 3
        ring_nf
      . have := bounds_toNat_64 r1
        have := bounds_toNat_64 r2
        rw [Int.toNat_emod (by nlinarith) (by simp)]
        simp only [Int.reduceToNat]
        rw [Int.toNat_mul (by omega) (by omega)]
        simp [Nat.mul_sub_right_distrib]
        repeat rw [Nat.mul_sub_left_distrib]
        rw [Nat.sub_sub_right _ (by nlinarith)]
        ring_nf
        suffices : (r1.toNat * 18446744073709551616) % 18446744073709551616 = 0
        . have : forall x y, y * 18446744073709551616 ≤ x → (x - y * 18446744073709551616) % 18446744073709551616 = x % 18446744073709551616 := by intro; omega
          rw [this]
          . omega
          . suffices : r1.toNat * 18446744073709551616 + r2.toNat * 18446744073709551616 ≤ r2.toNat * r1.toNat + 340282366920938463463374607431768211456
            . rw [← Nat.add_sub_assoc (by omega)]
              rw [Nat.le_sub_iff_add_le (by nlinarith)]
              assumption
            . nlinarith
        . omega

  . congr 2
    rw [mod_129_to_128]
    . rw [← BitVec.toNat_mul]
      apply BitVec.toInt_toInt_as_toNat_128

end MUL

section MULW

/-- execute_MULW pure part -/
def execute_MULW_pure (op1 : BitVec 64) (op2 : BitVec 64) : BitVec 64 :=
  let rs1_low : BitVec 32 := BitVec.extractLsb 31 0 op1
  let rs2_low : BitVec 32 := BitVec.extractLsb 31 0 op2
  let prod : BitVec 32 := rs1_low * rs2_low
  prod.extend 64 true

/-- execute_MULW pure part for BWord arguments -/
def execute_MULW_pure_bhw (op1 : BHWord (Fin BB)) (op2 : BHWord (Fin BB)) : BitVec 64 :=
  let prod : BitVec 32 := op1.toBitVec32 * op2.toBitVec32
  prod.extend 64 true

lemma exec_MULW_pure_bv_to_bhw (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) :
  op1.isU64 → op2.isU64 →
  execute_MULW_pure op1.toBitVec64 op2.toBitVec64 = execute_MULW_pure_bhw op1.toBWord.low op2.toBWord.low := by
  intro is_U64_op1 is_U64_op2
  have is_U64_bw1 := op1.toBWord_toU64 is_U64_op1
  have is_U64_bw2 := op2.toBWord_toU64 is_U64_op2

  simp [execute_MULW_pure, execute_MULW_pure_bhw, BitVec.extend]
  iterate 2 rw [← Word.toBitVec64_toBWord (by assumption), BWord.low_as_setWidth (by assumption)]

def execute_MULW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_MULW_pure rs1_bits rs2_bits))
  (pure RETIRE_SUCCESS)

@[simp]
lemma execute_MULW'_eq_execute_MULW :
  execute_MULW rs2 rs1 rd = execute_MULW' rs2 rs1 rd
    := by
  have mod_33_to_32 : forall (a : ℤ), (a % 8589934592).toNat % 4294967296 = (a % 4294967296).toNat := by omega
  have bounds_toInt_32 : forall (bv : BitVec 32), -2^31 ≤ bv.toInt ∧ bv.toInt < 2^31 := by
    simp [BitVec.toInt]; intros; split_ifs <;> omega
  have bounds_toNat_32 : forall (bv : BitVec 32), 0 ≤ bv.toNat ∧ bv.toNat < 2^32 := by omega

  simp_all [execute_MULW, execute_MULW', execute_MULW_pure, to_bits_truncate, Sail.get_slice_int, -BitVec.extractLsb, -BitVec.toInt_extractLsb]
  refine bind_congr ?_; intro r1
  refine bind_congr ?_; intro r2
  ext s; simp [-BitVec.extractLsb, -BitVec.toInt_extractLsb, BitVec.extend]; congr 4

  set r1w : BitVec 32 := BitVec.extractLsb 31 0 r1
  set r2w : BitVec 32 := BitVec.extractLsb 31 0 r2

  trans BitVec.signExtend 64 (BitVec.ofNat 32 (r1w.toInt * r2w.toInt % 4294967296).toNat)
  . congr 1
    simp [← BitVec.toNat_inj, mod_33_to_32]
    symm; apply Nat.mod_eq_of_lt (by omega)
  . congr 1
    trans (BitVec.ofInt 32 (r1w.toInt * r2w.toInt))
    . simp [BitVec.ofInt, ← BitVec.toNat_inj]
      omega
    . simp [← BitVec.toInt_inj]

end MULW

section DIV_REM

/-- Multiplication opcodes -/
inductive drop where | DRS | DRU | DRWS | DRWU
  deriving BEq, DecidableEq, Inhabited, Repr

def execute_DIV_REM_pure_int (op1 : BitVec 64) (op2 : BitVec 64) (op : drop) : ℤ × ℤ :=
  match op with
  | .DRS =>
      let nop1 := BitVec.toInt op1
      let nop2 := BitVec.toInt op2
      let q := bif nop2 == 0 then -1 else
                 bif nop1 == -2^63 && nop2 == -1 then -2^63 else
                   Int.tdiv nop1 nop2
      let r := Int.tmod nop1 nop2
      ⟨ q, r ⟩
  | .DRU =>
      let nop1 : ℤ := BitVec.toNat op1
      let nop2 : ℤ := BitVec.toNat op2
      let q := bif nop2 == 0 then 2^64 - 1 else Int.tdiv nop1 nop2
      let r := Int.tmod nop1 nop2
      ⟨ q, r ⟩
  | .DRWS =>
      let nop1 := BitVec.toInt (BitVec.extractLsb 31 0 op1)
      let nop2 := BitVec.toInt (BitVec.extractLsb 31 0 op2)
      let q := bif nop2 == 0 then -1 else
                 bif nop1 == -2^31 && nop2 == -1 then -2^31 else
                   Int.tdiv nop1 nop2
      let r := Int.tmod nop1 nop2
      ⟨ q, r ⟩
  | .DRWU =>
      let nop1 : ℤ := BitVec.toNat (BitVec.extractLsb 31 0 op1)
      let nop2 : ℤ := BitVec.toNat (BitVec.extractLsb 31 0 op2)
      let q := bif nop2 == 0 then 2^64 - 1 else Int.tdiv nop1 nop2
      let r := Int.tmod nop1 nop2
      ⟨ q, r ⟩

def execute_DIV_REM_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : drop) : BitVec 64 × BitVec 64 :=
  let ⟨ q, r ⟩ := execute_DIV_REM_pure_int op1 op2 op
  match op with
  | .DRS | .DRWS => ⟨ BitVec.ofInt 64 q, BitVec.ofInt 64 r ⟩
  | .DRU => ⟨ BitVec.ofNat 64 q, BitVec.ofNat 64 r ⟩
  | .DRWU => ⟨ BitVec.signExtend 64 (BitVec.ofNat 32 q), BitVec.signExtend 64 (BitVec.ofNat 32 r) ⟩

def execute_DIV' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let ⟨ result, _ ⟩ := execute_DIV_REM_pure rs1_bits rs2_bits (if is_unsigned then .DRU else .DRS)
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

def execute_REM' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let ⟨ _, result ⟩ := execute_DIV_REM_pure rs1_bits rs2_bits (if is_unsigned then .DRU else .DRS)
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

def execute_DIVW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let ⟨ result, _ ⟩ := execute_DIV_REM_pure rs1_bits rs2_bits (if is_unsigned then .DRWU else .DRWS)
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

def execute_REMW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (is_unsigned : Bool) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  let ⟨ _, result ⟩ := execute_DIV_REM_pure rs1_bits rs2_bits (if is_unsigned then .DRWU else .DRWS)
  (wX_bits rd result)
  (pure RETIRE_SUCCESS)

lemma div_overflow {x y : ℤ} :
  -9223372036854775808 ≤ x ∧ x < 9223372036854775808 →
    -9223372036854775808 ≤ y ∧ y < 9223372036854775808 →
      (9223372036854775808 ≤ x.tdiv y ↔ x = -9223372036854775808 ∧ y = -1) := by
  intro hx hy
  constructor <;> intro hc
  have : (x.tdiv y).sign = 1 := by rw [Int.sign_cases, if_neg (by omega), if_neg (by omega)]
  rw [Int.sign_tdiv] at this
  split_ifs at this with hyp <;> [ simp_all; clear hyp ]
  . simp [Int.sign_cases] at this
    split_ifs at this <;> simp_all
    . suffices : -x = 9223372036854775808 ∧ -y = 1
      . omega
      . have eq : x.tdiv y = (-x).tdiv (-y) := by simp
        rw [eq, Int.tdiv_eq_ediv_of_nonneg (by omega)] at hc
        by_cases yone : -y = 1
        . simp_all; omega
        . have := @Int.ediv_lt_self_of_pos_of_ne_one (-x) (-y) (by omega) (by omega)
          omega
    . rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at hc
      by_cases yone : y = 1
      . simp_all; omega
      . have := @Int.ediv_lt_self_of_pos_of_ne_one x y (by omega) (by omega)
        omega
  . simp_all

@[simp]
lemma execute_DIV'_eq_execute_DIV :
  execute_DIV rs2 rs1 rd usgn = execute_DIV' rs2 rs1 rd usgn := by
  simp_all [execute_DIV, execute_DIV']
  refine bind_congr ?_; intro r1
  refine bind_congr ?_; intro r2
  ext s; simp_all; congr
  have range_int_r1 : -9223372036854775808 ≤ r1.toInt ∧ r1.toInt < 9223372036854775808 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
  have range_int_r2 : -9223372036854775808 ≤ r2.toInt ∧ r2.toInt < 9223372036854775808 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
  have range_nat_r1 : 0 ≤ r1.toNat ∧ r1.toNat < 18446744073709551616 := by omega
  have range_nat_r2 : 0 ≤ r2.toNat ∧ r2.toNat < 18446744073709551616 := by omega
  by_cases usgn <;> simp_all [execute_DIV_REM_pure, execute_DIV_REM_pure_int, LeanRV64IM.Functions.not, LeanRV64IM.Functions.xlen, instHPowInt_leanRV64IM] <;>
  by_cases r2z : r2 = 0 <;> simp_all
  . simp [to_bits_truncate, Sail.get_slice_int]
  . repeat rw [ Bool.cond_neg (by rw [← BitVec.toNat_inj] at r2z; simp_all) ]
    rw [← BitVec.toNat_inj]
    simp [to_bits_truncate, Sail.get_slice_int]
    congr; rw [Int.emod_eq_of_lt]
    . apply Int.zero_le_ofNat
    . have := @Int.ediv_le_self r1.toNat r2.toNat (by omega)
      omega
  . simp [to_bits_truncate, Sail.get_slice_int]
  . repeat rw [ Bool.cond_neg (b := r2.toInt == 0) (by rw [← BitVec.toInt_inj] at r2z; simp_all) ]
    by_cases of : 9223372036854775808 ≤ r1.toInt.tdiv r2.toInt <;>
    have of' := div_overflow range_int_r1 range_int_r2 <;>
    simp_all [to_bits_truncate, Sail.get_slice_int]
    repeat rw [ Bool.cond_neg (by simp; omega )]
    simp [BitVec.ofNat, BitVec.ofInt]
    congr; simp [Fin.ext_iff]
    omega

lemma divw_overflow {x y : ℤ} :
  -2147483648 ≤ x ∧ x < 2147483648 →
    -2147483648 ≤ y ∧ y < 2147483648 →
      (2147483648 ≤ x.tdiv y ↔ x = -2147483648 ∧ y = -1) := by
  intro hx hy
  constructor <;> intro hc
  have : (x.tdiv y).sign = 1 := by rw [Int.sign_cases, if_neg (by omega), if_neg (by omega)]
  rw [Int.sign_tdiv] at this
  split_ifs at this with hyp <;> [ simp_all; clear hyp ]
  . simp [Int.sign_cases] at this
    split_ifs at this <;> simp_all
    . suffices : -x = 2147483648 ∧ -y = 1
      . omega
      . have eq : x.tdiv y = (-x).tdiv (-y) := by simp
        rw [eq, Int.tdiv_eq_ediv_of_nonneg (by omega)] at hc
        by_cases yone : -y = 1
        . simp_all; omega
        . have := @Int.ediv_lt_self_of_pos_of_ne_one (-x) (-y) (by omega) (by omega)
          omega
    . rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at hc
      by_cases yone : y = 1
      . simp_all; omega
      . have := @Int.ediv_lt_self_of_pos_of_ne_one x y (by omega) (by omega)
        omega
  . simp_all

lemma BitVec.signExtend_ofInt {x : ℤ} (lb : -2147483648 ≤ x) (ub : x < 2147483648) :
  BitVec.signExtend 64 (BitVec.ofInt 32 x) = BitVec.ofInt 64 x
    := by
  simp [← BitVec.toInt_inj]
  rw [BitVec.toInt_signExtend_of_le (by simp)]
  simp [Int.bmod_def]; omega

@[simp]
lemma execute_DIVW'_eq_execute_DIVW :
  execute_DIVW rs2 rs1 rd usgn = execute_DIVW' rs2 rs1 rd usgn := by
  simp_all [execute_DIVW, execute_DIVW', execute_DIV_REM_pure, execute_DIV_REM_pure_int, -BitVec.extractLsb, -BitVec.extractLsb_toNat, -BitVec.toInt_extractLsb]
  refine bind_congr ?_; intro r1
  refine bind_congr ?_; intro r2
  set r1 := BitVec.extractLsb 31 0 r1
  set r2 := BitVec.extractLsb 31 0 r2
  ext s; simp_all; congr
  have range_int_r1 : -2147483648 ≤ r1.toInt ∧ r1.toInt < 2147483648 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
  have range_int_r2 : -2147483648 ≤ r2.toInt ∧ r2.toInt < 2147483648 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
  have range_nat_r1 : 0 ≤ r1.toNat ∧ r1.toNat < 4294967296 := by omega
  have range_nat_r2 : 0 ≤ r2.toNat ∧ r2.toNat < 4294967296 := by omega
  by_cases usgn <;> simp_all [execute_DIV_REM_pure, execute_DIV_REM_pure_int, LeanRV64IM.Functions.not, LeanRV64IM.Functions.xlen, instHPowInt_leanRV64IM] <;>
  by_cases r2z : r2 = 0 <;> simp_all
  . simp [to_bits_truncate, Sail.get_slice_int]
  . repeat rw [ Bool.cond_neg (by rw [← BitVec.toNat_inj] at r2z; simp_all) ]
    trans BitVec.signExtend 64 (BitVec.ofInt 32 (r1.toNat / r2.toNat))
    . congr
      simp [to_bits_truncate, Sail.get_slice_int]
      simp [BitVec.ofNat, BitVec.ofInt]; congr
      rw [Int.emod_eq_of_lt]
      . trans (@Nat.cast ℤ instNatCastInt (r1.toNat / r2.toNat)).toNat
        . simp
        . rw [Int.toNat_natCast]
      . apply Int.zero_le_ofNat
      . have := @Int.ediv_le_self r1.toNat r2.toNat (by omega)
        omega
    . congr
  . simp [to_bits_truncate, Sail.get_slice_int]
  . repeat rw [ Bool.cond_neg (b := r2.toInt == 0) (by rw [← BitVec.toInt_inj] at r2z; simp_all) ]
    by_cases of : 2147483648 ≤ r1.toInt.tdiv r2.toInt <;>
    have of' := divw_overflow range_int_r1 range_int_r2 <;>
    simp_all [to_bits_truncate, Sail.get_slice_int, -not_and]
    repeat rw [ Bool.cond_neg (by simp; omega )]
    have : BitVec.ofNat 32 (r1.toInt.tdiv r2.toInt % 8589934592).toNat = BitVec.ofInt 32 (r1.toInt.tdiv r2.toInt) := by
      simp [BitVec.ofNat, BitVec.ofInt]
      congr; simp [Fin.ext_iff]
      omega
    rw [this, BitVec.signExtend_ofInt ?_ of']
    . by_contra hlt; simp at hlt
      have sgn : (r1.toInt.tdiv r2.toInt).sign = -1 := by rw [Int.sign_cases, if_pos (by omega)]
      rw [Int.sign_tdiv, Int.sign_cases, Int.sign_cases] at sgn
      split_ifs at sgn <;> simp_all
      . have hlt : ((-r1.toInt).tdiv (-r2.toInt) < -2147483648) := by simpa
        rw [Int.tdiv_eq_ediv_of_nonneg (by omega)] at hlt; simp_all
        by_cases eq_one : r2.toInt = 1
        . simp [eq_one] at *
          omega
        . have := @Int.ediv_lt_self_of_pos_of_ne_one (-r1.toInt) r2.toInt (by omega) eq_one
          omega
      . rw [Int.tdiv_eq_ediv_of_nonneg (by assumption)] at hlt
        suffices hneg : 2147483648 < r1.toInt / (-r2.toInt)
        . have hgt : (-r2.toInt > 0) := by omega
          set r2 := -r2.toInt
          by_cases eq_one : r2 = 1
          . simp [eq_one] at *
            omega
          . have := @Int.ediv_lt_self_of_pos_of_ne_one r1.toInt r2 (by omega) eq_one
            omega
        . simp; omega

@[simp]
lemma execute_REM'_eq_execute_REM :
  execute_REM rs2 rs1 rd usgn = execute_REM' rs2 rs1 rd usgn := by
  simp_all [execute_REM, execute_REM']
  refine bind_congr ?_; intro r1
  refine bind_congr ?_; intro r2
  ext s; simp_all; congr
  have range_int_r1 : -9223372036854775808 ≤ r1.toInt ∧ r1.toInt < 9223372036854775808 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
  have range_int_r2 : -9223372036854775808 ≤ r2.toInt ∧ r2.toInt < 9223372036854775808 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
  have range_nat_r1 : 0 ≤ r1.toNat ∧ r1.toNat < 18446744073709551616 := by omega
  have range_nat_r2 : 0 ≤ r2.toNat ∧ r2.toNat < 18446744073709551616 := by omega
  by_cases usgn <;> simp_all [execute_DIV_REM_pure, execute_DIV_REM_pure_int, LeanRV64IM.Functions.not, LeanRV64IM.Functions.xlen, instHPowInt_leanRV64IM] <;>
  by_cases r2z : r2 = 0 <;> simp_all
  . simp [to_bits_truncate, Sail.get_slice_int]
    rw [Nat.mod_eq_of_lt (by omega)]; simp
  . repeat rw [ Bool.cond_neg (by rw [← BitVec.toNat_inj] at r2z; simp_all) ]
    rw [← BitVec.toNat_inj]
    simp [to_bits_truncate, Sail.get_slice_int]
    congr; rw [Int.emod_eq_of_lt]
    . apply Int.zero_le_ofNat
    . rw [Int.tmod_eq_emod_of_nonneg (by omega)]
      trans (r2.toNat : ℤ)
      . simp [← BitVec.toNat_inj] at r2z
        apply Int.emod_lt_of_pos r1.toNat (by omega)
      . omega
  . simp [to_bits_truncate, Sail.get_slice_int]
    simp [← BitVec.toNat_inj]
    have mod_65_to_64 : forall (a : ℤ), (a % 36893488147419103232).toNat % 18446744073709551616 = (a % 18446744073709551616).toNat := by omega
    simp [mod_65_to_64, BitVec.toInt]
    split_ifs with hneg <;> [ skip; simp ] <;> rw [Int.emod_eq_of_lt (by omega)] <;> simp <;> omega
  . repeat rw [ Bool.cond_neg (b := r2.toInt == 0) (by rw [← BitVec.toInt_inj] at r2z; simp_all) ]
    simp_all [to_bits_truncate, Sail.get_slice_int]
    simp [BitVec.ofNat, BitVec.ofInt]
    congr; simp [Fin.ext_iff]
    omega

@[simp]
lemma execute_REMW'_eq_execute_REMW :
  execute_REMW rs2 rs1 rd usgn = execute_REMW' rs2 rs1 rd usgn := by
  simp_all [execute_REMW, execute_REMW', execute_DIV_REM_pure, execute_DIV_REM_pure_int, -BitVec.extractLsb, -BitVec.extractLsb_toNat, -BitVec.toInt_extractLsb]
  refine bind_congr ?_; intro r1
  refine bind_congr ?_; intro r2
  set r1 := BitVec.extractLsb 31 0 r1
  set r2 := BitVec.extractLsb 31 0 r2
  ext s; simp_all; congr
  have range_int_r1 : -2147483648 ≤ r1.toInt ∧ r1.toInt < 2147483648 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
  have range_int_r2 : -2147483648 ≤ r2.toInt ∧ r2.toInt < 2147483648 := by constructor <;> [ apply BitVec.le_toInt; apply BitVec.toInt_lt ]
  have range_nat_r1 : 0 ≤ r1.toNat ∧ r1.toNat < 4294967296 := by omega
  have range_nat_r2 : 0 ≤ r2.toNat ∧ r2.toNat < 4294967296 := by omega
  by_cases usgn <;> simp_all [execute_DIV_REM_pure, execute_DIV_REM_pure_int, LeanRV64IM.Functions.not, LeanRV64IM.Functions.xlen, instHPowInt_leanRV64IM] <;>
  by_cases r2z : r2 = 0 <;> simp_all
  . simp [to_bits_truncate, Sail.get_slice_int]
    rw [Nat.mod_eq_of_lt (by omega)]; simp
  . repeat rw [ Bool.cond_neg (by rw [← BitVec.toNat_inj] at r2z; simp_all) ]
    trans BitVec.signExtend 64 (BitVec.ofInt 32 (r1.toNat % r2.toNat))
    . congr
      simp [to_bits_truncate, Sail.get_slice_int]
      simp [BitVec.ofNat, BitVec.ofInt]; congr
      rw [Int.emod_eq_of_lt]
      . rw [Int.tmod_eq_emod_of_nonneg (by omega)]; simp; omega
      . apply Int.zero_le_ofNat
      . rw [Int.tmod_eq_emod_of_nonneg (by omega)]
        trans (r2.toNat : ℤ)
        . simp [← BitVec.toNat_inj] at r2z
          apply Int.emod_lt_of_pos r1.toNat (by omega)
        . omega
    . congr
  . suffices : to_bits_truncate r1.toInt = r1
    . simp [this]
      simp [← BitVec.toInt_inj]
      rw [BitVec.toInt_signExtend_of_le (by simp)]
      simp [BitVec.toInt, Int.bmod_def]
      split_ifs <;> omega
    . simp [to_bits_truncate, Sail.get_slice_int]
      simp [← BitVec.toNat_inj]
      have mod_33_to_32 : forall (a : ℤ), (a % 8589934592).toNat % 4294967296 = (a % 4294967296).toNat := by omega
      simp [mod_33_to_32, BitVec.toInt]
      split_ifs with hneg <;> [ skip; simp ] <;> rw [Int.emod_eq_of_lt (by omega)] <;> simp <;> omega
  . repeat rw [ Bool.cond_neg (b := r2.toInt == 0) (by rw [← BitVec.toInt_inj] at r2z; simp_all) ]
    have : to_bits_truncate (r1.toInt.tmod r2.toInt) = BitVec.ofInt 32 (r1.toInt.tmod r2.toInt) := by
      simp [to_bits_truncate, Sail.get_slice_int]
      simp [BitVec.ofNat, BitVec.ofInt]
      congr; simp [Fin.ext_iff]
      omega
    rw [this, BitVec.signExtend_ofInt]
    . by_contra hlt; simp at hlt
      have sgn : (r1.toInt.tmod r2.toInt).sign = -1 := by rw [Int.sign_cases, if_pos (by omega)]
      rw [Int.sign_tmod, Int.sign_cases] at sgn
      split_ifs at sgn
      . apply (Int.split_nzp r2.toInt) <;> intro h <;> simp_all
        . have : 2147483648 < (-r1.toInt).tmod (-r2.toInt) := by simp; omega
          have := @Int.tmod_lt_of_pos (-r1.toInt) (-r2.toInt) (by omega)
          omega
        . omega
        . have : 2147483648 < (-r1.toInt).tmod r2.toInt := by simp; omega
          have := @Int.tmod_lt_of_pos (-r1.toInt) r2.toInt (by omega)
          omega
    . apply (Int.split_nzp r2.toInt) <;> intro h <;> simp_all
      . have := @Int.tmod_lt_of_pos r1.toInt (-r2.toInt) (by omega)
        simp_all; omega
      . have := @Int.tmod_lt_of_pos r1.toInt r2.toInt (by omega)
        omega

end DIV_REM

end execution
