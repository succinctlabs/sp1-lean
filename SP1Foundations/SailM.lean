import SP1Foundations.BitVec
import SP1Foundations.Misc
import SP1Foundations.Register
import SP1Foundations.Word

open LeanRV64IM.Functions

-- /-- Axiom that the `misa` register is always zero. -/
-- axiom SailState.sp1_no_misa : ∀s : SailState, s.regs.get? Register.misa = some 0

-- -- dt: would be safer if we made this a hypothesis about specific states.
-- example (s : SailState) : False := by
--   let s' := {s with regs := s.regs.insert Register.misa 1}
--   have := SailState.sp1_no_misa s'
--   suffices : (0 : RegisterType Register.misa) = 1
--   · simp at this
--   simp [s'] at this

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
def get_reg? (s : SailState) (idx : BitVec 5) : Option (BitVec 64) :=
  if idx = 0 then some 0 else reg_idx_must_64 idx ▸ s.regs.get? (reg_idx_to_Register idx)

lemma get_reg?_insert_of_ne (idx : BitVec 5)
    (h : reg ≠ reg_idx_to_Register idx) :
    SailState.get_reg? { s with regs := s.regs.insert reg v } idx =
      SailState.get_reg? s idx := by
  simp [SailState.get_reg?]
  split_ifs
  rfl
  congr 1
  rw [Std.ExtDHashMap.get?_insert]
  simp [h]

-- dt: this might be dangerous because it introduces the casting here...
@[simp]
lemma get_reg?_insert_self (idx : BitVec 5) (s : SailState)
    (v : RegisterType (reg_idx_to_Register idx)) :
    let reg := reg_idx_to_Register idx
    SailState.get_reg? {s with regs := s.regs.insert reg v} idx =
      if idx = 0#5 then some 0 else reg_idx_must_64 idx ▸ some v := by
  simp [SailState.get_reg?]

@[simp]
lemma get_reg?_insert_nextPC (idx : BitVec 5) :
    SailState.get_reg? {s with regs := s.regs.insert Register.nextPC v} idx =
      SailState.get_reg? s idx := by
  rw [get_reg?_insert_of_ne]; simp [nextPC_ne_reg_idx_toRegister]

@[simp]
lemma get_reg?_insert_PC (idx : BitVec 5) :
    SailState.get_reg? {s with regs := s.regs.insert Register.PC v} idx =
      SailState.get_reg? s idx := by
  rw [get_reg?_insert_of_ne]; simp [PC_ne_reg_idx_toRegister]

end get_reg?

end SailState

namespace Sail

-- dt: This seems usually useful for simp, but low priority to be safe (could remove tag entirely)
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
  if idx != 0#5 then modify fun s =>
    { s with regs := s.regs.insert reg (reg_idx_must_64 idx ▸ val) }
  else if val ≠ 0#64 then throw Sail.Error.Unreachable

@[simp]
lemma run_write_reg (idx : BitVec 5) (val : BitVec 64) :
    (write_reg idx val).run s =
      let reg : Register := reg_idx_to_Register idx
      if idx = 0#5 then if val = 0#64 then .ok () s else .error Sail.Error.Unreachable s
        else .ok () { s with regs := s.regs.insert reg (reg_idx_must_64 idx ▸ val) } := by
  unfold write_reg; aesop

@[simp]
lemma write_reg_write_reg_self (idx : BitVec 5) (val val' : BitVec 64) :
    (do write_reg idx val; write_reg idx val') =
      if idx = 0#5 ∧ val ≠ 0#64 then throw .Unreachable else write_reg idx val' := by
  refine EStateM.ext fun s => ?_
  by_cases hidx : idx = 0#5
  · simp [hidx]
    by_cases hval : val = 0#64
    · simp [hval, run_write_reg]
    · simp [hval, run_write_reg]
  · simp [hidx, run_write_reg]

/-- Swap writes to two distinct registers, assuming only `0#5` written to the `0` register. -/
lemma write_reg_write_reg_comm (idx idx' : BitVec 5) (val val' : BitVec 64)
    (h : idx ≠ idx') (hval : idx = 0#5 → val = 0#5) (hval' : idx' = 0#5 → val' = 0#5) :
    (do write_reg idx val; write_reg idx' val') =
      (do write_reg idx' val'; write_reg idx val) := by
  refine EStateM.ext fun s => ?_
  by_cases hidx : idx = 0#5
  · by_cases hidx' : idx' = 0#5
    · refine (h (hidx.trans hidx'.symm)).elim
    · simp [hidx, hidx', hval hidx, run_write_reg]
  · by_cases hidx' : idx' = 0#5
    · simp [hidx, hidx', hval' hidx', run_write_reg]
    · simp [hidx', hidx, run_write_reg]
      rw [Std.ExtDHashMap.insert_insert_comm]
      simp [h, hidx, hidx', regidxToRegister_inj]

end write_reg

section write_reg'

/-- Version of `write_reg` that doesn't throw an error writing to the `0` register.
This matches more closely with the behavior of `wX_bits` -/
def write_reg' (idx : BitVec 5) (val : BitVec 64) : SailM Unit :=
  do if idx != 0#5 then modify fun s =>
    { s with regs := s.regs.insert (reg_idx_to_Register idx) (reg_idx_must_64 idx ▸ val) }

@[simp]
lemma run_write_reg' (idx : BitVec 5) (val : BitVec 64) :
    (write_reg' idx val).run s =
      let reg : Register := reg_idx_to_Register idx
      .ok () (if idx = 0#5 then s
        else { s with regs := s.regs.insert reg (reg_idx_must_64 idx ▸ val) }) := by
  unfold write_reg'; aesop

/-- `write_reg` and `write_reg'` align if not the `0` index of the value written is `0`. -/
lemma write_reg_eq_write_reg' (idx : BitVec 5) (val : BitVec 64) (h : idx ≠ 0#5 ∨ val = 0#64) :
    write_reg idx val = write_reg' idx val := by
  unfold write_reg write_reg'; aesop

lemma write_reg'_write_reg'_self (idx : BitVec 5) (val val' : BitVec 64) :
    (do write_reg' idx val; write_reg' idx val') = write_reg' idx val' := by
  refine EStateM.ext fun s => ?_
  by_cases hidx : idx = 0#5
  · simp [hidx, run_write_reg']
  · simp [hidx, run_write_reg']

/-- Swap writes to two distinct registers. -/
lemma write_reg'_write_reg'_comm (idx idx' : BitVec 5) (val val' : BitVec 64) (h : idx ≠ idx') :
    (do write_reg' idx val; write_reg' idx' val') =
      (do write_reg' idx' val'; write_reg' idx val) := by
  refine EStateM.ext fun s => ?_
  by_cases hidx : idx = 0#5
  · by_cases hidx' : idx' = 0#5 <;> simp [hidx, hidx', run_write_reg']
  · by_cases hidx' : idx' = 0#5
    · simp [hidx, hidx', run_write_reg']
    · simp [hidx', hidx, run_write_reg']
      rw [Std.ExtDHashMap.insert_insert_comm]
      simp [h, hidx, hidx', regidxToRegister_inj]

end write_reg'

section writeReg

@[simp]
lemma run_writeReg (reg : Register) (v : RegisterType reg) :
    (Sail.writeReg reg v).run s =
      .ok PUnit.unit { s with regs := s.regs.insert reg v} := rfl

lemma run_writeReg_bind (reg : Register) (v : RegisterType reg) (mx : Unit → SailM α) :
    (Sail.writeReg reg v >>= mx).run s =
      (mx ()).run {s with regs := s.regs.insert reg v} := by simp [run_writeReg]

@[simp]
lemma writeReg_writeReg_self (reg : Register) (v v' : RegisterType reg) :
    (do Sail.writeReg reg v; Sail.writeReg reg v') = Sail.writeReg reg v' := by
  simp [PreSail.writeReg]
  refine congr_arg modify ?_
  ext s
  cases s
  simp

/-- Swap writes to two different registers. -/
lemma writeReg_writeReg_comm (reg reg' : Register) (v : RegisterType reg)
    (v' : RegisterType reg') (h : reg ≠ reg') :
    (do Sail.writeReg reg v; Sail.writeReg reg' v') =
      (do Sail.writeReg reg' v'; Sail.writeReg reg v) := by
  refine EStateM.ext fun s => ?_
  simp [run_writeReg]
  rwa [Std.ExtDHashMap.insert_insert_comm]

end writeReg

section readReg

-- dt: why does simp not choose to apply this when it can?
@[simp]
lemma run_readReg (s : SailState) (reg : Register) :
    (Sail.readReg reg).run s = match s.regs.get? reg with
    | some v => .ok v s
    | none => .error Sail.Error.Unreachable s := by
  simp [Sail.readReg, PreSail.readReg]
  cases s.regs.get? reg with
  | some v => rfl
  | none => rfl

-- @[simp high] -- Prefer this over reducing on bind
lemma run_readReg_bind (reg : Register) (mx : RegisterType reg → SailM α) :
    (Sail.readReg reg >>= mx).run s = match s.regs.get? reg with
    | some v => (mx v).run s
    | none => (throw Sail.Error.Unreachable : SailM _).run s := by
  simp [run_readReg]
  cases s.regs.get? reg with | some v => rfl | none => rfl

lemma run_readReg_insert_of_ne (s : SailState) (reg reg' : Register) (h : reg ≠ reg')
    (v : RegisterType reg) : (Sail.readReg reg').run { s with regs := s.regs.insert reg v} =
      match s.regs.get? reg' with
      | some w => .ok w { s with regs := s.regs.insert reg v }
      | none => .error .Unreachable { s with regs := s.regs.insert reg v } := by
  simp [run_readReg, Std.ExtDHashMap.get?_insert, h]

@[simp]
lemma run_readReg_insert_self (s : SailState) (reg : Register) (v : RegisterType reg) :
    (Sail.readReg reg).run { s with regs := s.regs.insert reg v } =
      .ok v { s with regs := s.regs.insert reg v } := by
  simp only [run_readReg, Std.ExtDHashMap.get?_insert_self]

@[simp]
lemma map_const_run_readReg (reg : Register) (x : α)
    (h : (s.regs.get? reg).isSome) :
    ((Sail.readReg reg).run s).map (fun _ => x) = .ok x s := by
  rw [Option.isSome_iff_exists] at h
  obtain ⟨y, hy⟩ := h
  simp [hy, run_readReg]

lemma readReg_bind_bind_duplicate (reg : Register)
    (mx : RegisterType reg → SailM α) (my : RegisterType reg → α → SailM β) :
    (do let v ← Sail.readReg reg; let x ← mx v; my v x) =
      (do let v ← Sail.readReg reg; let v' ← Sail.readReg reg; let x ← mx v; my v' x) := by
  simpM
  refine EStateM.ext ?_
  unfold EStateM.bind EStateM.run
  simp; intro s
  rcases h_eq : (Sail.readReg reg s) with ⟨ mx', s' ⟩ <;> simp_all
  suffices : s = s'
  . simp_all
  . simp [Sail.readReg, PreSail.readReg, bind, EStateM.instMonad, EStateM.bind] at h_eq
    split at h_eq <;> [ subst_eqs; trivial ]
    rcases h_hmap_get : (s.regs.get?) reg <;> simp_all <;> [ trivial; skip ]
    obtain ⟨ _, _ ⟩ := h_eq; rfl

end readReg

section rX_bits

lemma rX_bits_eq_get_reg? {s : SailState} (idx : BitVec 5) :
    (rX_bits (regidx.Regidx idx)).run s = (s.get_reg? idx).toSailM.run s := by
    fin_cases idx
    · simp
      congr
    all_goals
      simp [Option.toSailM, SailState.get_reg?] at *
      simp [reg_idx_to_Register, Option.elim]
      simp [rX_bits, rX, Sail.readReg, PreSail.readReg, regval_from_reg]
      simpM
      match s.regs.get? _ with
      | none => rfl
      | some _ => rfl

@[simp]
lemma run_rX_bits (idx : BitVec 5) :
    (rX_bits (.Regidx idx)).run s =
    match SailState.get_reg? s idx with
    | some v => .ok v s
    | none => .error Sail.Error.Unreachable s := by
  rw [rX_bits_eq_get_reg?]
  simp [Option.toSailM, Option.elim]
  cases SailState.get_reg? s idx with
  | some v => rfl
  | none => rfl

-- problems with equality substitution again here
-- lemma rX_bits_eq_readReg (idx : BitVec 5) :
--     (rX_bits (.Regidx idx)) = if idx = 0#5 then pure 0#64
--       else regidxValToBitVec idx <$> Sail.readReg (reg_idx_to_Register idx) := by
--   refine EStateM.ext fun s => ?_
--   by_cases hidx : idx = 0#5
--   · simp [hidx, SailState.get_reg?]
--   · simp [hidx, SailState.get_reg?]
--     cases s.regs.get? (reg_idx_to_Register idx) with
--     | none => sorry
--     | some v => sorry

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

@[simp]
lemma run_wX_bits (reg : regidx) (data : BitVec 64) :
    (wX_bits reg data).run s = let .Regidx idx := reg
      .ok () (if idx = 0#5 then s else {s with
        regs := s.regs.insert (reg_idx_to_Register idx) (bitVecToRegidxVal idx data)}) := by
  unfold bitVecToRegidxVal
  simp [wX_bits, wX]
  let .Regidx idx := reg
  fin_cases idx
  · simp
  all_goals {
    simp [xreg_write_callback, reg_name_forwards, get_config_use_abi_names,
      LeanRV64IM.Functions.not]
    rfl
  }

@[simp]
lemma wX_bits_eq_writeReg (idx : BitVec 5) (val : BitVec 64) :
    wX_bits (.Regidx idx) val = if idx = 0#5 then pure () else
      Sail.writeReg (reg_idx_to_Register idx) (bitVecToRegidxVal idx val) := by
  refine EStateM.ext fun s => ?_
  by_cases hidx : idx = 0#5
  · simp [run_wX_bits, hidx]
  · simp [run_wX_bits, hidx, run_writeReg]

end wX_bits

@[simp]
lemma run_bool_bit_backwards (b : BitVec 1) :
    (bool_bit_backwards b).run s = match b with
    | 1#1 => .ok true s
    | 0#1 => .ok false s := by
  simp [bool_bit_backwards]
  fin_cases b <;> rfl

@[simp]
lemma run_bit_to_bool (b : BitVec 1) :
    (bit_to_bool b).run s = match b with
    | 1#1 => .ok true s
    | 0#1 => .ok false s := by
  fin_cases b <;> rfl

section write_read_bind

/-- Reading a just written value looks like just using the written value. -/
@[simp]
lemma writeReg_readReg_bind (reg : Register) (v : RegisterType reg)
    (mx : RegisterType reg → SailM α) :
    (do Sail.writeReg reg v; let w ← Sail.readReg reg; mx w) =
      (do Sail.writeReg reg v; mx v) := by
  refine EStateM.ext fun s => ?_
  simp [run_writeReg, regidxToRegister_inj, run_readReg]

-- dt: Lemmas that mix things like this are maybe less useful because of eq-subst / casts
-- @[simp] lemma write_reg_readReg_bind (idx : BitVec 5) (v : BitVec 64)
--     (mx : BitVec 64 → SailM α) :
--     (do write_reg idx v; let w ← Sail.readReg (reg_idx_to_Register idx); mx w) =
--       (do write_reg idx v; mx v) := by
--   sorry

-- @[simp] lemma write_reg_readReg_bind  (idx : BitVec 5) (data : BitVec 64)
--     (mx : RegisterType reg → SailM α) :
--     (do write_reg idx data; let w ← Sail.readReg (reg_idx_to_Register idx); mx w) =
--       (do write_reg idx data; mx data)

end write_read_bind

@[simp]
lemma writeReg_bind_map_readReg (reg : Register) (v : RegisterType reg)
    (f : RegisterType reg → α) :
    (do Sail.writeReg reg v; f <$> Sail.readReg reg) =
      (do Sail.writeReg reg v; return f v) := by
  rw [map_eq_bind_pure_comp, writeReg_readReg_bind, Function.comp_def]

/-- Writing a value overwrites the previous write. -/
@[simp]
lemma writeReg_wX_bits_writeReg (reg : Register) (v : RegisterType reg)
    (v' : RegisterType reg)
    (typ_0 : regidx) (data : BitVec 64) :
    (do Sail.writeReg reg v; wX_bits typ_0 data; Sail.writeReg reg v') =
      (do wX_bits typ_0 data; Sail.writeReg reg v') := by
  let .Regidx i : regidx := typ_0
  rw [wX_bits_eq_write_reg']
  rw [write_reg']
  by_cases hi : i = 0#5
  · cases hi
    simp [writeReg_writeReg_self]
  · simp [hi, Sail.writeReg, PreSail.writeReg]
    refine congr_arg modify ?_
    ext s
    simp

section pc

@[simp] lemma set_next_pc_eq (pc : BitVec 64) :
    set_next_pc pc = Sail.writeReg Register.nextPC pc := rfl

@[simp] lemma get_next_pc_eq (u : Unit) :
    get_next_pc u = Sail.readReg Register.nextPC := rfl

@[simp] lemma tick_pc_eq (u : Unit) :
    tick_pc u = (do Sail.writeReg Register.PC (← Sail.readReg Register.nextPC)) := by
  unfold tick_pc
  simp [pc_write_callback, writeReg_bind_map_readReg]

@[simp] lemma force_pc_eq (pc : BitVec 64) :
    force_pc pc = Sail.writeReg Register.PC pc := rfl

end pc

end Sail

end sailboats

section execution

open PreSail
open LeanRV64IM.Functions

@[simp]
lemma bool_bits_forwards_to_if (b : Bool) : bool_bits_forwards b = if b then 1#1 else 0#1 := by aesop

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

/-- `execute_RTYPE` pure part for `ByteWord` arguments -/
@[simp] def execute_RTYPE_pure_bw (op1 : ByteWord (Fin BB)) (op2 : ByteWord (Fin BB)) (op : rop) :=
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

lemma exec_RTYPE_pure_bv_to_bw (op1 : ByteWord (Fin BB)) (op2 : ByteWord (Fin BB)) (op : rop) :
  op1.isU64 → op2.isU64 →
  execute_RTYPE_pure op1.toBitVec64 op2.toBitVec64 op = execute_RTYPE_pure_bw op1 op2 op := by
  intro h_op1_isU64 h_op2_isU64
  cases op <;> simp [execute_RTYPE_pure, LeanRV64IM.Functions.log2_xlen]
  . rw [Sail.shift_bits_left]
    simp [ByteWord.toBitVec64_toNat h_op2_isU64]
  . simp [zopz0zI_s, bool_to_bits]
    repeat rw [ByteWord.toBitVec64_toInt (by assumption)]
    aesop
  . simp [zopz0zI_u, bool_to_bits]
    repeat rw [ByteWord.toBitVec64_toNat (by assumption)]
    aesop
  . rw [Sail.shift_bits_right]
    simp [ByteWord.toBitVec64_toNat h_op2_isU64]
  . have mod_lt_63 : (63 + (op2.toNat : ℤ) % 64).toNat = 63 + op2.toNat % 64 := by omega
    have mod_lt_64 : (64 + (op2.toNat : ℤ) % 64).toNat = 64 + op2.toNat % 64 := by omega
    simp [shift_bits_right_arith, shift_right_arith]
    rw [BitVec.toNat_setWidth, ByteWord.toBitVec64_toNat (by assumption)]
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

/-- `execute_RTYPEW` pure part - 32-bit for `HalfWord` arguments -/
@[simp] def execute_RTYPEW_pure_32_w (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : ropw) :=
  let op1 := op1.low32
  let op2 := op2.low32
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
  . apply Word.setWidth_eq_low32 op1 h_op1_isU64
  . apply Word.setWidth_eq_low32 op2 h_op2_isU64
  . apply Word.setWidth_eq_low32 op1 h_op1_isU64
  . apply Word.setWidth_eq_low32 op2 h_op2_isU64
  . rw [Sail.shift_bits_left]
    simp [Word.toBitVec64_toNat h_op2_isU64]
    rw [Word.setWidth_eq_low32 op1 h_op1_isU64]
    congr 1
    simp [Word.toNat, Word.low32, HalfWord.toBitVec32, HalfWord.toNat]
    omega
  . rw [Sail.shift_bits_right]
    simp [Word.toBitVec64_toNat h_op2_isU64]
    rw [Word.setWidth_eq_low32 op1 h_op1_isU64]
    congr 1
    simp [Word.toNat, Word.low32, HalfWord.toBitVec32, HalfWord.toNat]
    omega
  . have mod_lt_31: forall x : ℕ, (31 + (x : ℤ) % 32).toNat = 31 + x % 32 := by omega
    have mod_lt_32 : forall x : ℕ, (32 + (x : ℤ) % 32).toNat = 32 + x % 32 := by omega
    rw [Word.setWidth_eq_low32 _ h_op1_isU64]
    simp [bitVec_sshiftright_eq]
    simp [shift_bits_right_arith, shift_right_arith]
    (repeat rw [bitVec_ofNat_toNat]); simp
    have : op2.toBitVec64.toNat % 4294967296 % 32 = op2.toBitVec64.toNat % 32 := by omega
    rw [this]
    have : (op2.toBitVec64.toNat : ℤ) % 4294967296 % 32 = op2.toBitVec64.toNat % 32 := by omega
    rw [this, mod_lt_31, mod_lt_32]; simp
    have : op2.toBitVec64.toNat % 32 = op2.low32.toBitVec32.toNat % 32 := by
      simp [Word.toBitVec64, Word.toNat, Word.low32, HalfWord.toBitVec32, HalfWord.toNat]
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
    simp_all [execute_RTYPEW, execute_RTYPEW']
    refine bind_congr ?_; intro r1
    refine bind_congr ?_; intro r2
    simpM; ext s
    simp [Sail.run_wX_bits]
    split_ifs <;> [ rfl; (congr <;> ext s) ] <;>
    simp_all <;> congr <;> simp [← BitVec.toNat_inj]

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

/-- `execute_ITYPE` pure part for `ByteWord` arguments -/
def execute_ITYPE_pure_bw (op1 : ByteWord (Fin BB)) (op2 : ByteWord (Fin BB)) (op : iop) :=
  execute_RTYPE_pure_bw op1 op2 (rop_of_iop op)

lemma exec_ITYPE_pure_bv_to_w (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : iop) :
  op1.isU64 → op2.isU64 →
  execute_ITYPE_pure op1.toBitVec64 op2.toBitVec64 op = execute_ITYPE_pure_w op1 op2 op := by
  intro h_op1_isU64 h_op2_isU64
  simp [execute_ITYPE_pure_w, execute_ITYPE_pure]
  cases op <;> simp <;> exact exec_RTYPE_pure_bv_to_w _ _ _ h_op1_isU64 h_op2_isU64

lemma exec_ITYPE_pure_bv_to_bw (op1 : ByteWord (Fin BB)) (op2 : ByteWord (Fin BB)) (op : iop) :
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
    refine bind_congr ?_; intro r1
    simpM; ext s
    simp [Sail.run_wX_bits]
    split_ifs <;> [ rfl; (congr; bv_decide) ]

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
inductive mop where | MUL | MULH | MULHU | MULHSU
  deriving BEq, DecidableEq, Inhabited, Repr

def mul_op_of_mop (m : mop) : mul_op :=
  match m with
  | .MUL => { high := false, signed_rs1 := false, signed_rs2 := false }
  | .MULH => { high := true, signed_rs1 := true, signed_rs2 := true }
  | .MULHU => { high := true, signed_rs1 := false, signed_rs2 := false }
  | .MULHSU => { high := true, signed_rs1 := true, signed_rs2 := false }

/-- execute_MUL pure part -/
def execute_MUL_pure (op1 : BitVec 64) (op2 : BitVec 64) (m : mop) : BitVec 64 :=
  let rs1_int := if (m = .MULH ∨ m = .MULHSU ) then (BitVec.toInt op1) else (BitVec.toNat op1)
  let rs2_int := if (m = .MULH) then (BitVec.toInt op2) else (BitVec.toNat op2)
  let result_wide := (to_bits_truncate (l := (2 *i LeanRV64IM.Functions.xlen)) (rs1_int *i rs2_int))
  (if (m = .MUL)
    then (Sail.BitVec.extractLsb result_wide (LeanRV64IM.Functions.xlen -i 1) 0)
    else (Sail.BitVec.extractLsb result_wide ((2 *i LeanRV64IM.Functions.xlen) -i 1) LeanRV64IM.Functions.xlen))

def execute_MUL' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (m : mop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_MUL_pure rs1_bits rs2_bits m))
  (pure RETIRE_SUCCESS)

@[simp]
lemma execute_MUL'_eq_execute_MUL :
  execute_MUL rs2 rs1 rd (mul_op_of_mop m) = execute_MUL' rs2 rs1 rd m
  := by cases m <;> simp_all [execute_MUL', execute_MUL, execute_MUL_pure, mul_op_of_mop, LeanRV64IM.Functions.xlen]

end MUL

end execution
