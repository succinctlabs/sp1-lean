import Mathlib
import LeanRV64IM.RiscvInstsEnd
import LeanRV64IM.Defs
import SP1Foundations.BitVec
import SP1Foundations.Word
import SP1Foundations.Misc

open LeanRV64IM.Functions

macro "simpM" : tactic => `(tactic| simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet])

instance : Fintype (BitVec n) where
  elems := Finset.image (BitVec.ofFin) Finset.univ
  complete := by
    intro x
    simp [Finset.mem_image]

section sailboats

@[simp] abbrev SailState := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

/-- Axiom that the `misa` register is always zero. -/
axiom SailState.sp1_no_misa : ∀s : SailState, s.regs.get? Register.misa = some 0

-- dt: would be safer if we made this a hypothesis about specific states.
example (s : SailState) : False := by
  let s' := {s with regs := s.regs.insert Register.misa 1}
  have := SailState.sp1_no_misa s'
  suffices : (0 : RegisterType Register.misa) = 1
  · simp at this
  simp [s'] at this

def reg_idx_to_Register (idx : BitVec 5) : Register :=
  match idx with
  | 1 => Register.x1
  | 2 => Register.x2
  | 3 => Register.x3
  | 4 => Register.x4
  | 5 => Register.x5
  | 6 => Register.x6
  | 7 => Register.x7
  | 8 => Register.x8
  | 9 => Register.x9
  | 10 => Register.x10
  | 11 => Register.x11
  | 12 => Register.x12
  | 13 => Register.x13
  | 14 => Register.x14
  | 15 => Register.x15
  | 16 => Register.x16
  | 17 => Register.x17
  | 18 => Register.x18
  | 19 => Register.x19
  | 20 => Register.x20
  | 21 => Register.x21
  | 22 => Register.x22
  | 23 => Register.x23
  | 24 => Register.x24
  | 25 => Register.x25
  | 26 => Register.x26
  | 27 => Register.x27
  | 28 => Register.x28
  | 29 => Register.x29
  | 30 => Register.x30
  | _ => Register.x31

theorem reg_idx_must_64
  (idx : BitVec 5) : RegisterType (reg_idx_to_Register idx) = BitVec 64 :=
  by
    simp [reg_idx_to_Register]
    split <;> rfl

def regno_to_Register (regno : regno) : Register :=
  let .Regno n := regno
  match n with
  | 1 => Register.x1
  | 2 => Register.x2
  | 3 => Register.x3
  | 4 => Register.x4
  | 5 => Register.x5
  | 6 => Register.x6
  | 7 => Register.x7
  | 8 => Register.x8
  | 9 => Register.x9
  | 10 => Register.x10
  | 11 => Register.x11
  | 12 => Register.x12
  | 13 => Register.x13
  | 14 => Register.x14
  | 15 => Register.x15
  | 16 => Register.x16
  | 17 => Register.x17
  | 18 => Register.x18
  | 19 => Register.x19
  | 20 => Register.x20
  | 21 => Register.x21
  | 22 => Register.x22
  | 23 => Register.x23
  | 24 => Register.x24
  | 25 => Register.x25
  | 26 => Register.x26
  | 27 => Register.x27
  | 28 => Register.x28
  | 29 => Register.x29
  | 30 => Register.x30
  | _ => Register.x31

instance : DecidableEq regidx | .Regidx v, .Regidx v' => by simp; infer_instance

@[simp] lemma set_next_pc_def (pc : BitVec 64) :
    set_next_pc pc = Sail.writeReg Register.nextPC pc := rfl

@[simp] lemma get_next_pc_def (u : Unit) :
    get_next_pc u = Sail.readReg Register.nextPC := rfl

section EStateM_run

@[simp] lemma run_writeReg (reg : Register) (v : RegisterType reg) :
    (Sail.writeReg reg v).run s =
      .ok PUnit.unit { s with regs := s.regs.insert reg v} := rfl

lemma run_writeReg_bind (reg : Register) (v : RegisterType reg) (mx : Unit → SailM α) :
    (Sail.writeReg reg v >>= mx).run s =
      (mx ()).run {s with regs := s.regs.insert reg v} := by simp

@[simp] lemma run_readReg (reg : Register) :
    (Sail.readReg reg).run s = match s.regs.get? reg with
    | some v => .ok v s
    | none => .error Sail.Error.Unreachable s := by
  simp [Sail.readReg, PreSail.readReg]
  cases s.regs.get? reg with
  | some v => rfl
  | none => rfl

-- Viewed differently by lean sometimes
@[simp] lemma run_readReg' (s : SailState) (reg : Register) :
    (Sail.readReg reg).run s = match s.regs.get? reg with
    | some v => .ok v s
    | none => .error Sail.Error.Unreachable s := by
  simp [Sail.readReg, PreSail.readReg]
  cases s.regs.get? reg with
  | some v => rfl
  | none => rfl

@[simp high] -- Prefer this over reducing on bind
lemma run_readReg_bind (reg : Register) (mx : RegisterType reg → SailM α) :
    (Sail.readReg reg >>= mx).run s = match s.regs.get? reg with
    | some v => (mx v).run s
    | none => (throw Sail.Error.Unreachable : SailM _).run s := by
  simp
  cases s.regs.get? reg with | some v => rfl | none => rfl

@[simp]
lemma run_wX_bits (reg : regidx) (data : BitVec 64) :
    (wX_bits reg data).run s =
      let .Regidx idx := reg
      .ok () (if reg.1 = 0 then s else
        {s with regs := s.regs.insert (reg_idx_to_Register idx) (reg_idx_must_64 idx ▸ data)}) := by
  simp [wX_bits, wX]
  let .Regidx idx := reg
  fin_cases idx
  · simp
  all_goals {
    simp [xreg_write_callback, reg_name_forwards, get_config_use_abi_names,
      LeanRV64IM.Functions.not]
    rfl
  }

@[simp] lemma run_bool_bit_backwards (b : BitVec 1) :
    (bool_bit_backwards b).run s = match b with
    | 1#1 => .ok true s
    | 0#1 => .ok false s := by
  simp [bool_bit_backwards]
  fin_cases b <;> rfl

end EStateM_run

-----------

/-- Reading a just written value looks like just using the written value. -/
@[simp]
theorem writeReg_readReg_bind {α : Type} (reg : Register) (v : RegisterType reg)
    (mx : RegisterType reg → SailM α) :
    (do Sail.writeReg reg v; let w ← Sail.readReg reg; mx w) =
      (do Sail.writeReg reg v; mx v) := by
  simp [Sail.writeReg, PreSail.writeReg, Sail.readReg, PreSail.readReg]
  have := LawfulMonadStateOf.modify_bind_get_bind_of_forall_eq
    (f := fun s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource =>
        { regs := s.regs.insert reg v, choiceState := s.choiceState, mem := s.mem, tags := s.tags,
          cycleCount := s.cycleCount, sailOutput := s.sailOutput })
    (g := fun x => x.regs.get? reg)
    (mx := fun x : Option (RegisterType reg) => do
        let w ← (match x with
        | some s => pure s
        | x => throw Sail.Error.Unreachable)
        mx w)
    (x := v)
    (by
      intro s
      simp only [Std.ExtDHashMap.get?_insert_self])
  simp only [bind_assoc] at this
  convert this
  · ext _ _ x3
    cases x3
    rfl
    rfl

open Sail (trivialChoiceSource Error)

def SailState.get_reg? (s : SailState) (idx : BitVec 5) : Option (BitVec 64) :=
  if idx = 0
  then some 0
  else
    by
      let reg : Register := reg_idx_to_Register idx
      rw [←reg_idx_must_64 idx]
      exact s.regs.get? reg

/-- Alternative to `write_reg` that takes a `BitVec` rather than an explicit `Register`. -/
def SailState.write_reg (idx : BitVec 5) (val : BitVec 64) : SailM Unit :=
  do
    let reg : Register := reg_idx_to_Register idx
    if idx != 0 then
      modify fun s =>
        { s with regs := s.regs.insert reg (by rw [reg_idx_must_64 idx]; exact val) }
    else if val ≠ 0 then
      throw Error.Unreachable

@[simp] lemma run_write_reg (idx : BitVec 5) (val : BitVec 64) :
    (SailState.write_reg idx val).run s =
      let reg : Register := reg_idx_to_Register idx
      if idx = 0 then if val = 0 then .ok () s else .error Error.Unreachable s
        else .ok () { s with regs := s.regs.insert reg (by
          rw [reg_idx_must_64 idx]
          exact val) } := by
  aesop (add safe (by dsimp [SailState.write_reg]))

def SailState.regidx_write (idx : BitVec 5) (val : BitVec 64) : SailM Unit :=
  do
    let reg : Register := reg_idx_to_Register idx
    if idx != 0 then
      modify fun s =>
        { s with regs := s.regs.insert reg (by rw [reg_idx_must_64 idx]; exact val) }

def Option.toSailM {α} (o : Option α) : SailM α :=
  o.elim (throw (by exact Error.Unreachable)) pure

theorem SailState.get_reg?_is_rX {s : SailState}
  (idx : BitVec 5)
  : (rX_bits (regidx.Regidx idx)) s = (s.get_reg? idx).toSailM s :=
  by
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
    (rX_bits (regidx.Regidx idx)).run s =
    match SailState.get_reg? s idx with
    | some v => .ok v s
    | none => .error Sail.Error.Unreachable s := by
  refine (SailState.get_reg?_is_rX idx).trans ?_
  simp [Option.toSailM, Option.elim]
  cases SailState.get_reg? s idx with
  | some v => rfl
  | none => rfl

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

lemma run_readReg_insert_of_ne
    (s : PreSail.SequentialState RegisterType trivialChoiceSource)
    (reg reg' : Register) (h : reg ≠ reg')
    (v : RegisterType reg) :
    (Sail.readReg reg').run { s with regs := s.regs.insert reg v} =
      match s.regs.get? reg' with
      | some w => .ok w { s with regs := s.regs.insert reg v }
      | none => .error .Unreachable { s with regs := s.regs.insert reg v } := by
  simp [Sail.readReg, Std.ExtDHashMap.get?_insert, h]

@[simp] lemma run_readReg_insert_self
    (s : PreSail.SequentialState RegisterType trivialChoiceSource)
    (reg : Register) (v : RegisterType reg) :
    (Sail.readReg reg).run { s with regs := s.regs.insert reg v } =
      .ok v { s with regs := s.regs.insert reg v } := by
  simp only [run_readReg, Std.ExtDHashMap.get?_insert_self]

@[simp] lemma map_const_run_readReg (reg : Register) (x : α)
    (h : (s.regs.get? reg).isSome) :
    ((Sail.readReg reg).run s).map (fun _ => x) = .ok x s := by
  rw [Option.isSome_iff_exists] at h
  obtain ⟨y, hy⟩ := h
  simp [hy]


theorem SailState.reg_idx_never_nextPC
  {idx : BitVec 5}
  : (Register.nextPC == reg_idx_to_Register idx) = false :=
  by
    simp [reg_idx_to_Register]
    split <;> trivial

@[simp] lemma get_reg?_insert_nextPC (idx : BitVec 5) :
    SailState.get_reg? { s with regs := s.regs.insert Register.nextPC v } idx =
      SailState.get_reg? s idx := by
  rw [get_reg?_insert_of_ne]
  simp [reg_idx_to_Register]
  split <;> trivial

lemma case_31 {val : BitVec 64} {s : SailState}
  : s.regs.insert (reg_idx_to_Register 31#5) val = s.regs.insert Register.x31 val :=
  by
    apply congrArg
    rfl

theorem SailState.wX_bits_is_regidx_write (idx : BitVec 5) (val : BitVec 64)
  : SailState.regidx_write idx val = wX_bits (.Regidx idx) val
  :=
  by
    simp [SailState.regidx_write, wX_bits]
    by_cases x_is_31 : idx = 31#5
    · rw [x_is_31]
      simp
      conv =>
        lhs
        arg 1
        intro s
        arg 1
        rw [case_31]
      simp [wX, Sail.writeReg, PreSail.writeReg, xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names, LeanRV64IM.Functions.not, regval_into_reg]
    fin_cases idx
    · simp [wX]
    all_goals
      simp [wX, Sail.writeReg, PreSail.writeReg, xreg_write_callback, xreg_full_write_callback, reg_name_forwards, get_config_use_abi_names, LeanRV64IM.Functions.not, regval_into_reg, reg_idx_to_Register]
    simp at x_is_31

--------------



@[simp]
theorem writeReg_writeReg (reg : Register) (v v' : RegisterType reg) :
    (do Sail.writeReg reg v; Sail.writeReg reg v') = Sail.writeReg reg v' := by
  simp [PreSail.writeReg]
  refine congr_arg modify ?_
  ext s
  cases s
  simp

/-- Writing a value overwrites the previous write.
dt: might need `typ_0` condition when proving this. -/
@[simp]
theorem writeReg_wX_bits_writeReg (reg : Register) (v : RegisterType reg)
    (v' : RegisterType reg)
    (typ_0 : regidx) (data : BitVec 64) :
    (do Sail.writeReg reg v; wX_bits typ_0 data; Sail.writeReg reg v') =
      (do wX_bits typ_0 data; Sail.writeReg reg v') := by
  let .Regidx i : regidx := typ_0
  rw [← SailState.wX_bits_is_regidx_write]
  rw [SailState.regidx_write]
  by_cases hi : i = 0#5
  · cases hi
    simp
  · simp [hi, Sail.writeReg, PreSail.writeReg]
    refine congr_arg modify ?_
    ext s
    simp

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
def execute_RTYPE_pure_w (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : rop) :=
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
def execute_RTYPE_pure_bw (op1 : ByteWord (Fin BB)) (op2 : ByteWord (Fin BB)) (op : rop) :=
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
  cases op <;> simp [execute_RTYPE_pure_w, execute_RTYPE_pure, LeanRV64IM.Functions.log2_xlen]
  . rw [Sail.shift_bits_left, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero]
    simp [Word.toNat_toBitVec64 _ h_op2_isU64]
  . simp [zopz0zI_s, bool_to_bits]
    repeat rw [Word.toInt_toBitVec64 _ (by assumption)]
    aesop
  . simp [zopz0zI_u, bool_to_bits]
    repeat rw [Word.toNat_toBitVec64 _ (by assumption)]
    aesop
  . rw [Sail.shift_bits_right, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero]
    simp [Word.toNat_toBitVec64 _ h_op2_isU64]
  . have mod_lt_63 : (63 + (op2.toNat : ℤ) % 64).toNat = 63 + op2.toNat % 64 := by omega
    have mod_lt_64 : (64 + (op2.toNat : ℤ) % 64).toNat = 64 + op2.toNat % 64 := by omega
    rw [shift_bits_right_arith, shift_right_arith, sign_extend]
    rw [Sail.BitVec.extractLsb, Sail.BitVec.signExtend]
    rw [BitVec.extractLsb_toNat]
    simp
    rw [Word.toNat_toBitVec64 _ (by assumption)]
    rw [mod_lt_63, mod_lt_64]
    symm; apply bitVec_sshiftright_eq

lemma exec_RTYPE_pure_bv_to_bw (op1 : ByteWord (Fin BB)) (op2 : ByteWord (Fin BB)) (op : rop) :
  op1.isU64 → op2.isU64 →
  execute_RTYPE_pure op1.toBitVec64 op2.toBitVec64 op = execute_RTYPE_pure_bw op1 op2 op := by
  intro h_op1_isU64 h_op2_isU64
  cases op <;> simp [execute_RTYPE_pure_bw, execute_RTYPE_pure, LeanRV64IM.Functions.log2_xlen]
  . rw [Sail.shift_bits_left, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero]
    simp [ByteWord.toNat_toBitVec64 _ h_op2_isU64]
  . simp [zopz0zI_s, bool_to_bits]
    repeat rw [ByteWord.toInt_toBitVec64 _ (by assumption)]
    aesop
  . simp [zopz0zI_u, bool_to_bits]
    repeat rw [ByteWord.toNat_toBitVec64 _ (by assumption)]
    aesop
  . rw [Sail.shift_bits_right, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero]
    simp [ByteWord.toNat_toBitVec64 _ h_op2_isU64]
  . have mod_lt_63 : (63 + (op2.toNat : ℤ) % 64).toNat = 63 + op2.toNat % 64 := by omega
    have mod_lt_64 : (64 + (op2.toNat : ℤ) % 64).toNat = 64 + op2.toNat % 64 := by omega
    simp [shift_bits_right_arith, shift_right_arith, sign_extend]
    rw [Sail.BitVec.extractLsb, Sail.BitVec.signExtend]
    rw [BitVec.extractLsb_toNat]
    simp
    rw [ByteWord.toNat_toBitVec64 _ (by assumption)]
    rw [mod_lt_63, mod_lt_64]
    symm; apply bitVec_sshiftright_eq

/-- `execute_RTYPE` with isolated pure part -/
def execute_RTYPE' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_RTYPE_pure rs1_bits rs2_bits op))
  (pure RETIRE_SUCCESS)

@[simp]
lemma execute_RTYPE_eq_execute_RTYPE' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : rop) :
  execute_RTYPE rs2 rs1 rd op = execute_RTYPE' rs2 rs1 rd op
  := by cases op <;> simp_all [execute_RTYPE', execute_RTYPE, execute_RTYPE_pure, LeanRV64IM.Functions.xlen]

end RTYPE

section RTYPEW

/-- `execute_RTYPEW` pure part -/
def execute_RTYPEW_pure (op1 : BitVec 64) (op2 : BitVec 64) (op : ropw) :=
  let op1 := BitVec.setWidth 32 op1
  let op2 := BitVec.setWidth 32 op2
  match op with
  | .ADDW => sign_extend (m := 64) (op1 + op2)
  | .SUBW => sign_extend (m := 64) (op1 - op2)
  | .SLLW => sign_extend (m := 64) (Sail.shift_bits_left op1 (Sail.BitVec.extractLsb op2 4 0))
  | .SRLW => sign_extend (m := 64) (Sail.shift_bits_right op1 (Sail.BitVec.extractLsb op2 4 0))
  | .SRAW => sign_extend (m := 64) (shift_bits_right_arith op1 (Sail.BitVec.extractLsb op2 4 0))

/-- `execute_RTYPEW` pure part for `Word arguments -/
def execute_RTYPEW_pure_w (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : ropw) :=
let op1 := op1.low32
let op2 := op2.low32
match op with
  | .ADDW => sign_extend (m := 64) (op1.toBitVec32 + op2.toBitVec32)
  | .SUBW => sign_extend (m := 64) (op1.toBitVec32 - op2.toBitVec32)
  | .SLLW => sign_extend (m := 64) (op1.toBitVec32 <<< (BitVec.setWidth 5 op2.toBitVec32))
  | .SRLW => sign_extend (m := 64) (op1.toBitVec32 >>> (BitVec.setWidth 5 op2.toBitVec32))
  | .SRAW => sign_extend (m := 64) (op1.toBitVec32.sshiftRight (BitVec.setWidth 5 op2.toBitVec32).toNat)

lemma exec_RTYPEW_pure_bv_to_w (op1 : Word (Fin BB)) (op2 : Word (Fin BB)) (op : ropw) :
  op1.isU64 → op2.isU64 →
  execute_RTYPEW_pure op1.toBitVec64 op2.toBitVec64 op = execute_RTYPEW_pure_w op1 op2 op := by
  intro h_op1_isU64 h_op2_isU64
  have ha' := Word.lt_cases_of_isU64 h_op1_isU64
  have hb' := Word.lt_cases_of_isU64 h_op2_isU64
  cases op <;> simp [execute_RTYPEW_pure_w, execute_RTYPEW_pure] <;> congr
  . apply Word.setWidth_eq_low32 op1 h_op1_isU64
  . apply Word.setWidth_eq_low32 op2 h_op2_isU64
  . apply Word.setWidth_eq_low32 op1 h_op1_isU64
  . apply Word.setWidth_eq_low32 op2 h_op2_isU64
  . rw [Sail.shift_bits_left, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero]
    simp [Word.toNat_toBitVec64 _ h_op2_isU64]
    rw [Word.setWidth_eq_low32 op1 h_op1_isU64]
    congr 1
    simp [Word.toNat, Word.low32, HalfWord.toBitVec32, HalfWord.toNat]
    omega
  . rw [Sail.shift_bits_right, Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb', Nat.shiftRight_zero]
    simp [Word.toNat_toBitVec64 _ h_op2_isU64]
    rw [Word.setWidth_eq_low32 op1 h_op1_isU64]
    congr 1
    simp [Word.toNat, Word.low32, HalfWord.toBitVec32, HalfWord.toNat]
    omega
  . have mod_lt_31: forall x : ℕ, (31 + (x : ℤ) % 32).toNat = 31 + x % 32 := by omega
    have mod_lt_32 : forall x : ℕ, (32 + (x : ℤ) % 32).toNat = 32 + x % 32 := by omega
    rw [Word.setWidth_eq_low32 _ h_op1_isU64, Word.setWidth_eq_low32 _ h_op2_isU64]
    set op1 := op1.low32.toBitVec32
    set op2 := op2.low32.toBitVec32
    rw [bitVec_sshiftright_eq]
    rw [shift_bits_right_arith, shift_right_arith, sign_extend]
    rw [Sail.BitVec.signExtend]
    simp_all [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']
    have : ↑(BitVec.ofNat 5 op2.toNat).toNat = op2.toNat % 32 := by simp
    rw [this]; rfl

/-- `execute_RTYPEW` with isolated pure part -/
def execute_RTYPEW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) : SailM ExecutionResult := do
  let rs1_bits ← do (rX_bits rs1)
  let rs2_bits ← do (rX_bits rs2)
  (wX_bits rd (execute_RTYPEW_pure rs1_bits rs2_bits op))
  (pure RETIRE_SUCCESS)

@[simp]
lemma execute_RTYPEW_eq_execute_RTYPEW' (rs2 : regidx) (rs1 : regidx) (rd : regidx) (op : ropw) :
  execute_RTYPEW rs2 rs1 rd op = execute_RTYPEW' rs2 rs1 rd op
  := by
    simp_all [execute_RTYPEW', execute_RTYPEW, execute_RTYPEW_pure]
    refine bind_congr ?_; intro r1
    refine bind_congr ?_; intro r2
    simpM; ext s
    simp [run_wX_bits]
    split_ifs <;> [ rfl; congr ]
    cases op <;> simp_all [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb']

end RTYPEW

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

lemma execute_MUL'_eq_execute_MUL (rs2 : regidx) (rs1 : regidx) (rd : regidx) (m : mop) :
  execute_MUL' rs2 rs1 rd m = execute_MUL rs2 rs1 rd (mul_op_of_mop m)
  := by cases m <;> simp_all [execute_MUL', execute_MUL, execute_MUL_pure, mul_op_of_mop, LeanRV64IM.Functions.xlen]

end MUL

end execution
