import SP1Foundations.Register

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

/-- Version of `Option.getM` using `throw` instead of `failure`-/
def Option.toSailM {α} (x : Option α) : SailM α :=
  Option.elim x (throw Sail.Error.Unreachable) pure

@[simp] lemma toSailM_none : Option.toSailM (α := α) none = throw Sail.Error.Unreachable := rfl

@[simp] lemma toSailM_some (x : α) : Option.toSailM (some x) = pure x := rfl

@[simp] lemma toSailM_map (f : α → β) (x : Option α) :
    (Option.map f x).toSailM = f <$> x.toSailM := match x with | none => rfl | some _ => rfl

section get_reg?

/-- Read the value in the register corresponding to `idx`, giving an actual `BitVec 64`.
This avoids the issue of some (unused by us) registers having other length vectors. -/
def SailState.get_reg? (s : SailState) (idx : BitVec 5) : Option (BitVec 64) :=
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
@[simp] lemma get_reg?_insert_self (idx : BitVec 5) (s : SailState)
    (v : RegisterType (reg_idx_to_Register idx)) :
    let reg := reg_idx_to_Register idx
    SailState.get_reg? {s with regs := s.regs.insert reg v} idx =
      if idx = 0#5 then some 0 else reg_idx_must_64 idx ▸ some v := by
  simp [SailState.get_reg?]

@[simp] lemma get_reg?_insert_nextPC (idx : BitVec 5) :
    SailState.get_reg? {s with regs := s.regs.insert Register.nextPC v} idx =
      SailState.get_reg? s idx := by
  rw [get_reg?_insert_of_ne]; simp

@[simp] lemma get_reg?_insert_PC (idx : BitVec 5) :
    SailState.get_reg? {s with regs := s.regs.insert Register.PC v} idx =
      SailState.get_reg? s idx := by
  rw [get_reg?_insert_of_ne]; simp

end get_reg?

section write_reg

/-- Alternative to `write_reg` that takes a `BitVec` rather than an explicit `Register`. -/
def write_reg (idx : BitVec 5) (val : BitVec 64) : SailM Unit := do
  let reg : Register := reg_idx_to_Register idx
  if idx != 0#5 then modify fun s =>
    { s with regs := s.regs.insert reg (reg_idx_must_64 idx ▸ val) }
  else if val ≠ 0#64 then throw Sail.Error.Unreachable

@[simp] lemma run_write_reg (idx : BitVec 5) (val : BitVec 64) :
    (write_reg idx val).run s =
      let reg : Register := reg_idx_to_Register idx
      if idx = 0#5 then if val = 0#64 then .ok () s else .error Sail.Error.Unreachable s
        else .ok () { s with regs := s.regs.insert reg (reg_idx_must_64 idx ▸ val) } := by
  unfold write_reg; aesop

@[simp] lemma write_reg_write_reg_self (idx : BitVec 5) (val val' : BitVec 64) :
    (do write_reg idx val; write_reg idx val') =
      if idx = 0#5 ∧ val ≠ 0#64 then throw .Unreachable else write_reg idx val' := by
  refine EStateM.ext fun s => ?_
  by_cases hidx : idx = 0#5
  · simp [hidx]
    by_cases hval : val = 0#64
    · simp [hval]
    · simp [hval]
  · simp [hidx]

/-- Swap writes to two distinct registers, assuming only `0#5` written to the `0` register. -/
lemma write_reg_write_reg_comm (idx idx' : BitVec 5) (val val' : BitVec 64)
    (h : idx ≠ idx') (hval : idx = 0#5 → val = 0#5) (hval' : idx' = 0#5 → val' = 0#5) :
    (do write_reg idx val; write_reg idx' val') =
      (do write_reg idx' val'; write_reg idx val) := by
  refine EStateM.ext fun s => ?_
  by_cases hidx : idx = 0#5
  · by_cases hidx' : idx' = 0#5
    · refine (h (hidx.trans hidx'.symm)).elim
    · simp [hidx, hidx', hval hidx]
  · by_cases hidx' : idx' = 0#5
    · simp [hidx, hidx', hval' hidx']
    · simp [hidx', hidx]
      rw [Std.ExtDHashMap.insert_insert_comm]
      simp [h, hidx, hidx']

end write_reg

section write_reg'

/-- Version of `write_reg` that doesn't throw an error writing to the `0` register.
This matches more closely with the behavior of `wX_bits` -/
def write_reg' (idx : BitVec 5) (val : BitVec 64) : SailM Unit :=
  do if idx != 0#5 then modify fun s =>
    { s with regs := s.regs.insert (reg_idx_to_Register idx) (reg_idx_must_64 idx ▸ val) }

@[simp] lemma run_write_reg' (idx : BitVec 5) (val : BitVec 64) :
    (write_reg' idx val).run s =
      let reg : Register := reg_idx_to_Register idx
      if idx = 0#5 then .ok () s
        else .ok () { s with regs := s.regs.insert reg (reg_idx_must_64 idx ▸ val) } := by
  unfold write_reg'; aesop

/-- `write_reg` and `write_reg'` align if not the `0` index of the value written is `0`. -/
lemma write_reg_eq_write_reg' (idx : BitVec 5) (val : BitVec 64) (h : idx ≠ 0#5 ∨ val = 0#64) :
    write_reg idx val = write_reg' idx val := by
  unfold write_reg write_reg'; aesop

@[simp] lemma write_reg'_write_reg'_self (idx : BitVec 5) (val val' : BitVec 64) :
    (do write_reg' idx val; write_reg' idx val') = write_reg' idx val' := by
  refine EStateM.ext fun s => ?_
  by_cases hidx : idx = 0#5
  · simp [hidx]
  · simp [hidx]

/-- Swap writes to two distinct registers. -/
lemma write_reg'_write_reg'_comm (idx idx' : BitVec 5) (val val' : BitVec 64) (h : idx ≠ idx') :
    (do write_reg' idx val; write_reg' idx' val') =
      (do write_reg' idx' val'; write_reg' idx val) := by
  refine EStateM.ext fun s => ?_
  by_cases hidx : idx = 0#5
  · by_cases hidx' : idx' = 0#5 <;> simp [hidx, hidx']
  · by_cases hidx' : idx' = 0#5
    · simp [hidx, hidx']
    · simp [hidx', hidx]
      rw [Std.ExtDHashMap.insert_insert_comm]
      simp [h, hidx, hidx']

end write_reg'

section writeReg

@[simp] lemma run_writeReg (reg : Register) (v : RegisterType reg) :
    (Sail.writeReg reg v).run s =
      .ok PUnit.unit { s with regs := s.regs.insert reg v} := rfl

lemma run_writeReg_bind (reg : Register) (v : RegisterType reg) (mx : Unit → SailM α) :
    (Sail.writeReg reg v >>= mx).run s =
      (mx ()).run {s with regs := s.regs.insert reg v} := by simp

@[simp] lemma writeReg_writeReg_self (reg : Register) (v v' : RegisterType reg) :
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
  simp
  rwa [Std.ExtDHashMap.insert_insert_comm]

end writeReg

section readReg

@[simp] lemma run_readReg (reg : Register) :
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

lemma run_readReg_insert_of_ne (s : SailState) (reg reg' : Register) (h : reg ≠ reg')
    (v : RegisterType reg) : (Sail.readReg reg').run { s with regs := s.regs.insert reg v} =
      match s.regs.get? reg' with
      | some w => .ok w { s with regs := s.regs.insert reg v }
      | none => .error .Unreachable { s with regs := s.regs.insert reg v } := by
  simp [Sail.readReg, Std.ExtDHashMap.get?_insert, h]

@[simp] lemma run_readReg_insert_self (s : SailState) (reg : Register) (v : RegisterType reg) :
    (Sail.readReg reg).run { s with regs := s.regs.insert reg v } =
      .ok v { s with regs := s.regs.insert reg v } := by
  simp only [run_readReg, Std.ExtDHashMap.get?_insert_self]

@[simp] lemma map_const_run_readReg (reg : Register) (x : α)
    (h : (s.regs.get? reg).isSome) :
    ((Sail.readReg reg).run s).map (fun _ => x) = .ok x s := by
  rw [Option.isSome_iff_exists] at h
  obtain ⟨y, hy⟩ := h
  simp [hy]

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
    (rX_bits (regidx.Regidx idx)).run s = (s.get_reg? idx).toSailM s := by
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

@[simp] lemma run_rX_bits (idx : BitVec 5) :
    (rX_bits (regidx.Regidx idx)).run s =
    match SailState.get_reg? s idx with
    | some v => .ok v s
    | none => .error Sail.Error.Unreachable s := by
  rw [rX_bits_eq_get_reg?]
  simp [Option.toSailM, Option.elim]
  cases SailState.get_reg? s idx with
  | some v => rfl
  | none => rfl

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

lemma run_wX_bits (reg : regidx) (data : BitVec 64) :
    (wX_bits reg data).run s = let .Regidx idx := reg
      .ok () (if idx = 0 then s else {s with
        regs := s.regs.insert (reg_idx_to_Register idx) (reg_idx_must_64 idx ▸ data)}) := by
  simp [wX_bits, wX]
  let .Regidx idx := reg
  fin_cases idx
  · simp
  all_goals {
    simp [xreg_write_callback, reg_name_forwards, get_config_use_abi_names,
      LeanRV64IM.Functions.not]
    rfl
  }

end wX_bits

@[simp] lemma run_bool_bit_backwards (b : BitVec 1) :
    (bool_bit_backwards b).run s = match b with
    | 1#1 => .ok true s
    | 0#1 => .ok false s := by
  simp [bool_bit_backwards]
  fin_cases b <;> rfl

@[simp] lemma run_bit_to_bool (b : BitVec 1) :
    (bit_to_bool b).run s = match b with
    | 1#1 => .ok true s
    | 0#1 => .ok false s := by
  fin_cases b <;> rfl

section write_read_bind

/-- Reading a just written value looks like just using the written value. -/
@[simp] lemma writeReg_readReg_bind (reg : Register)
    (v : RegisterType reg) (mx : RegisterType reg → SailM α) :
    (do Sail.writeReg reg v; let w ← Sail.readReg reg; mx w) =
      (do Sail.writeReg reg v; mx v) := by
  simp [Sail.writeReg, PreSail.writeReg, Sail.readReg, PreSail.readReg]
  have := LawfulMonadStateOf.modify_bind_get_bind_of_forall_eq
    (f := fun s : SailState =>
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

end write_read_bind

@[simp] lemma writeReg_bind_map_readReg (reg : Register) (v : RegisterType reg)
    (f : RegisterType reg → α) :
    (do Sail.writeReg reg v; f <$> Sail.readReg reg) =
      (do Sail.writeReg reg v; return f v) := by
  simp [map_eq_bind_pure_comp]

/-- Writing a value overwrites the previous write.
dt: might need `typ_0` condition when proving this. -/
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
    simp
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
  simp [pc_write_callback]

@[simp] lemma force_pc_eq (pc : BitVec 64) :
    force_pc pc = Sail.writeReg Register.PC pc := rfl

end pc

end sailboats
