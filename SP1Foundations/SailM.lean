import Mathlib
import LeanRV64IM.RiscvInstsEnd
import SP1Foundations.Misc

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

-- dt: should this be a macro instead?
@[simp] abbrev SailState := PreSail.SequentialState RegisterType Sail.trivialChoiceSource

section regidx

instance : DecidableEq regidx | .Regidx v, .Regidx v' => by simp; infer_instance

/-- Convert a bitvec into the corresponding `RV64` register. -/
def reg_idx_to_Register (idx : BitVec 5) : Register :=
  match idx with
  | 1#5 => Register.x1
  | 2#5 => Register.x2
  | 3#5 => Register.x3
  | 4#5 => Register.x4
  | 5#5 => Register.x5
  | 6#5 => Register.x6
  | 7#5 => Register.x7
  | 8#5 => Register.x8
  | 9#5 => Register.x9
  | 10#5 => Register.x10
  | 11#5 => Register.x11
  | 12#5 => Register.x12
  | 13#5 => Register.x13
  | 14#5 => Register.x14
  | 15#5 => Register.x15
  | 16#5 => Register.x16
  | 17#5 => Register.x17
  | 18#5 => Register.x18
  | 19#5 => Register.x19
  | 20#5 => Register.x20
  | 21#5 => Register.x21
  | 22#5 => Register.x22
  | 23#5 => Register.x23
  | 24#5 => Register.x24
  | 25#5 => Register.x25
  | 26#5 => Register.x26
  | 27#5 => Register.x27
  | 28#5 => Register.x28
  | 29#5 => Register.x29
  | 30#5 => Register.x30
  | _ => Register.x31

lemma reg_idx_31_is_x31 : reg_idx_to_Register 31#5 = Register.x31 := rfl

/-- All of the registers corresponding to a `BitVec 5` contain 64-bit values. -/
lemma reg_idx_must_64 (idx : BitVec 5) :
    RegisterType (reg_idx_to_Register idx) = BitVec 64 := by
  simp [reg_idx_to_Register]
  split <;> rfl

lemma case_31 {val : BitVec 64} {s : SailState} :
    s.regs.insert (reg_idx_to_Register 31#5) val = s.regs.insert Register.x31 val := rfl

@[simp] lemma SailState.reg_idx_toRegister_ne_nextPC (idx : BitVec 5) :
    (reg_idx_to_Register idx ≠ Register.nextPC) := by
  unfold reg_idx_to_Register; split <;> trivial

@[simp] lemma SailState.reg_id_toRegister_ne_PC (idx : BitVec 5) :
    (reg_idx_to_Register idx ≠ Register.PC) := by
  unfold reg_idx_to_Register; split <;> trivial

end regidx

/-- Version of `Option.getM` using `throw` instead of `failure`-/
def Option.toSailM {α} (x : Option α) : SailM α :=
  Option.elim x (throw Sail.Error.Unreachable) pure

section get_reg?

/-- Read the value in the register corresponding to `idx`, giving an actual `BitVec 64`.
This avoids the issue of some (unused by us) registers having other length vectors. -/
def SailState.get_reg? (s : SailState) (idx : BitVec 5) : Option (BitVec 64) :=
  if idx = 0 then some 0 else reg_idx_must_64 idx ▸ s.regs.get? (reg_idx_to_Register idx)

-- dt: naming
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


@[simp] lemma get_reg?_insert_nextPC (idx : BitVec 5) :
    SailState.get_reg? { s with regs := s.regs.insert Register.nextPC v } idx =
      SailState.get_reg? s idx := by
  rw [get_reg?_insert_of_ne]
  simp [reg_idx_to_Register]
  split <;> trivial

end get_reg?

section write_reg

/-- Alternative to `write_reg` that takes a `BitVec` rather than an explicit `Register`. -/
def SailState.write_reg (idx : BitVec 5) (val : BitVec 64) : SailM Unit := do
  let reg : Register := reg_idx_to_Register idx
  if idx != 0 then modify fun s =>
    { s with regs := s.regs.insert reg (reg_idx_must_64 idx ▸ val) }
  else if val ≠ 0 then throw Sail.Error.Unreachable

@[simp] lemma run_write_reg (idx : BitVec 5) (val : BitVec 64) :
    (SailState.write_reg idx val).run s =
      let reg : Register := reg_idx_to_Register idx
      if idx = 0 then if val = 0 then .ok () s else .error Sail.Error.Unreachable s
        else .ok () { s with regs := s.regs.insert reg (by
          rw [reg_idx_must_64 idx]
          exact val) } := by
  aesop (add safe (by dsimp [SailState.write_reg]))

end write_reg

section write_reg'

/-- Version of `write_reg` that doesn't throw an error writing to the `0` register. -/
def SailState.write_reg' (idx : BitVec 5) (val : BitVec 64) : SailM Unit :=
  do if idx != 0 then modify fun s =>
    { s with regs := s.regs.insert (reg_idx_to_Register idx) (reg_idx_must_64 idx ▸ val) }

-- dt: rename
theorem SailState.wX_bits_is_regidx_write (idx : BitVec 5) (val : BitVec 64)
  : SailState.write_reg' idx val = wX_bits (.Regidx idx) val :=
  by
    simp [SailState.write_reg', wX_bits]
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

end write_reg'

@[simp] lemma set_next_pc_def (pc : BitVec 64) :
    set_next_pc pc = Sail.writeReg Register.nextPC pc := rfl

@[simp] lemma get_next_pc_def (u : Unit) :
    get_next_pc u = Sail.readReg Register.nextPC := rfl

section writeReg

@[simp] lemma run_writeReg (reg : Register) (v : RegisterType reg) :
    (Sail.writeReg reg v).run s =
      .ok PUnit.unit { s with regs := s.regs.insert reg v} := rfl

lemma run_writeReg_bind (reg : Register) (v : RegisterType reg) (mx : Unit → SailM α) :
    (Sail.writeReg reg v >>= mx).run s =
      (mx ()).run {s with regs := s.regs.insert reg v} := by simp

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

end readReg

section rX

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

end rX

section wX

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

end wX

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

section without_running -- lemmas about `SailM` without actually running the computation.

/-- Reading a just written value looks like just using the written value. -/
@[simp]
theorem writeReg_readReg_bind {α : Type} (reg : Register) (v : RegisterType reg)
    (mx : RegisterType reg → SailM α) :
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
  rw [SailState.write_reg']
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

end without_running

end sailboats
