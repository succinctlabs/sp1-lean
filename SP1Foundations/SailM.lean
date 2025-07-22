import Mathlib
import LeanRV64IM.RiscvInstsEnd
import LeanRV64IM.Defs
import SP1Foundations.Misc

open LeanRV64IM.Functions

macro "simpM" : tactic => `(tactic| simp [bind, StateT.bind, EStateM.bind, get, getThe, MonadStateOf.get, StateT.get, EStateM.get, pure, EStateM.pure, StateT.map, EStateM.map, modify, modifyGet, EStateM.modifyGet, StateT.modifyGet, MonadStateOf.modifyGet])

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

@[simp high] -- Prefer this over reducing on bind
lemma run_readReg_bind (reg : Register) (mx : RegisterType reg → SailM α) :
    (Sail.readReg reg >>= mx).run s = match s.regs.get? reg with
    | some v => (mx v).run s
    | none => (throw Sail.Error.Unreachable : SailM _).run s := by
  simp
  cases s.regs.get? reg with | some v => rfl | none => rfl

-- @[simp]
-- lemma run_rX (n : ℕ) :
--     (rX (.Regno n)).run s =

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

instance : Fintype (BitVec n) where
  elems := Finset.image (BitVec.ofFin) Finset.univ
  complete := by
    intro x
    simp [Finset.mem_image]

open Sail (trivialChoiceSource Error)


theorem reg_idx_31_is_x31 : reg_idx_to_Register 31#5 = Register.x31 :=
  by
    aesop

theorem reg_idx_must_64
  (idx : BitVec 5)
  : RegisterType (reg_idx_to_Register idx) = BitVec 64 :=
  by
    simp [reg_idx_to_Register]
    split <;> rfl

def SailState.get_reg? (s : SailState) (idx : BitVec 5) : Option (BitVec 64) :=
  if idx = 0
  then some 0
  else
    by
      let reg : Register := reg_idx_to_Register idx
      rw [←reg_idx_must_64 idx]
      exact s.regs.get? reg

def SailState.write_reg (idx : BitVec 5) (val : BitVec 64) : SailM Unit :=
  do
    let reg : Register := reg_idx_to_Register idx
    if idx != 0 then
      modify fun s =>
        { s with regs := s.regs.insert reg (by rw [reg_idx_must_64 idx]; exact val) }
    else if val ≠ 0 then
      throw Error.Unreachable

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

-- theorem SailState.write_reg_is_wX {s : SailState}
--   (idx : BitVec 5)
--   (val : BitVec 64)
--   : (wX_bits (regidx.Regidx idx) val) s = (write_reg idx val) s :=
--   by
--     sorry

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

theorem SailState.reg_idx_never_nextPC
  {idx : BitVec 5}
  : (Register.nextPC == reg_idx_to_Register idx) = false :=
  by
    simp [reg_idx_to_Register]
    split <;> trivial

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
    refine Std.ExtDHashMap.ext_get? fun a' => ?_
    simp [Std.ExtDHashMap.get?_insert]
    by_cases h : reg = a'
    · induction h
      simp
    · simp [h]

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

-- lemma run_readReg_bind_of_forall (reg : Register)
--     (f : RegisterType reg → β)
--     (mx : β → SailM α) (y : β)
--     (s : PreSail.SequentialState RegisterType Sail.trivialChoiceSource)
--     (hs : ∀ v, s.regs.get? reg = some v → f v = y)
--      :
--     (do let v ← Sail.readReg reg; mx (f v)).run s =
--       (mx y).run s
--     := by
--   simpM
--   unfold EStateM.bind EStateM.run
--   rcases h_eq : (Sail.readReg reg s) with ⟨ mx', s' ⟩ <;> simp_all
--   . congr; apply hs
--     . simp [Sail.readReg, readReg, bind, EStateM.instMonad, EStateM.bind] at h_eq
--       split at h_eq <;> [ subst_eqs; trivial ]
--       rcases h_hmap_get : (s.regs.get?) reg <;> simp_all <;> [ trivial; skip ]
--       obtain ⟨ _, _ ⟩ := h_eq; rfl
--     . sorry
--   . sorry

-- lemma readReg_bind_const (reg : Register) (mx : SailM α) :
--     (do let _ ← Sail.readReg reg; mx) = mx := by
--   simpM
--   refine EStateM.ext ?_
--   unfold EStateM.bind EStateM.run
--   simp; intro s
--   rcases h_eq : (Sail.readReg reg s) with ⟨ mx', s' ⟩ <;> simp_all
--   . suffices : s = s'
--     . simp_all
--     . simp [Sail.readReg, readReg, bind, EStateM.instMonad, EStateM.bind] at h_eq
--       split at h_eq <;> [ subst_eqs; trivial ]
--       rcases h_hmap_get : (s.regs.get?) reg <;> simp_all <;> [ trivial; skip ]
--       obtain ⟨ _, _ ⟩ := h_eq; rfl
--   . sorry

-- @[simp]
-- lemma wX_bits_rX_bits' (rs : regidx) (bv : BitVec 32) (cont : BitVec 32 → SailM α) :
--     (do let _ ← wX_bits rs bv; let bv' ← rX_bits rs; cont bv') =
--       (do let _ ← wX_bits rs bv; cont bv) := by
--   simp [wX_bits, rX_bits]
--   refine EStateM.ext fun reg_map => ?_
--   rw [EStateM.run]
--   show (EStateM.bind _ _) reg_map = (EStateM.bind _ _) reg_map
--   simp [EStateM.bind]
--   sorry

-- lemma wX_bits_rX_bits (rs : regidx) (v : BitVec 32) :
--     (do let _ ← wX_bits rs v; rX_bits rs) =
--       (do let _ ← wX_bits rs v; pure v) := by
--   rw [bind_pure_comp]
--   simp only [Nat.reducePow, Nat.reduceMul, bind_pure_comp]
--   refine EStateM.ext fun reg_map => ?_
--   simp
--   rw [EStateM.run]
--   rw [EStateM.Result.map.eq_def]
--   show (EStateM.bind _ _) reg_map = _
--   rw [EStateM.bind]
--   simp [EStateM.run]

--   sorry

-- lemma rX_bits_rX_bits_swap (cont : BitVec 32 → BitVec 32 → SailM α)
--     {rs rs' : regidx} (h : rs ≠ rs') :
--     (do let bv ← rX_bits rs; let bv' ← rX_bits rs'; cont bv bv') =
--       (do let bv' ← rX_bits rs'; let bv ← rX_bits rs; cont bv bv') := by
--   sorry

-- lemma wX_bits_rX_bits_swap (cont : Unit → BitVec 32 → SailM α)
--     {rs rs' : regidx} (h : rs ≠ rs') (bv : BitVec 32) :
--     (do let u ← wX_bits rs bv; let bv' ← rX_bits rs'; cont u bv') =
--       (do let bv' ← rX_bits rs'; let _ ← wX_bits rs bv; cont () bv') := by
--   sorry

-- lemma rX_bits_wX_bits_swap (cont : BitVec 32 → Unit → SailM α)
--     {rs rs' : regidx} (h : rs ≠ rs') (bv : BitVec 32) :
--     (do let bv ← rX_bits rs; let u ← wX_bits rs' bv; cont bv u) =
--       (do let _ ← wX_bits rs' bv; let bv ← rX_bits rs; cont bv ()) := by
--   sorry

-- lemma wX_bits_wX_bits_swap (cont : Unit → Unit → SailM α)
--     {rs rs' : regidx} (h : rs ≠ rs') (bv bv' : BitVec 32) :
--     (do let u ← wX_bits rs bv; let u' ← wX_bits rs' bv'; cont u u') =
--       (do let _ ← wX_bits rs' bv'; let _ ← wX_bits rs bv; cont () ()) := by
--   sorry

-- lemma run_rX_bind_of_get_mem_eq (id : ℕ)
--     (cont : BitVec 32 → SailM α)
--     (mstate : PreSail.SequentialState RegisterType trivialChoiceSource)
--     (v : ℕ)
--     (hmstate : mstate.mem[id]? = some ↑v) :
--     EStateM.run (rX (.Regno id) >>= cont) mstate =
--       EStateM.run (cont (BitVec.ofNat 32 v)) mstate := by
--   sorry

-- lemma run_wX_bind_of_get_mem_eq (id : ℕ)
--     (cont : Unit → SailM α)
--     (mstate : PreSail.SequentialState RegisterType trivialChoiceSource)
--     (v : ℕ) (hv : v < 2^32)
--     (hmstate : mstate.mem[id]? = some ↑v) :
--     EStateM.run (wX (.Regno id) (v#'hv) >>= cont) mstate =
--       EStateM.run (cont ()) mstate := by
--   sorry

-- lemma wX_comm_of_ne' (id id' : regno) (h : id ≠ id')
--     (v v' : BitVec 32) (cont : SailM α) :
--     (do wX id v; wX id' v'; cont) =
--       (do wX id' v'; wX id v; cont) := sorry

-- lemma wX_comm_of_ne (id id' : regno) (h : id ≠ id')
--     (v v' : BitVec 32) :
--     (do wX id v; wX id' v') =
--       (do wX id' v'; wX id v) := sorry

end sailboats
