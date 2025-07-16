import Mathlib
import LeanRV64IM.RiscvInstsEnd
import LeanRV64IM.Defs

section sailboats

open PreSail

open LeanRV64IM.Functions


-- inductive regidx where
--   | Regidx (_ : (BitVec 5))
--   deriving Inhabited, BEq, Repr

instance : DecidableEq regidx | .Regidx v, .Regidx v' => by simp; infer_instance


/-- Reading a just written value looks like just using the written value. -/
@[simp]
theorem writeReg_readReg_bind {α : Type} (reg : Register) (v : RegisterType reg)
    (mx : RegisterType reg → SailM α) :
    (do Sail.writeReg reg v; let w ← Sail.readReg reg; mx w) =
      (do Sail.writeReg reg v; mx v) := sorry

/-- Writing a value overwrites the previous write.
dt: might need `typ_0` condition when proving this. -/
@[simp]
theorem writeReg_wX_bits_writeReg (reg : Register) (v : RegisterType reg)
    (v' : RegisterType reg)
    (typ_0 : regidx) (data : BitVec 64) :
    (do Sail.writeReg reg v; wX_bits typ_0 data; Sail.writeReg reg v') =
      (do wX_bits typ_0 data; Sail.writeReg reg v') := sorry

-- lemma reg_map_ext (rmap rmap' : PreSail.SequentialState RegisterType trivialChoiceSource)
--     (hreg : rmap.regs = rmap'.regs)
--     (hcs : rmap.choiceState = rmap'.choiceState)
--     (hmem : rmap.mem = rmap'.mem)
--     (hcc : rmap.cycleCount = rmap'.cycleCount)
--     (hout : rmap.sailOutput = rmap'.sailOutput) :
--     rmap = rmap' := by
--   refine match rmap with | ⟨regs, cs, mem, (), cc, so⟩ => ?_
--   refine match rmap' with | ⟨regs', cs', mem', (), cc', so'⟩ => ?_
--   simp_all

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

open Sail (trivialChoiceSource)

@[simp]
abbrev SailState := SequentialState RegisterType trivialChoiceSource

def reg_idx_to_Register (idx : BitVec 5) : Register :=
  match idx with
  | 1 => Register.x1
  | 2 => Register.x2
  | 3 => Register.x3
  | 4 => Register.x4
  | 5 => Register.x5
  | _ => Register.x31

theorem reg_idx_must_64
  (idx : BitVec 5)
  : RegisterType (reg_idx_to_Register idx) = BitVec 64 :=
  by
    simp [reg_idx_to_Register]
    split <;> rfl

def SailState.get_reg? (s : SailState) (idx : BitVec 5) : Option (BitVec 64) :=
  by
    let reg : Register := reg_idx_to_Register idx
    rw [←reg_idx_must_64 idx]
    refine s.regs.get? reg

end sailboats
