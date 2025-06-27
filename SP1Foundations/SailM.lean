import SP1Foundations.Field
import SP1Foundations.ByteOpcode

import LeanRV32D.RiscvInstsEnd
open LeanRV32D.Functions Sail

section sailboats

instance : DecidableEq regidx | .Regidx v, .Regidx v' => by simp; infer_instance

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

end sailboats
