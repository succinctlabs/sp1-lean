import SP1Foundations
import LeanRV32D.RiscvInstsEnd
import LeanRV32D.RiscvRegs
import SP1Operations.CPUState
import SP1Operations.JTypeReader

namespace exp

-- Simple experiment with StateM Int to prove consecutive reads are equivalent
theorem simple_consecutive_reads :
  (do let x ← StateT.get; let y ← StateT.get; pure (x, y) : StateM Int (Int × Int)) =
  (do let x ← StateT.get; pure (x, x) : StateM Int (Int × Int)) := by
  -- Work directly with function extensionality
  funext s
  -- Both get operations read the state s, so they return the same value
  rfl

-- More general theorem about reads with no interfering operations
theorem reads_with_pure_operations :
  (do
    let x ← StateT.get
    let _ ← pure ()  -- Some pure operation that doesn't change state
    let y ← StateT.get
    pure (x, y) : StateM Int (Int × Int)) =
  (do
    let x ← StateT.get
    let _ ← pure ()
    pure (x, x) : StateM Int (Int × Int)) := by
  funext s
  simp [StateT.get, pure]
  rfl

-- Simple working version of monadic substitution
<<<<<<< HEAD
theorem simple_monadic_subst {α β : Type} {m : Type → Type} [Monad m]
  (ma : m α) (f : α → β) (mb : m β)
  (h : f <$> ma = mb) :
  (do let a ← ma; pure (f a)) = mb := by
  rw [← bind_pure_comp, ← map_bind, h]
=======
theorem simple_monadic_subst {α β : Type} {m : Type → Type} [Monad m] [LawfulMonad m]
    (ma : m α) (f : α → β) (mb : m β)
    (h : f <$> ma = mb) :
    (do let a ← ma; pure (f a)) = mb := by
  simpa
  -- rw [← bind_pure_comp, ← map_bind, h]
>>>>>>> 997c41403074de8dd357722fd646b205687876b6

end exp

open LeanRV32D.Functions
open Sail
open PreSail (SequentialState)

structure JalChip where
  state : CPUState
  adapter : JTypeReader U16
  is_real : U1

namespace JalChip

def constraints (chip : JalChip) : Prop := sorry

def trust_jmp : Prop := sorry

end JalChip

def sp1_jal
  (chip : JalChip)
  (constraints : chip.constraints)
  (h_is_real : chip.is_real = 1)
  (rd : regidx)
  (imm : BitVec 21)
  (read_b : chip.adapter.read_jal_b_fun imm)
  (read_c : chip.adapter.read_jal_c_fun)
  : SailM Unit :=
  do
    -- When we generate memory reads/writes,
    -- the order of the statements is based on `clk`
    wX_bits rd chip.adapter.c.toBV32_U16
    -- The order of PC write doesn't really matter to us, so for convention
    -- let's place them at the start
    writeReg (Register.nextPC) chip.adapter.b.toBV32_U16

def spec_jal (rd : regidx) (imm : BitVec 21) : SailM Unit := do
  writeReg Register.nextPC (BitVec.addInt (← readReg Register.PC) 4)
  let _ ← execute_JAL imm rd
  pure ()

def runSuccessState {α : Type} (m : SailM α) (s : SequentialState RegisterType trivialChoiceSource) :
    Option (SequentialState RegisterType trivialChoiceSource) :=
  match m.run s with
  | .ok _ s' => some s'
  | .error _ _ => none

theorem sp1_jal_implies_spec_jal
  (chip : JalChip)
  (constraints : chip.constraints)
  (h_is_real : chip.is_real = 1)
  (rd : regidx)
  (imm : BitVec 21)
  (read_b : chip.adapter.read_jal_b_fun imm)
  (read_c : chip.adapter.read_jal_c_fun)
  -- note: this is horrendously wrong, `trusted_jmp` should not be trusted.
  -- the equality should only hold when `pc ← readReg Register.PC`
  -- claude messed this one up
  (trusted_jmp : ∀ (pc : BitVec 32),
    bit_to_bool (BitVec.access (pc + sign_extend imm) 1) = pure false)
  (s : PreSail.SequentialState RegisterType trivialChoiceSource)
  : let res := (sp1_jal chip constraints h_is_real rd imm read_b read_c).run s
    let res_spec := (spec_jal rd imm).run s
    res = res_spec
  :=
  by
    simp [EStateM.run, sp1_jal, spec_jal, execute_JAL]
    simp only [JTypeReader.read_jal_b_fun] at read_b
    simp only [JTypeReader.read_jal_c_fun] at read_c

    simp [ext_control_check_pc]
    simp [get_next_pc, set_next_pc, bits_of_virtaddr]

    -- Now use trusted_jmp to replace bit_to_bool expressions
    simp [trusted_jmp]
    -- Now a_1 should be replaced with false everywhere

    -- -- Use read_b to substitute (a + sign_extend imm) with chip.adapter.b.toBV32_U16
    -- -- read_b tells us: (fun x ↦ x + sign_extend imm) <$> readReg Register.PC = pure chip.adapter.b.toBV32_U16
    -- -- This means: for the specific PC value `a`, we have (a + sign_extend imm) = chip.adapter.b.toBV32_U16
    -- -- Let's extract this equality and use it
    -- have h_pc_eq : (fun x ↦ x + sign_extend imm) <$> readReg Register.PC = pure chip.adapter.b.toBV32_U16 := read_b
    --
    -- -- We need to show that the bind where we read PC and then add imm is equivalent to using b directly
    -- -- Let's try to use our monadic substitution lemma
    -- conv_rhs =>
    --   -- Navigate to the final writeReg that uses (a + sign_extend imm)
    --   simp only [bind_assoc]

    /- simp [wX_bits] -/
    /- simp [PreSail.readReg, PreSail.writeReg] -/

    sorry
