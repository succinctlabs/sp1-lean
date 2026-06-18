import SP1Clean.FormalModel.Trace.GuestProgram

/-! # W6b — the non-vacuity witness: `IsInitialState` is satisfiable

The target theorem (`Soundness/TargetVm.lean`) is `∀ s0, IsInitialState prog s0 → …`; a vacuous
`IsInitialState` would make it trivially true. This file exhibits a concrete configured, fully-initialized
Sail state and a guest program it loads, proving `IsInitialState` is **satisfiable** (axiom-clean).

The reusable machinery is `configuredState pc` — a state with **every** register present
(`cfgState_init`: the `isInitialized` requirement, all 196 `Register` constructors), the program counter
pinned to `pc` (`cfgState_pc`), and `cur_privilege = Machine` (`cfgState_priv`, the strengthened
`SailConfigured` residue the decode reduction needs). Built by folding `insert` over `Finset.univ`
(`Fintype Register` is derived here) with each register's `default` value (every `RegisterType r` is
`Inhabited`). Enriching the witness to a non-empty ROM (real instruction bytes loaded into `mem`, so
`romLoaded` carries content) reuses `configuredState` and adds the byte-level `mem` lookups. -/

namespace SP1Clean.Soundness.Target

open Sail LeanRV64D

set_option maxRecDepth 100000

-- All `Register` constructors are enumerable — derived so `Finset.univ` enumerates them.
deriving instance Fintype for Register

/-- Every register's value type is inhabited, so a register can be default-filled. -/
noncomputable def regDefault : (r : Register) → RegisterType r := fun r => by cases r <;> exact default

/-- The fully-initialized register map: every register present, holding its `default` value. -/
noncomputable def fullRegs : Std.ExtDHashMap Register RegisterType :=
  (Finset.univ : Finset Register).toList.foldr
    (fun r (m : Std.ExtDHashMap Register RegisterType) => m.insert r (regDefault r)) ∅

private lemma mem_foldr_insert {l : List Register} {r : Register} (h : r ∈ l) :
    r ∈ l.foldr (fun r (m : Std.ExtDHashMap Register RegisterType) => m.insert r (regDefault r)) ∅ := by
  induction l with
  | nil => simp at h
  | cons a t ih =>
    simp only [List.foldr_cons, Std.ExtDHashMap.mem_insert]
    rcases List.mem_cons.mp h with rfl | hmem
    · exact Or.inl (by simp)
    · exact Or.inr (ih hmem)

/-- Every register is a key of `fullRegs` (`r ∈ univ`, and the fold inserts every list element). -/
lemma mem_fullRegs (r : Register) : r ∈ fullRegs :=
  mem_foldr_insert (Finset.mem_toList.mpr (Finset.mem_univ r))

/-- A runnable initial Sail state: every register initialized, PC pinned to `pc`, in machine mode. -/
noncomputable def configuredState (pc : BitVec 64) : SailState :=
  { (default : SailState) with
    regs := (fullRegs.insert Register.PC pc).insert Register.cur_privilege Privilege.Machine }

lemma cfgState_init (pc : BitVec 64) : (configuredState pc).isInitialized := by
  intro reg
  simp only [configuredState, Std.ExtDHashMap.mem_insert]
  exact Or.inr (Or.inr (mem_fullRegs reg))

lemma cfgState_pc (pc : BitVec 64) : (configuredState pc).regs.get? Register.PC = some pc := by
  simp only [configuredState]
  rw [Std.ExtDHashMap.get?_insert, Std.ExtDHashMap.get?_insert_self]; simp

lemma cfgState_priv (pc : BitVec 64) :
    (configuredState pc).regs.get? Register.cur_privilege = some Privilege.Machine := by
  simp only [configuredState, Std.ExtDHashMap.get?_insert_self]

/-- A minimal guest program (empty ROM/data, entry pc 0). Enough to exhibit that `IsInitialState` is
satisfiable; a richer program (real ROM bytes) reuses `configuredState` + adds `mem` content. -/
def emptyProgram : GuestProgram := ⟨[], 0, [], by simp, by simp⟩

/-- **The W6b non-vacuity witness.** `IsInitialState` is satisfiable: the configured initial state loads
the (minimal) guest program. So the target theorem's universally-quantified hypothesis is not vacuous. -/
theorem isInitialState_nonvacuous : ∃ s0, IsInitialState emptyProgram s0 :=
  ⟨configuredState 0,
   { initialized := cfgState_init 0
     pc := cfgState_pc 0
     romLoaded := by intro a w hf; simp [emptyProgram, GuestProgram.fetchWord] at hf
     imageLoaded := by intro av hav; simp [emptyProgram] at hav
     configured := ⟨cfgState_init 0, cfgState_priv 0⟩ }⟩

end SP1Clean.Soundness.Target
