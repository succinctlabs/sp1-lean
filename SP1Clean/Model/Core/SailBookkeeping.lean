import SP1Clean.Model.Core.ExecutionReplay

/-! # Retirement observations of the existing Sail state

The ordinary instruction counter is distinct from the interaction clock and simulator cycle
counter. Its enable bit reads the official machine-mode filter and inhibit fields. Host calls
preserve these fields. The observation fold below only records retirement bookkeeping; it does
not execute instructions or define another machine state.
-/

namespace SP1Clean.Model.Core

open LeanRV64D.Defs LeanRV64D.Functions Machine

/-- The official machine-mode retirement decision, with a total fallback on absent registers.
Successful interpreter evaluation authenticates both fields and proves agreement. -/
def retirementEnabled (state : SailState) : Bool :=
  (_get_Counterin_IR ((state.regs.get? Register.mcountinhibit).getD 0) == 0#1) &&
    (counter_priv_filter_bit ((state.regs.get? Register.minstretcfg).getD 0) Privilege.Machine == 0#1)

/-- The data-only decision agrees with the actual successful Sail filter computation. -/
theorem retirementEnabled_of_run {state : SailState} {enabled : Bool}
    (success : (should_inc_minstret Privilege.Machine).run state = .ok enabled state) :
    retirementEnabled state = enabled := by
  simp only [should_inc_minstret, bind, EStateM.bind, EStateM.run] at success
  have readInhibit := Sail.run_readReg state Register.mcountinhibit
  simp only [EStateM.run] at readInhibit
  rw [readInhibit] at success
  cases inhibit : state.regs.get? Register.mcountinhibit with
  | none => simp only [inhibit] at success; cases success
  | some inhibitValue =>
    simp only [inhibit] at success
    have readFilter := Sail.run_readReg state Register.minstretcfg
    simp only [EStateM.run] at readFilter
    rw [readFilter] at success
    cases filter : state.regs.get? Register.minstretcfg with
    | none => simp only [filter] at success; cases success
    | some filterValue =>
      simp only [filter] at success
      cases success
      simp only [retirementEnabled, inhibit, filter, Option.getD_some]

/-- One observation update: only a normally retired ordinary instruction changes these slots. -/
def retirementTick (values : Bool × Option Bool × Option (BitVec 64)) (ordinary : Bool) :
    Bool × Option Bool × Option (BitVec 64) :=
  if ordinary then
    (values.1, some values.1, values.2.2.map (fun value => value + if values.1 then 1 else 0))
  else values

/-- The enable bit is constant; the architectural counter adds the number of ordinary steps,
with 64-bit wraparound. An empty ordinary inventory preserves even the original increment flag. -/
theorem retirementTick_fold {ρ : Type*} (ordinary : ρ → Bool) (rows : List ρ)
    (enabled : Bool) (flag : Option Bool) (counter : Option (BitVec 64)) :
    rows.foldl (fun values row => retirementTick values (ordinary row)) (enabled, flag, counter) =
      (enabled, if rows.countP ordinary = 0 then flag else some enabled,
        counter.map (fun value => value + BitVec.ofNat 64 (if enabled then rows.countP ordinary else 0))) := by
  induction rows generalizing flag counter with
  | nil => simp
  | cons row rest ih =>
    rw [List.foldl_cons]
    cases active : ordinary row with
    | false =>
      rw [show retirementTick (enabled, flag, counter) false = (enabled, flag, counter) from rfl, ih]
      simp [active]
    | true =>
      rw [show retirementTick (enabled, flag, counter) true =
        (enabled, some enabled, counter.map (fun value => value + if enabled then 1 else 0)) from rfl, ih]
      cases enabled <;> simp [active, Option.map_map, Function.comp_def, BitVec.ofNat_add,
        BitVec.add_comm]
      congr 1
      funext value
      rw [← BitVec.add_assoc, BitVec.add_comm _ value, BitVec.add_assoc]

/-- Walk backward over the host-only suffix. Its first host PC is the last ordinary successor;
with no ordinary event, preserve the source nextPC even at a terminal final PC. -/
private def nextPcReverse (initial finalPc : Option (BitVec 64)) : List ExecutionEvent → Option (BitVec 64)
  | [] => initial
  | .ordinary :: _ => finalPc
  | .syscall call :: rest => nextPcReverse initial (some call.pc) rest

/-- Final nextPC from semantic labels and endpoint PCs, without instruction-row data. -/
def nextPcAfter (events : List ExecutionEvent) (initial finalPc : Option (BitVec 64)) : Option (BitVec 64) :=
  nextPcReverse initial finalPc events.reverse

@[simp] theorem nextPcAfter_nil (initial finalPc : Option (BitVec 64)) :
    nextPcAfter [] initial finalPc = initial := rfl

@[simp] theorem nextPcAfter_ordinary (events : List ExecutionEvent) (initial finalPc : Option (BitVec 64)) :
    nextPcAfter (events ++ [.ordinary]) initial finalPc = finalPc := by
  simp only [nextPcAfter, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, nextPcReverse]

@[simp] theorem nextPcAfter_syscall (events : List ExecutionEvent) (call : CoreSyscallEvent)
    (initial finalPc : Option (BitVec 64)) :
    nextPcAfter (events ++ [.syscall call]) initial finalPc = nextPcAfter events initial (some call.pc) := by
  simp only [nextPcAfter, List.reverse_append, List.reverse_cons, List.reverse_nil,
    List.nil_append, List.singleton_append, nextPcReverse]

/-- Local nextPC effects and the existing host-call PC authentication determine the whole tape's
bookkeeping. This does not require a separate physical trace or expose instruction splitting. -/
theorem replayEvents?_nextPC {policy : HostPolicy} {program : Soundness.Target.GuestProgram}
    {source target : ExecutionState} {events : List ExecutionEvent}
    (success : replayEvents? policy program source events = some target)
    (effect : ∀ n current next event, events[n]? = some event →
      replayEvents? policy program source (events.take n) = some current →
      replayStep? policy program current event = some next →
        next.sail.regs.get? Register.nextPC =
          if event.isOrdinary then next.sail.regs.get? Register.PC else current.sail.regs.get? Register.nextPC) :
    target.sail.regs.get? Register.nextPC =
      nextPcAfter events (source.sail.regs.get? Register.nextPC) (target.sail.regs.get? Register.PC) := by
  induction events using List.reverseRecOn generalizing target with
  | nil => cases success; rfl
  | append_singleton events event ih =>
    rw [replayEvents?_append] at success
    obtain ⟨middle, prefixRan, last⟩ := Option.bind_eq_some_iff.mp success
    have step : replayStep? policy program middle event = some target := by
      simpa only [replayEvents?, Option.bind_fun_some] using last
    have finalEffect := effect events.length middle target event (by simp)
      (by simpa only [List.take_append_length] using prefixRan) step
    cases event with
    | ordinary => simpa only [nextPcAfter_ordinary, ExecutionEvent.isOrdinary_ordinary, ↓reduceIte] using finalEffect
    | syscall call =>
      have hostStep := (replayHost?_eq_some_iff _ _ _ _ _).mp step
      have pc : middle.sail.regs.get? Register.PC = some call.pc := by
        cases hostStep with
        | syscall ran =>
          obtain ⟨pc, execution, atPc, _, _, _, _, eventEq⟩ := HostState.step_observations ran
          rw [eventEq]
          exact atPc
      rw [nextPcAfter_syscall, ← pc, finalEffect]
      apply ih prefixRan
      intro n current next label atLabel replay step
      have bound := (List.getElem?_eq_some_iff.mp atLabel).1
      apply effect n current next label (by rwa [List.getElem?_append_left bound]) _ step
      simpa only [List.take_append_of_le_length (Nat.le_of_lt bound)] using replay

end SP1Clean.Model.Core
