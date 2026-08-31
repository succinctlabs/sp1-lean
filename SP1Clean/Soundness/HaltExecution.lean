import SP1Clean.Soundness.GroundingInternal

/-! # From the halted grounding certificate to the eventful halting trace

The `.halted` twin of the ordinary event assembly: a `SupportedCoreHaltGrounding` certificate
yields a complete `EventExecutionTrace` — the grounded instruction prefix compiled by
`eventExecution_of_groundedRows`, with **one** terminal `EventStep.syscall` transition appended.
The terminal transition is honest host semantics: `ExecutableSyscallHandler.haltOnly` parks the
machine at `haltPc` on the exact canonical `HALT` code, and every event field is an architectural
observation of the reached pre-halt state (the halt row's pulled operands, grounded by the timed
memory walk). -/

open LeanRV64D.Defs

namespace SP1Clean.Soundness

open Air.Flat Circuit
open SP1Clean.Execution

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

omit [Fact p.Prime] [Fact (2 ^ 25 < p)] in
/-- Parking the pc changes no memory location's content: registers are keyed away from `PC`, and
RAM is untouched. -/
theorem locContent_insert_pc (s : SailState) (v : BitVec 64) (loc : Semantics.MemLoc) :
    Semantics.locContent
      { s with regs := s.regs.insert Register.PC (by exact v) } loc =
      Semantics.locContent s loc := by
  cases loc with
  | reg i =>
      show SailState.get_reg? _ i = SailState.get_reg? s i
      exact SailState.get_reg?_insert_of_ne (by revert i; decide)
  | ram cell => rfl

/-- The chained-prefix content bridge: micro-time at the halt row's pull time is the content of
the prefix chain's endpoint. -/
private theorem locContent_of_pullMicro
    {statement : SupportedCoreStatement p} {witness : SupportedCoreNativeWitness p}
    {initial finalState : SailState} {rows : List (DecodedInstructionRow p)}
    {halt : Array (ZMod p)}
    (hg : SupportedCoreHaltGrounding statement witness initial rows halt)
    (chain : Target.SailChain rows.length initial finalState)
    {loc : Semantics.MemLoc} {bv : BitVec 64}
    (current : Semantics.microValue initial (Commit.initClkNat witness.data) loc
      (Semantics.StateMsg.timeNat
        (HaltChip.statePulledMessage (haltRow (haltTable witness) halt))) = some bv) :
    Semantics.locContent finalState loc = some bv := by
  rw [hg.pullClock] at current
  rwa [Semantics.microValue_stepStart chain] at current

/-- The gated tail of the halt row's `Spec`, at its live selector. -/
private theorem haltGrounding_specTail
    {statement : SupportedCoreStatement p} {witness : SupportedCoreNativeWitness p}
    {initial : SailState} {rows : List (DecodedInstructionRow p)} {halt : Array (ZMod p)}
    (hg : SupportedCoreHaltGrounding statement witness initial rows halt) :
    ((haltRow (haltTable witness) halt).x5_memory.prev_value[0] = 0 ∧
      (haltRow (haltTable witness) halt).x5_memory.prev_value[1] = 0 ∧
      (haltRow (haltTable witness) halt).x5_memory.prev_value[2] = 0 ∧
      (haltRow (haltTable witness) halt).x5_memory.prev_value[3] = 0) ∧
    ((haltRow (haltTable witness) halt).x10_memory.prev_value[1] = 0 ∧
      (haltRow (haltTable witness) halt).x10_memory.prev_value[2] = 0 ∧
      (haltRow (haltTable witness) halt).x10_memory.prev_value[3] = 0) :=
  ⟨(hg.spec.2.2.2.2.2.2 hg.real).1, (hg.spec.2.2.2.2.2.2 hg.real).2.1⟩

/-- The pulled `x5` word is the canonical `HALT` code `0`. -/
private theorem haltGrounding_x5_bits
    {statement : SupportedCoreStatement p} {witness : SupportedCoreNativeWitness p}
    {initial : SailState} {rows : List (DecodedInstructionRow p)} {halt : Array (ZMod p)}
    (hg : SupportedCoreHaltGrounding statement witness initial rows halt) :
    Word.toBitVec64 (haltRow (haltTable witness) halt).x5_memory.prev_value =
      Target.HALT_SYSCALL := by
  obtain ⟨⟨z0, z1, z2, z3⟩, -⟩ := haltGrounding_specTail hg
  rw [Word.toBitVec64, Word.toNat, z0, z1, z2, z3]
  simp [Target.HALT_SYSCALL]

/-- The pulled `x10` word decodes to the committed public exit code: the two high limbs vanish
in-circuit, and the Exit hand-off binds the reduced word to the `exit_code` cell. -/
private theorem haltGrounding_x10_bits
    {statement : SupportedCoreStatement p} {witness : SupportedCoreNativeWitness p}
    {initial : SailState} {rows : List (DecodedInstructionRow p)} {halt : Array (ZMod p)}
    (hg : SupportedCoreHaltGrounding statement witness initial rows halt) :
    Word.toBitVec64 (haltRow (haltTable witness) halt).x10_memory.prev_value =
      statement.publicValues.exitCodeBits := by
  have hp := Fact.out (p := 2 ^ 25 < p)
  obtain ⟨-, z1, z2, z3⟩ := haltGrounding_specTail hg
  have codeEq : (haltRow (haltTable witness) halt).x10_memory.prev_value[0] =
      statement.publicValues.exit_code := by
    have := hg.exitBinding
    rw [HaltChip.exitMessage] at this
    have valueEq := congrArg Channels.ExitMsg.value this
    simp only at valueEq
    rw [z1, z2, z3] at valueEq
    linear_combination valueEq
  have codeVal : statement.publicValues.exit_code.val =
      (haltRow (haltTable witness) halt).x10_memory.prev_value[0].val := by
    rw [← codeEq]
  have v1 : (haltRow (haltTable witness) halt).x10_memory.prev_value[1].val = 0 := by
    rw [z1, ZMod.val_zero]
  have v2 : (haltRow (haltTable witness) halt).x10_memory.prev_value[2].val = 0 := by
    rw [z2, ZMod.val_zero]
  have v3 : (haltRow (haltTable witness) halt).x10_memory.prev_value[3].val = 0 := by
    rw [z3, ZMod.val_zero]
  rw [Word.toBitVec64, Word.toNat, SP1StateBoundary.exitCodeBits, codeVal, v1, v2, v3]
  norm_num

/-- The pre-halt state's three observed operand registers, at any Sail chain reaching the halt
row's pull position. -/
private theorem haltContents
    {statement : SupportedCoreStatement p} {witness : SupportedCoreNativeWitness p}
    {initial s : SailState} {rows : List (DecodedInstructionRow p)} {halt : Array (ZMod p)}
    (hg : SupportedCoreHaltGrounding statement witness initial rows halt)
    (chain : Target.SailChain rows.length initial s) :
    Semantics.locContent s (Semantics.MemLoc.reg 5) = some Target.HALT_SYSCALL ∧
    Semantics.locContent s (Semantics.MemLoc.reg 10) =
      some statement.publicValues.exitCodeBits ∧
    Semantics.locContent s (Semantics.MemLoc.reg 11) =
      some (Word.toBitVec64 (haltRow (haltTable witness) halt).x11_memory.prev_value) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [locContent_of_pullMicro hg chain hg.x5Value, haltGrounding_x5_bits hg]
  · rw [locContent_of_pullMicro hg chain hg.x10Value, haltGrounding_x10_bits hg]
  · exact locContent_of_pullMicro hg chain hg.x11Value

/-- **The plain-Sail halting facts.**  From the halted grounding certificate: a normally-retiring
prefix chain reaches a genuine `SP1Halted` state — the committed `ECALL` site under the pc, `t0`
holding the canonical `HALT` code, `a0` the committed exit code — together with the pre-halt
content bridge for the memory boundary. -/
theorem haltedSail_of_haltGrounding
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState) (rows : List (DecodedInstructionRow p)) (halt : Array (ZMod p))
    (hg : SupportedCoreHaltGrounding statement witness initial rows halt)
    (boundary : InitialBoundaryFacts statement witness initial) :
    ∃ preHalt : SailState,
      Target.SailRetireChain rows.length initial preHalt ∧
      Target.SP1Halted statement.program statement.publicValues.exitCodeBits preHalt ∧
      (∀ (loc : Semantics.MemLoc) (bv : BitVec 64),
        Semantics.microValue initial (Commit.initClkNat witness.data) loc
          (Semantics.StateMsg.timeNat
            (HaltChip.statePulledMessage (haltRow (haltTable witness) halt))) = some bv →
        Semantics.locContent preHalt loc = some bv) := by
  obtain ⟨preHalt, retire, prePc⟩ :=
    sailRetireChain_of_groundedRows
      (fun decoded : DecodedInstructionRow p => decoded.toChipRow witness.data)
      witness.data statement.program initial rows _ _ hg.walk hg.grounded
      boundary.codeMemoryCompatible boundary.initialPc boundary.romLoaded boundary.configured
  have chain : Target.SailChain rows.length initial preHalt := retire.toSailChain
  obtain ⟨content5, content10, -⟩ := haltContents hg chain
  exact ⟨preHalt, retire,
    ⟨_, prePc, hg.ecallFetch, content5, content10⟩,
    fun loc bv h => locContent_of_pullMicro hg chain h⟩

/-- **The halting event trace.** From the halted grounding certificate: the grounded instruction
prefix compiled to ordinary official-Sail transitions, plus the terminal canonical-`HALT` syscall
transition — with the endpoint clocks, pcs, the supported-prefix discipline, the terminal
`HaltsWith`, and the pre-halt content bridge for the memory boundary. -/
theorem haltedExecution_of_haltGrounding
    (statement : SupportedCoreStatement p) (witness : SupportedCoreNativeWitness p)
    (initial : SailState) (rows : List (DecodedInstructionRow p)) (halt : Array (ZMod p))
    (hg : SupportedCoreHaltGrounding statement witness initial rows halt)
    (boundary : InitialBoundaryFacts statement witness initial) :
    ∃ execution : Machine.EventExecutionTrace,
      execution.initialState = initial ∧
      execution.steps = rows.length + 1 ∧
      execution.Valid Machine.ExecutableSyscallHandler.haltOnly.relation statement.program ∧
      execution.Clocked (Semantics.clkNat statement.publicValues.init_clk_high
        statement.publicValues.init_clk_low) ∧
      execution.finalClock (Semantics.clkNat statement.publicValues.init_clk_high
          statement.publicValues.init_clk_low) =
        Semantics.clkNat statement.publicValues.final_clk_high
          statement.publicValues.final_clk_low ∧
      execution.initialState.regs.get? Register.PC = some
        (supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
          statement.publicValues.init_pc2) ∧
      execution.finalState.regs.get? Register.PC = some
        (supportedPcBits statement.publicValues.final_pc0 statement.publicValues.final_pc1
          statement.publicValues.final_pc2) ∧
      execution.HaltsWith statement.program statement.publicValues.exitCodeBits ∧
      (∀ transition ∈ execution.transitions.dropLast, transition.event = .ordinary) ∧
      (∀ located ∈ execution.locatedTransitions.dropLast,
        SupportedSP1Transition statement.program located) ∧
      execution.transitions.dropLast.length = rows.length ∧
      (∀ (loc : Semantics.MemLoc) (bv : BitVec 64),
        Semantics.microValue initial (Commit.initClkNat witness.data) loc
          (Semantics.StateMsg.timeNat
            (HaltChip.statePulledMessage (haltRow (haltTable witness) halt))) = some bv →
        Semantics.locContent execution.finalState loc = some bv) := by
  classical
  -- compile the grounded instruction prefix
  obtain ⟨execution₀, initialEq, stepsEq, finalPc₀, valid₀, clocked₀, finalClock₀, ordinary₀,
      supported₀⟩ :=
    eventExecution_of_groundedRows Machine.ExecutableSyscallHandler.haltOnly.relation
      (fun decoded : DecodedInstructionRow p => decoded.toChipRow witness.data)
      witness.data statement.program initial rows
      (supportedPcBits statement.publicValues.init_pc0 statement.publicValues.init_pc1
        statement.publicValues.init_pc2)
      (Semantics.StateMsg.pcBits (HaltChip.statePulledMessage (haltRow (haltTable witness) halt)))
      hg.walk hg.grounded boundary.codeMemoryCompatible boundary.initialPc
      boundary.romLoaded boundary.configured
      (Semantics.clkNat statement.publicValues.init_clk_high
        statement.publicValues.init_clk_low)
  -- the reached pre-halt state
  have chain₀ : Target.SailChain rows.length initial execution₀.finalState := by
    have := execution₀.sailChain valid₀ ordinary₀
    rw [initialEq, stepsEq] at this
    exact this
  have content := fun loc bv current =>
    locContent_of_pullMicro hg chain₀ (loc := loc) (bv := bv) current
  obtain ⟨content5, content10, content11⟩ := haltContents hg chain₀
  -- the terminal syscall event and transition
  set haltEvent : Machine.CoreSyscallEvent :=
    { clock := Semantics.clkNat statement.publicValues.init_clk_high
        statement.publicValues.init_clk_low + 8 * rows.length
      pc := Semantics.StateMsg.pcBits
        (HaltChip.statePulledMessage (haltRow (haltTable witness) halt))
      nextPc := Machine.haltPc
      rawCode := 0
      arg1 := statement.publicValues.exitCodeBits
      arg2 := Word.toBitVec64 (haltRow (haltTable witness) halt).x11_memory.prev_value
      result := 0 } with haltEventDef
  set target : SailState :=
    { execution₀.finalState with
        regs := execution₀.finalState.regs.insert Register.PC Machine.haltPc } with targetDef
  have ecall : Machine.AboutToExecuteEcall statement.program execution₀.finalState :=
    ⟨_, finalPc₀, hg.ecallFetch⟩
  have targetPc : target.regs.get? Register.PC = some Machine.haltPc := by
    rw [targetDef]
    simp
  have syscallStep : Machine.SyscallTransition
      Machine.ExecutableSyscallHandler.haltOnly.relation statement.program haltEvent
      execution₀.finalState target := by
    refine ⟨⟨Or.inl ?_, ?_, ?_, ?_⟩, ⟨finalPc₀, ?_, ?_, ?_, targetPc, ?_⟩, ?_⟩
    · -- WellRouted: byte one of the zero code is zero
      simp [Machine.CoreSyscallEvent.tableByte, haltEventDef]
    · -- ResultLaw: the canonical HALT id is neither ENTER_UNCONSTRAINED nor HINT_LEN
      simp [Machine.CoreSyscallEvent.ResultLaw, Machine.CoreSyscallEvent.syscallId,
        haltEventDef, Machine.enterUnconstrainedSyscallId, Machine.hintLenSyscallId]
    · -- PcLaw: HALT parks at `haltPc`
      simp [Machine.CoreSyscallEvent.PcLaw, Machine.CoreSyscallEvent.syscallId,
        haltEventDef, Machine.haltSyscallId]
    · -- HandlerAddressesFit: the zero code routes to no handler table
      intro hasTable
      exact absurd hasTable (by
        simp [Machine.CoreSyscallEvent.hasTable, Machine.CoreSyscallEvent.tableByte,
          haltEventDef])
    · -- x5 carries the raw code
      show execution₀.finalState.get_reg? 5 = some haltEvent.rawCode
      rw [show haltEvent.rawCode = Target.HALT_SYSCALL from rfl]
      exact content5
    · -- x10 carries the exit argument
      show execution₀.finalState.get_reg? 10 = some haltEvent.arg1
      exact content10
    · -- x11 carries the second argument
      show execution₀.finalState.get_reg? 11 = some haltEvent.arg2
      exact content11
    · -- x5 keeps the (zero) result across the pc park
      show target.get_reg? 5 = some haltEvent.result
      rw [targetDef]
      rw [SailState.get_reg?_insert_of_ne (by decide)]
      exact content5
    · -- the executable handler takes exactly this step
      show Machine.ExecutableSyscallHandler.haltOnly.run statement.program haltEvent
        execution₀.finalState = some target
      simp [Machine.ExecutableSyscallHandler.haltOnly, haltEventDef, targetDef]
  -- the assembled halting trace
  set execution : Machine.EventExecutionTrace :=
    ⟨execution₀.initialState,
      execution₀.transitions ++ [⟨.syscall haltEvent, target⟩]⟩ with executionDef
  have dropLastEq : execution.transitions.dropLast = execution₀.transitions := by
    rw [executionDef]
    exact List.dropLast_concat
  have finalStateEq : execution.finalState = target := by
    rw [executionDef]
    show Machine.stateAfterTransitions _ _ = target
    rw [Machine.stateAfterTransitions_append]
    rfl
  have stepsCount : execution.steps = rows.length + 1 := by
    have h : execution₀.transitions.length = rows.length := stepsEq
    rw [executionDef]
    show (execution₀.transitions ++ [(⟨.syscall haltEvent, target⟩ :
      Machine.EventTransition)]).length = rows.length + 1
    rw [List.length_append, h]
    rfl
  refine ⟨execution, initialEq, stepsCount, ?_, ?_, ?_,
    (by
      show execution₀.initialState.regs.get? Register.PC = _
      rw [initialEq]
      exact boundary.initialPc), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- validity: the ordinary prefix plus the checked syscall step
    rw [executionDef]
    refine Machine.EventTransitionsValid.append valid₀ ?_
    exact .cons _ (.syscall ecall syscallStep) (.nil _)
  · -- the schedule: eight-tick prefix, then the syscall window start
    rw [executionDef]
    refine Machine.eventTransitionsClocked_append clocked₀ ?_
    refine ⟨?_, trivial⟩
    show haltEvent.clock = Machine.clockAfterEvents
      (Semantics.clkNat statement.publicValues.init_clk_high
        statement.publicValues.init_clk_low)
      (execution₀.transitions.map Machine.EventTransition.event)
    rw [haltEventDef]
    exact finalClock₀.symm
  · -- final clock: the syscall window closes at the committed final boundary
    rw [executionDef]
    show Machine.clockAfterEvents _ ((execution₀.transitions ++ _).map _) =
      Semantics.clkNat statement.publicValues.final_clk_high
        statement.publicValues.final_clk_low
    have prefixClock : Machine.clockAfterEvents
        (Semantics.clkNat statement.publicValues.init_clk_high
          statement.publicValues.init_clk_low)
        (execution₀.transitions.map Machine.EventTransition.event) =
        Semantics.clkNat statement.publicValues.init_clk_high
          statement.publicValues.init_clk_low + 8 * rows.length := finalClock₀
    rw [List.map_append, Machine.clockAfterEvents_append, prefixClock]
    simp only [List.map_cons, List.map_nil, Machine.clockAfterEvents, List.foldl_cons,
      List.foldl_nil, Machine.ExecutionEvent.duration_syscall]
    have hfin := hg.finalClock
    have hpull := hg.pullClock
    have hinit := boundary.initialClock
    omega
  · -- final pc: the halt park at the committed final boundary
    rw [finalStateEq, targetPc, hg.finalPc]
  · -- the terminal halt condition
    rw [executionDef]
    have halted : Target.SP1Halted statement.program statement.publicValues.exitCodeBits
        execution₀.finalState :=
      ⟨_, finalPc₀, hg.ecallFetch, content5, content10⟩
    exact Machine.EventExecutionTrace.haltsWith_snoc statement.program _ execution₀ haltEvent
      target rfl rfl halted
  · -- the prefix is all-ordinary
    rw [dropLastEq]
    exact ordinary₀
  · -- the prefix is supported
    intro located locatedMem
    refine supported₀ located ?_
    have locEq : execution.locatedTransitions.dropLast = execution₀.locatedTransitions := by
      rw [executionDef]
      show (Machine.locateTransitions _ (execution₀.transitions ++ _)).dropLast = _
      rw [Machine.locateTransitions_append]
      exact List.dropLast_concat
    rwa [locEq] at locatedMem
  · -- the prefix length
    rw [dropLastEq]
    exact stepsEq
  · -- the pre-halt content bridge, transported across the pc park
    intro loc bv current
    rw [finalStateEq, targetDef, locContent_insert_pc]
    exact content loc bv current

end SP1Clean.Soundness
