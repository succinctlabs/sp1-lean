import SP1Clean.Model.Semantics.ProgramCommitment
import SP1Clean.Model.Semantics.MicroTime
import SP1Clean.Model.Semantics.Decode

/-! # Execution truth — conclusions of global grounding

These predicates describe how structural bus records are interpreted after balance and timing have
been established. They are deliberately not Clean channel guarantees: a row-local sender cannot prove
reachability, ROM commitment, or last-write currency.

There are two intentionally distinct execution scopes:

- `ExecutionStateTruth` is boot-relative and parameterized by a fixed `SP1MachineModel`. It belongs at
  the composed-execution boundary, where a shard has been anchored in the model-selected boot run.
- `LocalStateTruth`/`LocalValueAt`/`LocalMemTruth` are relative to one selected shard initial state and
  public initial clock. They are the canonical predicates for AIR grounding. A shard-local theorem must
  not silently require that its public initial state is a zero-register boot state.

`RowFacts`/`LocalStepFact` form the chip-agnostic per-row advance obligation: from the pulled state's
truth and engine-supplied current operand truths, the pushed state and written values are true. -/

open LeanRV64D.Defs
namespace SP1Clean.Semantics

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target
open SP1Clean.Channels (StateMsg MemoryMsg ProgramMsg)
open SP1Clean.Commit (progOf initClkNat)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- State truth relative to the fixed loader and schedule of an `SP1MachineModel`.  This is the
canonical predicate for the new AIR capstone. -/
noncomputable def ExecutionStateTruth (model : SP1Clean.Machine.SP1MachineModel)
    (m : StateMsg (ZMod p)) (data : ProverData (ZMod p)) : Prop :=
  ∃ ctx : SP1Clean.Machine.ExecutionCtx model, ctx.program = progOf data ∧
    ∃ (step : ℕ) (state : SailState),
      SP1Clean.Machine.trajectory ctx.initial step = some state ∧
      StateMsg.timeNat m =
        SP1Clean.Machine.executionClock ctx (initClkNat data) step ∧
      state.regs.get? Register.PC = some (pcBits m.pc0 m.pc1 m.pc2) ∧
      RomLoaded (progOf data) state ∧
      SailConfigured state

/-- **Shard-local ordinary-window state grounding.** Starting from the exact state selected by the
AIR boundary, a real `SailChain` reaches this message's pc at its decoded time, with ROM and platform
configuration preserved. Boot reachability is deliberately absent. -/
def LocalStateTruth (program : GuestProgram) (initial : SailState) (initialClock : ℕ)
    (m : StateMsg (ZMod p)) : Prop :=
  ∃ (n : ℕ) (state : SailState),
    SailChain n initial state ∧
    StateMsg.timeNat m = initialClock + 8 * n ∧
    state.regs.get? Register.PC = some (pcBits m.pc0 m.pc1 m.pc2) ∧
    RomLoaded program state ∧
    SailConfigured state

/-- `value` is the content of `location` at `time` on the selected shard-local execution. -/
def LocalValueAt (initial : SailState) (initialClock : ℕ) (location : MemLoc)
    (time : ℕ) (value : Word (ZMod p)) : Prop :=
  microValue initial initialClock location time = some (Word.toBitVec64 value)

/-- Shard-local Memory grounding: limb hygiene plus execution truth at the message's micro-time. -/
def LocalMemTruth (initial : SailState) (initialClock : ℕ)
    (message : MemoryMsg (ZMod p)) : Prop :=
  SP1Clean.Channels.MemoryMsg.isU64 message ∧
  LocalValueAt initial initialClock (MemoryMsg.locOf message)
    (MemoryMsg.timeNat message) message.value

set_option linter.unusedSectionVars false in
/-- Package an already-constructed local Sail prefix as the State truth at its endpoint. -/
theorem localStateTruth_of_sailChain {program : GuestProgram} {initial state : SailState}
    {initialClock steps : ℕ} {message : StateMsg (ZMod p)}
    (chain : SailChain steps initial state)
    (time : StateMsg.timeNat message = initialClock + 8 * steps)
    (pc : state.regs.get? Register.PC = some (StateMsg.pcBits message))
    (rom : RomLoaded program state) (configured : SailConfigured state) :
    LocalStateTruth program initial initialClock message :=
  ⟨steps, state, chain, time, pc, rom, configured⟩

set_option linter.unusedSectionVars false in
/-- The public initial State record is locally true once its clock, pc, ROM, and platform fields are
bound to the selected shard initial state. -/
theorem localStateTruth_initial {program : GuestProgram} {initial : SailState}
    {initialClock : ℕ} {message : StateMsg (ZMod p)}
    (time : StateMsg.timeNat message = initialClock)
    (pc : initial.regs.get? Register.PC = some (StateMsg.pcBits message))
    (rom : RomLoaded program initial) (configured : SailConfigured initial) :
    LocalStateTruth program initial initialClock message := by
  apply localStateTruth_of_sailChain (.refl initial) (steps := 0)
  · simpa using time
  · exact pc
  · exact rom
  · exact configured

set_option linter.unusedSectionVars false in
/-- Before or at the shard's first clock, `microValue` reads the selected initial state. -/
theorem localValueAt_of_initial {initial : SailState} {initialClock time : ℕ}
    {location : MemLoc} {value : Word (ZMod p)}
    (content : locContent initial location = some (Word.toBitVec64 value))
    (before : time ≤ initialClock) :
    LocalValueAt initial initialClock location time value := by
  unfold LocalValueAt microValue
  by_cases strict : time < initialClock
  · rw [if_pos strict]
    exact content
  · have equal : time = initialClock := by omega
    subst time
    rw [if_neg (Nat.lt_irrefl _)]
    cases location <;> simpa [SP1Clean.Machine.trajectory] using content

set_option linter.unusedSectionVars false in
/-- Initial-provider content and its in-circuit limb range check establish the local Memory truth. -/
theorem localMemTruth_of_initial {initial : SailState} {initialClock : ℕ}
    {message : MemoryMsg (ZMod p)}
    (isU64 : SP1Clean.Channels.MemoryMsg.isU64 message)
    (content : locContent initial (MemoryMsg.locOf message) =
      some (Word.toBitVec64 message.value))
    (before : MemoryMsg.timeNat message ≤ initialClock) :
    LocalMemTruth initial initialClock message :=
  ⟨isU64, localValueAt_of_initial content before⟩

set_option linter.unusedSectionVars false in
/-- At the beginning of semantic step `steps`, local micro-time reads exactly the reached pre-state.
This is the generic bridge from timed Memory currency to the live Sail state used by chip dispatch. -/
theorem localValueAt_stepStart_iff {initial state : SailState} {initialClock steps : ℕ}
    {location : MemLoc} {value : Word (ZMod p)}
    (chain : SailChain steps initial state) :
    LocalValueAt initial initialClock location (initialClock + 8 * steps) value ↔
      locContent state location = some (Word.toBitVec64 value) := by
  unfold LocalValueAt microValue
  rw [if_neg (by omega)]
  rw [Nat.add_sub_cancel_left]
  have divEq : 8 * steps / 8 = steps := by omega
  have modEq : 8 * steps % 8 = 0 := by omega
  rw [divEq, modEq]
  cases location <;> norm_num <;> rw [chainState_of_sailChain chain] <;> rfl

/-! ## The per-row advance obligation -/

/-- The chip-agnostic facts one real row contributes, in bus-message form: its state pull/push, its
pinned-opcode fetch, its memory read-priors (each with the micro-time at which the row *reads* — the
currency point), and its memory pushes (read-backs and writes). -/
structure RowFacts (p : ℕ) where
  statePull : StateMsg (ZMod p)
  statePush : StateMsg (ZMod p)
  fetch : ProgramMsg (ZMod p)
  /-- read-prior messages, paired with the row-local micro-time of the read. -/
  memPulls : List (MemoryMsg (ZMod p) × ℕ)
  memPushes : List (MemoryMsg (ZMod p))

/-- **The shard-local advance obligation** (the grounding engine's layer-C step): given the pulled
state's truth and current operand values, the pushed state and every pushed Memory value are true. -/
def LocalStepFact (program : GuestProgram) (initial : SailState) (initialClock : ℕ)
    (r : RowFacts p) : Prop :=
  LocalStateTruth program initial initialClock r.statePull →
  (∀ mp ∈ r.memPulls,
    SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
    LocalValueAt initial initialClock (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
  LocalStateTruth program initial initialClock r.statePush ∧
    ∀ message ∈ r.memPushes, LocalMemTruth initial initialClock message

/-! ## Committed-program grounding -/

/-- A Program-bus message projected to the committed program-row column shape — a trivial field-rename now
that `ProgramMsg.op_b`/`op_c` are already `Word`s — so `decodedInROM` can be applied to a `ProgramMsg`. -/
def rowOfMsg (m : ProgramMsg (ZMod p)) : SP1Clean.ProgramChip.ProgramRow (ZMod p) where
  pc0 := m.pc0
  pc1 := m.pc1
  pc2 := m.pc2
  opcode := m.opcode
  op_a := m.op_a
  op_b := m.op_b
  imm_b := m.imm_b
  op_c := m.op_c
  op_a_0 := m.op_a_0
  imm_c := m.imm_c

/-- **Committed-program truth** — the fetch-decode correspondence: the message's decode
bounds (`RowSpec`) **plus** that the fetched row is the decode of the committed program's ROM at its pc
(`decodedInROM`, over `Commit.progOf data`). So the `is_real`-gated opcode a chip pins in its fetch is a
real decode of the committed guest program — the foundation of opcode-based Sail dispatch. Structural
`RowSpec` is established locally and by the structural Program channel; the `decodedInROM` half is
derived from balance against the ROM provider plus the program-commitment binding. -/
def ProgTruth (m : ProgramMsg (ZMod p)) (data : ProverData (ZMod p)) : Prop :=
  SP1Clean.Channels.ProgramMsg.RowSpec m ∧
    SP1Clean.Soundness.Target.decodedInROM (Commit.progOf data) (rowOfMsg m)

set_option linter.unusedSectionVars false in
/-- **`ProgTruth` → the RV64-decoded instruction.** From a fetch message's `ProgTruth`, the genuine
LeanRV64D `ext_decode` instruction whose `instrToProgramRow` is the message's row — the callable RV64
surface the Phase-4 per-chip `advance` consumes (its opcode-based Sail dispatch). A thin re-export of the
`decodedInROM.decodes` accessor through the `ProgTruth` conjunction. -/
theorem ProgTruth.decodes {m : ProgramMsg (ZMod p)} {data : ProverData (ZMod p)}
    (h : ProgTruth m data) (s : SailState) (hs : SailConfigured s) :
    ∃ w i, (Commit.progOf data).fetchWord (pcBitsOfRow (rowOfMsg m)) = some w ∧
      (ext_decode w).run s = .ok i s ∧
      instrToProgramRow (rowPcVec (rowOfMsg m)) i = some (rowOfMsg m) :=
  h.2.decodes s hs

end SP1Clean.Semantics
