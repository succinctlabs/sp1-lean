import SP1Clean.Model.Semantics.ProgramCommitment
import SP1Clean.Model.Semantics.MicroTime
import SP1Clean.Model.Semantics.Decode

/-! # Execution truth — the semantic channel payloads

The predicates the semantic channels carry (wired to the channels in the Phase-2 waves; defined here so
all semantic reasoning happens against the real definitions while circuit proofs thread them opaquely):

- `StateTruth m data` — the State channel's guarantee: the deterministic execution of the committed
  program (`Commit.progOf data`) is at `m`'s pc at `m`'s time, with the ROM intact and the platform
  residue preserved (write-protection and the W7 decode residue travel inside the guarantee).
- `ValueAt`/`MemTruth m data` — the Memory channel's guarantee: `m.value` is the true register/RAM
  content of `m`'s location at `m`'s own micro-time on that same execution. Memory is *bookkeeping*:
  this predicate is consumed only inside the grounding engine and the chips' step facts — the capstone
  never mentions it.
- `RowFacts`/`StepFact` — the chip-agnostic per-row advance obligation (the Phase-4 `advance` target):
  from the pulled state's truth and engine-supplied **current** operand truths (value true at the
  *read* time — currency is the engine's per-address chain fact, provably not row-local), the pushed
  state and written values are true.

Initial-state convention: `IsInitialState` is a relation (underdetermined `s0`), so truths quantify
over all loaders; `ZeroRegs` (SP1's zero-initialized register file) is conjoined rather than added to
`IsInitialState` (zero blast radius on its existing consumers). -/

namespace SP1Clean.Semantics

open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target
open SP1Clean.Channels (StateMsg MemoryMsg ProgramMsg)
open SP1Clean.Commit (progOf initClkNat)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- SP1's zero-initialized register file (kept separate from `IsInitialState` — conjoined at use). -/
def ZeroRegs (s : SailState) : Prop :=
  ∀ i : BitVec 5, s.get_reg? i = some 0

/-- **The State channel's semantic guarantee.** The committed program's execution is at this
`(clk, pc)`: for every zero-registered loader `s0`, a real `SailChain` of the clk-determined length
reaches a state at the message's pc, ROM intact, still configured. ROM-intactness inside the guarantee
is the write-protection threading; `SailConfigured` is the W7 decode residue. -/
def StateTruth (m : StateMsg (ZMod p)) (data : ProverData (ZMod p)) : Prop :=
  ∀ s0, IsInitialState (progOf data) s0 → ZeroRegs s0 →
    ∃ (n : ℕ) (s : SailState),
      SailChain n s0 s ∧
      StateMsg.timeNat m = initClkNat data + 8 * n ∧
      s.regs.get? Register.PC = some (pcBits m.pc0 m.pc1 m.pc2) ∧
      RomLoaded (progOf data) s ∧
      SailConfigured s

/-- `v` is the true content of `loc` at micro-time `τ` on the committed execution. -/
def ValueAt (data : ProverData (ZMod p)) (loc : MemLoc) (τ : ℕ) (v : Word (ZMod p)) : Prop :=
  ∀ s0, IsInitialState (progOf data) s0 → ZeroRegs s0 →
    microValue s0 (initClkNat data) loc τ = some (Word.toBitVec64 v)

/-- **The Memory channel's semantic guarantee** — execution-truth of the value at the message's own
micro-time (plus the limb hygiene the current channel carries). Subsumes today's `isU64`-only
guarantee: true values of a valid execution are U64. -/
def MemTruth (m : MemoryMsg (ZMod p)) (data : ProverData (ZMod p)) : Prop :=
  SP1Clean.Channels.MemoryMsg.isU64 m ∧
  ValueAt data (MemoryMsg.locOf m) (MemoryMsg.timeNat m) m.value

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

/-- **The advance obligation** (the Phase-4 `advance` target, the engine's layer-C step): given the
pulled state's truth and, for every operand, isU64 plus execution-truth **at the read time** (currency
— supplied by the engine's structural layers, never provable row-locally), the pushed state and every
pushed value are true. Discharged per chip from its `Spec` via
`tryStepReduction ∘ opcode-inversion ∘ correct_<op>_native`. -/
def StepFact (data : ProverData (ZMod p)) (r : RowFacts p) : Prop :=
  StateTruth r.statePull data →
  (∀ mp ∈ r.memPulls,
    SP1Clean.Channels.MemoryMsg.isU64 mp.1 ∧
    ValueAt data (MemoryMsg.locOf mp.1) mp.2 mp.1.value) →
  StateTruth r.statePush data ∧ ∀ m ∈ r.memPushes, MemTruth m data

/-! ## The Program channel's semantic guarantee -/

/-- A Program-bus message projected to the committed program-row column shape — the operands' four limbs
reassembled as `Word`s — so `decodedInROM` can be applied to a `ProgramMsg`. -/
def rowOfMsg (m : ProgramMsg (ZMod p)) : SP1Clean.ProgramChip.ProgramRow (ZMod p) where
  pc0 := m.pc0
  pc1 := m.pc1
  pc2 := m.pc2
  opcode := m.opcode
  op_a := m.op_a
  op_b := #v[m.op_b0, m.op_b1, m.op_b2, m.op_b3]
  imm_b := m.imm_b
  op_c := #v[m.op_c0, m.op_c1, m.op_c2, m.op_c3]
  op_a_0 := m.op_a_0
  imm_c := m.imm_c

/-- **The Program channel's semantic guarantee** — the fetch-decode correspondence: the message's decode
bounds (`RowSpec`) **plus** that the fetched row is the decode of the committed program's ROM at its pc
(`decodedInROM`, over `Commit.progOf data`). So the `is_real`-gated opcode a chip pins in its fetch is a
real decode of the committed guest program — the foundation of opcode-based Sail dispatch. Structural
`RowSpec` is what a push proves row-locally (the `Owed`); the `decodedInROM` half is the finished-channel
balance/vkey fact a pull receives (grounded by the ROM provider), so `programChannel` becomes a semantic
`VmChannel` (`Owed := RowSpec`, `Guarantees := ProgTruth`) exactly like the State channel. -/
def ProgTruth (m : ProgramMsg (ZMod p)) (data : ProverData (ZMod p)) : Prop :=
  SP1Clean.Channels.ProgramMsg.RowSpec m ∧
    SP1Clean.Soundness.Target.decodedInROM (Commit.progOf data) (rowOfMsg m)

end SP1Clean.Semantics
