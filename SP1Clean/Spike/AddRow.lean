import SP1Clean.Spike.Channels
import SP1Clean.Spike.Engine
import SP1Clean.Proofs.Operations.AddOperation.Formal
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Spike `AddRow` — one chip-shaped `GeneralFormalCircuit` over the semantic channels

**Phase-1 de-risk spike.** One row mirroring the essential `AddChip` emission shape, simplified but
honest (spike license, all deviations noted):

- **Emissions** (via the `VmChannel` veneer): `spikeState.pullIf is_real` of the current `(clk, pc)`
  and `pushIf` of the advanced `(clk+8, pc0+4)`; `spikeMemory.pullIf is_real` of the three register
  read-priors (rs1/rs2/rd at their previous timestamps) and `pushIf` of the rs1/rs2 read-backs at
  `clk+2`/`clk+3` and the rd write of `result` at `clk+4`.
- **One real gadget**: the production `AddOperation.circuit` is composed as a true subcircuit (its
  byte-bus range checks ride along), so the add identity and `isU64 result` are *derived*, with the
  operand `isU64`s flowing from the memory pulls' `MemTruth` — the production Option-B cycle-break.
- **Elided** (spike license): the clock byte-timestamp gadgets and the program bus. The numeric
  bounds they would prove are carried in `Assumptions` (`clk_low + 8` fits 24 bits, `pc0 + 4` fits
  16 bits, register indices `< 32`), and the fetch/decode content is folded into the `TryStepLift`
  seam. The clock is the production single-`clk_low` 24-bit convention (no 16/8 split).
- **`Spec` = opaque re-exports**: the pull guarantees (`StateTruth`/`MemTruth` of the pulled
  messages) threaded verbatim from `h_holds`, plus `is_real` binarity and the derived add facts.
- **`ProverAssumptions` = `Spec`**: Clean's completeness obligation for a `pullIf` interact op is the
  pull's own `Guarantees` (`ConstraintsHold.Completeness`, `.interact i ↦ i.Guarantees env`), so the
  honest prover must supply exactly the semantic truths the `Spec` re-exports.
- **`stepFact`/`frameFact`**: `Spec` (at `is_real = 1`) discharges the engine's per-row `StepFact`
  and `FrameFact` obligations, given the **`TryStepLift` named hypothesis** — the Phase-3
  TryStepReduction seam (one `try_step` of the committed program at this pc, with current operands,
  lands at `pc+4` with `rd := result` and all other registers preserved). In the spike this seam also
  subsumes the fetch/decode obligation (that the committed ROM at this pc decodes to this ADD), which
  production Phase 3 will discharge from the program bus + `correct_add_native`. Note the honest
  gap: `TryStepLift` is unprovable for `rd = x0` with a non-zero result (production handles `op_a_0`
  separately); the spike's concrete rows use `rd ∈ {x3, x4}`. -/

namespace SP1Clean.Spike.AddRow

open Circuit
open Sail LeanRV64D LeanRV64D.Functions
open SP1Clean.Soundness.Target
open SP1Clean.Semantics
open SP1Clean.Channels (StateMsg MemoryMsg byteChannel)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

/-- The row's columns: the 24-bit-split clock, the 3-limb pc, the three register indices, the two
operand words (= the read-prior values of rs1/rs2), the result word, the three read-priors'
timestamps (rd's prior value is pulled and discarded), and the `is_real` selector. -/
structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  pc0 : F
  pc1 : F
  pc2 : F
  rs1 : F
  rs2 : F
  rd : F
  op_b_val : Word F
  op_c_val : Word F
  result : Word F
  b_prev_clk_high : F
  b_prev_clk_low : F
  c_prev_clk_high : F
  c_prev_clk_low : F
  a_prev_clk_high : F
  a_prev_clk_low : F
  a_prev_val : Word F
  is_real : F
deriving ProvableStruct

/-! ## The row's bus messages (value level, shared by `Spec`/`rowFactsOf`/the engine) -/

def statePullMsg (input : Inputs (ZMod p)) : StateMsg (ZMod p) :=
  ⟨input.clk_high, input.clk_low, input.pc0, input.pc1, input.pc2⟩

def statePushMsg (input : Inputs (ZMod p)) : StateMsg (ZMod p) :=
  ⟨input.clk_high, input.clk_low + 8, input.pc0 + 4, input.pc1, input.pc2⟩

def bPullMsg (input : Inputs (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨input.b_prev_clk_high, input.b_prev_clk_low, input.rs1, 0, 0, input.op_b_val⟩

def cPullMsg (input : Inputs (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨input.c_prev_clk_high, input.c_prev_clk_low, input.rs2, 0, 0, input.op_c_val⟩

def aPullMsg (input : Inputs (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨input.a_prev_clk_high, input.a_prev_clk_low, input.rd, 0, 0, input.a_prev_val⟩

def bPushMsg (input : Inputs (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨input.clk_high, input.clk_low + 2, input.rs1, 0, 0, input.op_b_val⟩

def cPushMsg (input : Inputs (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨input.clk_high, input.clk_low + 3, input.rs2, 0, 0, input.op_c_val⟩

def aPushMsg (input : Inputs (ZMod p)) : MemoryMsg (ZMod p) :=
  ⟨input.clk_high, input.clk_low + 4, input.rd, 0, 0, input.result⟩

/-! ## The circuit -/

/-- The gate, the composed `AddOperation`, and the eight veneer emissions. -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  -- the `is_real` boolean gate, inline/shallow (the production idiom — it also discharges the
  -- off-gate pull `Requirements` without listing the pull channels in `channelsWithRequirements`)
  assertZero (input.is_real * (input.is_real - 1))
  -- the one real gadget: SP1's AddOperation as a composed subcircuit
  assertion AddOperation.circuit
    ⟨input.op_b_val, input.op_c_val, { value := input.result }, input.is_real⟩
  -- State bus: pull the current (clk, pc), push the advanced (clk+8, pc0+4)
  spikeState.pullIf input.is_real
    ⟨input.clk_high, input.clk_low, input.pc0, input.pc1, input.pc2⟩
  spikeState.pushIf input.is_real
    ⟨input.clk_high, input.clk_low + 8, input.pc0 + 4, input.pc1, input.pc2⟩
  -- Memory bus: the three read-priors at their previous timestamps (pulls receive `MemTruth`)
  spikeMemory.pullIf input.is_real
    ⟨input.b_prev_clk_high, input.b_prev_clk_low, input.rs1, 0, 0, input.op_b_val⟩
  spikeMemory.pullIf input.is_real
    ⟨input.c_prev_clk_high, input.c_prev_clk_low, input.rs2, 0, 0, input.op_c_val⟩
  spikeMemory.pullIf input.is_real
    ⟨input.a_prev_clk_high, input.a_prev_clk_low, input.rd, 0, 0, input.a_prev_val⟩
  -- the rs1/rs2 read-backs at clk+2/clk+3 and the rd write at clk+4 (pushes owe `isU64`)
  spikeMemory.pushIf input.is_real
    ⟨input.clk_high, input.clk_low + 2, input.rs1, 0, 0, input.op_b_val⟩
  spikeMemory.pushIf input.is_real
    ⟨input.clk_high, input.clk_low + 3, input.rs2, 0, 0, input.op_c_val⟩
  spikeMemory.pushIf input.is_real
    ⟨input.clk_high, input.clk_low + 4, input.rd, 0, 0, input.result⟩

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRaw, spikeState.toRaw, spikeMemory.toRaw]
  channelsLawful := by
    simp [circuit_norm, main, AddOperation.circuit, spikeState, spikeMemory, byteChannel]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p)))
      = [byteChannel.toRaw, spikeState.toRaw, spikeMemory.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- The numeric bounds the elided byte-timestamp gadgets would prove, plus the register-index bounds
the elided program bus would decode (spike license — carried as `Assumptions`). -/
def Assumptions (input : Inputs (ZMod p)) (_ : ProverData (ZMod p)) : Prop :=
  input.is_real = 1 →
    input.clk_low.val + 8 < 2 ^ 24 ∧
    input.pc0.val + 4 < 2 ^ 16 ∧
    input.rs1.val < 32 ∧ input.rs2.val < 32 ∧ input.rd.val < 32

/-- The row's semantic contract: `is_real` binary, and on a real row the **opaque re-exports** of the
four pull guarantees (the state pull's `StateTruth`, the three read-priors' `MemTruth`s — threaded
verbatim from `h_holds`) plus the derived add facts (`isU64 result` and the 64-bit add identity, from
the composed `AddOperation`). -/
def Spec (input : Inputs (ZMod p)) (data : ProverData (ZMod p)) : Prop :=
  (input.is_real = 0 ∨ input.is_real = 1) ∧
  (input.is_real = 1 →
    StateTruth (statePullMsg input) data ∧
    MemTruth (bPullMsg input) data ∧
    MemTruth (cPullMsg input) data ∧
    MemTruth (aPullMsg input) data ∧
    Word.isU64 input.result ∧
    Word.toBitVec64 input.result
      = Word.toBitVec64 input.op_b_val + Word.toBitVec64 input.op_c_val)

theorem soundness : GeneralFormalCircuit.Soundness (F := ZMod p) (Output := unit) main Assumptions
    (fun input _ data => Spec input data) := by
  circuit_proof_start
  simp only [circuit_norm, spikeState, spikeMemory] at h_holds ⊢
  obtain ⟨h_gate, h_add, h_spull, h_bpull, h_cpull, h_apull⟩ := h_holds
  have h_bin := bool_of_mul_pred h_gate
  have h_operands : input_is_real = 1 →
      Word.isU64 input_op_b_val ∧ Word.isU64 input_op_c_val := by
    intro hr
    have hneg : -(input_is_real) = -1 := by rw [hr]
    exact ⟨(h_bpull hneg).1, (h_cpull hneg).1⟩
  have h_addspec := h_add ⟨h_operands, h_bin⟩
  refine ⟨⟨h_bin, fun hr => ?_⟩, ?_⟩
  · have hneg : -(input_is_real) = -1 := by rw [hr]
    simp only [statePullMsg, bPullMsg, cPullMsg, aPullMsg]
    exact ⟨h_spull hneg, h_bpull hneg, h_cpull hneg, h_apull hneg,
      (h_addspec hr).1, (h_addspec hr).2⟩
  · and_intros <;>
      first
        | exact Or.inl rfl
        | exact fun h1 h0 => off_gate_vacuous h_bin h1 h0
        | exact fun _ h0 => (h_bpull (by rw [h_bin.resolve_left h0])).1
        | exact fun _ h0 => (h_cpull (by rw [h_bin.resolve_left h0])).1
        | exact fun _ h0 => (h_addspec (h_bin.resolve_left h0)).1

theorem completeness :
    GeneralFormalCircuit.Completeness (F := ZMod p) (Output := unit) main
      (fun input data _ => Spec input data) (fun _ _ _ => True) := by
  circuit_proof_start
  obtain ⟨h_bin, h_truths⟩ := h_assumptions
  simp only [circuit_norm, spikeState, spikeMemory, statePullMsg, bPullMsg, cPullMsg,
    aPullMsg, AddOperation.circuit, AddOperation.Assumptions, AddOperation.Spec] at h_truths ⊢
  refine ⟨?_, ⟨⟨?_, h_bin⟩, ?_⟩, ?_, ?_, ?_, ?_⟩
  · rcases h_bin with h | h <;> rw [h] <;> simp
  · exact fun hr => ⟨((h_truths hr).2.1).1, ((h_truths hr).2.2.1).1⟩
  · exact fun hr => ⟨(h_truths hr).2.2.2.2.1, (h_truths hr).2.2.2.2.2⟩
  · exact fun hr => (h_truths (neg_inj.mp hr)).1
  · exact fun hr => (h_truths (neg_inj.mp hr)).2.1
  · exact fun hr => (h_truths (neg_inj.mp hr)).2.2.1
  · exact fun hr => (h_truths (neg_inj.mp hr)).2.2.2.1

/-- The spike AddRow as a `GeneralFormalCircuit`. `ProverAssumptions = Spec` — the completeness
obligation of a semantic `pullIf` is the pull's own guarantee, so the honest prover supplies exactly
the truths the `Spec` re-exports. -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  elaborated
  Assumptions := Assumptions
  Spec := fun input _ data => Spec input data
  ProverAssumptions := fun input data _ => Spec input data
  ProverSpec := fun _ _ _ => True
  soundness := soundness
  completeness := completeness
  channelsWithRequirements := [spikeMemory.toRaw]
  requirementsChannelsLawful := fun input_var i₀ => by
    simp only [circuit_norm, main, spikeState, spikeMemory, byteChannel, AddOperation.circuit]
    grind

/-! ## The engine-facing step/frame facts -/

/-- The engine-facing row facts of one AddRow: state pull/push, a dummy fetch (the spike carries no
program bus), the three read-priors with their read times (`+2`/`+3`/`+3` — rd's prior is observed
pre-write), and the three pushes. -/
def rowFactsOf (input : Inputs (ZMod p)) : RowFacts p where
  statePull := statePullMsg input
  statePush := statePushMsg input
  fetch := ⟨0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0⟩
  memPulls := [(bPullMsg input, StateMsg.timeNat (statePullMsg input) + 2),
               (cPullMsg input, StateMsg.timeNat (statePullMsg input) + 3),
               (aPullMsg input, StateMsg.timeNat (statePullMsg input) + 3)]
  memPushes := [bPushMsg input, cPushMsg input, aPushMsg input]

/-- **The TryStepReduction seam (named hypothesis; Phase 3 closes it).** From any state of the
committed program at this row's pc — ROM intact, configured, operand registers holding the current
operand values, and the result related to the operands by the 64-bit add identity — one real
`try_step` lands at `pc0 + 4` with `rd := result` and every other register preserved. In production
this is `tryStepReduction ∘ opcode-inversion ∘ correct_add_native`, consuming the program-bus fetch;
the spike has no program bus, so the "this pc holds this ADD" content is folded into the seam. -/
def TryStepLift (input : Inputs (ZMod p)) (data : ProverData (ZMod p)) : Prop :=
  ∀ s : SailState,
    s.regs.get? Register.PC = some (pcBits input.pc0 input.pc1 input.pc2) →
    RomLoaded (Commit.progOf data) s →
    SailConfigured s →
    s.get_reg? (BitVec.ofNat 5 input.rs1.val) = some (Word.toBitVec64 input.op_b_val) →
    s.get_reg? (BitVec.ofNat 5 input.rs2.val) = some (Word.toBitVec64 input.op_c_val) →
    Word.toBitVec64 input.result
      = Word.toBitVec64 input.op_b_val + Word.toBitVec64 input.op_c_val →
    ∃ s' : SailState,
      SailStep s s' ∧
      s'.regs.get? Register.PC = some (pcBits (input.pc0 + 4) input.pc1 input.pc2) ∧
      RomLoaded (Commit.progOf data) s' ∧
      SailConfigured s' ∧
      s'.get_reg? (BitVec.ofNat 5 input.rd.val) = some (Word.toBitVec64 input.result) ∧
      ∀ j : BitVec 5, j ≠ BitVec.ofNat 5 input.rd.val → s'.get_reg? j = s.get_reg? j

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- A register-shaped memory message's decoded location. -/
lemma locOf_regMsg {hi lo a : ZMod p} {v : Word (ZMod p)} (ha : a.val < 32) :
    MemoryMsg.locOf (⟨hi, lo, a, 0, 0, v⟩ : MemoryMsg (ZMod p))
      = MemLoc.reg (BitVec.ofNat 5 a.val) := by
  simp only [MemoryMsg.locOf]
  rw [if_pos ⟨ha, trivial, trivial⟩]

omit [Fact (2 ^ 17 < p)] in
/-- The row's message times, ℕ-decoded: the pushes at `t+2`/`t+3`/`t+4` and the state push at `t+8`
(where `t` is the state pull's time), from the 24-bit clock bound. Needs `2 ^ 24 < p` (the low clock
must not wrap in the field). -/
lemma msg_times [Fact (2 ^ 24 < p)] {input : Inputs (ZMod p)}
    (hclk : input.clk_low.val + 8 < 2 ^ 24) :
    MemoryMsg.timeNat (bPushMsg input) = StateMsg.timeNat (statePullMsg input) + 2 ∧
    MemoryMsg.timeNat (cPushMsg input) = StateMsg.timeNat (statePullMsg input) + 3 ∧
    MemoryMsg.timeNat (aPushMsg input) = StateMsg.timeNat (statePullMsg input) + 4 ∧
    StateMsg.timeNat (statePushMsg input) = StateMsg.timeNat (statePullMsg input) + 8 := by
  have hp : 2 ^ 24 < p := Fact.out
  have hv : ∀ k : ℕ, k ≤ 8 → (input.clk_low + (k : ℕ)).val = input.clk_low.val + k := by
    intro k hk
    have hkv : ((k : ℕ) : ZMod p).val = k := ZMod.val_natCast_of_lt (by omega)
    rw [ZMod.val_add_of_lt (by rw [hkv]; omega), hkv]
  simp only [bPushMsg, cPushMsg, aPushMsg, statePushMsg, statePullMsg,
    MemoryMsg.timeNat, StateMsg.timeNat, clkNat]
  rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast,
      show (3 : ZMod p) = ((3 : ℕ) : ZMod p) by norm_cast,
      show (4 : ZMod p) = ((4 : ℕ) : ZMod p) by norm_cast,
      show (8 : ZMod p) = ((8 : ℕ) : ZMod p) by norm_cast,
      hv 2 (by omega), hv 3 (by omega), hv 4 (by omega), hv 8 (by omega)]
  omega

/-- **`Spec` (on a real row) discharges the engine's `StepFact`**, given the `TryStepLift` seam:
the state advances one chain step (via the seam), the read-back pushes' `MemTruth`s are literally
the pulls' read-time currencies, and the write push's `MemTruth` is the seam's `rd := result`
landed at the write epoch. -/
theorem stepFact [Fact (2 ^ 24 < p)] {input : Inputs (ZMod p)} {data : ProverData (ZMod p)}
    (h_lift : TryStepLift input data) (h_spec : Spec input data)
    (h_assm : Assumptions input data) (h_real : input.is_real = 1) :
    StepFact data (rowFactsOf input) := by
  obtain ⟨hclk, hpc4, hrs1, hrs2, hrd⟩ := h_assm h_real
  obtain ⟨-, htr⟩ := h_spec
  obtain ⟨-, -, -, -, hres_u64, hres_add⟩ := htr h_real
  obtain ⟨htb, htc, hta, ht8⟩ := msg_times (input := input) hclk
  intro h_pull h_mem
  simp only [rowFactsOf] at h_pull h_mem ⊢
  have hbcur := h_mem (bPullMsg input, StateMsg.timeNat (statePullMsg input) + 2) (by simp)
  have hccur := h_mem (cPullMsg input, StateMsg.timeNat (statePullMsg input) + 3) (by simp)
  have hlocb : MemoryMsg.locOf (bPullMsg input) = MemLoc.reg (BitVec.ofNat 5 input.rs1.val) :=
    locOf_regMsg hrs1
  have hlocc : MemoryMsg.locOf (cPullMsg input) = MemLoc.reg (BitVec.ofNat 5 input.rs2.val) :=
    locOf_regMsg hrs2
  -- the common per-loader step derivation (chain to `s`, operands current at `s`, the seam's step)
  have h_step_at : ∀ s0, IsInitialState (Commit.progOf data) s0 → ZeroRegs s0 →
      ∃ (n : ℕ) (s s' : SailState),
        SailChain n s0 s ∧ chainState s0 n = some s ∧
        StateMsg.timeNat (statePullMsg input) = Commit.initClkNat data + 8 * n ∧
        SailStep s s' ∧
        s'.regs.get? Register.PC = some (pcBits (input.pc0 + 4) input.pc1 input.pc2) ∧
        RomLoaded (Commit.progOf data) s' ∧ SailConfigured s' ∧
        s'.get_reg? (BitVec.ofNat 5 input.rd.val) = some (Word.toBitVec64 input.result) := by
    intro s0 hini hzero
    obtain ⟨n, s, hchain, htime, hpc, hrom, hcfg⟩ := h_pull s0 hini hzero
    have hcs : chainState s0 n = some s := chainState_of_sailChain hchain
    have hbreg : s.get_reg? (BitVec.ofNat 5 input.rs1.val)
        = some (Word.toBitVec64 input.op_b_val) := by
      have hv := hbcur.2 s0 hini hzero
      rw [hlocb, microValue_reg, regEpoch_eq_of (n := n) (by omega) (by omega), hcs] at hv
      simpa [locContent, bPullMsg] using hv
    have hcreg : s.get_reg? (BitVec.ofNat 5 input.rs2.val)
        = some (Word.toBitVec64 input.op_c_val) := by
      have hv := hccur.2 s0 hini hzero
      rw [hlocc, microValue_reg, regEpoch_eq_of (n := n) (by omega) (by omega), hcs] at hv
      simpa [locContent, cPullMsg] using hv
    obtain ⟨s', hstep, hpc', hrom', hcfg', hrd', -⟩ :=
      h_lift s hpc hrom hcfg hbreg hcreg hres_add
    exact ⟨n, s, s', hchain, hcs, htime, hstep, hpc', hrom', hcfg', hrd'⟩
  constructor
  · -- StateTruth of the pushed state: one more chain step
    intro s0 hini hzero
    obtain ⟨n, s, s', hchain, hcs, htime, hstep, hpc', hrom', hcfg', hrd'⟩ :=
      h_step_at s0 hini hzero
    refine ⟨n + 1, s', hchain.snoc hstep, by rw [ht8]; omega, ?_, hrom', hcfg'⟩
    simpa [statePushMsg] using hpc'
  · -- the pushes' MemTruth
    intro m hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl | rfl | rfl
    · -- rs1 read-back: literally the pull's currency at the same micro-time
      refine ⟨hbcur.1, ?_⟩
      rw [show MemoryMsg.locOf (bPushMsg input) = MemLoc.reg (BitVec.ofNat 5 input.rs1.val)
        from locOf_regMsg hrs1, htb]
      rw [hlocb] at hbcur
      exact hbcur.2
    · refine ⟨hccur.1, ?_⟩
      rw [show MemoryMsg.locOf (cPushMsg input) = MemLoc.reg (BitVec.ofNat 5 input.rs2.val)
        from locOf_regMsg hrs2, htc]
      rw [hlocc] at hccur
      exact hccur.2
    · -- rd write: the seam's `rd := result`, landed at the write epoch
      refine ⟨hres_u64, ?_⟩
      rw [show MemoryMsg.locOf (aPushMsg input) = MemLoc.reg (BitVec.ofNat 5 input.rd.val)
        from locOf_regMsg hrd, hta]
      intro s0 hini hzero
      obtain ⟨n, s, s', hchain, hcs, htime, hstep, hpc', hrom', hcfg', hrd'⟩ :=
        h_step_at s0 hini hzero
      rw [microValue_reg, regEpoch_eq_succ_of (n := n) (by omega) (by omega),
        chainState_succ_of hcs (stepOnce_of_sailStep hstep)]
      simpa [locContent, aPushMsg] using hrd'

/-- **`Spec` (on a real row) discharges the engine's `FrameFact`**, given the `TryStepLift` seam:
the step writes only `rd` (the seam's preservation clause), so any register value the row's pushes
agree with persists across the window. -/
theorem frameFact [Fact (2 ^ 24 < p)] {input : Inputs (ZMod p)} {data : ProverData (ZMod p)}
    (h_lift : TryStepLift input data) (h_spec : Spec input data)
    (h_assm : Assumptions input data) (h_real : input.is_real = 1) :
    FrameFact data (rowFactsOf input) := by
  obtain ⟨hclk, hpc4, hrs1, hrs2, hrd⟩ := h_assm h_real
  obtain ⟨-, htr⟩ := h_spec
  obtain ⟨-, -, -, -, hres_u64, hres_add⟩ := htr h_real
  obtain ⟨htb, htc, hta, ht8⟩ := msg_times (input := input) hclk
  intro h_pull h_mem i v hpush hv
  simp only [rowFactsOf] at h_pull h_mem hpush hv ⊢
  have hbcur := h_mem (bPullMsg input, StateMsg.timeNat (statePullMsg input) + 2) (by simp)
  have hccur := h_mem (cPullMsg input, StateMsg.timeNat (statePullMsg input) + 3) (by simp)
  have hlocb : MemoryMsg.locOf (bPullMsg input) = MemLoc.reg (BitVec.ofNat 5 input.rs1.val) :=
    locOf_regMsg hrs1
  have hlocc : MemoryMsg.locOf (cPullMsg input) = MemLoc.reg (BitVec.ofNat 5 input.rs2.val) :=
    locOf_regMsg hrs2
  rw [ht8]
  intro s0 hini hzero
  obtain ⟨n, s, hchain, htime, hpc, hrom, hcfg⟩ := h_pull s0 hini hzero
  have hcs : chainState s0 n = some s := chainState_of_sailChain hchain
  have hbreg : s.get_reg? (BitVec.ofNat 5 input.rs1.val)
      = some (Word.toBitVec64 input.op_b_val) := by
    have hv' := hbcur.2 s0 hini hzero
    rw [hlocb, microValue_reg, regEpoch_eq_of (n := n) (by omega) (by omega), hcs] at hv'
    simpa [locContent, bPullMsg] using hv'
  have hcreg : s.get_reg? (BitVec.ofNat 5 input.rs2.val)
      = some (Word.toBitVec64 input.op_c_val) := by
    have hv' := hccur.2 s0 hini hzero
    rw [hlocc, microValue_reg, regEpoch_eq_of (n := n) (by omega) (by omega), hcs] at hv'
    simpa [locContent, cPullMsg] using hv'
  obtain ⟨s', hstep, hpc', hrom', hcfg', hrd', hpres⟩ :=
    h_lift s hpc hrom hcfg hbreg hcreg hres_add
  have hvs := hv s0 hini hzero
  rw [microValue_reg, regEpoch_eq_of (n := n) (by omega) (by omega), hcs] at hvs
  rw [microValue_reg, regEpoch_eq_succ_of (n := n) (by omega) (by omega),
    chainState_succ_of hcs (stepOnce_of_sailStep hstep)]
  by_cases hird : i = BitVec.ofNat 5 input.rd.val
  · subst hird
    have hval : input.result = v :=
      hpush (aPushMsg input) (by simp) (locOf_regMsg hrd)
    simpa [locContent, hval] using hrd'
  · rw [show ((some s').bind fun st => locContent st (MemLoc.reg i))
        = s'.get_reg? i from rfl, hpres i hird]
    simpa [locContent] using hvs

end SP1Clean.Spike.AddRow
