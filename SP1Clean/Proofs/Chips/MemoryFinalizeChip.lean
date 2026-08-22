import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics
import Clean.Utils.Tactics.ProvableStructDeriving

/-! # The in-circuit Memory-boundary finalizer (pull side of SP1's memory init/finalize chips)

The pull twin of `MemoryProviderChip` (`Proofs/Chips/MemoryProviderChip.lean`). On the W11-flipped
Memory bus every per-address access chain leaves **two** unmatched endpoints: the first access's
read-prior (a chip `pullIf`, cancelled by the init provider's boundary *push*) and the last access's
write/read-back (a chip `pushIf`, which nothing pulls). Without an in-circuit **finalize pull** the
memory channel's `BalancedInteractions` is unsatisfiable for any real execution — the bus could never
close. This chip is that finalize row: it reads an explicit **boolean** multiplicity `m` (inline shallow
`assertZero (m*(m-1))`, the Phase-0c gate idiom, so the capstone seam can extract mult-binarity from
`ConstraintsHold.Shallow` — the field→ℤ balance translation needs every memory-bus multiplicity in
`{-1, 0, 1}`; SP1's memory-global finalize chip is likewise one boolean-gated row per address) and
`pullIf m`-pulls the claimed final record.

A pull *receives* the channel guarantee (`MemoryMsg.isU64`) and owes nothing, so
`channelsWithRequirements = []` and the local `Spec` is `True` — the finalize row's meaning (its key
really is the last access of its address chain) is a bus-balance fact established at the capstone
(`Soundness/MemoryGlobal.lean`'s boundary predicates), not a per-row constraint. -/

namespace SP1Clean.MemoryFinalizeChip

open Circuit
open SP1Clean.Channels (memoryChannel MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- One memory-finalize row: the claimed final message and its boolean activity selector. -/
structure Inputs (F : Type) where
  clk_high : F
  clk_low : F
  addr0 : F
  addr1 : F
  addr2 : F
  value : Word F
  multiplicity : F
deriving ProvableStruct

/-- Forget the provider-only multiplicity column and recover the Memory-bus payload. -/
def Inputs.toMessage {R : Type} (input : Inputs R) : MemoryMsg R where
  clk_high := input.clk_high
  clk_low := input.clk_low
  addr0 := input.addr0
  addr1 := input.addr1
  addr2 := input.addr2
  value := input.value

omit [Fact p.Prime] [Fact (2 ^ 17 < p)] in
/-- The selector is the field immediately following the nine-field Memory message prefix. -/
@[circuit_norm] theorem Inputs.varFromOffset_multiplicity (offset : ℕ) :
    (varFromOffset Inputs offset : Var Inputs (ZMod p)).multiplicity =
      var { index := offset + size MemoryMsg } := by
  simp only [circuit_norm]

/-- Read a boolean multiplicity `m` and pull the claimed final memory record `input.message` with
multiplicity `m` (the flipped bus's finalize side: the pull cancelling the chain's last push). -/
def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertZero (input.multiplicity * (input.multiplicity - 1))
  memoryChannel.pullIf input.multiplicity input.toMessage

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 0
  output _ _ := ()
  channelsWithGuarantees := [memoryChannel.toRaw]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) =
      [memoryChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var Inputs (ZMod p)) :
    (elaborated (p := p)).localLength x = 0 := rfl

/-- The Memory-boundary finalizer: pulls the claimed final record of an address chain. `Spec := True`
(a pull receives the `isU64` guarantee and owes nothing on the verifier side; the finalize key's
validity is a bus-balance fact at the capstone, not a per-row constraint). `ProverAssumptions` is
the channel guarantee `MemoryMsg.isU64 ∧ MemoryMsg.ClkBound`: a pull's *completeness* must exhibit the
pulled record's guarantee — in a real trace the finalize value is the chain's last written word, already
`U64`, at that chain's last access clock, already `< 2^24`; it also supplies the explicit boolean
selector. The off-gate obligations (a pull at
a multiplicity other than `-1`/`0` would act as a send) are vacuous under the boolean gate
(`off_gate_vacuous`). -/
def circuit : GeneralFormalCircuit (ZMod p) Inputs unit where
  main
  Spec _ _ _ := True
  ProverAssumptions input _ _ := MemoryMsg.isU64 input.toMessage ∧
    MemoryMsg.ClkBound input.toMessage ∧ (input.multiplicity = 0 ∨ input.multiplicity = 1)
  channelsWithRequirements := []
  soundness := by
    circuit_proof_start [Inputs.toMessage]
    have hb : input_multiplicity * (input_multiplicity - 1) = 0 := h_holds.1
    exact off_gate_vacuous (bool_of_mul_pred hb)
  completeness := by
    circuit_proof_start [Inputs.toMessage]
    refine ⟨?_, fun _ => ⟨h_assumptions.1, h_assumptions.2.1⟩⟩
    rcases h_assumptions.2.2 with h | h <;> simp [h]
  requirementsChannelsLawful := fun input_var i₀ => by
    simp only [circuit_norm, main, memoryChannel]; grind

end SP1Clean.MemoryFinalizeChip
