import SP1Clean.Model.Channels
import Clean.Circuit.Basic
import Clean.Circuit.Subcircuit
import Clean.Circuit.Channel
import Clean.Utils.Tactics

/-! # The in-circuit Memory-boundary finalizer (pull side of SP1's memory init/finalize chips)

The pull twin of `MemoryProviderChip` (`Proofs/Chips/MemoryProviderChip.lean`). On the W11-flipped
Memory bus every per-address access chain leaves **two** unmatched endpoints: the first access's
read-prior (a chip `pullIf`, cancelled by the init provider's boundary *push*) and the last access's
write/read-back (a chip `pushIf`, which nothing pulls). Without an in-circuit **finalize pull** the
memory channel's `BalancedInteractions` is unsatisfiable for any real execution — the bus could never
close. This chip is that finalize row: it witnesses a **boolean** multiplicity `m` (inline shallow
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

/-- Witness a boolean multiplicity `m` and pull the claimed final memory record `input` with
multiplicity `m` (the flipped bus's finalize side: the pull cancelling the chain's last push). -/
def main (input : Var MemoryMsg (ZMod p)) : Circuit (ZMod p) Unit := do
  let m ← witnessField 1
  assertZero (m * (m - 1))
  memoryChannel.pullIf m input

instance elaborated : ElaboratedCircuit (ZMod p) MemoryMsg unit main where
  localLength _ := 1
  output _ _ := ()
  channelsWithGuarantees := [memoryChannel.toRaw]

set_option linter.unusedSectionVars false in
@[circuit_norm] lemma channelsWithGuarantees_eq :
    ((elaborated (p := p)).channelsWithGuarantees : List (RawChannel (ZMod p))) =
      [memoryChannel.toRaw] := rfl
set_option linter.unusedSectionVars false in
@[circuit_norm] lemma localLength_eq (x : Var MemoryMsg (ZMod p)) :
    (elaborated (p := p)).localLength x = 1 := rfl

/-- The Memory-boundary finalizer: pulls the claimed final record of an address chain. `Spec := True`
(a pull receives the `isU64` guarantee and owes nothing on the verifier side; the finalize key's
validity is a bus-balance fact at the capstone, not a per-row constraint). `ProverAssumptions` is
the channel guarantee `MemoryMsg.isU64 ∧ MemoryMsg.ClkBound`: a pull's *completeness* must exhibit the
pulled record's guarantee — in a real trace the finalize value is the chain's last written word, already
`U64`, at that chain's last access clock, already `< 2^24`. The off-gate obligations (a pull at
a multiplicity other than `-1`/`0` would act as a send) are vacuous under the boolean gate
(`off_gate_vacuous`). -/
def circuit : GeneralFormalCircuit (ZMod p) MemoryMsg unit where
  main
  Spec _ _ _ := True
  ProverAssumptions input _ _ := MemoryMsg.isU64 input ∧ MemoryMsg.ClkBound input
  channelsWithRequirements := []
  soundness := by
    circuit_proof_start
    have hb : env.get i₀ * (env.get i₀ - 1) = 0 := h_holds.1
    exact fun h1 h0 => off_gate_vacuous (bool_of_mul_pred hb) h1 h0
  completeness := by
    circuit_proof_start
    refine ⟨by simp [h_env], fun _ => ?_⟩
    simp only [memoryChannel, MemoryMsg.isU64, MemoryMsg.ClkBound]
    exact h_assumptions
  requirementsChannelsLawful := fun input_var i₀ => by
    simp only [circuit_norm, main, memoryChannel]; grind

end SP1Clean.MemoryFinalizeChip
