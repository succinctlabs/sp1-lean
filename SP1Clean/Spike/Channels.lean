import SP1Clean.Model.VmChannel
import SP1Clean.Model.Semantics.Truth
import SP1Clean.Model.Channels

/-! # Spike channels — semantic `VmChannel`s over the real truth predicates

**Phase-1 de-risk spike** (`SP1Clean/Spike/`, to be deleted after the real sweep). The two semantic
channels the spike threads end-to-end, built on the Phase-0 `VmChannel` veneer
(`Model/VmChannel.lean`) and the real execution-truth predicates (`Model/Semantics/Truth.lean`):

- `spikeState` — pull-side `Guarantees := Semantics.StateTruth` (the committed program's execution is
  at this `(clk, pc)`), push-side `Owed := True` (today's State-bus strength: a state push proves
  nothing row-locally; the engine closes the gap globally).
- `spikeMemory` — pull-side `Guarantees := Semantics.MemTruth` (the value is the true register/RAM
  content at the message's own micro-time), push-side `Owed := MemoryMsg.isU64` (today's Memory-bus
  strength: a memory push still owes only the value's limb hygiene).

The message types are the **production** `StateMsg`/`MemoryMsg` (`Model/Channels.lean`); the names are
distinct (`"SpikeState"`/`"SpikeMemory"`) so the spike never collides with the production buses. -/

namespace SP1Clean.Spike

open SP1Clean.Channels (StateMsg MemoryMsg)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The spike State channel: pulls receive full execution truth (`StateTruth`), pushes owe nothing
row-locally (the timestamped grounding engine closes the gap). -/
def spikeState : VmChannel (ZMod p) StateMsg where
  name := "SpikeState"
  Guarantees := Semantics.StateTruth
  Owed _ _ := True

/-- The spike Memory channel: pulls receive execution truth of the value at the message's own
micro-time (`MemTruth`, which subsumes `isU64`), pushes owe only `isU64` (today's row-local
strength — a read-back/write cannot locally prove "no intervening write"). -/
def spikeMemory : VmChannel (ZMod p) MemoryMsg where
  name := "SpikeMemory"
  Guarantees := Semantics.MemTruth
  Owed m _ := SP1Clean.Channels.MemoryMsg.isU64 m

omit [Fact (2 ^ 17 < p)] in
/-- Distinctness of the two spike buses, in the `= False` simp shape the production channel pairs use
(`Model/Channels.lean`), so `interactionsWith`-style filters and channel-list membership goals reduce
without record expansion. -/
@[circuit_norm] lemma spikeState_eq_spikeMemory_false :
    ((spikeState (p := p)).toRaw = (spikeMemory (p := p)).toRaw) = False := by
  simp only [eq_iff_iff, iff_false]
  intro h
  have : (spikeState (p := p)).toRaw.name = (spikeMemory (p := p)).toRaw.name := by rw [h]
  simp [VmChannel.toRaw, spikeState, spikeMemory] at this

omit [Fact (2 ^ 17 < p)] in
@[circuit_norm] lemma spikeMemory_eq_spikeState_false :
    ((spikeMemory (p := p)).toRaw = (spikeState (p := p)).toRaw) = False := by
  simp only [eq_iff_iff, iff_false]
  intro h
  have : (spikeMemory (p := p)).toRaw.name = (spikeState (p := p)).toRaw.name := by rw [h]
  simp [VmChannel.toRaw, spikeState, spikeMemory] at this

end SP1Clean.Spike
