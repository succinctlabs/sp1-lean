import SP1Clean.Soundness.MemoryConsistency

/-! # W4a — the MemoryGlobalInit provider, constructed (not assumed)

`Soundness/MemoryConsistency.lean` derives the offline-memory link (`TraceMemoryValid`: every read
returns the most-recent write at its address) from the balanced Memory bus via
`isConsistentOnline_of_memBalance`, which threads `MemProviderGenesis memProv rows` — the off-chip
MemoryGlobalInit chip's genesis side, modeled only as a *predicate*. This file removes that hypothesis:
it **constructs** the init chip's native contributions and proves `MemProviderGenesis` for them — the
Memory-bus analog of `ProgramProviderSpike.programProvider_of_validRom`.

SP1's MemoryGlobalInit chip seeds each accessed register/address with initial value `0` at a genesis
timestamp below every real access. `memGenesisContributions` is exactly that — one bus entry per address
at key `[clk_high, t0, addr, 0, 0, 0,0,0,0]` (value `0` at timestamp `t0`). `MemProviderGenesis` holds
for it because a real event whose send key matches a genesis entry must, by the key components, read value
`0` (the value limbs are `0`) at `prevTs = t0`; and the only residual is `t0` distinct from every real
event's clock — exactly "the init timestamp is below all accesses". `traceMemoryValid_of_genesis_and_balance`
feeds the constructed provider into `isConsistentOnline_of_memBalance`, so the single-shard Memory link
needs only the constructed contributions + the ordering side conditions + the LogUp balance — no standalone
provider assumption. Binding the genesis value/boundary to a concrete `prog.memImage` / committed final
image (the per-address *value* the bus pins) is the remaining W4a step (W2's replay precision). -/

namespace SP1Clean.Soundness

open SP1Clean SP1Clean.LookupAccessList

variable {p : ℕ}

/-- One MemoryGlobalInit genesis contribution at `addr`: initial value `0` at the genesis timestamp `t0`
(the bus key `[clk_high, t0, addr, 0, 0, 0,0,0,0]`). -/
def memGenesisAccess (clkHigh t0 addr : ℕ) (mult : ℤ) : LookupAccess :=
  (.Memory, "SP1Memory", [clkHigh, t0, addr, 0, 0, 0, 0, 0, 0], mult)

/-- The MemoryGlobalInit chip's native contributions: one genesis entry (value `0` at `t0`) per address.
A concrete list — the native content of SP1's memory-init chip, not a predicate. -/
def memGenesisContributions (clkHigh t0 : ℕ) (addrs : List ℕ) (mult : ℕ → ℤ) : LookupAccessList :=
  addrs.map (fun addr => memGenesisAccess clkHigh t0 addr (mult addr))

/-- **The genesis provider is constructed, not assumed.** Every genesis contribution sits at a key with
value limbs `0` and timestamp `t0`, so any real event whose send key matches it reads value `0` at
`prevTs = t0`; with `t0` distinct from every real clock (`h_t0` — the init timestamp below all accesses),
this is exactly `MemProviderGenesis`. Discharges the hypothesis `isConsistentOnline_of_memBalance` requires. -/
theorem memProviderGenesis_of_contributions (rows : List (Trace.RowView (ZMod p)))
    (clkHigh t0 : ℕ) (addrs : List ℕ) (mult : ℕ → ℤ)
    (h_t0 : ∀ e ∈ memEventsFiltered rows, t0 ≠ e.clk.val) :
    MemProviderGenesis (memGenesisContributions clkHigh t0 addrs mult) rows := by
  intro b hb e he hkey
  simp only [memGenesisContributions, List.mem_map] at hb
  obtain ⟨addr, -, rfl⟩ := hb
  rw [show keyOf (memGenesisAccess clkHigh t0 addr (mult addr))
        = (InteractionKind.Memory, "SP1Memory", [clkHigh, t0, addr, 0, 0, 0, 0, 0, 0]) from rfl,
      memEvent_sendKey] at hkey
  simp only [Prod.mk.injEq, List.cons.injEq, and_true, true_and] at hkey
  obtain ⟨-, hpts, -, hv0, hv1, hv2, hv3⟩ := hkey
  refine ⟨?_, ?_⟩
  · simp only [wordToNat, ← hv0, ← hv1, ← hv2, ← hv3, Nat.zero_mul, Nat.add_zero]
  · intro e'' he''; rw [← hpts]; exact h_t0 e'' he''

/-- **W4a end-to-end: `TraceMemoryValid` from the constructed genesis provider + balance.** Every read
returns the most-recent write at its address — derived from the constructed MemoryGlobalInit contributions
(no standalone `MemProviderGenesis` assumption) + the ordering side conditions + the balanced Memory bus.
The Memory-bus twin of `ProgramProviderSpike.traceProgramLink_of_validRom_and_balance`. -/
theorem traceMemoryValid_of_genesis_and_balance [NeZero p] (rows : List (Trace.RowView (ZMod p)))
    (clkHigh t0 : ℕ) (addrs : List ℕ) (mult : ℕ → ℤ)
    (hwf : ∀ r ∈ rows, MemRowWellFormed r)
    (h_clk : TraceMemClkValid rows)
    (h_prev : memPrevLink rows)
    (h_prevlt : ∀ e ∈ memEventsFiltered rows, e.prevTs < e.clk.val)
    (h_t0 : ∀ e ∈ memEventsFiltered rows, t0 ≠ e.clk.val)
    (h_bal : isConsistentBalanced
      (aggregateChipRows rows memoryLookups ++ memGenesisContributions clkHigh t0 addrs mult)) :
    TraceMemoryValid rows :=
  { clk := h_clk
    online := isConsistentOnline_of_memBalance rows (memGenesisContributions clkHigh t0 addrs mult)
      hwf h_clk h_prev h_prevlt
      (memProviderGenesis_of_contributions rows clkHigh t0 addrs mult h_t0) h_bal }

end SP1Clean.Soundness
