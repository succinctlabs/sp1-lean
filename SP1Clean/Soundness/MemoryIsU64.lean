import SP1Clean.Soundness.MemoryConsistency
import SP1Clean.Soundness.MemoryGlobal

/-! # Trace-level `isU64` operand recovery from the Memory-bus balance (W1c)

The chip `Assumptions` ask each register operand word (`op_*_memory.prev_value`) to be `Word.isU64` —
four genuine 16-bit limbs. At the whole-machine level that is not free: a balance canceller only
equates the bus keys' `.val` *lists*, and each limb `.val` is merely `< p`. Worse, an `op_b`/`op_c`
read-back *receives* the same `prev_value` it *sends*, so naive send/receive cancellation is circular.
This file recovers the bound non-circularly by chaining through the per-address access order of
`Soundness/MemoryConsistency.lean`'s offline-memory derivation:

* a read's `prevValue` equals — **limb-wise**, extracted from the syntactic bus-key equality
  (`recvKey_eq_sendKey_limbs`), *not* from the `wordToNat`-recombined equality the vendored
  `isConsistentOnline` states (recombination is not injective without the very bounds being
  recovered) — the most-recent earlier write's `value` at that address
  (`memEvent_prevValue_eq_writer`, the same canceller skeleton as
  `isConsistentSingleAddress_of_balance`);
* genuine writes are `op_a` events whose written `value = rdWrite`, the chip-`Spec`-range-checked ALU
  result — threaded as the per-row hypothesis `MemBalanceHyps.writeU64`; `op_b`/`op_c` events write
  back their own `prevValue` (definitionally — `memEventsFiltered_value_cases`), so they *inherit*
  the bound along the chain instead of supplying it;
* the chain bottoms out at the provider genesis (`MemProviderGenesis`), whose value is `0`
  (`eventsAt_genesis_reads_zero`) — `isU64` for free, since an ℕ-sum `wordToNat … = 0` zeroes
  every limb.

The structural induction along the per-address decreasing-timestamp event list (`isU64_of_limbChain`,
assembled in `eventsAt_values_isU64`) gives every bus-backed access `isU64` read *and* written words;
the headline `operand_{a,b,c}_isU64_of_memBalance` family projects that back to a real row's operands.
This is W1c: the recovery feeding `sp1_gatedExecution_prereqs` part (c); the wiring into the capstone
waits on W1b's row decode. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.LookupAccessList

variable {p : ℕ}

/-- Limb-level "reads exactly what the writer wrote": `e.prevValue` equals `e'.value` in each of the
four limb slots, at the `.val` level the bus keys carry. Strictly stronger than the
`wordToNat`-recombined equality of the vendored chain — recombination is not injective unless the
limbs are already bounded, which is the very fact W1c recovers. -/
def limbReadEq (e e' : MemEvent (ZMod p)) : Prop :=
  (e.prevValue[0]).val = (e'.value[0]).val ∧ (e.prevValue[1]).val = (e'.value[1]).val ∧
    (e.prevValue[2]).val = (e'.value[2]).val ∧ (e.prevValue[3]).val = (e'.value[3]).val

/-- **Limb-level key extraction.** A canceller match `recvKey e' = sendKey e` equates the four value
limbs *individually* — the keys carry them as separate `List ℕ` entries. The limb-level refinement of
`recvKey_eq_sendKey` the `isU64` recovery rides. -/
theorem recvKey_eq_sendKey_limbs {e' e : MemEvent (ZMod p)}
    (h : memEvent_recvKey e' = memEvent_sendKey e) :
    (e'.value[0]).val = (e.prevValue[0]).val ∧ (e'.value[1]).val = (e.prevValue[1]).val ∧
      (e'.value[2]).val = (e.prevValue[2]).val ∧ (e'.value[3]).val = (e.prevValue[3]).val := by
  rw [memEvent_recvKey, memEvent_sendKey] at h
  simp only [Prod.mk.injEq, List.cons.injEq, true_and, and_true] at h
  obtain ⟨_, _, _, hv0, hv1, hv2, hv3⟩ := h
  exact ⟨hv0, hv1, hv2, hv3⟩

/-- **Read = writer, limb-wise (the W1c value extraction).** Along the per-address filtered event list
(decreasing-timestamp, head = latest), every adjacent pair satisfies `limbReadEq`: a read's
`prevValue` is — limb by limb — the next-listed (most-recent earlier) event's written `value`. Same
canceller skeleton as the adjacency case of `isConsistentSingleAddress_of_balance`, but extracting the
limb-level equalities from the key match instead of the recombined one. -/
theorem memEvent_prevValue_eq_writer [NeZero p] (rows : List (Trace.RowView (ZMod p)))
    (memProv : LookupAccessList) (addr : ℕ)
    (hwf : ∀ r ∈ rows, MemRowWellFormed r)
    (h_clk : TraceMemClkValid rows)
    (h_prev : memPrevLink rows)
    (h_prov : MemProviderGenesis memProv rows)
    (h_bal : isConsistentBalanced (aggregateChipRows rows memoryLookups ++ memProv)) :
    List.IsChain limbReadEq (eventsAt rows addr) := by
  have hsub : ∀ {e}, e ∈ eventsAt rows addr → e ∈ memEventsFiltered rows := by
    intro e he; rw [eventsAt] at he; exact List.mem_of_mem_filter he
  rw [List.isChain_iff_getElem]
  intro i hi
  have he_mem := hsub (List.getElem_mem (show i < (eventsAt rows addr).length by omega))
  have he'_mem := hsub (List.getElem_mem (show i + 1 < (eventsAt rows addr).length from hi))
  have hprevts := h_prev addr i hi
  rcases memEvent_canceller rows memProv hwf h_bal _ he_mem with
    ⟨e'', he''_mem, he''_key⟩ | ⟨b, hb, hbkey, _⟩
  · have hclk := (recvKey_eq_sendKey he''_key).1
    have heq : e'' = (eventsAt rows addr)[i + 1]'hi :=
      memEventsFiltered_clk_inj rows h_clk he''_mem he'_mem (by rw [hclk, hprevts])
    obtain ⟨h0, h1, h2, h3⟩ := recvKey_eq_sendKey_limbs he''_key
    rw [← heq]
    exact ⟨h0.symm, h1.symm, h2.symm, h3.symm⟩
  · obtain ⟨_, hnotts⟩ := h_prov b hb _ he_mem hbkey
    exact absurd hprevts (hnotts _ he'_mem)

/-- **Genesis reads zero.** The chronologically-first access at an address (the `getLast` of the
decreasing-timestamp per-address list) reads the provider's genesis value `0` — the genesis case of
`isConsistentSingleAddress_of_balance`, restated standalone. An ℕ-sum `wordToNat … = 0` zeroes every
limb, so the genesis word is `isU64` with no extra hypothesis. -/
theorem eventsAt_genesis_reads_zero [NeZero p] (rows : List (Trace.RowView (ZMod p)))
    (memProv : LookupAccessList) (addr : ℕ)
    (hwf : ∀ r ∈ rows, MemRowWellFormed r)
    (h_clk : TraceMemClkValid rows)
    (h_prevlt : ∀ e ∈ memEventsFiltered rows, e.prevTs < e.clk.val)
    (h_prov : MemProviderGenesis memProv rows)
    (h_bal : isConsistentBalanced (aggregateChipRows rows memoryLookups ++ memProv))
    (hne : eventsAt rows addr ≠ []) :
    wordToNat ((eventsAt rows addr).getLast hne).prevValue = 0 := by
  have hsub : ∀ {e}, e ∈ eventsAt rows addr → e ∈ memEventsFiltered rows := by
    intro e he; rw [eventsAt] at he; exact List.mem_of_mem_filter he
  have haddr : ∀ {e}, e ∈ eventsAt rows addr → e.addr.val = addr := by
    intro e he; rw [eventsAt] at he; have := (List.mem_filter.mp he).2; simpa using this
  have h_sorted : MemoryAccessList.isTimestampSorted ((eventsAt rows addr).map MemEvent.toAccess) := by
    rw [← filterAddress_memAccessListFiltered]
    exact MemoryAccessList.filterAddress_sorted _ (memAccessListFiltered_isTimestampSorted rows h_clk) addr
  have he_mem := hsub (List.getLast_mem hne)
  rcases memEvent_canceller rows memProv hwf h_bal _ he_mem with
    ⟨e'', he''_mem, he''_key⟩ | ⟨b, hb, hbkey, _⟩
  · exfalso
    obtain ⟨hclk, haddr', _⟩ := recvKey_eq_sendKey he''_key
    have he''_at : e'' ∈ eventsAt rows addr := by
      rw [eventsAt]
      exact List.mem_filter.mpr ⟨he''_mem,
        decide_eq_true_eq.mpr (haddr'.trans (haddr (List.getLast_mem hne)))⟩
    have hle := getLast_clk_le h_sorted hne he''_at
    have hlt := h_prevlt _ he_mem
    omega
  · exact (h_prov b hb _ he_mem hbkey).1

/-- **What an event writes.** A bus-backed event is either a row's `op_a` write — written value
`rdWrite`, the chip-range-checked ALU result — or an `op_b`/`op_c` read-back, which writes back its own
`prevValue` (definitionally). The case split that breaks the read-back circularity: read-backs
*inherit* `isU64` along the chain, genuine writes get it from the chip `Spec`. -/
theorem memEventsFiltered_value_cases (rows : List (Trace.RowView (ZMod p)))
    (e : MemEvent (ZMod p)) (he : e ∈ memEventsFiltered rows) :
    (∃ r ∈ rows, r.is_real ≠ 0 ∧ e = opAEvent r) ∨ e.value = e.prevValue := by
  rw [memEventsFiltered, List.mem_flatMap] at he
  obtain ⟨r, hr, he⟩ := he
  rw [List.mem_reverse] at hr
  rw [rowMemEventsGated] at he
  by_cases hreal : r.is_real = 0
  · rw [if_pos hreal] at he; exact absurd he List.not_mem_nil
  rw [if_neg hreal, List.mem_cons] at he
  rcases he with rfl | he
  · exact Or.inl ⟨r, hr, hreal, rfl⟩
  · refine Or.inr ?_
    rw [List.mem_append] at he
    rcases he with he | he
    · by_cases himmb : r.adapter.imm_b = 0
      · rw [if_pos himmb, List.mem_singleton] at he
        subst he; rfl
      · rw [if_neg himmb] at he; exact absurd he List.not_mem_nil
    · by_cases himmc : r.adapter.imm_c = 0
      · rw [if_pos himmc, List.mem_singleton] at he
        subst he; rfl
      · rw [if_neg himmc] at he; exact absurd he List.not_mem_nil

/-- **The chain induction (W1c core).** Along a per-address decreasing-timestamp event list that (a)
satisfies the limb-level read=writer chain, (b) bottoms out reading the genesis `0`, and (c) at every
event either writes a known-`isU64` word or writes back its own read, every event's read *and* written
words are `isU64`. Structural induction from the genesis upward: a read inherits from the next-listed
event's write; a write from its own read (read-backs) or from hypothesis (c) (genuine writes). -/
theorem isU64_of_limbChain [NeZero p] :
    ∀ events : List (MemEvent (ZMod p)),
      List.IsChain limbReadEq events →
      (∀ h : events ≠ [], wordToNat (events.getLast h).prevValue = 0) →
      (∀ e ∈ events, Word.isU64 e.prevValue → Word.isU64 e.value) →
      ∀ e ∈ events, Word.isU64 e.prevValue ∧ Word.isU64 e.value := by
  intro events
  induction events with
  | nil => intro _ _ _ e he; exact absurd he List.not_mem_nil
  | cons e rest ih =>
    intro hchain hgen hval x hx
    cases rest with
    | nil =>
      have hx' : x = e := List.mem_singleton.mp hx
      have hz := hgen (by simp)
      simp only [List.getLast_singleton, wordToNat] at hz
      rw [hx']
      have hprevU : Word.isU64 e.prevValue :=
        Word.isU64_of_cases (by omega) (by omega) (by omega) (by omega)
      exact ⟨hprevU, hval e (by simp) hprevU⟩
    | cons e2 rest' =>
      have hcc := List.isChain_cons_cons.mp hchain
      have hrec := ih hcc.2
        (by intro _
            have hg := hgen (by simp)
            rwa [List.getLast_cons (by simp)] at hg)
        (fun y hy hyU => hval y (List.mem_cons_of_mem _ hy) hyU)
      rcases List.mem_cons.mp hx with hx' | hx'
      · rw [hx']
        obtain ⟨u0, u1, u2, u3⟩ :=
          Word.lt_cases_of_isU64 (hrec e2 (List.mem_cons.mpr (Or.inl rfl))).2
        obtain ⟨h0, h1, h2, h3⟩ := hcc.1
        have hprevU : Word.isU64 e.prevValue :=
          Word.isU64_of_cases (by omega) (by omega) (by omega) (by omega)
        exact ⟨hprevU, hval e (List.mem_cons.mpr (Or.inl rfl)) hprevU⟩
      · exact hrec x hx'

/-- **W1c hypothesis bundle.** Exactly the hypothesis list of `isConsistentOnline_of_memBalance`
(trace-shape facts, provider genesis, balanced Memory bus) plus the one non-circular value bound: the
chip-`Spec`-supplied `isU64` of every real row's written `rdWrite`. All residuals are named hypotheses
(never `sorry`); discharging them at the capstone rides W1a (balance) and W1b (row decode). -/
structure MemBalanceHyps [NeZero p] (rows : List (Trace.RowView (ZMod p)))
    (memProv : LookupAccessList) : Prop where
  wellFormed : ∀ r ∈ rows, MemRowWellFormed r
  clk : TraceMemClkValid rows
  prevLink : memPrevLink rows
  prevLt : ∀ e ∈ memEventsFiltered rows, e.prevTs < e.clk.val
  genesis : MemProviderGenesis memProv rows
  balanced : isConsistentBalanced (aggregateChipRows rows memoryLookups ++ memProv)
  writeU64 : ∀ r ∈ rows, r.is_real ≠ 0 → Word.isU64 r.rdWrite

/-- **Every bus-backed access is `isU64` (read and written words).** The per-address assembly: the
limb-level chain (`memEvent_prevValue_eq_writer`) + the genesis zero (`eventsAt_genesis_reads_zero`) +
the write case split (`memEventsFiltered_value_cases`) feed the chain induction `isU64_of_limbChain`.
-/
theorem eventsAt_values_isU64 [NeZero p] {rows : List (Trace.RowView (ZMod p))}
    {memProv : LookupAccessList} (h : MemBalanceHyps rows memProv) (addr : ℕ) :
    ∀ e ∈ eventsAt rows addr, Word.isU64 e.prevValue ∧ Word.isU64 e.value := by
  refine isU64_of_limbChain (eventsAt rows addr)
    (memEvent_prevValue_eq_writer rows memProv addr h.wellFormed h.clk h.prevLink h.genesis h.balanced)
    (fun hne => eventsAt_genesis_reads_zero rows memProv addr h.wellFormed h.clk h.prevLt h.genesis
      h.balanced hne)
    ?_
  intro e he hprevU
  have he_mem : e ∈ memEventsFiltered rows := by
    rw [eventsAt] at he
    exact List.mem_of_mem_filter he
  rcases memEventsFiltered_value_cases rows e he_mem with ⟨r, hr, hreal, hev⟩ | hval
  · rw [hev]
    exact h.writeU64 r hr hreal
  · rw [hval]
    exact hprevU

/-- A filtered event sits in its own address's per-address list. -/
theorem mem_eventsAt_self {rows : List (Trace.RowView (ZMod p))} {e : MemEvent (ZMod p)}
    (he : e ∈ memEventsFiltered rows) : e ∈ eventsAt rows e.addr.val := by
  rw [eventsAt]
  exact List.mem_filter.mpr ⟨he, by simp⟩

/-- A real row's `op_a` (`rd` write) event is bus-backed. -/
theorem opAEvent_mem_memEventsFiltered {rows : List (Trace.RowView (ZMod p))}
    {r : Trace.RowView (ZMod p)} (hr : r ∈ rows) (h_real : r.is_real ≠ 0) :
    opAEvent r ∈ memEventsFiltered rows := by
  rw [memEventsFiltered, List.mem_flatMap]
  refine ⟨r, List.mem_reverse.mpr hr, ?_⟩
  rw [rowMemEventsGated, if_neg h_real]
  exact List.mem_cons.mpr (Or.inl rfl)

/-- A real row's `op_b` (`rs1` read) event is bus-backed when the operand is a register (`imm_b = 0`).
-/
theorem opBEvent_mem_memEventsFiltered {rows : List (Trace.RowView (ZMod p))}
    {r : Trace.RowView (ZMod p)} (hr : r ∈ rows) (h_real : r.is_real ≠ 0)
    (h_immb : r.adapter.imm_b = 0) : opBEvent r ∈ memEventsFiltered rows := by
  rw [memEventsFiltered, List.mem_flatMap]
  refine ⟨r, List.mem_reverse.mpr hr, ?_⟩
  rw [rowMemEventsGated, if_neg h_real, if_pos h_immb]
  exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inl rfl)))))

/-- A real row's `op_c` (`rs2` read) event is bus-backed when the operand is a register (`imm_c = 0`).
-/
theorem opCEvent_mem_memEventsFiltered {rows : List (Trace.RowView (ZMod p))}
    {r : Trace.RowView (ZMod p)} (hr : r ∈ rows) (h_real : r.is_real ≠ 0)
    (h_immc : r.adapter.imm_c = 0) : opCEvent r ∈ memEventsFiltered rows := by
  rw [memEventsFiltered, List.mem_flatMap]
  refine ⟨r, List.mem_reverse.mpr hr, ?_⟩
  rw [rowMemEventsGated, if_neg h_real, if_pos h_immc]
  exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))

/-- **W1c headline (`op_a`).** On the balanced Memory bus, a real row's `op_a` operand —
`op_a_memory.prev_value`, the prior value of `x[rd]` the chip reads — is `isU64`: each limb a genuine
16-bit value. The recovery of the chip `Assumptions`' operand range facts from the bus, feeding
`sp1_gatedExecution_prereqs` part (c); the wiring into the capstone rides W1b's row decode. -/
theorem operand_a_isU64_of_memBalance [NeZero p] {rows : List (Trace.RowView (ZMod p))}
    {memProv : LookupAccessList} (h : MemBalanceHyps rows memProv)
    {r : Trace.RowView (ZMod p)} (hr : r ∈ rows) (h_real : r.is_real ≠ 0) :
    Word.isU64 r.adapter.op_a_memory.prev_value :=
  (eventsAt_values_isU64 h (opAEvent r).addr.val _
    (mem_eventsAt_self (opAEvent_mem_memEventsFiltered hr h_real))).1

/-- **W1c headline (`op_b`).** A real row's register `op_b` operand (`imm_b = 0`) —
`op_b_memory.prev_value`, the `rs1` value the chip computes on — is `isU64`. -/
theorem operand_b_isU64_of_memBalance [NeZero p] {rows : List (Trace.RowView (ZMod p))}
    {memProv : LookupAccessList} (h : MemBalanceHyps rows memProv)
    {r : Trace.RowView (ZMod p)} (hr : r ∈ rows) (h_real : r.is_real ≠ 0)
    (h_immb : r.adapter.imm_b = 0) :
    Word.isU64 r.adapter.op_b_memory.prev_value :=
  (eventsAt_values_isU64 h (opBEvent r).addr.val _
    (mem_eventsAt_self (opBEvent_mem_memEventsFiltered hr h_real h_immb))).1

/-- **W1c headline (`op_c`).** A real row's register `op_c` operand (`imm_c = 0`) —
`op_c_memory.prev_value`, the `rs2` value the chip computes on — is `isU64`. -/
theorem operand_c_isU64_of_memBalance [NeZero p] {rows : List (Trace.RowView (ZMod p))}
    {memProv : LookupAccessList} (h : MemBalanceHyps rows memProv)
    {r : Trace.RowView (ZMod p)} (hr : r ∈ rows) (h_real : r.is_real ≠ 0)
    (h_immc : r.adapter.imm_c = 0) :
    Word.isU64 r.adapter.op_c_memory.prev_value :=
  (eventsAt_values_isU64 h (opCEvent r).addr.val _
    (mem_eventsAt_self (opCEvent_mem_memEventsFiltered hr h_real h_immc))).1

/-- **W2/W1c: the operand-recovery hypotheses ride the constructed MemoryGlobalInit provider.** Assemble
`MemBalanceHyps` at the W4a genesis contributions (`memGenesisContributions`) — so every operand fact
above (`operand_{a,b,c}_isU64_of_memBalance`, `eventsAt_values_isU64`, the limb value chain) holds with
**no standalone `MemProviderGenesis` assumption**: the genesis side is discharged by
`memProviderGenesis_of_contributions`, leaving only the structural ordering/range side conditions + the
`t0`-below-all residue + the balanced Memory bus. The value twin of
`traceMemoryValid_of_genesis_and_balance`; the operand-binding entry point W2 builds on. -/
def memBalanceHyps_of_genesis [NeZero p] (rows : List (Trace.RowView (ZMod p)))
    (clkHigh t0 : ℕ) (addrs : List ℕ) (mult : ℕ → ℤ)
    (hwf : ∀ r ∈ rows, MemRowWellFormed r)
    (h_clk : TraceMemClkValid rows)
    (h_prev : memPrevLink rows)
    (h_prevlt : ∀ e ∈ memEventsFiltered rows, e.prevTs < e.clk.val)
    (h_t0 : ∀ e ∈ memEventsFiltered rows, t0 ≠ e.clk.val)
    (h_writeU64 : ∀ r ∈ rows, r.is_real ≠ 0 → Word.isU64 r.rdWrite)
    (h_bal : isConsistentBalanced
      (aggregateChipRows rows memoryLookups ++ memGenesisContributions clkHigh t0 addrs mult)) :
    MemBalanceHyps rows (memGenesisContributions clkHigh t0 addrs mult) :=
  { wellFormed := hwf, clk := h_clk, prevLink := h_prev, prevLt := h_prevlt,
    genesis := memProviderGenesis_of_contributions rows clkHigh t0 addrs mult h_t0,
    balanced := h_bal, writeU64 := h_writeU64 }

end SP1Clean.Soundness
