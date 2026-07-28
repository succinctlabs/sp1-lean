import SP1Clean.Soundness.RowView
import SP1Clean.Model.InteractionBus
import SP1Clean.Model.ByteTable
import SP1Clean.Proofs.Chips.ByteChip.Provider

/-! # Trace-level Byte-bus consistency

The trace-level meaning of the Byte interactions that `Readers/CPUState.lean` and
`Readers/RTypeReader.lean` emit on `Foundations/Channels.lean`'s `byteChannel` (row emission → bus data →
trace consistency), the Byte-bus sibling of `Soundness/StateConsistency.lean`. Each row sends **eight**
byte rows into the preprocessed `ByteChip` (SP1's `send_byte`), all gated by `is_real`:

- two from `CPUState` — a 13-bit `Range` on `(clk_0_16 - 1)·8⁻¹` and a `U8Range` on `clk_16_24`; and
- two per register operand (`rs1`/`rs2`/`rd`) — a 16-bit `Range` on `diff_low_limb` and a `U8Range` on
  the scaled timestamp high part — i.e. six from `RTypeReader`.

Each row projects to eight signed `LookupAccess` sends (multiplicity `+is_real`, vacuous on padding —
`byteLookups_padding`) feeding `Foundations/InteractionBus.lean`, and to the per-row validity predicate
`byteAccessValid` (every sent row is a valid `ByteChip` row, `ByteRowSpec`).

## Honest scope

`byteRows`, `byteLookups`, `byteAccessValid`, the aggregator, and `byteLookups_padding` are proven. The
link **multiset-balance ⟹ `byteAccessValid`** needs the provider side — a native `ByteChip` that pushes
the table with count multiplicities — absent here, exactly as `StateConsistency`'s receiving `ProgramChip`
is absent. It is threaded as `TraceByteLink`: an honest assumption, not a `sorry`/axiom. This is a weaker
per-row membership claim than State's cross-row PC chain — there is no inter-row reasoning. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.LookupAccessList

variable {p : ℕ} [NeZero p]

/-- The recombined low clock the readers reconstruct from the CPUState block. -/
def clkLow (r : Trace.RowView (ZMod p)) : ZMod p :=
  r.state.clk_0_16 + r.state.clk_16_24 * 65536

/-- The eight byte rows an Add row sends into the byte table, each the `⟨opcode, value, width, 0⟩`
message the corresponding reader pulls on `byteChannel` (the value is **raw**, multiplicity-gated by
`is_real` in `byteSend` — faithful to SP1's `send_byte(…, is_real)`, no `is_real·value` fold). Order: the
two `CPUState` clock checks, then the two timestamp checks for each of `op_a`/`op_b`/`op_c` (access clocks
`clkLow + 4/3/2`). -/
def byteRows (r : Trace.RowView (ZMod p)) : List (ByteRow (ZMod p)) :=
  let s := r.state
  let a := r.adapter
  let cl := clkLow r
  let ts := fun (m : Extracted.RegisterAccessCols (ZMod p)) (clk : ZMod p) =>
    [(⟨6, m.access_timestamp.diff_low_limb, 16, 0⟩ : ByteRow (ZMod p)),
     ⟨3, (clk - m.access_timestamp.prev_low - 1 - m.access_timestamp.diff_low_limb) *
       (65536 : ZMod p)⁻¹, 0, 0⟩]
  [ ⟨6, (s.clk_0_16 - 1) * (8 : ZMod p)⁻¹, 13, 0⟩,
    ⟨3, s.clk_16_24, 0, 0⟩ ]
  ++ ts a.op_a_memory (cl + 4) ++ ts a.op_b_memory (cl + 3) ++ ts a.op_c_memory (cl + 2)

/-- Project a byte row to its signed `LookupAccess` send: bus `Byte`, table `"SP1Byte"`, entry the four
columns through `ZMod.val`, multiplicity `+is_real` (positive send; `0` on padding). -/
def byteSend (is_real : ZMod p) (row : ByteRow (ZMod p)) : LookupAccess :=
  (.Byte, "SP1Byte", [row.opcode.val, row.a.val, row.b.val, row.c.val], (is_real.val : ℤ))

/-- The eight signed Byte-bus contributions an Add row emits (all multiplicity `+is_real`, so a padding
row contributes `0` to every key — `byteLookups_padding`). -/
def byteLookups (r : Trace.RowView (ZMod p)) : LookupAccessList :=
  (byteRows r).map (byteSend r.is_real)

/-- The per-row Byte-bus invariant: on a real row every sent byte row is a valid `ByteChip` row
(`ByteRowSpec`). Vacuous on padding. This is the per-row membership the multiset balance should deliver
(the `ByteChip` receives each sent row and its own constraints make it valid). -/
def byteAccessValid (r : Trace.RowView (ZMod p)) : Prop :=
  r.is_real = 1 → ∀ row ∈ byteRows r, ByteRowSpec row

/-- Trace-shape Byte-bus invariant: every row's sent byte rows are valid. -/
structure TraceByteValid (rows : List (Trace.RowView (ZMod p))) : Prop where
  rows_valid : ∀ r ∈ rows, byteAccessValid r

/-- **The crux (threaded).** Every byte row each chip `send`s is `receive`d by the preprocessed
`ByteChip`, whose constraints force its rows to be valid — so a multiset-balanced Byte bus makes every
sent row a valid `ByteRowSpec`. Deriving this needs the (absent) native `ByteChip` provider + the
balance; `StateConsistency` likewise threads its `TraceStateLink`. -/
def TraceByteLink (rows : List (Trace.RowView (ZMod p))) : Prop :=
  ∀ r ∈ rows, byteAccessValid r

/-- Discharge of `TraceByteValid` from the threaded byte link (a re-bundling). -/
theorem traceByteValid_of_byteLink (rows : List (Trace.RowView (ZMod p)))
    (h_link : TraceByteLink rows) : TraceByteValid rows :=
  ⟨h_link⟩

/-- The trace-level claim a future `ByteChip`-aware soundness discharges: the aggregated per-row byte
contributions form a balanced bus. -/
def TraceByteConsistent (rows : List (Trace.RowView (ZMod p))) : Prop :=
  (aggregateChipRows rows byteLookups).isConsistentOnline

/-- A list whose every contribution carries multiplicity `0` sums to `0` on every key. -/
private theorem multiplicitySum_eq_zero_of_multOf {l : LookupAccessList} (k : LookupKey)
    (h : ∀ a ∈ l, multOf a = 0) : multiplicitySum l k = 0 := by
  simp only [multiplicitySum]
  refine List.sum_eq_zero fun x hx => ?_
  obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hx
  exact h a (List.mem_of_mem_filter ha)

omit [NeZero p] in
/-- **Gating is real.** A padding row (`is_real = 0`) contributes `0` to *every* Byte-bus key: all eight
sends have multiplicity `is_real.val = 0`. The emission is genuinely `is_real`-gated, matching SP1's
`send_byte(…, is_real)`. -/
theorem byteLookups_padding (r : Trace.RowView (ZMod p)) (h : r.is_real = 0) :
    ∀ k, multiplicitySum (byteLookups r) k = 0 := by
  refine fun k => multiplicitySum_eq_zero_of_multOf k fun a ha => ?_
  simp only [byteLookups, List.mem_map] at ha
  obtain ⟨row, _, rfl⟩ := ha
  simp only [byteSend, multOf, h, ZMod.val_zero, Nat.cast_zero]

open SP1Clean.ByteChip (ByteProvider byteRowKey byteRowSpec_of_provider)

/-- **`TraceByteLink` discharged down to bus balance.** Given a native `ByteProvider` (SP1's preprocessed
`ByteChip` — it carries only valid byte rows, `Chips/ByteChip.lean`) and a *balanced* Byte bus (the
LogUp/GKR fact, the lone remaining threaded assumption), every real row's sent byte rows are valid
(`byteAccessValid`). The argument: a real send has multiplicity `is_real.val = 1 > 0`; on a balanced bus
the provider must cancel it (`provider_touches_pos_send`), so it carries an entry at that key; the provider
only carries valid rows, and the key determines the row, so the sent row is that valid row. Reduces the
raw `TraceByteLink` assumption to `isConsistentBalanced` + the native `ByteProvider`. -/
theorem byteAccessValid_of_balance [Fact (1 < p)]
    (rows : List (Trace.RowView (ZMod p))) (prov : LookupAccessList)
    (h_prov : ByteProvider (p := p) prov)
    (h_bal : isConsistentBalanced (aggregateChipRows rows byteLookups ++ prov)) :
    TraceByteLink rows := by
  intro r hr h_real row h_row_mem
  set a := byteSend r.is_real row with ha_def
  have ha_mem : a ∈ aggregateChipRows rows byteLookups :=
    List.mem_flatMap.mpr ⟨r, hr, List.mem_map.mpr ⟨row, h_row_mem, rfl⟩⟩
  have h_pos : 0 < multOf a := by
    simp only [ha_def, byteSend, multOf, h_real, ZMod.val_one]; norm_num
  have h_nonneg : ∀ b ∈ aggregateChipRows rows byteLookups, 0 ≤ multOf b := by
    intro b hb
    obtain ⟨r', _, hb'⟩ := List.mem_flatMap.mp hb
    obtain ⟨row', _, rfl⟩ := List.mem_map.mp hb'
    simp only [byteSend, multOf]; positivity
  obtain ⟨b, hb, hkey⟩ := provider_touches_pos_send _ prov h_nonneg h_bal a ha_mem h_pos
  have hak : keyOf a = byteRowKey row := by simp only [ha_def, byteSend, keyOf, byteRowKey]
  exact byteRowSpec_of_provider h_prov hb (hkey.trans hak)

end SP1Clean.Soundness
