import SP1Clean.Soundness.RowView
import SP1Clean.Native.Readers.RTypeReader
import SP1Clean.Model.InteractionBus
import SP1Clean.Model.InteractionProjection
import ToClean.Circuit.InteractionRecovery
import SP1Clean.Native.Readers.MemoryAccess
import Clean.Utils.OfflineMemory

/-! # Trace-level Memory-bus (register read/write) consistency

The trace-level meaning of the `.memory` interactions that `Readers/RTypeReader.lean` + the chip emit
(sibling of `Soundness/StateConsistency.lean`). SP1's `RTypeReader::eval` emits, per row, two `.memory`
interactions per register operand (the `interactions` list of `Extracted/RTypeReader.lean`): a `send`
of the prior-state
value at the previous timestamp and a `receive` of the new-state value at the current timestamp — for
`op_a` the new value is the `rd` **write**; for `op_b`/`op_c` the new value equals the prior (a
**read**). All six are `is_real`-gated. (The native circuit emits the same physical lookups with the
W11 polarity flip — read-priors as pulls, write/read-backs as pushes; see `memoryReadLookups`.)

Each row projects to six signed `LookupAccess` contributions (`memoryLookups`, send `+is_real`, receive
`−is_real`) feeding the multiset bus, and to a list of `MemEvent`s. The memory-bus consistency is the
**offline-memory** property: every read returns the value of the most-recent write at that address
(timestamp-ordered). That property is order-sensitive — not implied by multiset balance alone; it is
derived by the timed grounding engine (`Soundness/TypedMemory.lean` / `TimeExtraction.lean`, the
memory-clock discipline), and `TraceMemoryLink` below is kept as a named interface alias of
`TraceMemoryValid`. The per-row projection and `memoryLookups_padding` are proven here. -/

namespace SP1Clean.Soundness

open SP1Clean
open SP1Clean.LookupAccessList

variable {p : ℕ}

private theorem two_lt_p_aux [Fact (2 ^ 17 < p)] : 2 < p :=
  lt_of_lt_of_le (by norm_num) (Fact.out (p := 2 ^ 17 < p)).le

/-- A nonzero `ZMod p` element has strictly-positive `ℤ`-cast value — the multiplicity-positivity
workhorse for the Memory-bus send contributions. -/
private theorem valCast_pos_aux [NeZero p] {x : ZMod p} (hx : x ≠ 0) : 0 < (x.val : ℤ) := by
  have : x.val ≠ 0 := fun hv => hx (ZMod.val_injective p (by rw [ZMod.val_zero]; exact hv))
  omega

/-- The recombined low clock for a row (`clk_0_16 + clk_16_24 * 2^16`), matching the Add Rust oracle's
CS2 `clk_low` argument. -/
def rowClkLow (r : Trace.RowView (ZMod p)) : ZMod p :=
  r.state.clk_0_16 + r.state.clk_16_24 * 65536

/-- The six signed Memory-bus contributions a row emits — per operand a `send` of the prior value at the
previous timestamp (`+is_real`) and a `receive` of the new value at `clk_low + offset` (`−is_real`). For
`op_a` the received value is the `rd` write; for `op_b`/`op_c` it is the read-back prior value. 9-tuple
entries match the `.memory` entries of `Extracted/RTypeReader.lean`'s `interactions` list. On padding
rows both signs vanish
(`memoryLookups_padding`). -/
def memoryLookups (r : Trace.RowView (ZMod p)) : LookupAccessList :=
  let chk := r.state.clk_high
  let cl := rowClkLow r
  let ir := (r.is_real.val : ℤ)
  let a := r.adapter
  -- op_b/op_c are gated by `is_real * (1 - imm_b/c)` (an immediate operand does no register read): for a
  -- register read (`imm = 0`) this is `is_real`; for an immediate (`imm = 1`, J-type) it is `0` on every
  -- row (so SP1 emits no such memory interaction). This multiplicative form agrees with SP1's additive
  -- `is_real - imm` on all well-formed rows (`imm = 0`, or `is_real = 0` on padding) and stays `0` for the
  -- J-type immediate case where the additive form would wrongly give `-1` on padding rows.
  let ibr := ((r.is_real * (1 - a.imm_b)).val : ℤ)
  let icr := ((r.is_real * (1 - a.imm_c)).val : ℤ)
  [ -- op_a: read prior (send), write add result (receive)
    (.Memory, "SP1Memory",
      [chk.val, a.op_a_memory.access_timestamp.prev_low.val, a.op_a.val, 0, 0,
        a.op_a_memory.prev_value[0].val, a.op_a_memory.prev_value[1].val,
        a.op_a_memory.prev_value[2].val, a.op_a_memory.prev_value[3].val], ir),
    (.Memory, "SP1Memory",
      [chk.val, (cl + 4).val, a.op_a.val, 0, 0,
        r.rdWrite[0].val, r.rdWrite[1].val,
        r.rdWrite[2].val, r.rdWrite[3].val], - ir),
    -- op_b: read prior (send), read-back prior (receive); gated by `is_real * (1 - imm_b)`, address its low limb
    (.Memory, "SP1Memory",
      [chk.val, a.op_b_memory.access_timestamp.prev_low.val, a.op_b[0].val, 0, 0,
        a.op_b_memory.prev_value[0].val, a.op_b_memory.prev_value[1].val,
        a.op_b_memory.prev_value[2].val, a.op_b_memory.prev_value[3].val], ibr),
    (.Memory, "SP1Memory",
      [chk.val, (cl + 3).val, a.op_b[0].val, 0, 0,
        a.op_b_memory.prev_value[0].val, a.op_b_memory.prev_value[1].val,
        a.op_b_memory.prev_value[2].val, a.op_b_memory.prev_value[3].val], - ibr),
    -- op_c: read prior (send), read-back prior (receive); gated by `is_real * (1 - imm_c)`, address its low limb
    (.Memory, "SP1Memory",
      [chk.val, a.op_c_memory.access_timestamp.prev_low.val, a.op_c[0].val, 0, 0,
        a.op_c_memory.prev_value[0].val, a.op_c_memory.prev_value[1].val,
        a.op_c_memory.prev_value[2].val, a.op_c_memory.prev_value[3].val], icr),
    (.Memory, "SP1Memory",
      [chk.val, (cl + 2).val, a.op_c[0].val, 0, 0,
        a.op_c_memory.prev_value[0].val, a.op_c_memory.prev_value[1].val,
        a.op_c_memory.prev_value[2].val, a.op_c_memory.prev_value[3].val], - icr) ]

/-- A single register-access event. Mirrors the vendored `MemoryAccess` tuple `(timestamp, addr,
readValue, writeValue)`: `addr`, timestamp `clk` (compared via `.val`, since `ZMod p` has no canonical
order), the **read-old** value `prevValue` (what this access reads = the prior state at that address),
the **write-new** value `value` (what it leaves), and `is_write` (a read leaves `value = prevValue`). The
read/write split is what makes the offline-memory consistency check faithful for genuine writes. -/
structure MemEvent (F : Type) where
  addr : F
  clk : F
  prevValue : Vector F 4
  value : Vector F 4
  is_write : Bool
  /-- The *previous* timestamp this access names — the bus send key carries it
  (`op_X_memory.access_timestamp.prev_low.val`), but `MemEvent.toAccess`'s vendored 4-tuple drops it.
  Carried here so the ordering side condition (`memPrevLink`) and the bus↔access-list correspondence can
  reference it. Not part of `toAccess`. -/
  prevTs : ℕ
  /-- The row-level clock high limb `r.state.clk_high.val` — the bus key's slot-0 (shared by an access's
  send and receive). Carried so `memEvent_sendKey`/`memEvent_recvKey` are functions of the event alone and
  thus match the `memoryLookups` keys exactly. Not part of `toAccess` (which uses the low `clk.val` only —
  single-shard, where `clkHigh` is constant; the multi-shard extension generalises). -/
  clkHigh : ℕ

-- (`TraceMemoryValid`/`TraceMemoryLink` use the vendored `isConsistentOnline` shape, defined below
-- after `isConsistentOnline_of_memBalance`.)

/-- The `op_a` (`rd` write) register event: reads x[rd]'s prior value, writes the result `rdWrite`. -/
def opAEvent (r : Trace.RowView (ZMod p)) : MemEvent (ZMod p) :=
  { addr := r.adapter.op_a, clk := rowClkLow r + 4,
    prevValue := r.adapter.op_a_memory.prev_value, value := r.rdWrite, is_write := true,
    prevTs := r.adapter.op_a_memory.access_timestamp.prev_low.val, clkHigh := r.state.clk_high.val }

/-- The `op_b` (`rs1` read) register event: reads and writes back the prior value. -/
def opBEvent (r : Trace.RowView (ZMod p)) : MemEvent (ZMod p) :=
  { addr := r.adapter.op_b[0], clk := rowClkLow r + 3,
    prevValue := r.adapter.op_b_memory.prev_value, value := r.adapter.op_b_memory.prev_value,
    is_write := false, prevTs := r.adapter.op_b_memory.access_timestamp.prev_low.val,
    clkHigh := r.state.clk_high.val }

/-- The `op_c` (`rs2` read) register event: reads and writes back the prior value. -/
def opCEvent (r : Trace.RowView (ZMod p)) : MemEvent (ZMod p) :=
  { addr := r.adapter.op_c[0], clk := rowClkLow r + 2,
    prevValue := r.adapter.op_c_memory.prev_value, value := r.adapter.op_c_memory.prev_value,
    is_write := false, prevTs := r.adapter.op_c_memory.access_timestamp.prev_low.val,
    clkHigh := r.state.clk_high.val }

/-- The register-access events an Add row contributes (three: the `rd` write and the `rs1`/`rs2`
read-backs), at their current timestamps. -/
def rowMemEvents (r : Trace.RowView (ZMod p)) : List (MemEvent (ZMod p)) :=
  [opAEvent r, opBEvent r, opCEvent r]

/-- All register-access events of a trace, in chronological order. -/
def memEvents (rows : List (Trace.RowView (ZMod p))) : List (MemEvent (ZMod p)) :=
  rows.flatMap rowMemEvents

-- (`TraceMemoryValid`/`TraceMemoryLink`/`traceMemoryValid_of_memoryLink` are defined below in the
-- vendored `isConsistentOnline` shape, after `isConsistentOnline_of_memBalance`.)

/-- **Gating is real.** A padding row (`is_real = 0`) contributes zero to every Memory-bus key: all six
signed contributions have multiplicity `±0`. The emission is `is_real`-gated, matching SP1's
`send/receive … is_real`. -/
theorem memoryLookups_padding [NeZero p] (r : Trace.RowView (ZMod p)) (h : r.is_real = 0) :
    ∀ k, multiplicitySum (memoryLookups r) k = 0 := by
  -- With the multiplicative gate `is_real * (1 - imm)`, `is_real = 0` zeroes op_b/op_c regardless of imm.
  intro k
  simp only [memoryLookups, multiplicitySum_cons, multiplicitySum_nil, multOf, h, zero_mul,
    ZMod.val_zero, Nat.cast_zero, neg_zero, ite_self, add_zero]

open Circuit InteractionRecovery
open SP1Clean.Channels (memoryChannel MemoryMsg)

/-- The **five** Memory-bus contributions `Readers/RTypeReader.main` actually emits after the W11 polarity
flip: per operand the read-prior *pull* (`−is_real` — the chip *derives* `MemoryMsg.isU64` of the operand's
prior value) and the op_b/op_c read-back *pushes* (`+is_real`). The op_a (`rd`) **write** push is factored
out into `Readers/RegisterWrite` (composed by the chip after its operation), so it is absent here. These are
`memoryLookups`'s five *read* entries (all but the op_a write, `memoryLookups` entry 1) with flipped signs —
the pull/push polarity; on a register row (`imm_b = imm_c = 0`, where `memoryLookups` gates op_b/op_c by
plain `±is_real`) they carry identical keys. Both feed the same `multiplicitySum` bus, so the offline-memory
model (`isConsistentOnline_of_memBalance`) — stated over `memoryLookups`, balance being `negMult`-invariant
— is unaffected. -/
def memoryReadLookups (r : Trace.RowView (ZMod p)) : LookupAccessList :=
  let chk := r.state.clk_high
  let cl := rowClkLow r
  let ir := (r.is_real.val : ℤ)
  let a := r.adapter
  [ -- op_a: read-prior pull
    (.Memory, "SP1Memory",
      [chk.val, a.op_a_memory.access_timestamp.prev_low.val, a.op_a.val, 0, 0,
        a.op_a_memory.prev_value[0].val, a.op_a_memory.prev_value[1].val,
        a.op_a_memory.prev_value[2].val, a.op_a_memory.prev_value[3].val], - ir),
    -- op_b: read-prior pull, read-back push
    (.Memory, "SP1Memory",
      [chk.val, a.op_b_memory.access_timestamp.prev_low.val, a.op_b[0].val, 0, 0,
        a.op_b_memory.prev_value[0].val, a.op_b_memory.prev_value[1].val,
        a.op_b_memory.prev_value[2].val, a.op_b_memory.prev_value[3].val], - ir),
    (.Memory, "SP1Memory",
      [chk.val, (cl + 3).val, a.op_b[0].val, 0, 0,
        a.op_b_memory.prev_value[0].val, a.op_b_memory.prev_value[1].val,
        a.op_b_memory.prev_value[2].val, a.op_b_memory.prev_value[3].val], ir),
    -- op_c: read-prior pull, read-back push
    (.Memory, "SP1Memory",
      [chk.val, a.op_c_memory.access_timestamp.prev_low.val, a.op_c[0].val, 0, 0,
        a.op_c_memory.prev_value[0].val, a.op_c_memory.prev_value[1].val,
        a.op_c_memory.prev_value[2].val, a.op_c_memory.prev_value[3].val], - ir),
    (.Memory, "SP1Memory",
      [chk.val, (cl + 2).val, a.op_c[0].val, 0, 0,
        a.op_c_memory.prev_value[0].val, a.op_c_memory.prev_value[1].val,
        a.op_c_memory.prev_value[2].val, a.op_c_memory.prev_value[3].val], ir) ]

/-- **Projection = emission (register reads).** The reader's read-only projection `memoryReadLookups` equals
the `Memory`-filtered, `toAccess`-imaged interactions the native `Readers/RTypeReader` block emits — the
register analogue of `memAccessLookups_eq_emitted`. The three `RegisterAccessCols` sub-assertions emit only
`byteChannel`, the program pull is a different channel, and the `op_a_0` gates emit nothing, leaving exactly
the five read pulls/pushes: op_a/b/c read-prior *pulls* (`−is_real`, `toAccess_pullIf_memory`) and op_b/c
read-back *pushes* (`+is_real`, `toAccess_pushIf_memory`). The op_a *write* push lives in
`Readers/RegisterWrite`, so it is not among the reader's emissions. -/
theorem memoryLookups_eq_emitted (r : Trace.RowView (ZMod p)) (env : Environment (ZMod p)) (offset : ℕ)
    [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (input : Var Readers.RTypeReader.Inputs (ZMod p))
    (h_real : r.is_real = 0 ∨ r.is_real = 1)
    (h_ir : Expression.eval env input.is_real = r.is_real)
    (h_ch : Expression.eval env input.clk_high = r.state.clk_high)
    (h_cl : Expression.eval env input.clk_low = rowClkLow r)
    (h_oa : Expression.eval env input.cols.op_a = r.adapter.op_a)
    (h_ob : Expression.eval env input.cols.op_b = r.adapter.op_b[0])
    (h_oc : Expression.eval env input.cols.op_c = r.adapter.op_c[0])
    (h_pl_a : Expression.eval env input.cols.op_a_memory.access_timestamp.prev_low =
      r.adapter.op_a_memory.access_timestamp.prev_low)
    (h_pv_a0 : Expression.eval env input.cols.op_a_memory.prev_value[0] =
      r.adapter.op_a_memory.prev_value[0])
    (h_pv_a1 : Expression.eval env input.cols.op_a_memory.prev_value[1] =
      r.adapter.op_a_memory.prev_value[1])
    (h_pv_a2 : Expression.eval env input.cols.op_a_memory.prev_value[2] =
      r.adapter.op_a_memory.prev_value[2])
    (h_pv_a3 : Expression.eval env input.cols.op_a_memory.prev_value[3] =
      r.adapter.op_a_memory.prev_value[3])
    (h_pl_b : Expression.eval env input.cols.op_b_memory.access_timestamp.prev_low =
      r.adapter.op_b_memory.access_timestamp.prev_low)
    (h_pv_b0 : Expression.eval env input.cols.op_b_memory.prev_value[0] =
      r.adapter.op_b_memory.prev_value[0])
    (h_pv_b1 : Expression.eval env input.cols.op_b_memory.prev_value[1] =
      r.adapter.op_b_memory.prev_value[1])
    (h_pv_b2 : Expression.eval env input.cols.op_b_memory.prev_value[2] =
      r.adapter.op_b_memory.prev_value[2])
    (h_pv_b3 : Expression.eval env input.cols.op_b_memory.prev_value[3] =
      r.adapter.op_b_memory.prev_value[3])
    (h_pl_c : Expression.eval env input.cols.op_c_memory.access_timestamp.prev_low =
      r.adapter.op_c_memory.access_timestamp.prev_low)
    (h_pv_c0 : Expression.eval env input.cols.op_c_memory.prev_value[0] =
      r.adapter.op_c_memory.prev_value[0])
    (h_pv_c1 : Expression.eval env input.cols.op_c_memory.prev_value[1] =
      r.adapter.op_c_memory.prev_value[1])
    (h_pv_c2 : Expression.eval env input.cols.op_c_memory.prev_value[2] =
      r.adapter.op_c_memory.prev_value[2])
    (h_pv_c3 : Expression.eval env input.cols.op_c_memory.prev_value[3] =
      r.adapter.op_c_memory.prev_value[3]) :
    memoryReadLookups r =
      (((Readers.RTypeReader.main input).operations offset).interactionsWith
          memoryChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have hp2 : 2 < p := two_lt_p_aux
  -- The three `RegisterAccessCols` sub-assertions emit only `byteChannel`, and the five `op_a_0` Equality
  -- gates emit nothing — so their `memoryChannel` filter is empty (`filter_interactions_formalAssertion_eq_nil`).
  have hrac := fun (n : ℕ) (inp : Var Readers.RegisterAccessCols.Inputs (ZMod p)) =>
    filter_interactions_formalAssertion_eq_nil Readers.RegisterAccessCols.circuit memoryChannel.toRaw
      (n := n) inp (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
      (by simp [circuit_norm, Readers.RegisterAccessCols.circuit])
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) memoryChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [Readers.RTypeReader.main, circuit_norm, hrac, heq,
    SP1Clean.Channels.programChannel_eq_memoryChannel_false, if_false]
  -- W11 flip: the read-priors are now `pull`s (`toAccess_pullIf_memory`, mult `signedVal (-is_real)`), the
  -- read-backs `push`es (`toAccess_pushIf_memory`, mult `signedVal is_real`) — matching `memoryReadLookups`.
  simp only [toAccess_pushIf_memory, toAccess_pullIf_memory]
  simp [circuit_norm, signedVal_is_real hp2 h_real, signedVal_neg_is_real hp2 h_real,
    memoryReadLookups, rowClkLow, h_ir, h_ch, h_cl, h_oa, h_ob, h_oc,
    h_pl_a, h_pv_a0, h_pv_a1, h_pv_a2, h_pv_a3, h_pl_b, h_pv_b0, h_pv_b1, h_pv_b2, h_pv_b3,
    h_pl_c, h_pv_c0, h_pv_c1, h_pv_c2, h_pv_c3]

/-! ## Real-address memory access (the `LoadDouble` / `StoreDouble` write path)

The register projections above commit `.memory` interactions at *register* addresses (`addr1 = addr2 =
0`, the operand index in `addr0`). The memory chips (`Chips/{LoadDouble,StoreDouble}Chip.lean`) add one
more `.memory` access — emitted by the `Readers/MemoryAccess` block — at a **real 48-bit address**
(`AddressOperation.value`, three 16-bit limbs in `addr0/addr1/addr2`). It is the same send-prior /
receive-new pair, so it feeds the same `multiplicitySum` bus and the same `MemEvent` /
`isConsistentOnline` offline-memory model — only the address limbs differ (nonzero), and the received word
is the loaded value (a read: `new = prev`) or the stored `rs2` word (a write: `new = store_value`). The
projections below are standalone (parameterised by the `MemoryAccess` input data rather than `RowView`,
which carries no memory-access columns); they compose with the per-row register projections to give a
load/store row's full Memory-bus contribution. The model itself needs no change — exactly the Phase-F
claim that real-address read/write events plug into the existing offline memory. -/

/-- The two signed Memory-bus contributions the `MemoryAccess` block emits at a **real 3-limb address**
(W11 polarity flip): a `pull` of the prior word at the previous timestamp (`−is_real` — the chip *derives*
`MemoryMsg.isU64 prev_value`) and a `push` of `new_value` at the current timestamp `(clk_high, clk_low + 1)`
(`+is_real` — the chip *proves* `isU64 new_value`). Matches `Readers/MemoryAccess.lean:99-108`. On padding
rows both vanish (`memAccessLookups_padding`). -/
def memAccessLookups (mem : Extracted.MemoryAccessCols (ZMod p))
    (clk_high clk_low addr0 addr1 addr2 : ZMod p) (new_value : Word (ZMod p)) (is_real : ZMod p) :
    LookupAccessList :=
  let ts := mem.access_timestamp
  let ir := (is_real.val : ℤ)
  [ (.Memory, "SP1Memory",
      [ts.prev_high.val, ts.prev_low.val, addr0.val, addr1.val, addr2.val,
        mem.prev_value[0].val, mem.prev_value[1].val, mem.prev_value[2].val,
        mem.prev_value[3].val], - ir),
    (.Memory, "SP1Memory",
      [clk_high.val, (clk_low + 1).val, addr0.val, addr1.val, addr2.val,
        new_value[0].val, new_value[1].val, new_value[2].val, new_value[3].val], ir) ]

/-- The single offline-memory event a memory access contributes at the **real** recombined 48-bit
address (`addr0 + addr1·2^16 + addr2·2^32`), at the current timestamp `clk_low + 1`: value `new_value`
(for a load `new = prev`, the loaded word; for a store the stored `rs2` word), `is_write` distinguishing
a store (`true`) from a load (`false`). Uses the same `MemEvent` carrier as the register events, so it
joins the same `memEvents`/`memoryConsistent` model. -/
def memAccessEvent (clk_low addr0 addr1 addr2 : ZMod p) (prev_value new_value : Word (ZMod p))
    (is_write : Bool) (prev_ts clk_high : ℕ) : MemEvent (ZMod p) :=
  { addr := addr0 + addr1 * 65536 + addr2 * 65536 ^ 2,
    clk := clk_low + 1,
    prevValue := prev_value,
    value := new_value,
    is_write := is_write,
    prevTs := prev_ts,
    clkHigh := clk_high }

/-- **Gating is real (memory access).** A padding row (`is_real = 0`) contributes zero to every Memory
key: both signed contributions of the real-address access have multiplicity `±0`. The real-address
analogue of `memoryLookups_padding`. -/
theorem memAccessLookups_padding [NeZero p] (mem : Extracted.MemoryAccessCols (ZMod p))
    (clk_high clk_low addr0 addr1 addr2 : ZMod p) (new_value : Word (ZMod p)) (is_real : ZMod p)
    (h : is_real = 0) :
    ∀ k, multiplicitySum
        (memAccessLookups mem clk_high clk_low addr0 addr1 addr2 new_value is_real) k = 0 := by
  intro k
  simp only [memAccessLookups, multiplicitySum_cons, multiplicitySum_nil, multOf, h, ZMod.val_zero,
    Nat.cast_zero, neg_zero, ite_self, add_zero]

/-- **Projection = emission (memory access).** The real-address projection `memAccessLookups` equals the
`Memory`-filtered, `toAccess`-imaged interactions the native `Readers/MemoryAccess` block emits — the
real-address analogue of `memoryLookups_eq_emitted`. The two `byteChannel` range pulls and the three
`assertZero` timestamp gates are filtered out (`byteChannel ≠ memoryChannel`; asserts emit nothing),
leaving exactly the send-prior / receive-new pair. -/
theorem memAccessLookups_eq_emitted (env : Environment (ZMod p)) (offset : ℕ)
    [Fact p.Prime] [Fact (2 ^ 17 < p)]
    (input : Var Readers.MemoryAccess.Inputs (ZMod p))
    (mem : Extracted.MemoryAccessCols (ZMod p))
    (clk_high clk_low addr0 addr1 addr2 : ZMod p) (new_value : Word (ZMod p)) (is_real : ZMod p)
    (h_real : is_real = 0 ∨ is_real = 1)
    (h_ir : Expression.eval env input.is_real = is_real)
    (h_ch : Expression.eval env input.clk_high = clk_high)
    (h_cl : Expression.eval env input.clk_low = clk_low)
    (h_a0 : Expression.eval env input.addr0 = addr0)
    (h_a1 : Expression.eval env input.addr1 = addr1)
    (h_a2 : Expression.eval env input.addr2 = addr2)
    (h_ph : Expression.eval env input.mem.access_timestamp.prev_high = mem.access_timestamp.prev_high)
    (h_pl : Expression.eval env input.mem.access_timestamp.prev_low = mem.access_timestamp.prev_low)
    (h_pv0 : Expression.eval env input.mem.prev_value[0] = mem.prev_value[0])
    (h_pv1 : Expression.eval env input.mem.prev_value[1] = mem.prev_value[1])
    (h_pv2 : Expression.eval env input.mem.prev_value[2] = mem.prev_value[2])
    (h_pv3 : Expression.eval env input.mem.prev_value[3] = mem.prev_value[3])
    (h_nv0 : Expression.eval env input.new_value[0] = new_value[0])
    (h_nv1 : Expression.eval env input.new_value[1] = new_value[1])
    (h_nv2 : Expression.eval env input.new_value[2] = new_value[2])
    (h_nv3 : Expression.eval env input.new_value[3] = new_value[3]) :
    memAccessLookups mem clk_high clk_low addr0 addr1 addr2 new_value is_real =
      (((Readers.MemoryAccess.main input).operations offset).interactionsWith
          memoryChannel.toRaw).map (AbstractInteraction.toAccess env) := by
  have hp2 : 2 < p := two_lt_p_aux
  -- the three `=== 0` timestamp gates compile to `Gadgets.Equality.circuit field` subcircuits, which emit
  -- nothing on `memoryChannel`; the two `byteChannel.pullIf`s are filtered by channel-distinctness.
  have heq := fun (n : ℕ) (inp : Var (ProvablePair field field) (ZMod p)) =>
    @filter_interactions_formalAssertion_eq_nil (ZMod p) _ (ProvablePair field field)
      ProvablePair.instance (Gadgets.Equality.circuit field) memoryChannel.toRaw n inp
      List.not_mem_nil List.not_mem_nil
  simp only [Readers.MemoryAccess.main, circuit_norm, heq,
    SP1Clean.Channels.byteChannel_eq_memoryChannel_false, if_false]
  simp only [toAccess_pushIf_memory, toAccess_pullIf_memory]
  simp [circuit_norm, signedVal_is_real hp2 h_real, signedVal_neg_is_real hp2 h_real,
    memAccessLookups, h_ir, h_ch, h_cl, h_a0, h_a1, h_a2, h_ph, h_pl,
    h_pv0, h_pv1, h_pv2, h_pv3, h_nv0, h_nv1, h_nv2, h_nv3]

/-! ## Bridge to the vendored OfflineMemory permutation closure

`Clean.Utils.OfflineMemory` ships the address-sorted permutation closure
(`MemoryAccessList.isConsistentOnline_iff_isConsistentOffline`) over `MemoryAccess := ℕ×ℕ×ℕ×ℕ` tuples. To
reuse it we encode the native field-valued `MemEvent`s into that tuple form, and derive the offline-memory
link from the Memory-bus balance + a `MemoryProvider` init/finalize receiver (the closed-bus analogue of
`ProgramProvider`).

**Encoding faithfulness.** All four tuple fields are faithful: `timestamp = clk.val` and `addr = addr.val`
(drive the sortedness discharge), `readValue = prevValue` (the value read), `writeValue = value` (the value
left). The read/write split — `MemEvent` carries the read-old `prevValue` *and* the write-new `value` —
is what makes the vendored `isConsistentOnline` check (`readValue = lastWriteValue`) faithful for genuine
writes: the `rd` write reads x[rd]'s prior value (`op_a_memory.prev_value`) and writes `rdWrite`, so a later
read of x[rd] returns exactly the written value, matching SP1's offline memory. -/

/-- Recombine a 4-limb value word into a single `ℕ` (16-bit limbs). Load-bearing only for the deferred
`isConsistentOnline` bridge; see the faithfulness note above. -/
def wordToNat (v : Vector (ZMod p) 4) : ℕ :=
  v[0].val + v[1].val * 2 ^ 16 + v[2].val * 2 ^ 32 + v[3].val * 2 ^ 48

/-- Encode a native `MemEvent` into the vendored `(timestamp, addr, readValue, writeValue)` tuple — all
four fields faithful: timestamp `clk.val`, address `addr.val`, **readValue** `prevValue` (the value this
access reads), **writeValue** `value` (the value it leaves; for a read `value = prevValue`). -/
def MemEvent.toAccess (e : MemEvent (ZMod p)) : MemoryAccess :=
  (e.clk.val, e.addr.val, wordToNat e.prevValue, wordToNat e.value)

/-- The trace's memory accesses in the vendored model's **decreasing-timestamp** orientation (head = latest):
`rows.reverse`, then per row the `rowMemEvents` (already emitted in decreasing offset order `[+4,+3,+2]`),
encoded via `MemEvent.toAccess`. -/
def memAccessList (rows : List (Trace.RowView (ZMod p))) : MemoryAccessList :=
  rows.reverse.flatMap (fun r => (rowMemEvents r).map MemEvent.toAccess)

/-- Clock-monotonicity trace-shape bundle: per-row accesses are timestamp-decreasing, and across
`rows.reverse` every earlier-listed (chronologically later) row's accesses strictly post-date a later-listed
row's. The single residual trace-shape fact dischargeable from per-row Specs + a clock-link (needs `2^24 < p`
so the encoded clock does not wrap). -/
structure TraceMemClkValid (rows : List (Trace.RowView (ZMod p))) : Prop where
  intra_row_sorted : ∀ r ∈ rows,
    ((rowMemEvents r).map MemEvent.toAccess).Pairwise timestamp_ordering
  inter_row_sorted : rows.reverse.Pairwise (fun r₁ r₂ =>
    ∀ x ∈ (rowMemEvents r₁).map MemEvent.toAccess,
      ∀ y ∈ (rowMemEvents r₂).map MemEvent.toAccess, timestamp_ordering x y)

/-- **Sortedness discharge.** Under `TraceMemClkValid`, the encoded access list is timestamp-sorted — the
hypothesis the vendored closure (`isConsistentOnline_iff_isConsistentOffline`) requires. -/
theorem memAccessList_isTimestampSorted (rows : List (Trace.RowView (ZMod p)))
    (h : TraceMemClkValid rows) : (memAccessList rows).isTimestampSorted := by
  rw [MemoryAccessList.isTimestampSorted, memAccessList, List.pairwise_flatMap]
  exact ⟨fun r hr => h.intra_row_sorted r (List.mem_reverse.mp hr), h.inter_row_sorted⟩

/-- **No-duplicate-timestamps discharge.** Under `TraceMemClkValid`, the encoded access list has no
repeated timestamps — the closure's second hypothesis. -/
theorem memAccessList_Notimestampdup (rows : List (Trace.RowView (ZMod p)))
    (h : TraceMemClkValid rows) : (memAccessList rows).Notimestampdup := by
  refine List.Pairwise.imp ?_ (memAccessList_isTimestampSorted rows h)
  rintro ⟨t2, _, _, _⟩ ⟨t1, _, _, _⟩ hxy
  simp only [timestamp_ordering] at hxy
  simp only [MemoryAccessList.timestamps_neq]
  omega

/-! ## Filtered aggregator + ordering side condition

The unfiltered `memAccessList` (and `memEvents`) emit three events per row *ungated*, but the Memory bus
gates op_a by `±is_real` and op_b/op_c by `±is_real·(1-imm)`. So a padding row (`is_real = 0`, garbage
columns) and an *immediate* operand on a real row (`imm = 1`, no bus entry) both contribute an event with
**no backing bus contribution**, which would pollute the per-address chains in `isConsistentOnline` with
accesses balance cannot match. The *filtered* aggregator drops exactly those, so every event it keeps is
backed by a bus send/receive pair. -/

/-- The register events of a row that have a backing Memory-bus contribution: the `rd` write (on a real
row), plus the `rs1`/`rs2` read-backs only when that operand is a register (`imm = 0`). On a padding row,
none. Matches `memoryLookups`'s gating (`±is_real`, `±is_real·(1-imm_b/c)`). -/
def rowMemEventsGated (r : Trace.RowView (ZMod p)) : List (MemEvent (ZMod p)) :=
  if r.is_real = 0 then []
  else opAEvent r :: ((if r.adapter.imm_b = 0 then [opBEvent r] else [])
    ++ (if r.adapter.imm_c = 0 then [opCEvent r] else []))

/-- `rowMemEventsGated` keeps a subsequence of `rowMemEvents` (drop padding entirely; drop op_b/op_c for
immediate operands). -/
theorem rowMemEventsGated_sublist (r : Trace.RowView (ZMod p)) :
    List.Sublist (rowMemEventsGated r) (rowMemEvents r) := by
  simp only [rowMemEventsGated, rowMemEvents]
  split_ifs <;>
    repeat' first
      | exact List.Sublist.refl _
      | exact List.nil_sublist _
      | apply List.Sublist.cons_cons
      | apply List.Sublist.cons

/-- Generic: a per-element sublist of the bodies lifts to a sublist of the `flatMap`s. -/
theorem flatMap_sublist_flatMap {α β : Type*} {l : List α} {f g : α → List β}
    (h : ∀ a ∈ l, List.Sublist (f a) (g a)) :
    List.Sublist (l.flatMap f) (l.flatMap g) := by
  induction l with
  | nil => simp
  | cons a t ih =>
    simp only [List.flatMap_cons]
    exact (h a (by simp)).append (ih (fun x hx => h x (by simp [hx])))

/-- All filtered register events of a trace, in the vendored model's decreasing-timestamp orientation
(head = latest), matching `memAccessList`. -/
def memEventsFiltered (rows : List (Trace.RowView (ZMod p))) : List (MemEvent (ZMod p)) :=
  rows.reverse.flatMap rowMemEventsGated

/-- The trace's *backed* memory accesses, vendored-tuple form: the filtered events encoded by `toAccess`.
This — not `memAccessList` — is what the offline-memory link should range over (padding/immediate events
have no bus backing). -/
def memAccessListFiltered (rows : List (Trace.RowView (ZMod p))) : MemoryAccessList :=
  (memEventsFiltered rows).map MemEvent.toAccess

/-- The filtered access list is a sublist of the unfiltered one. -/
theorem memAccessListFiltered_sublist (rows : List (Trace.RowView (ZMod p))) :
    List.Sublist (memAccessListFiltered rows) (memAccessList rows) := by
  rw [memAccessListFiltered, memEventsFiltered, memAccessList, List.map_flatMap]
  exact flatMap_sublist_flatMap (fun r _ => (rowMemEventsGated_sublist r).map MemEvent.toAccess)

/-- **Sortedness (filtered).** Inherited from the unfiltered discharge via the sublist. -/
theorem memAccessListFiltered_isTimestampSorted (rows : List (Trace.RowView (ZMod p)))
    (h : TraceMemClkValid rows) : (memAccessListFiltered rows).isTimestampSorted :=
  (memAccessList_isTimestampSorted rows h).sublist (memAccessListFiltered_sublist rows)

/-- **No-duplicate-timestamps (filtered).** Inherited likewise. -/
theorem memAccessListFiltered_Notimestampdup (rows : List (Trace.RowView (ZMod p)))
    (h : TraceMemClkValid rows) : (memAccessListFiltered rows).Notimestampdup :=
  (memAccessList_Notimestampdup rows h).sublist (memAccessListFiltered_sublist rows)

/-- The filtered events of a trace at a single address `addr` (compared via `.val`, the vendored tuple's
address). The per-address single-address chain ranges over `(eventsAt rows addr).map toAccess`. -/
def eventsAt (rows : List (Trace.RowView (ZMod p))) (addr : ℕ) : List (MemEvent (ZMod p)) :=
  (memEventsFiltered rows).filter (fun e => decide (e.addr.val = addr))

/-- A per-address access (`∈ eventsAt`) is one of the trace's bus-backed events
(`∈ memEventsFiltered`). Shared by the single-address chain proof and the `isU64` recovery. -/
theorem mem_memEventsFiltered_of_mem_eventsAt {rows : List (Trace.RowView (ZMod p))}
    {addr : ℕ} {e : MemEvent (ZMod p)} (he : e ∈ eventsAt rows addr) :
    e ∈ memEventsFiltered rows :=
  List.mem_of_mem_filter he

/-- Membership in `eventsAt rows addr` pins the event's address (`.val`). -/
theorem addr_of_mem_eventsAt {rows : List (Trace.RowView (ZMod p))}
    {addr : ℕ} {e : MemEvent (ZMod p)} (he : e ∈ eventsAt rows addr) :
    e.addr.val = addr := by
  simpa using (List.mem_filter.mp he).2

/-- The vendored `filterAddress` of the filtered access list is `eventsAt` mapped through `toAccess` —
the bridge that lets the per-address single-address proof work at the event level (where `prevTs` lives).
-/
theorem filterAddress_memAccessListFiltered (rows : List (Trace.RowView (ZMod p))) (addr : ℕ) :
    MemoryAccessList.filterAddress (memAccessListFiltered rows) addr
      = (eventsAt rows addr).map MemEvent.toAccess := by
  rw [MemoryAccessList.filterAddress, memAccessListFiltered, eventsAt, List.filter_map]
  rfl

/-- **Memory ordering side condition (the residual; M4a-1).** A pure timestamp/address structure
fact about the per-address filtered event lists (decreasing-timestamp order, head = latest): for adjacent
same-address events, the earlier-in-list (chronologically *later*) event's `prevTs` names the next event's
timestamp. No value claim — values come from balance; this only fixes *which* earlier access is the
relevant writer (so the balance-matched receive is the most-recent earlier write). The Memory analogue of
State's `TraceClkAdvance`; SP1 enforces it via the memory-argument timestamp range checks (`prev_ts < ts`)
+ the global per-address ordering of the memory permutation. -/
def memPrevLink (rows : List (Trace.RowView (ZMod p))) : Prop :=
  ∀ addr : ℕ, ∀ i : ℕ, (hi : i + 1 < (eventsAt rows addr).length) →
    ((eventsAt rows addr)[i]'(by omega)).prevTs = ((eventsAt rows addr)[i + 1]'hi).clk.val

/-- **Read-send matched from balance (the Memory balance-core).** On the balanced Memory bus (consumers
plus the init/finalize `memProv`), every real row's `op_a` read-send — the positive contribution
`(clk_high, prev_ts, op_a, 0, 0, prev_value)` claiming x[rd]'s prior value — is cancelled by *some*
strictly-negative contribution at the same key (another access's receive, or a provider boundary entry).
This is the genuine balance-derived content for Memory, the closed-bus analogue of
`StateConsistency.state_successor_of_balance` (a direct `balanced_pos_has_neg`). It is the foundation of the
offline-memory derivation: the canceling receive is the writer whose value the read returns. Pinning *which*
access cancels it — and hence `isConsistentOnline` — additionally needs the timestamp-ordering side
condition + the bus↔access-list correspondence documented below. -/
theorem mem_opA_read_send_matched [NeZero p]
    (rows : List (Trace.RowView (ZMod p))) (memProv : LookupAccessList)
    (h_bal : isConsistentBalanced (aggregateChipRows rows memoryLookups ++ memProv))
    (r : Trace.RowView (ZMod p)) (hr : r ∈ rows) (h_real : r.is_real ≠ 0) :
    ∃ b ∈ aggregateChipRows rows memoryLookups ++ memProv,
      keyOf b = (InteractionKind.Memory, "SP1Memory",
        [r.state.clk_high.val, r.adapter.op_a_memory.access_timestamp.prev_low.val,
          r.adapter.op_a.val, 0, 0,
          r.adapter.op_a_memory.prev_value[0].val, r.adapter.op_a_memory.prev_value[1].val,
          r.adapter.op_a_memory.prev_value[2].val, r.adapter.op_a_memory.prev_value[3].val]) ∧
      multOf b < 0 := by
  set send : LookupAccess :=
    (.Memory, "SP1Memory",
      [r.state.clk_high.val, r.adapter.op_a_memory.access_timestamp.prev_low.val,
        r.adapter.op_a.val, 0, 0,
        r.adapter.op_a_memory.prev_value[0].val, r.adapter.op_a_memory.prev_value[1].val,
        r.adapter.op_a_memory.prev_value[2].val, r.adapter.op_a_memory.prev_value[3].val],
      (r.is_real.val : ℤ)) with hsend
  have h_send_mem : send ∈ aggregateChipRows rows memoryLookups ++ memProv :=
    List.mem_append_left _ (List.mem_flatMap.mpr ⟨r, hr, by rw [hsend]; simp [memoryLookups]⟩)
  have hpos : 0 < multOf send := by rw [hsend]; simpa only [multOf] using valCast_pos_aux h_real
  obtain ⟨b, hb, hbk, hbneg⟩ :=
    balanced_pos_has_neg (aggregateChipRows rows memoryLookups ++ memProv) (keyOf send)
      h_bal send h_send_mem rfl hpos
  exact ⟨b, hb, by rw [hbk, hsend], hbneg⟩

/-! ## Correspondence + canceller split

Every filtered event's Memory-bus *send* and *receive* keys are functions of the event alone
(`MemEvent` carries `clkHigh`/`prevTs`), so they match the `memoryLookups` keys exactly. The canceller of an
event's send (from balance) is then either another filtered event's *receive* (the writer) or a `memProv`
boundary entry. Needs per-row well-formedness (`is_real`/`imm_b`/`imm_c` binary) so the bus multiplicity
`is_real·(1-imm)` is exactly `±1`, matching one event per access (the chip constrains all three binary). -/

/-- The Memory-bus SEND key of an event: `[clkHigh, prevTs, addr, 0, 0, prevValue-limbs]`. For every operand
the send carries the *prior* value at the *previous* timestamp, uniformly. -/
def memEvent_sendKey (e : MemEvent (ZMod p)) : LookupKey :=
  (InteractionKind.Memory, "SP1Memory",
    [e.clkHigh, e.prevTs, e.addr.val, 0, 0,
      e.prevValue[0].val, e.prevValue[1].val, e.prevValue[2].val, e.prevValue[3].val])

/-- The Memory-bus RECEIVE key of an event: `[clkHigh, clk, addr, 0, 0, value-limbs]` — the *new* value at
the *current* timestamp. -/
def memEvent_recvKey (e : MemEvent (ZMod p)) : LookupKey :=
  (InteractionKind.Memory, "SP1Memory",
    [e.clkHigh, e.clk.val, e.addr.val, 0, 0,
      e.value[0].val, e.value[1].val, e.value[2].val, e.value[3].val])

/-- Per-row well-formedness for the offline-memory derivation: the gate selectors are binary, so the bus
multiplicities `is_real`, `is_real·(1-imm_b)`, `is_real·(1-imm_c)` are each exactly `0` or `1` — one event
per active access. The chip constrains all three binary; assumed here as a trace-shape fact. -/
def MemRowWellFormed (r : Trace.RowView (ZMod p)) : Prop :=
  (r.is_real = 0 ∨ r.is_real = 1) ∧ (r.adapter.imm_b = 0 ∨ r.adapter.imm_b = 1) ∧
    (r.adapter.imm_c = 0 ∨ r.adapter.imm_c = 1)

/-- **Send in bus (positive).** Every filtered event's send sits in the Memory bus at `memEvent_sendKey e`
with strictly-positive multiplicity (the operand is gated-in: real row, register operand). Generalises the
op_a-only `mem_opA_read_send_matched` to all three operands. -/
theorem memEvent_send_pos_in_bus [NeZero p] (rows : List (Trace.RowView (ZMod p)))
    (e : MemEvent (ZMod p)) (he : e ∈ memEventsFiltered rows) :
    ∃ s ∈ aggregateChipRows rows memoryLookups, keyOf s = memEvent_sendKey e ∧ 0 < multOf s := by
  rw [memEventsFiltered, List.mem_flatMap] at he
  obtain ⟨r, hr, he⟩ := he
  rw [List.mem_reverse] at hr
  simp only [aggregateChipRows]
  rw [rowMemEventsGated] at he
  by_cases hreal : r.is_real = 0
  · rw [if_pos hreal] at he; exact absurd he List.not_mem_nil
  rw [if_neg hreal, List.mem_cons] at he
  rcases he with rfl | he
  · -- op_a: the head event
    refine ⟨(.Memory, "SP1Memory",
        [r.state.clk_high.val, r.adapter.op_a_memory.access_timestamp.prev_low.val, r.adapter.op_a.val,
          0, 0, r.adapter.op_a_memory.prev_value[0].val, r.adapter.op_a_memory.prev_value[1].val,
          r.adapter.op_a_memory.prev_value[2].val, r.adapter.op_a_memory.prev_value[3].val],
        (r.is_real.val : ℤ)),
      List.mem_flatMap.mpr ⟨r, hr, by simp [memoryLookups]⟩, ?_, ?_⟩
    · simp [keyOf, memEvent_sendKey, opAEvent]
    · simp only [multOf]; exact valCast_pos_aux hreal
  rw [List.mem_append] at he
  rcases he with he | he
  · -- op_b: present only when imm_b = 0
    by_cases himmb : r.adapter.imm_b = 0
    · rw [if_pos himmb, List.mem_singleton] at he; subst he
      refine ⟨(.Memory, "SP1Memory",
          [r.state.clk_high.val, r.adapter.op_b_memory.access_timestamp.prev_low.val,
            r.adapter.op_b[0].val, 0, 0, r.adapter.op_b_memory.prev_value[0].val,
            r.adapter.op_b_memory.prev_value[1].val, r.adapter.op_b_memory.prev_value[2].val,
            r.adapter.op_b_memory.prev_value[3].val],
          ((r.is_real * (1 - r.adapter.imm_b)).val : ℤ)),
        List.mem_flatMap.mpr ⟨r, hr, by simp [memoryLookups]⟩, ?_, ?_⟩
      · simp [keyOf, memEvent_sendKey, opBEvent]
      · simp only [multOf, himmb, sub_zero, mul_one]; exact valCast_pos_aux hreal
    · rw [if_neg himmb] at he; exact absurd he List.not_mem_nil
  · -- op_c: present only when imm_c = 0
    by_cases himmc : r.adapter.imm_c = 0
    · rw [if_pos himmc, List.mem_singleton] at he; subst he
      refine ⟨(.Memory, "SP1Memory",
          [r.state.clk_high.val, r.adapter.op_c_memory.access_timestamp.prev_low.val,
            r.adapter.op_c[0].val, 0, 0, r.adapter.op_c_memory.prev_value[0].val,
            r.adapter.op_c_memory.prev_value[1].val, r.adapter.op_c_memory.prev_value[2].val,
            r.adapter.op_c_memory.prev_value[3].val],
          ((r.is_real * (1 - r.adapter.imm_c)).val : ℤ)),
        List.mem_flatMap.mpr ⟨r, hr, by simp [memoryLookups]⟩, ?_, ?_⟩
      · simp [keyOf, memEvent_sendKey, opCEvent]
      · simp only [multOf, himmc, sub_zero, mul_one]; exact valCast_pos_aux hreal
    · rw [if_neg himmc] at he; exact absurd he List.not_mem_nil

/-- **Negative entry is a receive.** A strictly-negative `memoryLookups r` entry (under per-row
well-formedness) is the *receive* of a gated event — its key is `memEvent_recvKey e` for some
`e ∈ rowMemEventsGated r`. The three *sends* have non-negative multiplicity (`≥ 0`), so a negative entry
must be one of the three receives, whose operand is then gated-in (real row, register operand). -/
theorem mem_neg_entry_is_recv [NeZero p] (r : Trace.RowView (ZMod p)) (hwf : MemRowWellFormed r)
    (b : LookupAccess) (hb : b ∈ memoryLookups r) (hneg : multOf b < 0) :
    ∃ e ∈ rowMemEventsGated r, keyOf b = memEvent_recvKey e := by
  obtain ⟨_, hwfb, hwfc⟩ := hwf
  simp only [memoryLookups, List.mem_cons, List.not_mem_nil, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl | rfl | rfl
  · -- op_a send: multiplicity `is_real.val ≥ 0`
    exact absurd hneg (not_lt.mpr (Int.natCast_nonneg _))
  · -- op_a receive
    simp only [multOf] at hneg
    have hisreal : r.is_real ≠ 0 := fun h0 => by simp [h0] at hneg
    refine ⟨opAEvent r, ?_, ?_⟩
    · rw [rowMemEventsGated, if_neg hisreal]; exact List.mem_cons.mpr (Or.inl rfl)
    · simp [keyOf, memEvent_recvKey, opAEvent]
  · -- op_b send
    exact absurd hneg (not_lt.mpr (Int.natCast_nonneg _))
  · -- op_b receive
    simp only [multOf] at hneg
    have hisreal : r.is_real ≠ 0 := fun h0 => by simp [h0] at hneg
    have himmb : r.adapter.imm_b = 0 := hwfb.resolve_right fun h => by simp [h] at hneg
    refine ⟨opBEvent r, ?_, ?_⟩
    · rw [rowMemEventsGated, if_neg hisreal, if_pos himmb]
      exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (List.mem_cons.mpr (Or.inl rfl)))))
    · simp [keyOf, memEvent_recvKey, opBEvent]
  · -- op_c send
    exact absurd hneg (not_lt.mpr (Int.natCast_nonneg _))
  · -- op_c receive
    simp only [multOf] at hneg
    have hisreal : r.is_real ≠ 0 := fun h0 => by simp [h0] at hneg
    have himmc : r.adapter.imm_c = 0 := hwfc.resolve_right fun h => by simp [h] at hneg
    refine ⟨opCEvent r, ?_, ?_⟩
    · rw [rowMemEventsGated, if_neg hisreal, if_pos himmc]
      exact List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inl rfl)))))
    · simp [keyOf, memEvent_recvKey, opCEvent]

/-- **Canceller split (M4a-2).** From balance, every filtered event's send is cancelled either by another
filtered event's *receive* (`memEvent_recvKey e' = memEvent_sendKey e` — the writer at the previous
timestamp whose value `e` reads) or by a `memProv` boundary entry. The genuine balance-derived content for
the offline-memory link; the closed-bus analogue of `state_successor_of_balance`. -/
theorem memEvent_canceller [NeZero p] (rows : List (Trace.RowView (ZMod p)))
    (memProv : LookupAccessList) (hwf : ∀ r ∈ rows, MemRowWellFormed r)
    (h_bal : isConsistentBalanced (aggregateChipRows rows memoryLookups ++ memProv))
    (e : MemEvent (ZMod p)) (he : e ∈ memEventsFiltered rows) :
    (∃ e' ∈ memEventsFiltered rows, memEvent_recvKey e' = memEvent_sendKey e)
      ∨ (∃ b ∈ memProv, keyOf b = memEvent_sendKey e ∧ multOf b < 0) := by
  obtain ⟨s, hs_mem, hs_key, hs_pos⟩ := memEvent_send_pos_in_bus rows e he
  obtain ⟨b, hb_mem, hb_key, hb_neg⟩ :=
    balanced_pos_has_neg (aggregateChipRows rows memoryLookups ++ memProv) (memEvent_sendKey e)
      h_bal s (List.mem_append_left _ hs_mem) hs_key hs_pos
  rcases List.mem_append.mp hb_mem with hb_bus | hb_prov
  · left
    rw [aggregateChipRows, List.mem_flatMap] at hb_bus
    obtain ⟨r, hr, hb_in⟩ := hb_bus
    obtain ⟨e', he'_mem, he'_key⟩ := mem_neg_entry_is_recv r (hwf r hr) b hb_in hb_neg
    refine ⟨e', ?_, he'_key.symm.trans hb_key⟩
    rw [memEventsFiltered, List.mem_flatMap]
    exact ⟨r, List.mem_reverse.mpr hr, he'_mem⟩
  · right
    exact ⟨b, hb_prov, hb_key, hb_neg⟩

/-! ## Single-address consistency from balance -/

/-- **Structural reduction.** `isConsistentSingleAddress` of a `toAccess`-mapped event list follows from a
per-adjacent-pair `readValue = next.writeValue` chain (`wordToNat e.prevValue = wordToNat e'.value`) plus
the genesis fact (the last event reads `0`). -/
theorem isConsistentSingleAddress_of_chain :
    ∀ (events : List (MemEvent (ZMod p)))
      (h_sorted : MemoryAccessList.isTimestampSorted (events.map MemEvent.toAccess)),
      List.IsChain (fun e e' => wordToNat e.prevValue = wordToNat e'.value) events →
      (∀ (h : events ≠ []), wordToNat (events.getLast h).prevValue = 0) →
      MemoryAccessList.isConsistentSingleAddress (events.map MemEvent.toAccess) h_sorted := by
  intro events
  induction events with
  | nil => intro _ _ _; exact trivial
  | cons e rest ih =>
    intro h_sorted h_adj h_gen
    cases rest with
    | nil =>
      simpa [MemEvent.toAccess, MemoryAccessList.isConsistentSingleAddress] using h_gen (by simp)
    | cons e' rest' =>
      have hrec := ih (List.Pairwise.of_cons h_sorted) (List.isChain_cons_cons.mp h_adj).2 (by
        intro _
        have hg := h_gen (by simp)
        rwa [List.getLast_cons (by simp)] at hg)
      simp only [List.map_cons, MemoryAccessList.isConsistentSingleAddress, MemEvent.toAccess]
      exact ⟨(List.isChain_cons_cons.mp h_adj).1, hrec⟩

/-- **Timestamp injectivity of filtered events.** Two filtered events with equal low clock are equal
(from `Notimestampdup`: the mapped access list has pairwise-distinct timestamps). The Memory analogue of
`clkInjective_getElem`; pins a balance-matched receive to a unique event. -/
theorem memEventsFiltered_clk_inj (rows : List (Trace.RowView (ZMod p))) (h_clk : TraceMemClkValid rows)
    {e1 e2 : MemEvent (ZMod p)} (h1 : e1 ∈ memEventsFiltered rows) (h2 : e2 ∈ memEventsFiltered rows)
    (heq : e1.clk.val = e2.clk.val) : e1 = e2 := by
  have hpw : (memEventsFiltered rows).Pairwise (fun a b => a.clk.val ≠ b.clk.val) := by
    have hnd := memAccessListFiltered_Notimestampdup rows h_clk
    rw [memAccessListFiltered, MemoryAccessList.Notimestampdup, List.pairwise_map] at hnd
    exact hnd.imp (fun {a b} hab => by simpa [MemoryAccessList.timestamps_neq, MemEvent.toAccess] using hab)
  obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp h1
  obtain ⟨j, hj, hgj⟩ := List.mem_iff_getElem.mp h2
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · exact absurd (hgi ▸ hgj ▸ heq) (List.pairwise_iff_getElem.mp hpw i j hi hj hlt)
  · rw [← hgi, ← hgj]
  · exact absurd (hgi ▸ hgj ▸ heq).symm (List.pairwise_iff_getElem.mp hpw j i hj hi hgt)

/-- From `recvKey e' = sendKey e` recover the timestamp/address/value matches: the receiver's new
timestamp is `e.prevTs`, same address, and the written value equals the value `e` reads. -/
theorem recvKey_eq_sendKey {e' e : MemEvent (ZMod p)} (h : memEvent_recvKey e' = memEvent_sendKey e) :
    e'.clk.val = e.prevTs ∧ e'.addr.val = e.addr.val ∧ wordToNat e'.value = wordToNat e.prevValue := by
  rw [memEvent_recvKey, memEvent_sendKey] at h
  simp only [Prod.mk.injEq, List.cons.injEq, true_and, and_true] at h
  obtain ⟨_, hclk, haddr, hv0, hv1, hv2, hv3⟩ := h
  exact ⟨hclk, haddr, by simp [wordToNat, hv0, hv1, hv2, hv3]⟩

/-- The last element of a timestamp-sorted (decreasing) event list has the minimal clock — it is the
chronologically first access, the genesis. -/
theorem getLast_clk_le {events : List (MemEvent (ZMod p))}
    (hs : MemoryAccessList.isTimestampSorted (events.map MemEvent.toAccess))
    (hne : events ≠ []) {e'' : MemEvent (ZMod p)} (hx : e'' ∈ events) :
    (events.getLast hne).clk.val ≤ e''.clk.val := by
  obtain ⟨i, hi, hgi⟩ := List.mem_iff_getElem.mp hx
  rw [List.getLast_eq_getElem]
  rcases Nat.lt_or_ge i (events.length - 1) with hlt | hge
  · have hp := List.pairwise_iff_getElem.mp hs i (events.length - 1)
      (by rw [List.length_map]; omega) (by rw [List.length_map]; omega) (by omega)
    simp only [List.getElem_map, MemEvent.toAccess, timestamp_ordering] at hp
    rw [← hgi]; omega
  · obtain rfl : i = events.length - 1 := by omega
    exact le_of_eq (by rw [← hgi])

/-- **Provider-is-genesis (honest residual).** A `memProv` boundary entry sitting at an event's send key
forces that event to read `0` (the init chip's genesis value) and its `prevTs` to be below every real
event's timestamp (the genesis pointer). SP1's memory init/finalize chip provides initial value `0` at a
timestamp below all accesses; this captures exactly that, so the provider can only cancel a genesis send. -/
def MemProviderGenesis (memProv : LookupAccessList) (rows : List (Trace.RowView (ZMod p))) : Prop :=
  ∀ b ∈ memProv, ∀ e ∈ memEventsFiltered rows, keyOf b = memEvent_sendKey e →
    wordToNat e.prevValue = 0 ∧ ∀ e'' ∈ memEventsFiltered rows, e.prevTs ≠ e''.clk.val

/-- **Single-address consistency from balance (M4a-3, the de-risk gate).** For each address, the
balance-derived canceller + the ordering side conditions give the vendored `isConsistentSingleAddress`:
each read returns the most-recent earlier write at that address, and the genesis read returns `0`. -/
theorem isConsistentSingleAddress_of_balance [NeZero p] (rows : List (Trace.RowView (ZMod p)))
    (memProv : LookupAccessList) (addr : ℕ)
    (hwf : ∀ r ∈ rows, MemRowWellFormed r)
    (h_clk : TraceMemClkValid rows)
    (h_prev : memPrevLink rows)
    (h_prevlt : ∀ e ∈ memEventsFiltered rows, e.prevTs < e.clk.val)
    (h_prov : MemProviderGenesis memProv rows)
    (h_bal : isConsistentBalanced (aggregateChipRows rows memoryLookups ++ memProv))
    (h_sorted : MemoryAccessList.isTimestampSorted ((eventsAt rows addr).map MemEvent.toAccess)) :
    MemoryAccessList.isConsistentSingleAddress ((eventsAt rows addr).map MemEvent.toAccess) h_sorted := by
  have hsub : ∀ {e}, e ∈ eventsAt rows addr → e ∈ memEventsFiltered rows :=
    mem_memEventsFiltered_of_mem_eventsAt
  have haddr : ∀ {e}, e ∈ eventsAt rows addr → e.addr.val = addr := addr_of_mem_eventsAt
  refine isConsistentSingleAddress_of_chain (eventsAt rows addr) h_sorted ?_ ?_
  · -- adjacency: each read equals the next (earlier) write
    rw [List.isChain_iff_getElem]
    intro i hi
    have he_mem := hsub (List.getElem_mem (show i < (eventsAt rows addr).length by omega))
    have he'_mem := hsub (List.getElem_mem (show i + 1 < (eventsAt rows addr).length from hi))
    have hprevts := h_prev addr i hi
    rcases memEvent_canceller rows memProv hwf h_bal _ he_mem with
      ⟨e'', he''_mem, he''_key⟩ | ⟨b, hb, hbkey, _⟩
    · obtain ⟨hclk, _, hval⟩ := recvKey_eq_sendKey he''_key
      have heq : e'' = (eventsAt rows addr)[i + 1]'hi :=
        memEventsFiltered_clk_inj rows h_clk he''_mem he'_mem (by rw [hclk, hprevts])
      rw [← heq]; exact hval.symm
    · obtain ⟨_, hnotts⟩ := h_prov b hb _ he_mem hbkey
      exact absurd hprevts (hnotts _ he'_mem)
  · -- genesis: the chronologically-first read returns 0
    intro hne
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

/-- `isConsistentSingleAddress` transports across a list equality (its value is proof-irrelevant in the
sortedness witness). -/
theorem isConsistentSingleAddress_congr {a b : MemoryAccessList} (hab : a = b)
    (ha : MemoryAccessList.isTimestampSorted a) (hb : MemoryAccessList.isTimestampSorted b) :
    MemoryAccessList.isConsistentSingleAddress a ha → MemoryAccessList.isConsistentSingleAddress b hb := by
  subst hab; exact id

/-- **`isConsistentOnline` from the Memory bus balance (M4, assembled).** The offline-memory link — every
read returns the most-recent write at its address — derived from balance + the ordering/provider
side conditions, over the bus-backed (filtered) access list. The single-shard Memory theorem; the closed-bus
analogue of `pcChain_of_balance_and_clkInj`. -/
theorem isConsistentOnline_of_memBalance [NeZero p] (rows : List (Trace.RowView (ZMod p)))
    (memProv : LookupAccessList)
    (hwf : ∀ r ∈ rows, MemRowWellFormed r)
    (h_clk : TraceMemClkValid rows)
    (h_prev : memPrevLink rows)
    (h_prevlt : ∀ e ∈ memEventsFiltered rows, e.prevTs < e.clk.val)
    (h_prov : MemProviderGenesis memProv rows)
    (h_bal : isConsistentBalanced (aggregateChipRows rows memoryLookups ++ memProv)) :
    MemoryAccessList.isConsistentOnline (memAccessListFiltered rows)
      (memAccessListFiltered_isTimestampSorted rows h_clk) := by
  rw [MemoryAccessList.isConsistent_iff_all_single_address]
  intro addr
  have hs : MemoryAccessList.isTimestampSorted ((eventsAt rows addr).map MemEvent.toAccess) := by
    rw [← filterAddress_memAccessListFiltered]
    exact MemoryAccessList.filterAddress_sorted _ (memAccessListFiltered_isTimestampSorted rows h_clk) addr
  exact isConsistentSingleAddress_congr (filterAddress_memAccessListFiltered rows addr).symm hs _
    (isConsistentSingleAddress_of_balance rows memProv addr hwf h_clk h_prev h_prevlt h_prov h_bal hs)

/-- **Trace-shape Memory invariant.** The bus-backed (filtered) memory accesses are offline-online-consistent:
every read returns the most-recent write at its address. Bundles `TraceMemClkValid` so the dependent
`isTimestampSorted` proof is self-contained. -/
structure TraceMemoryValid (rows : List (Trace.RowView (ZMod p))) : Prop where
  clk : TraceMemClkValid rows
  online : MemoryAccessList.isConsistentOnline (memAccessListFiltered rows)
    (memAccessListFiltered_isTimestampSorted rows clk)

/-- The threaded Memory link — the vendored offline-online consistency of the bus-backed access list (equal
to `TraceMemoryValid`). Derived from balance by `isConsistentOnline_of_memBalance`; threaded where the
Memory bus balance is not yet supplied. -/
def TraceMemoryLink (rows : List (Trace.RowView (ZMod p))) : Prop := TraceMemoryValid rows

/-- Discharge of `TraceMemoryValid` from the threaded memory link (the identity re-bundling). -/
theorem traceMemoryValid_of_memoryLink (rows : List (Trace.RowView (ZMod p)))
    (h_link : TraceMemoryLink rows) : TraceMemoryValid rows := h_link

/- `isConsistentOnline_of_memBalance` derives the offline-memory link — every read returns the
most-recent write at its address — from the Memory-bus balance plus ordering/provider side conditions. Chain:
`memEvent_canceller` → `isConsistentSingleAddress_of_balance` (per-address via `memPrevLink` +
`memEventsFiltered_clk_inj` + `getLast_clk_le` + `MemProviderGenesis`) → assembled via
`isConsistent_iff_all_single_address`. The residuals (named hypotheses, never sorry): `TraceMemClkValid`,
`memPrevLink`, `h_prevlt` (`prev_ts < ts` range check), `MemRowWellFormed` (binary gates),
`MemProviderGenesis` (init chip = genesis value 0 below all), and `isConsistentBalanced`. -/

end SP1Clean.Soundness
