import SP1Clean.Proofs.Completeness.Providers

/-! # The interaction ledger: from a signed row ledger to channel balance

Clean's `BalancedInteractions` is the *verifier's* per-channel obligation, and every use of it in
this repository so far reads it as a hypothesis: the soundness capstone consumes balance and derives
execution facts (`Soundness/TypedInteractions.lean`, `Model/BalanceBridge.lean`). The completeness
direction has to go the other way — an assembled trace must be shown to *satisfy* it — and nothing
in Clean or in this tree produces a `BalancedInteractions` from anything except another one.

This module is that missing direction, at the granularity the assembled AIR actually has:

* `balanceOf_eq_pushed_sub_pulled` — for an interaction list whose multiplicities are all in
  `{-1, 0, 1}` (which is exactly the shape SP1's `is_real`-gated pushes and pulls produce), the
  field-valued balance at a message is the *integer* difference of two counts: how many rows pushed
  that message and how many pulled it.
* `balancedInteractions_of_signed_perm` — hence, if the pushed message list is a permutation of the
  pulled message list, the channel balances. The count bound `length < ringChar` is the one genuine
  side condition, and it is the honest one: it says the shard's interaction count does not wrap the
  field, which for KoalaBear bounds a shard at `< p ≈ 2^31` interactions.
* `balancedInteractions_append` / `balancedInteractions_flatMap` — the compositional forms, matching
  the two shapes an assembled ensemble presents (`Tables.interactionsWith` is a `flatMap` over
  tables, and each `Table.interactionsWith` is a `flatMap` over rows).

## The per-table channel profile

The other half of a ledger argument is knowing *which* channels a table can contribute to at all.
That is a static fact about the component — it does not mention a row, a witness, or an
environment — and Clean already turns it into the strongest possible statement:
`Table.interactionsWith_nil_of_channel_not_mem` reduces a whole table's contribution to `[]` on a
channel its circuit never names. The `*_channels` lemmas below record that list for each of the
twenty-six single-bus components in the current twenty-eight-table provider/boundary tail. The two
W3 system tables are multi-bus and are handled explicitly by the assembly; for the other tables the
profile discharges three of the four channels without touching a row.

This is deliberately the *static* profile rather than a per-row evaluated one. Evaluating a built
row to read its interactions back is the documented performance catastrophe of this code base
(`docs/agents/proof-patterns.md`, "Compile-time / performance landmines"); the row-dependent half of
a profile belongs on the soundness side's decode layer, applied to rows that satisfy
`Constraints` — which `Air.Flat.Table.build_constraints` supplies for every table built by
`Proofs/Completeness/`.

## What is not here

The four whole-machine channel closures (the State telescope, the per-address memory chains, and the
byte/program per-occurrence matchings) are the *consumers* of this bridge and belong to the shard
assembly (W5). What this module fixes is the shape they have to produce: a permutation between
pushed and pulled message lists, per channel, plus a count bound. -/

namespace SP1Clean.Ledger

open Air.Flat (Component Table)

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-! ## The signed row ledger -/

/-- The messages an interaction list **pushes**: one entry per interaction of multiplicity `1`. -/
def pushedMessages (ins : List (Interaction (ZMod p))) : List (Array (ZMod p)) :=
  (ins.filter fun i => i.mult = 1).map (·.msg)

/-- The messages an interaction list **pulls**: one entry per interaction of multiplicity `-1`. -/
def pulledMessages (ins : List (Interaction (ZMod p))) : List (Array (ZMod p)) :=
  (ins.filter fun i => i.mult = -1).map (·.msg)

/-- Every multiplicity is a signed bit. This is what an SP1 row's interactions satisfy: each is
`pushIf g` or `pullIf g` at a gate `g` the row's own constraints force boolean, so the evaluated
multiplicity is `0`, `1`, or `-1`. -/
def SignedMults (ins : List (Interaction (ZMod p))) : Prop :=
  ∀ i ∈ ins, i.mult = 0 ∨ i.mult = 1 ∨ i.mult = -1

set_option linter.unusedSectionVars false in
@[simp] lemma pushedMessages_nil : pushedMessages ([] : List (Interaction (ZMod p))) = [] := rfl

set_option linter.unusedSectionVars false in
@[simp] lemma pulledMessages_nil : pulledMessages ([] : List (Interaction (ZMod p))) = [] := rfl

set_option linter.unusedSectionVars false in
@[simp] lemma pushedMessages_append (as bs : List (Interaction (ZMod p))) :
    pushedMessages (as ++ bs) = pushedMessages as ++ pushedMessages bs := by
  simp [pushedMessages, List.filter_append]

set_option linter.unusedSectionVars false in
@[simp] lemma pulledMessages_append (as bs : List (Interaction (ZMod p))) :
    pulledMessages (as ++ bs) = pulledMessages as ++ pulledMessages bs := by
  simp [pulledMessages, List.filter_append]

/-- `1 ≠ -1` in the field: the fact that separates a push from a pull, and the only place the
ledger needs the characteristic to be odd. -/
lemma one_ne_neg_one : (1 : ZMod p) ≠ -1 := by
  haveI : NeZero p := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩
  intro h
  have h2 : (2 : ZMod p) = 0 := by linear_combination h
  have := congrArg ZMod.val h2
  rw [val_2_zmod_p, ZMod.val_zero] at this
  exact absurd this (by norm_num)

/-- `0 ≠ -1` in the field. -/
lemma zero_ne_neg_one : (0 : ZMod p) ≠ -1 := by
  intro h
  exact one_ne_zero (α := ZMod p) (by linear_combination h)

set_option linter.unusedSectionVars false in
/-- The pushed-message list of a cons, split on whether the head is a push. -/
lemma pushedMessages_cons (i : Interaction (ZMod p)) (ins : List (Interaction (ZMod p))) :
    pushedMessages (i :: ins)
      = if i.mult = 1 then i.msg :: pushedMessages ins else pushedMessages ins := by
  by_cases h : i.mult = 1 <;> simp [pushedMessages, h]

set_option linter.unusedSectionVars false in
/-- The pulled-message list of a cons, split on whether the head is a pull. -/
lemma pulledMessages_cons (i : Interaction (ZMod p)) (ins : List (Interaction (ZMod p))) :
    pulledMessages (i :: ins)
      = if i.mult = -1 then i.msg :: pulledMessages ins else pulledMessages ins := by
  by_cases h : i.mult = -1 <;> simp [pulledMessages, h]

/--
**The signed ledger's closed form.** For an interaction list whose multiplicities are all signed
bits, the field balance at a message is the difference of the two counts: how many interactions
pushed that message, and how many pulled it.

This is the whole content of the completeness direction — everything below is this equation plus a
permutation.
-/
theorem balanceOf_eq_pushed_sub_pulled (ins : List (Interaction (ZMod p)))
    (hbin : SignedMults ins) (msg : Array (ZMod p)) :
    balanceOf ins msg =
      (((pushedMessages ins).count msg : ℕ) : ZMod p)
        - (((pulledMessages ins).count msg : ℕ) : ZMod p) := by
  induction ins with
  | nil => simp [balanceOf]
  | cons i ins ih =>
    have hins : SignedMults ins := fun j hj => hbin j (List.mem_cons_of_mem _ hj)
    have hp := pushedMessages_cons i ins
    have hq := pulledMessages_cons i ins
    rcases hbin i List.mem_cons_self with h | h | h
    · -- an off-gate interaction contributes to neither side
      rw [h, if_neg zero_ne_one] at hp
      rw [h, if_neg zero_ne_neg_one] at hq
      rw [balanceOf_cons, ih hins, hp, hq, h]
      simp
    · -- a push adds one to the pushed count exactly when its message is the one being weighed
      rw [h, if_pos rfl] at hp
      rw [h, if_neg one_ne_neg_one] at hq
      rw [balanceOf_cons, ih hins, hp, hq, h]
      by_cases hmsg : i.msg = msg
      · simp [hmsg]; ring
      · simp [hmsg]
    · -- a pull adds one to the pulled count
      rw [h, if_neg fun hh => one_ne_neg_one hh.symm] at hp
      rw [h, if_pos rfl] at hq
      rw [balanceOf_cons, ih hins, hp, hq, h]
      by_cases hmsg : i.msg = msg
      · simp [hmsg]; ring
      · simp [hmsg]

/--
**The ledger bridge.** A channel balances as soon as its interaction list has signed multiplicities,
its pushed message list is a permutation of its pulled message list, and the shard does not emit so
many interactions that the count wraps the field.

This is the exact converse of the soundness-side `producedMessages_perm_consumedMessages`
(`Soundness/TypedInteractions.lean`): that theorem turns balance into a permutation, this one turns
a permutation into balance, so an assembly that *builds* the trail and a capstone that *reads* it
meet on the same object.
-/
theorem balancedInteractions_of_signed_perm (ins : List (Interaction (ZMod p)))
    (hlen : ins.length < p) (hbin : SignedMults ins)
    (hperm : (pushedMessages ins).Perm (pulledMessages ins)) :
    BalancedInteractions ins := by
  refine ⟨Or.inl ?_, fun msg => ?_⟩
  · rwa [ZMod.ringChar_zmod_n]
  · rw [balanceOf_eq_pushed_sub_pulled ins hbin msg, hperm.count_eq msg, sub_self]

/-! ## Composition

The two shapes an assembled ensemble presents: `Tables.interactionsWith` concatenates the tables'
lists, and each `Table.interactionsWith` concatenates the rows'. Both reduce to `++`. -/

set_option linter.unusedSectionVars false in
/-- Signed multiplicities are inherited by both halves of a concatenation, and conversely. -/
@[simp] lemma signedMults_append (as bs : List (Interaction (ZMod p))) :
    SignedMults (as ++ bs) ↔ SignedMults as ∧ SignedMults bs := by
  constructor
  · exact fun h => ⟨fun i hi => h i (List.mem_append_left _ hi),
      fun i hi => h i (List.mem_append_right _ hi)⟩
  · rintro ⟨ha, hb⟩ i hi
    rcases List.mem_append.mp hi with hi | hi
    exacts [ha i hi, hb i hi]

set_option linter.unusedSectionVars false in
/-- Signed multiplicities of a `flatMap`, from the pieces. -/
lemma signedMults_flatMap {α : Type} (l : List α) (f : α → List (Interaction (ZMod p)))
    (h : ∀ a ∈ l, SignedMults (f a)) : SignedMults (l.flatMap f) := by
  intro i hi
  obtain ⟨a, ha, hia⟩ := List.mem_flatMap.mp hi
  exact h a ha i hia

/-- Pushed messages of a `flatMap` are the `flatMap` of the pushed messages. -/
lemma pushedMessages_flatMap {α : Type} (l : List α) (f : α → List (Interaction (ZMod p))) :
    pushedMessages (l.flatMap f) = l.flatMap fun a => pushedMessages (f a) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, pushedMessages_append, ih]

/-- Pulled messages of a `flatMap` are the `flatMap` of the pulled messages. -/
lemma pulledMessages_flatMap {α : Type} (l : List α) (f : α → List (Interaction (ZMod p))) :
    pulledMessages (l.flatMap f) = l.flatMap fun a => pulledMessages (f a) := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.flatMap_cons, pulledMessages_append, ih]

/-- The assembly-shaped form: a channel balances when the *whole machine's* pushed and pulled
message lists — assembled table by table, row by row — are a permutation of each other. -/
theorem balancedInteractions_of_flatMap_perm {α : Type} (l : List α)
    (f : α → List (Interaction (ZMod p))) (hlen : (l.flatMap f).length < p)
    (hbin : ∀ a ∈ l, SignedMults (f a))
    (hperm : (l.flatMap fun a => pushedMessages (f a)).Perm
      (l.flatMap fun a => pulledMessages (f a))) :
    BalancedInteractions (l.flatMap f) :=
  balancedInteractions_of_signed_perm _ hlen (signedMults_flatMap l f hbin)
    (by rwa [pushedMessages_flatMap, pulledMessages_flatMap])

/-! ## The per-table channel profile

Which of the four buses each provider/boundary component can contribute to at all. These are static
facts about the circuits — no row, no witness, no environment — and Clean's
`Table.interactionsWith_nil_of_channel_not_mem` turns each `∉` into a whole table's contribution
being literally `[]`.

The shape of the segment: **twenty-three byte-only providers** (the six opcode tables and all
seventeen range widths) plus the Program-ROM provider touch exactly one bus each; the two memory boundary tables
touch the Memory bus only; the two W3 system tables are the only provider-segment rows on more than
one bus (MemoryBump: Byte and Memory; StateBump: Byte and State); and the verifier row is on State
and Byte. -/

section Profile

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 24 < p)]

open SP1Clean.Channels (stateChannel byteChannel programChannel memoryChannel)

/-- Every channel a component names is `ch0` — the shape the nil corollary below consumes. Stated
as a subset rather than a list equality so it is insensitive to the order and repetition the
elaborated `channelsWithGuarantees`/`channelsWithRequirements` lists happen to have. -/
def OnlyChannel (c : Component (ZMod p)) (ch0 : RawChannel (ZMod p)) : Prop :=
  ∀ channel ∈ c.circuit.channels, channel = ch0

theorem onlyChannel_U8Range :
    OnlyChannel (ByteChip.U8Range.component (p := p)) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ByteChip.U8Range.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ByteChip.U8Range.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_MSB :
    OnlyChannel (ByteChip.MSB.component (p := p)) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ByteChip.MSB.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ByteChip.MSB.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_AndByte :
    OnlyChannel (ByteChip.AndByte.component (p := p)) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ByteChip.AndByte.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ByteChip.AndByte.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_OrByte :
    OnlyChannel (ByteChip.OrByte.component (p := p)) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ByteChip.OrByte.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ByteChip.OrByte.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_XorByte :
    OnlyChannel (ByteChip.XorByte.component (p := p)) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ByteChip.XorByte.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ByteChip.XorByte.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_Ltu :
    OnlyChannel (ByteChip.Ltu.component (p := p)) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ByteChip.Ltu.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ByteChip.Ltu.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_Range (n : ℕ) (hn : 2 ^ n < p) :
    OnlyChannel (RangeChip.component (p := p) n hn) byteChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (RangeChip.circuit n hn).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold RangeChip.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_ProgramProvider :
    OnlyChannel (ProgramProviderChip.component (p := p)) programChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (ProgramProviderChip.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold ProgramProviderChip.circuit at h'
  simpa [circuit_norm] using h'

theorem onlyChannel_MemoryProvider :
    OnlyChannel (MemoryProviderChip.component (p := p)) memoryChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (MemoryProviderChip.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold MemoryProviderChip.circuit at h'
  simpa [circuit_norm] using h'

set_option linter.unusedSectionVars false in
theorem onlyChannel_MemoryFinalize :
    OnlyChannel (MemoryFinalizeChip.component (p := p)) memoryChannel.toRaw := by
  intro channel h
  have h' : channel ∈ (MemoryFinalizeChip.circuit (p := p)).channels := h
  simp only [GeneralFormalCircuit.channels] at h'
  unfold MemoryFinalizeChip.circuit at h'
  simpa [circuit_norm] using h'

set_option linter.unusedSectionVars false in
/-- The corollary the assembly uses: a single-bus component's built table contributes literally
nothing to every other bus, so three of the four channel ledgers are discharged without touching a
row. -/
theorem builtTable_interactionsWith_eq_nil_of_ne (c : Component (ZMod p))
    (inputs : List (c.Input (ZMod p))) (data : ProverData (ZMod p)) (hint : ProverHint (ZMod p))
    {channel ch0 : RawChannel (ZMod p)} (hsub : OnlyChannel c ch0) (hne : channel ≠ ch0) :
    (Table.build c inputs data hint).interactionsWith channel = [] :=
  Table.interactionsWith_nil_of_channel_not_mem (by
    simp only [Table.build_component]
    exact fun hmem => hne (hsub channel hmem))

end Profile

end SP1Clean.Ledger
