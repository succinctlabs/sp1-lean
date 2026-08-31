import SP1Clean.Proofs.Chips.HaltChip.Formal
import ToClean.Gadgets.ComputableWitnesses
import ToClean.Air.TableBuild

/-! # Halt table: component, padding row, and honest witness generation

The build-side substrate shared by the deterministic completeness compiler
(`Proofs/Completeness/Providers.lean`) and the exact-artifact transport
(`Composition/SystemTables.lean`): the flat-AIR component, the all-zero padding row with its `Spec`
proof, and the vacuous `ComputableWitnesses` (the halt table declares no cells — its composed
readers are zero-witness input-takers).

Every shard's halt table carries **exactly one** row: the padding row on ordinary shards (its
`1 - is_real` Exit push of `⟨0⟩` is what balances the state-boundary verifier's ungated
`⟨exit_code⟩` pull and forces `exit_code = 0`), or the one real ECALL witness row on halting
shards. -/

namespace SP1Clean.HaltChip

open Circuit
open Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- The Halt table as a flat-AIR component. -/
def component : Component (ZMod p) := ⟨circuit⟩

/-- The all-zero Halt row: the selector off, so every gated conjunct is vacuous. -/
def paddingInputs : Inputs (ZMod p) where
  state := { clk_high := 0, clk_16_24 := 0, clk_0_16 := 0, pc := #v[0, 0, 0] }
  x5_memory :=
    { prev_value := #v[0, 0, 0, 0], access_timestamp := { prev_low := 0, diff_low_limb := 0 } }
  x10_memory :=
    { prev_value := #v[0, 0, 0, 0], access_timestamp := { prev_low := 0, diff_low_limb := 0 } }
  x11_memory :=
    { prev_value := #v[0, 0, 0, 0], access_timestamp := { prev_low := 0, diff_low_limb := 0 } }
  is_real := 0

omit [Fact (2 ^ 17 < p)] in
theorem spec_paddingInputs : Spec (paddingInputs (p := p)) := by
  have h0 : (paddingInputs (p := p)).is_real ≠ 1 := by simp [paddingInputs]
  exact ⟨Or.inl rfl, fun h => absurd h h0, fun h => absurd h h0, fun h => absurd h h0,
    fun h => absurd h h0, fun h => absurd h h0, fun h => absurd h h0⟩

/-- Halt has computable witnesses vacuously: the table declares no cells (its composed readers are
zero-witness input-takers). -/
theorem computableWitnesses : (circuit (p := p)).base.ComputableWitnesses := fun k input env env' =>
  Operations.forAllFlat_witnessCongr_of_localLength_zero _ _
    (by simp [circuit, main, Readers.CPUState.circuit, Readers.RegisterAccessCols.circuit,
      circuit_norm])

/-- The halt table's row list from its (for now uninhabited) occurrence list: exactly one padding
row. The deterministic compiler emits no real halt rows yet — `Occurrence .halt := Empty` makes
that type-level; the 2.4b tranche replaces `Empty` with the semantic halt event and this map with
the real row builder. -/
def haltTraceInputs (events : List Empty) : List (Inputs (ZMod p)) :=
  match events with
  | [] => [paddingInputs]
  | e :: _ => e.elim

omit [Fact (2 ^ 17 < p)] in
theorem haltTraceInputs_spec (events : List Empty) :
    ∀ r ∈ haltTraceInputs (p := p) events, Spec r := by
  cases events with
  | nil =>
      intro r hr
      rw [haltTraceInputs, List.mem_singleton] at hr
      exact hr ▸ spec_paddingInputs
  | cons e _ => exact e.elim

theorem traceTable_constraints (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ r ∈ rows, Spec r) :
    (Table.build (component (p := p)) rows data hint).Constraints :=
  Table.build_constraints _ _ _ _ computableWitnesses fun r hr => h r hr

theorem traceTable_guarantees (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (h : ∀ r ∈ rows, Spec r) :
    (Table.build (component (p := p)) rows data hint).Guarantees :=
  Table.build_guarantees _ _ _ _ computableWitnesses fun r hr => h r hr

theorem traceTable_interactionsWith (rows : List (Inputs (ZMod p))) (data : ProverData (ZMod p))
    (hint : ProverHint (ZMod p)) (channel : RawChannel (ZMod p)) :
    (Table.build (component (p := p)) rows data hint).interactionsWith channel =
      rows.flatMap fun input =>
        (component (p := p)).operations.interactionValuesWith channel
          (Environment.fromArray ((component (p := p)).buildRow input data hint) data) :=
  Table.build_interactions _ _ _ _ channel

end SP1Clean.HaltChip
