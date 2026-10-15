module

public import ToClean.Air.EnsembleBuild

/-! # Reindexing an ensemble's channel registry

Clean channel registries are conjunctions, so repeated registrations are redundant. This
upstream-facing helper changes only that registry: physical tables, the public verifier, data,
public inputs, and every interaction occurrence remain unchanged. Full `RawChannel` membership,
including the channel predicate, is the required equivalence; matching names alone is insufficient.
-/

@[expose] public section

namespace Air.Flat

variable {F : Type} [FiniteField F] {PublicIO : TypeMap} [ProvableType PublicIO]

/-- Replace the channel registry while retaining the complete physical ensemble. -/
def Ensemble.withChannels (ens : Ensemble F PublicIO) (channels : List (RawChannel F)) :
    Ensemble F PublicIO := { ens with channels }

/-- Reuse the identical witness after replacing only the channel registry. -/
def EnsembleWitness.withChannels {ens : Ensemble F PublicIO} (witness : EnsembleWitness ens)
    (channels : List (RawChannel F)) : EnsembleWitness (ens.withChannels channels) :=
  EnsembleWitness.ofTables _ witness.tables witness.publicInput witness.tables_map_component

/-- Changing a registry preserves all raw assertions and fixed-table lookups. -/
theorem EnsembleWitness.withChannels_constraints {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) (channels : List (RawChannel F)) :
    (witness.withChannels channels).Constraints ↔ witness.Constraints := Iff.rfl

/-- Full raw-channel membership equivalence transports every balance and capacity condition. -/
theorem EnsembleWitness.withChannels_balanced {ens : Ensemble F PublicIO}
    (witness : EnsembleWitness ens) (channels : List (RawChannel F))
    (same : ∀ channel, channel ∈ channels ↔ channel ∈ ens.channels) :
    (witness.withChannels channels).BalancedChannels ↔ witness.BalancedChannels := by
  change (∀ channel ∈ channels, witness.BalancedChannel channel) ↔
    ∀ channel ∈ ens.channels, witness.BalancedChannel channel
  simp only [same]

end Air.Flat
