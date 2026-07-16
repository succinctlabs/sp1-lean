import SP1Clean.Proofs.Chips.ProgramProviderChip
import Clean.Air.Vm

/-! # Finishing the structural Program channel

The provider proves `ProgramMsg.RowSpec` for every pushed row.  Since that is exactly the plain
channel guarantee, Clean can finish the channel and deliver the structural decode bounds to every
consumer.  Program-specific ROM membership is intentionally stronger and is proved separately from
provider balance plus the program commitment. -/

namespace SP1Clean.ProgramProviderChip

open Circuit
open SP1Clean.Channels (programChannel)
open Air.Flat

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

/-- Add the structural Program provider and finish its channel. -/
def programProviderEnsemble (PublicIO : TypeMap) [ProvableType PublicIO] :
    SoundEnsemble (ZMod p) PublicIO :=
  SoundEnsemble.empty (ZMod p) PublicIO
    |>.addTable ⟨circuit⟩
        (by simp [circuit_norm, circuit]) (by simp [circuit_norm, circuit])
    |>.addFinishedChannel programChannel.toRaw

@[simp] theorem programProviderEnsemble_finished (PublicIO : TypeMap) [ProvableType PublicIO] :
    (programChannel (p := p)).toRaw ∈ (programProviderEnsemble (p := p) PublicIO).finished := by
  simp [programProviderEnsemble, circuit_norm]

end SP1Clean.ProgramProviderChip
