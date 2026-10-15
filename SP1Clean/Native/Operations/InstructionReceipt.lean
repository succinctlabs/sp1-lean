import SP1Clean.Model.Channels
import ToClean.Circuit.Receipt

/-! # Ordinary instruction observations for outgoing Sail bookkeeping

An instruction retains its original row, constraints, lookups and semantic contract. Its
activity gate and successor State payload are also published on a dedicated receipt channel.
The registry proves these are the actual State emissions read by the existing decoder.
Ordered receipt consumption, count and endpoint binding remain separate ensemble obligations.
-/

namespace SP1Clean.InstructionReceipt

open Circuit Channels

variable {p : ℕ} [Fact p.Prime]

/-- Original successor State payloads, one gated occurrence per physical ordinary row. -/
def channel : Channel (ZMod p) StateMsg where
  name := "SP1OrdinaryStateReceipt"
  Guarantees _ _ := True

/-- Publish an authenticated registry projection while composing the complete original chip. -/
def circuit {Input Output : TypeMap} [ProvableType Input] [ProvableType Output]
    (provider : GeneralFormalCircuit (ZMod p) Input Output)
    (projection : Receipt.Projection (ZMod p) Input StateMsg) :
    GeneralFormalCircuit (ZMod p) Input Output :=
  Receipt.circuit provider channel (fun _ _ => trivial) projection

end SP1Clean.InstructionReceipt
