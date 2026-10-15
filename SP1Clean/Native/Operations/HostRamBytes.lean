import SP1Clean.FormalModel.Contracts.HostRamBytes
import SP1Clean.Circuits.Gadgets.U16toU8Safe

/-! # A byte-decoding consumer of host RAM reads

Compose the existing safe limb-to-byte decoder and consume exactly the supplied read message.
Its low-byte columns are computed by the constructor; the high bytes are circuit expressions.
There are no extra physical Memory accesses or witness-program cells.
-/

namespace SP1Clean.HostRamBytes

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def bytes {R : Type} [Sub R] [Mul R] (inverse : R) (input : Inputs R) : Vector R 8 :=
  #v[input.low[0], (input.read.value[0] - input.low[0]) * inverse,
    input.low[1], (input.read.value[1] - input.low[1]) * inverse,
    input.low[2], (input.read.value[2] - input.low[2]) * inverse,
    input.low[3], (input.read.value[3] - input.low[3]) * inverse]

def populate (read : HostRamReadChip.Message (ZMod p)) : Inputs (ZMod p) :=
  ⟨read, (U16toU8OperationSafe.populate read.value).low_bytes⟩

def ProverAssumptions (input : Inputs (ZMod p)) : Prop :=
  input.read.Valid ∧ input.low = (U16toU8OperationSafe.populate input.read.value).low_bytes

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var (fields 8) (ZMod p)) := do
  assertion U16toU8OperationSafe.circuit ⟨input.read.value, ⟨input.low⟩, 1⟩
  HostRamReadChip.channel.pull input.read
  return bytes (Expression.const (256 : ZMod p)⁻¹) input

instance elaborated : ElaboratedCircuit (ZMod p) Inputs (fields 8) main := by
  elaborate_circuit

end SP1Clean.HostRamBytes
