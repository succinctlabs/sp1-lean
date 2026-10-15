import SP1Clean.FormalModel.Contracts.HostBuffer32
import SP1Clean.Proofs.Operations.HostRamBytes
import SP1Clean.Proofs.Operations.AddOperation.Formal
import SP1Clean.Model.Semantics.Decode

/-! # A complete buffer assembled from bounded shared reads

Each offset variant consumes exactly four or five words. Bundled addition gadgets bind their
addresses and the query, equality gadgets bind their clocks, and the byte decoder supplies all
32 output bytes. Every internal operation is a proved Clean subcircuit.
-/

namespace SP1Clean.HostBuffer32

open Circuit SP1Clean.Soundness.Target

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

def start (offset : Fin 8) : Fin (cellCount offset) := ⟨0, cellCount_pos offset⟩

private instance (offset : Fin 8) : Inhabited (Fin (cellCount offset)) := ⟨start offset⟩

def wordOffset (amount : ℕ) : Word (ZMod p) := bitVecToWord (BitVec.ofNat 64 amount)

def payload {R : Type} [Sub R] [Mul R] (offset : Fin 8) (inverse : R)
    (cells : Vector (HostRamBytes.Inputs R) (cellCount offset)) : Vector R 32 :=
  Vector.ofFn fun index =>
    let word := HostRamBytes.bytes inverse cells[(byteCell offset index).val]
    word[(offset.val + index.val) % 8]

def ProverAssumptions (offset : Fin 8) (input : Inputs offset (ZMod p)) : Prop :=
  (∀ index : Fin (cellCount offset),
    HostRamBytes.ProverAssumptions input.cells[index.val] ∧
    input.cells[index.val].read.clk_high = input.message.clk_high ∧
    input.cells[index.val].read.clk_low = input.message.clk_low ∧
    Word.toBitVec64 input.cells[index.val].read.address =
      Word.toBitVec64 input.cells[(start offset).val].read.address + BitVec.ofNat 64 (8 * index.val)) ∧
  Word.isU64 input.message.address ∧
  Word.toBitVec64 input.message.address =
    Word.toBitVec64 input.cells[(start offset).val].read.address + BitVec.ofNat 64 offset.val ∧
  input.message.bytes = payload offset (256 : ZMod p)⁻¹ input.cells

def main (offset : Fin 8) (input : Var (Inputs offset) (ZMod p)) : Circuit (ZMod p) Unit := do
  Circuit.forEach (Vector.finRange (cellCount offset)) fun index => do
    let _ ← HostRamBytes.circuit input.cells[index.val]
    assertion AddOperation.circuit
      ⟨input.cells[(start offset).val].read.address, const (wordOffset (8 * index.val)),
        ⟨input.cells[index.val].read.address⟩, 1⟩
    assertion (Gadgets.Equality.circuit fieldPair)
      ⟨(input.cells[index.val].read.clk_high, input.cells[index.val].read.clk_low),
        (input.message.clk_high, input.message.clk_low)⟩
  assertion AddOperation.circuit
    ⟨input.cells[(start offset).val].read.address, const (wordOffset offset.val), ⟨input.message.address⟩, 1⟩
  assertion (Gadgets.Equality.circuit (fields 32))
    ⟨input.message.bytes, payload offset (Expression.const (256 : ZMod p)⁻¹) input.cells⟩
  channel.push input.message

instance elaborated (offset : Fin 8) :
    ElaboratedCircuit (ZMod p) (Inputs offset) unit (main offset) := by
  elaborate_circuit

end SP1Clean.HostBuffer32
