import SP1Clean.FormalModel.Contracts.HostRamAccess
import SP1Clean.Proofs.Chips.FinalRamProvider
import SP1Clean.Native.Readers.MemoryAccess

/-! # A native host RAM access circuit

Compose the existing address and Memory readers. Local bit checks establish both high-clock
bounds and the CPU low-clock discipline; the new word is range checked before its Memory push.
Each row also publishes the exact call-facing old/new word record. There is no padding gate:
the later call tables must account for every row through the coordination channel.
-/

namespace SP1Clean.HostRamAccessChip

open Circuit Channels

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 25 < p)]

local instance : Fact (2 ^ 17 < p) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩
local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 25 < p); omega⟩

def Inputs.reader {R : Type} [Add R] [Mul R] [OfNat R 65536] [One R] (input : Inputs R) : Readers.MemoryAccess.Inputs R :=
  ⟨input.access, input.clk_high, input.clockLow, input.addr0, input.addr1, input.addr2,
    input.new_value, 1⟩

def ProverAssumptions (input : Inputs (ZMod p)) : Prop :=
  FinalRamProvider.Domain input.pushed ∧ Word.isU64 input.new_value ∧
    ((input.clk_0_16 - 1) * (8 : ZMod p)⁻¹).val < 2 ^ 13 ∧
    input.clk_16_24.val < 2 ^ 8 ∧ input.clk_high.val < 2 ^ 24 ∧
    input.access.access_timestamp.prev_high.val < 2 ^ 24 ∧
    Readers.MemoryAccess.Spec input.reader

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) Unit := do
  assertion WordRangeCheck.circuit (MemoryBoundary.address input.pushed)
  let _ ← AddressOperation.circuit (FinalRamProvider.addressInput input.pushed)
  assertion WordRangeCheck.circuit input.new_value
  assertion (Gadgets.ToBits.rangeCheck 13 (by have := Fact.out (p := 2 ^ 25 < p); omega))
    ((input.clk_0_16 - 1) * Expression.const (8 : ZMod p)⁻¹)
  assertion (Gadgets.ToBits.rangeCheck 8 (by have := Fact.out (p := 2 ^ 25 < p); omega))
    input.clk_16_24
  assertion (Gadgets.ToBits.rangeCheck 24 (by have := Fact.out (p := 2 ^ 25 < p); omega))
    input.clk_high
  assertion (Gadgets.ToBits.rangeCheck 24 (by have := Fact.out (p := 2 ^ 25 < p); omega))
    input.access.access_timestamp.prev_high
  let _ ← Readers.MemoryAccess.circuit input.reader
  channel.push input.message

@[local circuit_norm] private theorem word_guarantees :
    (WordRangeCheck.circuit (p := p)).channelsWithGuarantees = [] := rfl

@[local circuit_norm] private theorem address_guarantees :
    (AddressOperation.circuit (p := p)).channelsWithGuarantees = [byteChannel.toRaw] := rfl

omit [Fact (2 ^ 25 < p)] in
set_option linter.unusedSectionVars false in
@[local circuit_norm] private theorem range_guarantees (n : ℕ) (bound : 2 ^ n < p) :
    (Gadgets.ToBits.rangeCheck n bound).channelsWithGuarantees = [] := rfl

@[local circuit_norm] private theorem reader_guarantees :
    (Readers.MemoryAccess.circuit (p := p)).channelsWithGuarantees =
      [byteChannel.toRaw, memoryChannel.toRaw] := rfl

instance elaborated : ElaboratedCircuit (ZMod p) Inputs unit main where
  localLength _ := 201
  output _ _ := ()
  channelsWithGuarantees := [byteChannel.toRaw, memoryChannel.toRaw]

end SP1Clean.HostRamAccessChip
