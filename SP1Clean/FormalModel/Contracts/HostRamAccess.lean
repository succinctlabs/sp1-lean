import SP1Clean.FormalModel.Contracts.MemoryBoundary
import SP1Clean.Circuits.Types.MemoryAccess

/-! # One authenticated host RAM word access

The access belongs to the event clock carried by its coordination message and updates one
aligned guest RAM cell at that clock plus one. Read-only host consumers request equal old and
new words. Which cells a call needs and which writes it permits are separate host-table facts.
-/

namespace SP1Clean.HostRamAccessChip

open Circuit Channels

structure Inputs (F : Type) where
  access : Circuits.Types.MemoryAccessCols F
  clk_high : F
  clk_0_16 : F
  clk_16_24 : F
  addr0 : F
  addr1 : F
  addr2 : F
  new_value : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

/-- The call-facing record excludes the internal predecessor timestamp witness. -/
structure Message (F : Type) where
  clk_high : F
  clk_low : F
  addr0 : F
  addr1 : F
  addr2 : F
  previous : Word F
  current : Word F
deriving ProvableStruct
provable_struct_eval_lemmas Message

def channel {p : ℕ} [Fact p.Prime] : Channel (ZMod p) Message where
  name := "sp1.native.host_ram_access"
  Guarantees _ _ := True

def Inputs.clockLow {R : Type} [Add R] [Mul R] [OfNat R 65536] [One R] (input : Inputs R) : R :=
  input.clk_0_16 + input.clk_16_24 * 65536

def Inputs.prior {R : Type} (input : Inputs R) : MemoryMsg R :=
  ⟨input.access.access_timestamp.prev_high, input.access.access_timestamp.prev_low,
    input.addr0, input.addr1, input.addr2, input.access.prev_value⟩

def Inputs.pushed {R : Type} [Add R] [Mul R] [OfNat R 65536] [One R] (input : Inputs R) : MemoryMsg R :=
  ⟨input.clk_high, input.clockLow + 1, input.addr0, input.addr1, input.addr2, input.new_value⟩

def Inputs.message {R : Type} [Add R] [Mul R] [OfNat R 65536] [One R] (input : Inputs R) : Message R :=
  ⟨input.clk_high, input.clockLow, input.addr0, input.addr1, input.addr2,
    input.access.prev_value, input.new_value⟩

/-- An aligned eight-byte cell wholly inside the native guest RAM window. -/
def RamKey {p : ℕ} [Fact p.Prime] (record : MemoryMsg (ZMod p)) : Prop :=
  2 ^ 16 ≤ Word.toNat (MemoryBoundary.address record) ∧
    Word.toNat (MemoryBoundary.address record) < 2 ^ 48 ∧
    Word.toNat (MemoryBoundary.address record) % 8 = 0

/-- An authentic word transfer at a canonical location with strictly increasing bounded time.
The ensemble proves the global meaning of the prior word from Memory balance. -/
def Spec {p : ℕ} [Fact p.Prime] (input : Inputs (ZMod p)) : Prop :=
  MemoryBoundary.CanonicalSpec input.pushed ∧ RamKey input.pushed ∧
    MemoryMsg.isU64 input.prior ∧ MemoryMsg.isU64 input.pushed ∧
    input.prior.clk_high.val < 2 ^ 24 ∧ MemoryMsg.ClkBound input.prior ∧
    input.pushed.clk_high.val < 2 ^ 24 ∧ MemoryMsg.ClkBound input.pushed ∧
    Semantics.MemoryMsg.timeNat input.prior < Semantics.MemoryMsg.timeNat input.pushed ∧
    Semantics.MemoryMsg.timeNat input.pushed = Semantics.clkNat input.clk_high input.clockLow + 1

end SP1Clean.HostRamAccessChip
