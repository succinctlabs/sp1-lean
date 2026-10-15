import SP1Clean.FormalModel.Contracts.HintReadStep
import SP1Clean.FormalModel.Contracts.HostRamAccess

/-! # A call-bound hint word transfer

The private cursor retains the event clock, immutable node identity, next word index, and RAM
address. Each row writes exactly its authenticated word and advances that cursor. The final
row leaves the last address in the cursor; the count still advances past the final index.
-/

namespace SP1Clean.HintReadWordChip

open Circuit

structure State (F : Type) where
  clk_high : F
  clk_low : F
  pointer : fields 3 F
  index : fields 3 F
  address : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas State

structure Inputs (F : Type) where
  ram : HostRamAccessChip.Inputs F
  pointer : fields 3 F
  index : fields 3 F
  nextIndex : fields 3 F
  nextAddress : fields 3 F
deriving ProvableStruct
provable_struct_eval_lemmas Inputs

def stateChannel {p : ℕ} : Channel (ZMod p) State where
  name := "sp1.native.hint_read_state"
  Guarantees _ _ := True

def Inputs.address {F : Type} (input : Inputs F) : fields 3 F :=
  #v[input.ram.addr0, input.ram.addr1, input.ram.addr2]

def Inputs.step {F : Type} [Zero F] [One F] (last : Bool) (input : Inputs F) : HintReadStep.Inputs F :=
  ⟨⟨input.pointer, input.index, input.ram.new_value, if last then 1 else 0⟩,
    input.address, input.nextIndex, input.nextAddress⟩

def Inputs.previous {F : Type} [Add F] [Mul F] [OfNat F 65536] [One F] (input : Inputs F) : State F :=
  ⟨input.ram.clk_high, input.ram.clockLow, input.pointer, input.index, input.address⟩

def Inputs.next {F : Type} [Add F] [Mul F] [OfNat F 65536] [One F] (input : Inputs F) : State F :=
  ⟨input.ram.clk_high, input.ram.clockLow, input.pointer, input.nextIndex, input.nextAddress⟩

def Spec {p : ℕ} [Fact p.Prime] (last : Bool) (input : Inputs (ZMod p)) : Prop :=
  HostRamAccessChip.Spec input.ram ∧ HintReadStep.Spec last (input.step last)

end SP1Clean.HintReadWordChip
