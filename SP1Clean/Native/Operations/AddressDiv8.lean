import SP1Clean.FormalModel.Contracts.AddressDiv8
import Clean.Gadgets.Bits

/-! # A native quotient/remainder circuit for eight-byte words

Each limb splits into a thirteen-bit partial quotient and a three-bit remainder. Reassembling
the neighboring pieces gives the full quotient; no lookup channel or division witness oracle
is needed. The constructor supplies the partial quotients and Clean computes every range bit.
-/

namespace SP1Clean.AddressDiv8

open Circuit

variable {p : ℕ} [Fact p.Prime] [Fact (2 ^ 17 < p)]

local instance : Fact (p > 2) := ⟨by have := Fact.out (p := 2 ^ 17 < p); omega⟩

def Inputs.rest {F : Type} [Sub F] [Mul F] [OfNat F 8] (input : Inputs F) (index : Fin 3) : F :=
  input.value[index.val] - input.quotients[index.val] * 8

def Inputs.output {F : Type} [Sub F] [Mul F] [Add F] [Zero F] [OfNat F 8] [OfNat F 8192]
    (input : Inputs F) : Output F :=
  ⟨#v[input.quotients[0] + input.rest 1 * 8192, input.quotients[1] + input.rest 2 * 8192, input.quotients[2]],
    input.rest 0, #v[input.quotients[0] * 8, input.value[1], input.value[2], 0]⟩

def main (input : Var Inputs (ZMod p)) : Circuit (ZMod p) (Var Output (ZMod p)) := do
  assertion (Gadgets.ToBits.rangeCheck 13 (by have := Fact.out (p := 2 ^ 17 < p); omega)) input.quotients[0]
  assertion (Gadgets.ToBits.rangeCheck 3 (by have := Fact.out (p := 2 ^ 17 < p); omega)) (input.rest 0)
  assertion (Gadgets.ToBits.rangeCheck 13 (by have := Fact.out (p := 2 ^ 17 < p); omega)) input.quotients[1]
  assertion (Gadgets.ToBits.rangeCheck 3 (by have := Fact.out (p := 2 ^ 17 < p); omega)) (input.rest 1)
  assertion (Gadgets.ToBits.rangeCheck 13 (by have := Fact.out (p := 2 ^ 17 < p); omega)) input.quotients[2]
  assertion (Gadgets.ToBits.rangeCheck 3 (by have := Fact.out (p := 2 ^ 17 < p); omega)) (input.rest 2)
  assertZero input.value[3]
  return input.output

instance elaborated : ElaboratedCircuit (ZMod p) Inputs Output main := by elaborate_circuit

end SP1Clean.AddressDiv8
