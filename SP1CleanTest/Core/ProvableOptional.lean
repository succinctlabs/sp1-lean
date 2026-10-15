module

public import ToClean.Circuit.ProvableOptional
import Clean.Utils.Tactics.ProvableStructDeriving

/-! Kernel-checked layout regressions for mode-specific fields, including following-field offsets.
This checks the representation needed by SP1's mode-associated columns, not mprotect semantics. -/

@[expose] public section

namespace SP1CleanTest.ProvableOptional

structure Reader (enabled : Bool) (F : Type) where
  word : Vector F 4
  mode : ProvableOptional enabled field F
  next : F
deriving ProvableStruct

example : size (Reader false) = 5 := rfl
example : size (Reader true) = 6 := rfl

example : toElements (Reader.mk (F := Nat) (enabled := true) #v[1, 2, 3, 4] 5 6) =
    #v[1, 2, 3, 4, 5, 6] := by
  change ProvableStruct.structToElements _ = _
  rw [ProvableStruct.structToElements_eq]
  rfl

example : toElements (Reader.mk (F := Nat) (enabled := false) #v[1, 2, 3, 4] () 6) =
    #v[1, 2, 3, 4, 6] := by
  change ProvableStruct.structToElements _ = _
  rw [ProvableStruct.structToElements_eq]
  rfl

-- The generic instance retains Clean's exact vector isomorphism in either mode.
example {present : Bool} {M : TypeMap} [ProvableType M] {F : Type}
    (value : ProvableOptional present M F) : fromElements (toElements value) = value :=
  ProvableType.fromElements_toElements value

end SP1CleanTest.ProvableOptional
