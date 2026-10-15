import SP1Clean.Model.Register

/-! # Exact executable comparison of the complete Sail register file

The generated model supplies Boolean equality for its register-value types but does not prove
that equality lawful. These instances close that gap for the types used by `RegisterType`.
The resulting finite-map comparison includes platform registers, nextPC, retirement bookkeeping,
and absent keys; it does not identify states merely because their integer registers agree.
-/

namespace SP1Clean.Model.Core

open LeanRV64D.Defs

deriving instance ReflBEq, LawfulBEq for WaitReason, HartState, Privilege, misaligned_exception,
  MemoryRegionType, AtomicSupport, Reservability, PMAMisalignedExceptions, PMA, PMA_Region,
  physaddr, TLB_Entry

namespace SailRegisterFile

abbrev Map := Std.ExtDHashMap Register RegisterType

private instance valueBEq (reg : Register) : BEq (RegisterType reg) := by
  cases reg <;> infer_instance

private instance valueLawfulBEq (reg : Register) : LawfulBEq (RegisterType reg) := by
  cases reg <;> infer_instance

/-- Compare every stored register using Std's extensional finite-map comparison. -/
def equivalent (left right : Map) : Bool := left == right

theorem equivalent_iff (left right : Map) : equivalent left right = true ↔ left = right := by
  exact beq_iff_eq

end SailRegisterFile

end SP1Clean.Model.Core
