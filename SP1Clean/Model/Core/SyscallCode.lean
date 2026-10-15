import Mathlib.Data.BitVec

/-! # The native core's guest-runtime syscall profile

These eight full-register codes are the selected native profile. Their numeric values follow
SP1 v6.4.0 (`f66b4bff51d0ccff51d152e0f7f66b2ffedf3529`),
`crates/core/executor/src/syscall_code.rs`. This is a deliberate restriction: SP1's executor
casts x5 to u32, whereas this profile requires the complete 64-bit register to be canonical.
Membership says which call is allowed, not that its host effects have been verified.
-/

namespace SP1Clean.Model.Core

/-- Calls admitted by the native guest-runtime profile. -/
inductive SyscallKind
  | halt | write | enterUnconstrained | commit | commitDeferred | verifyProof | hintLength | hintRead
deriving DecidableEq, Repr, Inhabited

namespace SyscallKind

/-- Exact full-register code, with all unused bytes zero. -/
def code : SyscallKind → BitVec 64
  | .halt => 0
  | .write => 2
  | .enterUnconstrained => 3
  | .commit => 16
  | .commitDeferred => 26
  | .verifyProof => 27
  | .hintLength => 240
  | .hintRead => 241

/-- The finite inventory used by decoding and the native fixed lookup. -/
def all : List SyscallKind :=
  [.halt, .write, .enterUnconstrained, .commit, .commitDeferred, .verifyProof, .hintLength, .hintRead]

theorem mem_all (kind : SyscallKind) : kind ∈ all := by cases kind <;> simp [all]

theorem code_injective : Function.Injective code := by
  intro left right equal
  cases left <;> cases right <;> simp_all [code]

/-- The executable full-word parser; high-bit aliases and unselected calls are rejected. -/
def decode? (word : BitVec 64) : Option SyscallKind := all.find? (fun kind => kind.code == word)

/-- Semantic membership, independent of a field representation or circuit witness. -/
def Supported (word : BitVec 64) : Prop := ∃ kind : SyscallKind, kind.code = word

instance (word : BitVec 64) : Decidable (Supported word) :=
  decidable_of_iff (word ∈ all.map code) (by simp [Supported, mem_all])

theorem decode?_eq_some_iff (word : BitVec 64) (kind : SyscallKind) :
    decode? word = some kind ↔ kind.code = word := by
  constructor
  · intro found
    simpa only [beq_iff_eq] using List.find?_some found
  · intro equal
    rw [← equal]
    cases kind <;> decide

theorem decode?_isSome_iff (word : BitVec 64) : (decode? word).isSome = true ↔ Supported word := by
  rw [Option.isSome_iff_exists]
  exact exists_congr (fun kind => decode?_eq_some_iff word kind)

end SyscallKind
end SP1Clean.Model.Core
