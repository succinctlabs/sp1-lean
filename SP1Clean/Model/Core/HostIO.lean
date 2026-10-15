import SP1Clean.Model.Core.Memory
import SP1Clean.Model.Core.NativeLayout

/-! # Executable guest-visible hint and output semantics

This is the byte-level host I/O substrate for the native Core execution environment. It does not
use circuit rows or prover data. `HINT_READ` follows the pinned SP1 executor's
`crates/core/executor/src/minimal/hint.rs`: it always writes a final padded eight-byte word, even
for an empty hint or a length divisible by eight. `WRITE` to the hint descriptor prepends to the
queue, while a public-values write appends to the output stream.

External hooks receive an explicit request and reply. The reply is input to the execution model;
this module checks request identity and queue effects, not the hook's cryptographic correctness.
The AIR and Sail adapters must separately establish that these byte operations are the effects of
the executed syscall. These definitions alone do not discharge that grounding obligation.
-/

namespace SP1Clean.Model.Core

/-- Byte strings exchanged with the guest. -/
abbrev Bytes := List (BitVec 8)

/-- Mutable host I/O state. Hooks and unconstrained input producers are supplied separately. -/
structure HostIO where
  hints : List Bytes := []
  publicOutput : Bytes := []
deriving DecidableEq, Repr, Inhabited

/-- An explicit request to an external hook. The descriptor is the executor's low-u32 view. -/
structure HookRequest where
  descriptor : BitVec 32
  input : Bytes
deriving DecidableEq, Repr

/-- A supplied response, bound to its complete request. -/
structure HookReply where
  request : HookRequest
  hints : List Bytes
deriving DecidableEq, Repr

/-- Native memory policy. Code protection is byte-precise, including padding writes. -/
structure HostMemoryPolicy where
  readOnly : ℕ → Bool
  /-- The complete permitted guest address window. -/
  range : AddressRange := NativeLayout.guestMemory

/-- Compatibility projections; the range owns both endpoints. -/
abbrev HostMemoryPolicy.lower (policy : HostMemoryPolicy) : ℕ := policy.range.lower
abbrev HostMemoryPolicy.upper (policy : HostMemoryPolicy) : ℕ := policy.range.upper

/-- A finite check: no wrapping address arithmetic and no overlap with instruction bytes. -/
def HostMemoryPolicy.permits (policy : HostMemoryPolicy) (address length : ℕ) : Bool :=
  decide (policy.range.ContainsSpan address length) &&
    (List.range length).all (fun offset => !policy.readOnly (address + offset))

theorem HostMemoryPolicy.permits_iff (policy : HostMemoryPolicy) (address length : ℕ) :
    policy.permits address length = true ↔
      policy.lower ≤ address ∧ address + length ≤ policy.upper ∧
        ByteMemory.Avoids policy.readOnly address length := by
  simp [permits, AddressRange.ContainsSpan, ByteMemory.Avoids, List.all_eq_true, and_assoc]

/-- `HINT_LEN` observes the next queue item without consuming it. -/
def HostIO.hintLength (host : HostIO) : BitVec 64 :=
  match host.hints with
  | [] => BitVec.allOnes 64
  | bytes :: _ => BitVec.ofNat 64 bytes.length

/-- The actual bytes written by the pinned executor, including its mandatory final word. -/
def hintWriteBytes (bytes : Bytes) : Bytes :=
  bytes ++ List.replicate (8 - bytes.length % 8) 0

theorem hintWriteBytes_length (bytes : Bytes) :
    (hintWriteBytes bytes).length = 8 * (bytes.length / 8 + 1) := by
  simp only [hintWriteBytes, List.length_append, List.length_replicate]
  have := Nat.mod_add_div bytes.length 8
  have := Nat.mod_lt bytes.length (by decide : 0 < 8)
  omega

/-- Consume one hint and perform all writes, or reject the request before changing either state. -/
def HostIO.readHint (host : HostIO) (memory : ByteMemory) (policy : HostMemoryPolicy)
    (address length : ℕ) : Option (HostIO × ByteMemory) :=
  match host.hints with
  | [] => none
  | bytes :: rest =>
      if bytes.length = length ∧ address % 8 = 0 ∧
          policy.permits address (hintWriteBytes bytes).length = true then
        some ({ host with hints := rest }, memory.writeBytes address (hintWriteBytes bytes))
      else none

/-- Exact success conditions, queue consumption, and memory effects of `HINT_READ`. -/
theorem HostIO.readHint_eq_some_iff (host nextHost : HostIO) (memory nextMemory : ByteMemory)
    (policy : HostMemoryPolicy) (address length : ℕ) :
    host.readHint memory policy address length = some (nextHost, nextMemory) ↔
      ∃ bytes rest, host.hints = bytes :: rest ∧ bytes.length = length ∧ address % 8 = 0 ∧
        policy.permits address (hintWriteBytes bytes).length = true ∧
        nextHost = { host with hints := rest } ∧
        nextMemory = memory.writeBytes address (hintWriteBytes bytes) := by
  constructor
  · intro success
    unfold readHint at success
    split at success
    · contradiction
    · next bytes rest hintsEq =>
        split at success
        · next conditions =>
            obtain ⟨hostEq, memoryEq⟩ := Prod.mk.inj (Option.some.inj success)
            exact ⟨bytes, rest, hintsEq, conditions.1, conditions.2.1,
              conditions.2.2, hostEq.symm, memoryEq.symm⟩
        · contradiction
  · rintro ⟨bytes, rest, hintsEq, lengthEq, aligned, permitted, rfl, rfl⟩
    simp [readHint, hintsEq, lengthEq, aligned, permitted]

/-- Successful hint reads preserve code bytes, including when a final padding word is required. -/
theorem HostIO.readHint_preserves_readOnly {host nextHost : HostIO}
    {memory nextMemory : ByteMemory} {policy : HostMemoryPolicy} {address length : ℕ}
    (success : host.readHint memory policy address length = some (nextHost, nextMemory))
    (query : ℕ) (isReadOnly : policy.readOnly query = true) :
    nextMemory.read query = memory.read query := by
  obtain ⟨bytes, rest, _, _, _, permitted, _, rfl⟩ :=
    (host.readHint_eq_some_iff nextHost memory nextMemory policy address length).mp success
  exact memory.read_writeBytes_of_readOnly policy.readOnly address (hintWriteBytes bytes)
    ((policy.permits_iff _ _).mp permitted).2.2 query isReadOnly

/-- The guest can prepend its own byte string to the hint queue (`FD_HINT = 14`). -/
def HostIO.writeHint (host : HostIO) (bytes : Bytes) : HostIO :=
  { host with hints := bytes :: host.hints }

/-- Public values are accumulated in call order (`FD_PUBLIC_VALUES = 13`). -/
def HostIO.writePublic (host : HostIO) (bytes : Bytes) : HostIO :=
  { host with publicOutput := host.publicOutput ++ bytes }

/-- Consume a supplied hook reply only when its descriptor and input bytes match the call.
Returned hints retain their order and precede the existing queue. -/
def HostIO.applyHook (host : HostIO) (request : HookRequest) (replies : List HookReply) :
    Option (HostIO × List HookReply) :=
  match replies with
  | [] => none
  | reply :: rest =>
      if reply.request = request then
        some ({ host with hints := reply.hints ++ host.hints }, rest)
      else none

/-- A hook reply cannot be reused for another descriptor or another input byte string. -/
theorem HostIO.applyHook_eq_some_iff (host nextHost : HostIO) (request : HookRequest)
    (replies rest : List HookReply) :
    host.applyHook request replies = some (nextHost, rest) ↔
      ∃ hints, replies = ⟨request, hints⟩ :: rest ∧
        nextHost = { host with hints := hints ++ host.hints } := by
  cases replies with
  | nil => simp [applyHook]
  | cons reply tail =>
      rcases reply with ⟨actual, hints⟩
      by_cases h : actual = request
      · subst actual
        simp [applyHook, eq_comm, and_comm]
      · simp [applyHook, h]

end SP1Clean.Model.Core
