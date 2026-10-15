import SP1Clean.Model.Core.HostIO
import SP1Clean.Model.Core.SyscallCode

/-! # Stateful execution of the native eight-call host profile

The interpreter reads actual register and memory observations through a partial read interface.
In particular, WRITE obtains its length from x12; output and hook requests contain bytes read
from the addressed buffer. HINT_LEN is computed from the queue, and HINT_READ returns the full
padded write interval. Memory updates and architectural PC/x5 updates are applied by the machine
adapter, which must authenticate these observations and effects in the AIR.

The sources are SP1 v6.4.0 (`f66b4bff51d0ccff51d152e0f7f66b2ffedf3529`):
`crates/core/executor/src/minimal/{ecall,write,hint}.rs`,
`crates/core/executor/src/vm/syscall/{commit,deferred,halt}.rs`, and
`crates/primitives/src/consts.rs`. The descriptor macro adds ten to its literal values.

This native profile models constrained replay: ENTER_UNCONSTRAINED returns zero. Deferred
commitments are explicit outputs with canonical field values, rather than the minimal executor's
no-op or the replay VM's truncating assignment. VERIFY_SP1_PROOF records the two addressed
32-byte digests; it does not verify a proof. Hook responses are explicit, request-bound inputs.
Standard output/error record bytes before Rust's lossy UTF-8 rendering and profiling effects.
Guest reads specify the requested byte slice; aligned word covers belong to the AIR footprint.
The finite native memory window, ROM-write exclusion, and canonical exit/deferred values are
deliberate profile conditions, not consequences of arbitrary successful Rust dispatch.

Both commitment banks use mutable slot updates. The exact syscall AIR instead checks every
commit in a shard against one fixed public-values vector
(`crates/core/machine/src/syscall/instructions/air.rs`, `eval_commit`). Distinct overwrites of one
slot within that shard therefore need a separate restriction or refinement
argument; successful native execution alone does not imply that exact public-value binding.
-/

namespace SP1Clean.Model.Core

/-- Observations supplied by the executing machine, not by the syscall event's claimed result. -/
structure HostReadContext where
  register : BitVec 5 → Option (BitVec 64)
  byte : ℕ → Option (BitVec 8)

/-- One guest-visible memory update; its bytes include any required padding. -/
structure HostMemoryWrite where
  address : ℕ
  bytes : Bytes
deriving DecidableEq, Repr

/-- A request to an external verifier contains the bytes observed at the two guest pointers.
Proof acceptance and the guest's subsequent digest computation are separate claims. -/
structure ProofRequest where
  verificationKey : Bytes
  publicValues : Bytes
deriving DecidableEq, Repr

inductive HostRequest
  | hook (request : HookRequest)
  | proof (request : ProofRequest)
deriving DecidableEq, Repr

/-- The state threaded between calls. A recorded exit prevents every subsequent host call. -/
structure HostState where
  io : HostIO := {}
  replies : List HookReply := []
  committed : Vector (BitVec 32) 8 := Vector.replicate 8 0
  deferred : Vector (BitVec 32) 8 := Vector.replicate 8 0
  requests : List HostRequest := []
  stdout : Bytes := []
  stderr : Bytes := []
  exitCode : Option (BitVec 32) := none
deriving DecidableEq, Repr, Inhabited

/-- The characteristic is explicit because Exit and deferred commitment cells are field values.
The pinned SP1 profile uses KoalaBear. Machine integration must match this policy to the circuit's
word-range bound; this interpreter uses no field arithmetic. -/
structure HostPolicy where
  memory : HostMemoryPolicy
  characteristic : ℕ

/-- The seven hooks selected by the pinned executor's WRITE dispatch. -/
def hookDescriptors : List (BitVec 32) := [15, 16, 17, 18, 19, 20, 21]

namespace HostReadContext

/-- Read consecutive observed bytes, failing if any byte is absent. -/
def readBytes? (context : HostReadContext) (address length : ℕ) : Option Bytes :=
  (List.range length).mapM (fun offset => context.byte (address + offset))

/-- Reads permit ROM bytes. Natural-number arithmetic rules out address wrapping. -/
def readGuest? (context : HostReadContext) (policy : HostMemoryPolicy)
    (address length : ℕ) : Option Bytes :=
  if policy.lower ≤ address ∧ address + length ≤ policy.upper then
    context.readBytes? address length
  else none

end HostReadContext

/-- Host state changes and the optional memory write, before architectural register updates. -/
structure HostEffect where
  state : HostState
  write : Option HostMemoryWrite := none
deriving DecidableEq, Repr

namespace HostState

/-- Descriptor dispatch after reading the actual guest buffer. Standard output/error match the
full descriptor; all other dispatch follows its low-u32 view, as in the pinned executor. -/
def writeOutput (host : HostState) (descriptor : BitVec 64) (bytes : Bytes) : Option HostState :=
  if descriptor = 1 then some { host with stdout := host.stdout ++ bytes }
  else if descriptor = 2 then some { host with stderr := host.stderr ++ bytes }
  else if descriptor.setWidth 32 = 13 then some { host with io := host.io.writePublic bytes }
  else if descriptor.setWidth 32 = 14 then some { host with io := host.io.writeHint bytes }
  else if descriptor.setWidth 32 ∈ hookDescriptors then do
    let request : HookRequest := ⟨descriptor.setWidth 32, bytes⟩
    let (io, rest) ← host.io.applyHook request host.replies
    some { host with io, replies := rest, requests := host.requests ++ [.hook request] }
  else some host

/-- The return register is determined by the kind and the pre-call queue. It is never an input
chosen by an instruction witness. -/
def result (host : HostState) : SyscallKind → BitVec 64
  | .enterUnconstrained => 0
  | .hintLength => host.io.hintLength
  | kind => kind.code

/-- Execute one decoded call. `run` below supplies its arguments from the machine and enforces
terminality. The complete memory-write plan belongs to the result, not to an external oracle. -/
def executeKind (host : HostState) (policy : HostPolicy) (context : HostReadContext)
    (kind : SyscallKind) (arg1 arg2 : BitVec 64) : Option HostEffect :=
  match kind with
  | .halt =>
      if arg1.toNat < policy.characteristic ∧ arg1.toNat < 2 ^ 32 then
        some ⟨{ host with exitCode := some (arg1.setWidth 32) }, none⟩
      else none
  | .enterUnconstrained | .hintLength => some ⟨host, none⟩
  | .commit =>
      if index : arg1.toNat < 8 then
        if arg2.toNat < 2 ^ 32 then
          some ⟨{ host with committed := host.committed.set arg1.toNat (arg2.setWidth 32) }, none⟩
        else none
      else none
  | .commitDeferred =>
      if index : arg1.toNat < 8 then
        if arg2.toNat < policy.characteristic ∧ arg2.toNat < 2 ^ 32 then
          some ⟨{ host with deferred := host.deferred.set arg1.toNat (arg2.setWidth 32) }, none⟩
        else none
      else none
  | .verifyProof => do
      let key ← context.readGuest? policy.memory arg1.toNat 32
      let values ← context.readGuest? policy.memory arg2.toNat 32
      some ⟨{ host with requests := host.requests ++ [.proof ⟨key, values⟩] }, none⟩
  | .write => do
      let length ← context.register 12
      let bytes ← context.readGuest? policy.memory arg2.toNat length.toNat
      let next ← host.writeOutput arg1 bytes
      some ⟨next, none⟩
  | .hintRead =>
      match host.io.hints with
      | [] => none
      | bytes :: rest =>
          if bytes.length = arg2.toNat ∧ arg1.toNat % 8 = 0 ∧
              policy.memory.permits arg1.toNat (hintWriteBytes bytes).length = true then
            some ⟨{ host with io := { host.io with hints := rest } },
              some ⟨arg1.toNat, hintWriteBytes bytes⟩⟩
          else none

end HostState

/-- A decoded call and its fully determined effects, ready for architectural application. -/
structure HostExecution where
  kind : SyscallKind
  arg1 : BitVec 64
  arg2 : BitVec 64
  result : BitVec 64
  effect : HostEffect
deriving DecidableEq, Repr

/-- Execute from observed x5/x10/x11 (and WRITE's x12). The event carries no caller-supplied
return value, memory payload, or target host state. -/
def HostState.run (host : HostState) (policy : HostPolicy) (context : HostReadContext) :
    Option HostExecution := do
  if host.exitCode.isSome then none else do
    let code ← context.register 5
    let kind ← SyscallKind.decode? code
    let arg1 ← context.register 10
    let arg2 ← context.register 11
    let effect ← host.executeKind policy context kind arg1 arg2
    some ⟨kind, arg1, arg2, host.result kind, effect⟩

end SP1Clean.Model.Core
