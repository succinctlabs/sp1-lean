import SP1Clean.Model.Machine.Syscall
import SP1Clean.Model.Core.NativeLayout

/-! # Native execution profile

Shared semantic restrictions for execution and physical witnesses. These contracts are independent
of Rust extraction and table layouts. Release provenance belongs to scripts/provenance.json;
Rust comparisons check agreement on this restricted domain, not a formal lowering theorem.
-/

namespace SP1Clean.Model.Core.Profile

/-- Maximum execution-clock budget of one Core shard in the pinned executor.  This is
`MAX_SHARD_SIZE = 1 << 24` from `crates/core/executor/src/opts.rs` at the released target in
`scripts/provenance.json`. The ordinary instruction schedule consumes eight clock ticks per row. -/
def maxShardCycles : ℕ := NativeLayout.maxShardTicks

/-- Maximum number of ordinary instruction rows in a shard that uses no syscall windows. -/
def maxOrdinaryTransitions : ℕ := maxShardCycles / 8

@[simp] theorem maxOrdinaryTransitions_eq : maxOrdinaryTransitions = 2 ^ 21 := by decide

/-- The shared native capacity predicate.  Semantic executions project `steps` into it and
native AIR witnesses project their active instruction-row count into it; neither direction owns a
separate spelling of the row budget. -/
def WithinOrdinaryRowLimit (rows : ℕ) : Prop :=
  rows ≤ maxOrdinaryTransitions

/-- Every syscall in this supported profile uses a full-word canonical inline code.

The AIR selects syscall arms from byte 0 and uses byte 1 for dispatch multiplicity. The executor
instead calls `SyscallCode::from_u32` on `x5 as u32`, rejecting unrecognized low-32-bit codes but
ignoring the upper 32 bits. Requiring the entire 64-bit register to equal an inline code is therefore
a profile restriction; successful executor dispatch alone does not establish it. For example,
`0x100000003 as u32` selects `ENTER_UNCONSTRAINED`, although that raw word is not canonical here.
The row proofs do not derive this premise from AIR validity.

It is stated over the shard's syscall events so that neither direction owns a separate spelling: the
semantic side projects its transcript's syscall events into it, the native side its active syscall
rows' decoded events — exactly the arrangement `WithinOrdinaryRowLimit` uses for the row budget. -/
def CanonicalSyscallCodes (events : List SP1Clean.Machine.CoreSyscallEvent) : Prop :=
  ∀ e ∈ events, e.IsInlineCanonical

end SP1Clean.Model.Core.Profile
