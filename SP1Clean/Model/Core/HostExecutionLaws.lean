import SP1Clean.Model.Core.HostExecution
import ToMathlib.ListMapMOption

/-! # Authentic observations and memory effects of host execution

Successful execution binds the full syscall code and all observed operands to the machine's
read interface. Byte reads are characterized pointwise, including empty intervals. Memory-write
protection concerns the complete returned write, so HINT_READ padding is included.
-/

namespace SP1Clean.Model.Core

/-- Every byte in the result is observed at its corresponding guest address. -/
def HostReadContext.ObservesBytes (context : HostReadContext) (address : ℕ) (bytes : Bytes) : Prop :=
  ∀ index (bound : index < bytes.length), context.byte (address + index) = some bytes[index]

theorem HostReadContext.readBytes?_eq_some_iff (context : HostReadContext)
    (address length : ℕ) (bytes : Bytes) :
    context.readBytes? address length = some bytes ↔
      bytes.length = length ∧ context.ObservesBytes address bytes := by
  rw [readBytes?, List.mapM_option_eq_some_iff, List.forall₂_iff_get]
  simp only [List.length_range, List.get_eq_getElem, List.getElem_range]
  constructor
  · rintro ⟨equal, reads⟩
    exact ⟨equal.symm, fun index bound => reads index (by omega) bound⟩
  · rintro ⟨equal, reads⟩
    exact ⟨equal.symm, fun index _ bound => reads index bound⟩

/-- Successful reads establish bounds and exact observed contents; these are not caller premises. -/
theorem HostReadContext.readGuest?_eq_some_iff (context : HostReadContext)
    (policy : HostMemoryPolicy) (address length : ℕ) (bytes : Bytes) :
    context.readGuest? policy address length = some bytes ↔
      policy.lower ≤ address ∧ address + length ≤ policy.upper ∧
        bytes.length = length ∧ context.ObservesBytes address bytes := by
  by_cases bounds : policy.lower ≤ address ∧ address + length ≤ policy.upper
  · simp [readGuest?, bounds, readBytes?_eq_some_iff]
  · simp [readGuest?, bounds, ← and_assoc]

/-- Successful dispatch authenticates x5/x10/x11 and computes the return value from the old host.
The selected arm remains folded so callers can use its semantic effects separately. -/
theorem HostState.run_eq_some_iff (host : HostState) (policy : HostPolicy)
    (context : HostReadContext) (execution : HostExecution) :
    host.run policy context = some execution ↔
      host.exitCode = none ∧ context.register 5 = some execution.kind.code ∧
        context.register 10 = some execution.arg1 ∧ context.register 11 = some execution.arg2 ∧
        execution.result = host.result execution.kind ∧
        host.executeKind policy context execution.kind execution.arg1 execution.arg2 =
          some execution.effect := by
  cases stopped : host.exitCode with
  | some exit => simp [HostState.run, stopped]
  | none =>
      simp only [HostState.run, stopped, Option.isSome_none, Bool.false_eq_true, ↓reduceIte,
        bind, Option.bind_eq_some_iff, Option.some.injEq]
      constructor
      · rintro ⟨code, observedCode, kind, decoded, arg1, observedArg1, arg2, observedArg2,
          effect, executed, rfl⟩
        have canonical := (SyscallKind.decode?_eq_some_iff code kind).mp decoded
        exact ⟨trivial, canonical ▸ observedCode, observedArg1, observedArg2, rfl, executed⟩
      · rintro ⟨_, observedCode, observedArg1, observedArg2, resultEq, executed⟩
        refine ⟨execution.kind.code, observedCode, execution.kind,
          (SyscallKind.decode?_eq_some_iff _ _).mpr rfl, execution.arg1, observedArg1,
          execution.arg2, observedArg2, execution.effect, executed, ?_⟩
        cases execution
        simp_all

/-- WRITE's length comes from x12, and its payload from the exact addressed byte interval. -/
theorem HostState.execute_write_iff (host : HostState) (policy : HostPolicy)
    (context : HostReadContext) (descriptor address : BitVec 64) (effect : HostEffect) :
    host.executeKind policy context .write descriptor address = some effect ↔
      ∃ length bytes next, context.register 12 = some length ∧
        context.readGuest? policy.memory address.toNat length.toNat = some bytes ∧
        host.writeOutput descriptor bytes = some next ∧ effect = ⟨next, none⟩ := by
  simp only [executeKind, bind, Option.bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨length, observed, bytes, read, next, written, rfl⟩
    exact ⟨length, bytes, next, observed, read, written, rfl⟩
  · rintro ⟨length, bytes, next, observed, read, written, rfl⟩
    exact ⟨length, observed, bytes, read, next, written, rfl⟩

/-- HINT_READ consumes exactly one queue item and produces its complete protected write. -/
theorem HostState.execute_hintRead_iff (host : HostState) (policy : HostPolicy)
    (context : HostReadContext) (address length : BitVec 64) (effect : HostEffect) :
    host.executeKind policy context .hintRead address length = some effect ↔
      ∃ bytes rest, host.io.hints = bytes :: rest ∧ bytes.length = length.toNat ∧
        address.toNat % 8 = 0 ∧ policy.memory.permits address.toNat (hintWriteBytes bytes).length = true ∧
        effect = ⟨{ host with io := { host.io with hints := rest } },
          some ⟨address.toNat, hintWriteBytes bytes⟩⟩ := by
  cases hints : host.io.hints with
  | nil => simp [executeKind, hints]
  | cons bytes rest =>
      simp only [executeKind, hints]
      split_ifs with permitted <;> simp_all
      exact eq_comm

/-- Every emitted write is checked against the complete native write policy. No other arm can
silently write RAM, including through a supplied hook reply. -/
theorem HostState.executeKind_write_permitted {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {kind : SyscallKind} {arg1 arg2 : BitVec 64} {effect : HostEffect}
    (executed : host.executeKind policy context kind arg1 arg2 = some effect)
    (write : HostMemoryWrite) (present : effect.write = some write) :
    policy.memory.permits write.address write.bytes.length = true := by
  cases kind with
  | hintRead =>
      obtain ⟨bytes, rest, _, _, _, permitted, rfl⟩ :=
        (host.execute_hintRead_iff policy context arg1 arg2 effect).mp executed
      cases present
      exact permitted
  | write =>
      obtain ⟨_, _, _, _, _, _, rfl⟩ :=
        (host.execute_write_iff policy context arg1 arg2 effect).mp executed
      contradiction
  | verifyProof =>
      simp only [executeKind, bind, Option.bind_eq_some_iff, Option.some.injEq] at executed
      obtain ⟨_, _, _, _, rfl⟩ := executed
      contradiction
  | enterUnconstrained | hintLength =>
      cases executed
      contradiction
  | halt | commit | commitDeferred =>
      simp only [executeKind] at executed
      split_ifs at executed
      all_goals simp_all
      all_goals
        cases executed
        contradiction

end SP1Clean.Model.Core
