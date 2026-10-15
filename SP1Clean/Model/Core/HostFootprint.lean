import SP1Clean.Model.Core.HostExecutionLaws
import SP1Clean.Model.Core.MemorySpan

/-! # The complete native host observation and write footprint

The footprint is computed from the decoded call and actual observations. Register inputs include
WRITE's x12; RAM cells cover all requested bytes and every emitted write byte, including hint
padding. Shared cells occur once even when the two proof-request buffers overlap. Matching the
observations on this finite footprint suffices to replay the same host execution.

This is the semantic contract for host AIR accesses. It does not supply those AIR rows, their
timestamps, or a balance proof. Its minimal empty-byte cover deliberately makes no claim to match
Rust's untraced read inventory (an unaligned zero-length WRITE can still read an aligned word).
-/

namespace SP1Clean.Model.Core

structure HostFootprint where
  registers : List (BitVec 5)
  ramCells : List ℕ
deriving DecidableEq, Repr

/-- One full cell of an emitted write, ready for the byte-to-field-word circuit. -/
def HostMemoryWrite.wordBytes (write : HostMemoryWrite) (offset : ℕ)
    (bound : 8 * offset + 8 ≤ write.bytes.length) : Vector (BitVec 8) 8 :=
  Vector.ofFn fun index => write.bytes[8 * offset + index.val]'(by have := index.isLt; omega)

/-- Agreement on every register and every byte of every inventoried aligned cell. -/
def HostFootprint.Agrees (footprint : HostFootprint) (left right : HostReadContext) : Prop :=
  (∀ index ∈ footprint.registers, left.register index = right.register index) ∧
    ∀ address, address / 8 ∈ footprint.ramCells → left.byte address = right.byte address

def HostExecution.readRegisters (execution : HostExecution) : List (BitVec 5) :=
  [5, 10, 11] ++ if execution.kind = .write then [12] else []

/-- WRITE's byte count is an observed register, not the pointer or a witness-supplied span. -/
def HostExecution.readSpans? (execution : HostExecution) (context : HostReadContext) :
    Option (List MemorySpan) :=
  match execution.kind with
  | .write => (context.register 12).map fun length => [⟨execution.arg2.toNat, length.toNat⟩]
  | .verifyProof => some [⟨execution.arg1.toNat, 32⟩, ⟨execution.arg2.toNat, 32⟩]
  | _ => some []

def HostExecution.writeSpans (execution : HostExecution) : List MemorySpan :=
  execution.effect.write.toList.map fun write => ⟨write.address, write.bytes.length⟩

/-- The full observation/write inventory, with one physical access per distinct RAM cell. -/
def HostExecution.footprint? (execution : HostExecution) (context : HostReadContext) :
    Option HostFootprint :=
  (execution.readSpans? context).map fun reads =>
    ⟨execution.readRegisters, MemorySpan.unionCells (reads ++ execution.writeSpans)⟩

theorem HostExecution.footprint?_eq_some_iff (execution : HostExecution)
    (context : HostReadContext) (footprint : HostFootprint) :
    execution.footprint? context = some footprint ↔
      ∃ reads, execution.readSpans? context = some reads ∧
        footprint = ⟨execution.readRegisters, MemorySpan.unionCells (reads ++ execution.writeSpans)⟩ := by
  simp [footprint?, eq_comm]

theorem HostExecution.footprint_nodup {execution : HostExecution} {context : HostReadContext}
    {footprint : HostFootprint} (built : execution.footprint? context = some footprint) :
    footprint.registers.Nodup ∧ footprint.ramCells.Nodup := by
  obtain ⟨reads, _, rfl⟩ := (execution.footprint?_eq_some_iff context footprint).mp built
  constructor
  · change execution.readRegisters.Nodup
    unfold readRegisters
    split_ifs <;> decide
  · exact MemorySpan.nodup_unionCells _

/-- Every emitted write byte belongs to the inventory, independently of any claimed read data. -/
theorem HostExecution.write_covered {execution : HostExecution} {context : HostReadContext}
    {footprint : HostFootprint} (built : execution.footprint? context = some footprint)
    {write : HostMemoryWrite} (written : execution.effect.write = some write)
    (offset : ℕ) (bound : offset < write.bytes.length) :
    (write.address + offset) / 8 ∈ footprint.ramCells := by
  obtain ⟨reads, _, rfl⟩ := (execution.footprint?_eq_some_iff context footprint).mp built
  apply (MemorySpan.mem_unionCells _ _).mpr
  refine ⟨⟨write.address, write.bytes.length⟩, ?_, MemorySpan.byte_cell_mem _ offset bound⟩
  simp [writeSpans, written]

/-- A successful host call always has a computed footprint; no further observations are required. -/
theorem HostState.run_footprint {host : HostState} {policy : HostPolicy} {context : HostReadContext}
    {execution : HostExecution} (run : host.run policy context = some execution) :
    ∃ footprint, execution.footprint? context = some footprint := by
  have executed := ((host.run_eq_some_iff policy context execution).mp run).2.2.2.2.2
  cases kind : execution.kind with
  | write =>
      rw [kind] at executed
      obtain ⟨length, _, _, observed, _, _, _⟩ :=
        (host.execute_write_iff policy context execution.arg1 execution.arg2 execution.effect).mp executed
      simp only [HostExecution.footprint?, HostExecution.readSpans?, kind, observed,
        Option.map_some]
      exact ⟨_, rfl⟩
  | halt | enterUnconstrained | commit | commitDeferred | verifyProof | hintLength | hintRead =>
      simp [HostExecution.footprint?, HostExecution.readSpans?, kind]

/-- Every listed read span was successfully observed during execution. -/
theorem HostState.readSpans_observed {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {execution : HostExecution} {reads : List MemorySpan}
    (run : host.run policy context = some execution)
    (spans : execution.readSpans? context = some reads) :
    ∀ span ∈ reads, ∃ bytes,
      context.readGuest? policy.memory span.address span.length = some bytes := by
  have executed := ((host.run_eq_some_iff policy context execution).mp run).2.2.2.2.2
  cases kind : execution.kind with
  | write =>
      rw [kind] at executed
      obtain ⟨length, bytes, _, observed, fetched, _, _⟩ :=
        (host.execute_write_iff policy context execution.arg1 execution.arg2 execution.effect).mp executed
      simp only [HostExecution.readSpans?, kind, observed, Option.map_some, Option.some.injEq] at spans
      subst reads
      simpa only [List.mem_singleton, forall_eq] using (⟨bytes, fetched⟩ : ∃ bytes,
        context.readGuest? policy.memory execution.arg2.toNat length.toNat = some bytes)
  | verifyProof =>
      rw [kind] at executed
      simp only [HostState.executeKind, bind, Option.bind_eq_some_iff, Option.some.injEq] at executed
      obtain ⟨key, keyRead, values, valuesRead, _⟩ := executed
      simp only [HostExecution.readSpans?, kind, Option.some.injEq] at spans
      subst reads
      intro span member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · exact ⟨key, keyRead⟩
      · exact ⟨values, valuesRead⟩
  | halt | enterUnconstrained | commit | commitDeferred | hintLength | hintRead =>
      simp only [HostExecution.readSpans?, kind, Option.some.injEq] at spans
      subst reads
      simp

/-- Native guest bounds are inherited by whole cells, including unaligned read endpoints. -/
theorem HostState.footprint_in_window {host : HostState} {policy : HostPolicy}
    {context : HostReadContext} {execution : HostExecution} {footprint : HostFootprint}
    (run : host.run policy context = some execution)
    (built : execution.footprint? context = some footprint)
    (lower : 2 ^ 16 ≤ policy.memory.lower) (upper : policy.memory.upper ≤ 2 ^ 48)
    (cell : ℕ) (member : cell ∈ footprint.ramCells) :
    2 ^ 16 ≤ cell * 8 ∧ cell * 8 + 8 ≤ 2 ^ 48 := by
  obtain ⟨reads, spans, rfl⟩ := (execution.footprint?_eq_some_iff context footprint).mp built
  obtain ⟨span, spanMem, covered⟩ := (MemorySpan.mem_unionCells _ _).mp member
  apply span.cell_in_window ?_ ?_ cell covered
  all_goals
    rcases List.mem_append.mp spanMem with read | write
    · obtain ⟨bytes, observed⟩ := host.readSpans_observed run spans span read
      have bounds := (context.readGuest?_eq_some_iff policy.memory span.address span.length bytes).mp observed
      omega
    · obtain ⟨written, present, rfl⟩ := List.mem_map.mp write
      have actual : execution.effect.write = some written := by simpa using present
      have executed := ((host.run_eq_some_iff policy context execution).mp run).2.2.2.2.2
      have permitted := (policy.memory.permits_iff _ _).mp
        (host.executeKind_write_permitted executed written actual)
      dsimp only
      omega

/-- Equal cell observations give equal reads of any covered byte span. -/
theorem HostReadContext.readGuest?_congr {left right : HostReadContext} {span : MemorySpan}
    (agree : ∀ address, address / 8 ∈ span.cells → left.byte address = right.byte address)
    (policy : HostMemoryPolicy) :
    left.readGuest? policy span.address span.length =
      right.readGuest? policy span.address span.length := by
  apply Option.ext
  intro bytes
  rw [left.readGuest?_eq_some_iff, right.readGuest?_eq_some_iff]
  constructor
  · rintro ⟨lower, upper, length, observed⟩
    refine ⟨lower, upper, length, fun offset bound => ?_⟩
    rw [← agree _ (span.byte_cell_mem offset (by omega))]
    exact observed offset bound
  · rintro ⟨lower, upper, length, observed⟩
    refine ⟨lower, upper, length, fun offset bound => ?_⟩
    rw [agree _ (span.byte_cell_mem offset (by omega))]
    exact observed offset bound

/-- All host computation depends only on the footprint's observed registers and RAM cells.
In particular, replacing every other byte or register cannot change the return value, outputs,
requests, queue effects, or padded write. -/
theorem HostState.run_congr_of_footprint {host : HostState} {policy : HostPolicy}
    {left right : HostReadContext} {execution : HostExecution} {footprint : HostFootprint}
    (run : host.run policy left = some execution)
    (built : execution.footprint? left = some footprint)
    (agree : footprint.Agrees left right) :
    host.run policy right = some execution := by
  obtain ⟨reads, spans, rfl⟩ := (execution.footprint?_eq_some_iff left footprint).mp built
  have registerAgree (index : BitVec 5) (member : index ∈ execution.readRegisters) :
      left.register index = right.register index := agree.1 index member
  have readAgree (span : MemorySpan) (member : span ∈ reads) :
      left.readGuest? policy.memory span.address span.length =
        right.readGuest? policy.memory span.address span.length := by
    apply HostReadContext.readGuest?_congr
    intro address covered
    exact agree.2 address ((MemorySpan.mem_unionCells _ _).mpr
      ⟨span, List.mem_append_left _ member, covered⟩)
  have sameEffect : host.executeKind policy left execution.kind execution.arg1 execution.arg2 =
      host.executeKind policy right execution.kind execution.arg1 execution.arg2 := by
    cases kind : execution.kind with
    | write =>
        have lengthAgree := registerAgree 12 (by simp [HostExecution.readRegisters, kind])
        simp only [HostExecution.readSpans?, kind, Option.map_eq_some_iff] at spans
        obtain ⟨length, observed, rfl⟩ := spans
        have bytes := readAgree ⟨execution.arg2.toNat, length.toNat⟩ (by simp)
        simp only [HostState.executeKind, observed, ← lengthAgree, bind, Option.bind_some, bytes]
    | verifyProof =>
        simp only [HostExecution.readSpans?, kind, Option.some.injEq] at spans
        subst reads
        have key := readAgree ⟨execution.arg1.toNat, 32⟩ (by simp)
        have values := readAgree ⟨execution.arg2.toNat, 32⟩ (by simp)
        simp only [HostState.executeKind, key, values]
    | halt | enterUnconstrained | commit | commitDeferred | hintLength | hintRead => rfl
  have binding := (host.run_eq_some_iff policy left execution).mp run
  apply (host.run_eq_some_iff policy right execution).mpr
  refine ⟨binding.1, ?_, ?_, ?_, binding.2.2.2.2.1, sameEffect ▸ binding.2.2.2.2.2⟩
  · rw [← registerAgree 5 (by simp [HostExecution.readRegisters])]
    exact binding.2.1
  · rw [← registerAgree 10 (by simp [HostExecution.readRegisters])]
    exact binding.2.2.1
  · rw [← registerAgree 11 (by simp [HostExecution.readRegisters])]
    exact binding.2.2.2.1

end SP1Clean.Model.Core
