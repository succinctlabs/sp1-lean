import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Public values on the formal-model audit surface

This file deliberately separates the small State boundary consumed by the current 25-chip ensemble
from SP1's real shard public-values record.  The latter mirrors
`sp1_hypercube::air::PublicValues<[F; 4], [F; 3], [F; 4], F>`; keeping the distinction in the type
names prevents a supported-core theorem from silently presenting itself as full SP1 AIR
soundness.

**Reserved cross-shard layer.**  Beyond the types the exact-AIR relation consumes today
(`SP1PublicValues`, its `WellFormed` family, `SP1ShardStatement`), this file also carries the
shard-ledger layer written ahead of its consumer: the continuity predicates
(`ExecutionContinues`/`ExecutionContinuous`, `LedgerContinues`/`LedgerContinuous`), the
boundary predicates (`InitialLedgerBoundary`, `FinalLedgerBoundary`,
`HasUniqueFirstExecutionShard`), and the statement plumbing (`shardStatements`,
`ConfigurationMatches`, `toBaseVector`, the `toNat`/`*Bits` decoders).  Their intended consumer
is the boot-to-halt shard-composition theorem — the reserved `sp1_execution_sound` layer
(`docs/roadmap.md`, after the exact-AIR bundle closes).  They are deliberately declared now so
the cross-shard statement shape is fixed and auditable before that proof exists; a reference
census will find them unreferenced in-tree, which is this design choice, not dead code. -/

namespace SP1Clean

/-- The State-bus endpoints and terminal cells committed by the current Clean ensemble —
**split-limb form** (W3 D5-A, external report Finding 2). Each end carries its clock as the
upstream `SP1Timestamp` `(16, 8, 8, 16)` limbs (`clk_0_16`/`clk_16_24`/`clk_24_32`/`clk_32_48`,
ascending) plus the three 16-bit pc limbs; the folded State-bus pair is recovered by the
`init_clk_high`/`init_clk_low`/`final_clk_high`/`final_clk_low` recombination projections below,
so `Semantics.clkNat` call sites and the boundary State messages read exactly as before. The
split is what lets the boundary verifier range-check every committed limb in-circuit
(`sp1StateVerifier`'s byte pulls), making the initial State message's canonicity a theorem of the
ensemble rather than an `InitialBoundaryFacts` premise — and it is the faithful shape: SP1's real
public values commit timestamps in precisely these limbs.

The three terminal fields mirror the corresponding cells of the 160-cell upstream record
(`exit_code`, `is_execution_shard`, and the flattened 8×4-byte `committed_value_digest`).  They
are **committed but deliberately unconstrained** by the boundary verifier, faithful to upstream:
SP1's own AIR gives `exit_code` no independent range check (the halt row binds it to the reduced
`op_b` word) and constrains the digest cells only on COMMIT rows.  Their meaning arrives with the
halt/COMMIT-row semantics (semantics-gap campaign Track 2). -/
structure SP1StateBoundary (F : Type) where
  init_clk_0_16 : F
  init_clk_16_24 : F
  init_clk_24_32 : F
  init_clk_32_48 : F
  init_pc0 : F
  init_pc1 : F
  init_pc2 : F
  final_clk_0_16 : F
  final_clk_16_24 : F
  final_clk_24_32 : F
  final_clk_32_48 : F
  final_pc0 : F
  final_pc1 : F
  final_pc2 : F
  exit_code : F
  is_execution_shard : F
  committed_value_digest : Vector F 32
deriving ProvableStruct

section Recombined

variable {F : Type} [Add F] [Mul F] [OfNat F 256] [OfNat F 65536]

/-- The initial boundary's State-bus `clk_high` (bits 24–48), recombined from its two limbs. -/
@[circuit_norm] def SP1StateBoundary.init_clk_high (b : SP1StateBoundary F) : F :=
  b.init_clk_24_32 + b.init_clk_32_48 * 256

/-- The initial boundary's State-bus `clk_low` (bits 0–24), recombined from its two limbs. -/
@[circuit_norm] def SP1StateBoundary.init_clk_low (b : SP1StateBoundary F) : F :=
  b.init_clk_0_16 + b.init_clk_16_24 * 65536

/-- The final boundary's State-bus `clk_high`, recombined from its two limbs. -/
@[circuit_norm] def SP1StateBoundary.final_clk_high (b : SP1StateBoundary F) : F :=
  b.final_clk_24_32 + b.final_clk_32_48 * 256

/-- The final boundary's State-bus `clk_low`, recombined from its two limbs. -/
@[circuit_norm] def SP1StateBoundary.final_clk_low (b : SP1StateBoundary F) : F :=
  b.final_clk_0_16 + b.final_clk_16_24 * 65536

end Recombined

/-- The boundary limbs' range facts — exactly what the verifier row's twelve byte pulls prove
in-circuit (`sp1StateVerifier.Spec`): each clock in genuine `(16, 8, 8, 16)` limbs and each pc limb
16-bit. This is the goodness-filter base case: the pushed initial State message is canonical by
construction, with no boundary premise. -/
def SP1StateBoundary.LimbBounds {p : ℕ} [Fact p.Prime] (b : SP1StateBoundary (ZMod p)) : Prop :=
  b.init_clk_0_16.val < 2 ^ 16 ∧ b.init_clk_16_24.val < 2 ^ 8 ∧
  b.init_clk_24_32.val < 2 ^ 8 ∧ b.init_clk_32_48.val < 2 ^ 16 ∧
  b.init_pc0.val < 2 ^ 16 ∧ b.init_pc1.val < 2 ^ 16 ∧ b.init_pc2.val < 2 ^ 16 ∧
  b.final_clk_0_16.val < 2 ^ 16 ∧ b.final_clk_16_24.val < 2 ^ 8 ∧
  b.final_clk_24_32.val < 2 ^ 8 ∧ b.final_clk_32_48.val < 2 ^ 16 ∧
  b.final_pc0.val < 2 ^ 16 ∧ b.final_pc1.val < 2 ^ 16 ∧ b.final_pc2.val < 2 ^ 16

/-- Compatibility name used by the existing circuit layer. -/
abbrev SP1PublicIO := SP1StateBoundary

/-- Exact public-values type of the supported-core prefix theorem.  Naming the prefix explicitly
records that this is still a strict prefix of the full 160-cell layout below: the ensemble
constrains the State-bus boundary limbs in-circuit, while the terminal cells (`exit_code`,
`is_execution_shard`, `committed_value_digest`) are committed carrier data awaiting their
halt/COMMIT-row semantics. -/
abbrev SupportedCorePrefixPublicValues := SP1StateBoundary

/-! ## The real SP1 shard public-values layout

The aliases below name the three Rust word representations directly.  They are semantic data types,
not yet a `ProvableType`: the full AIR will receive its own verifier/public-input circuit only when
all fields below are constrained and extraction-faithful. -/

/-- One 32-bit word represented by four byte limbs (`W1 = [F; 4]`). -/
abbrev SP1Word32 (F : Type) := Vector F 4

/-- One 48-bit address or pc represented by three 16-bit limbs (`W2 = [F; 3]`). -/
abbrev SP1Word48 (F : Type) := Vector F 3

/-- One timestamp represented by the upstream `(16, 8, 8, 16)` limbs (`W3 = [F; 4]`). -/
abbrev SP1Timestamp (F : Type) := Vector F 4

/-- The field representation of SP1's septic-curve cumulative-sum digest. -/
structure SP1SepticDigest (F : Type) where
  x : Vector F 7
  y : Vector F 7

/-- Public values present only when SP1 is built with the `mprotect` feature. -/
structure SP1MProtectPublicValues (F : Type) where
  enable_trap_handler : F
  trap_context : Vector (SP1Word48 F) 3
  untrusted_memory : Vector (SP1Word48 F) 2

/-- Verifying-key configuration corresponding to Rust's `UntrustedConfig`.  As with public values,
the `Option` is a type-level rendering of the compile-time `mprotect` layout choice, not data a
prover may select independently of the verifier. -/
structure SP1UntrustedConfig (F : Type) where
  enable_untrusted_programs : F
  mprotect : Option (SP1MProtectPublicValues F)

/-- The public portion of Rust's `MachineVerifyingKey`.  `Digest` is left abstract until the ArkLib
commitment adapter fixes the concrete PCS digest representation. -/
structure SP1MachineVerifyingKey (F Digest : Type) where
  pc_start : SP1Word48 F
  initial_global_cumulative_sum : SP1SepticDigest F
  preprocessed_commit : Digest
  untrusted_config : SP1UntrustedConfig F

/-- The full public record of one upstream SP1 core shard.

`mprotect = none` models the base layout and `some values` the feature-enabled extension.  The AIR
configuration must bind which variant is legal; a prover is not allowed to choose it per witness. -/
structure SP1PublicValues (F : Type) where
  prev_committed_value_digest : Vector (SP1Word32 F) 8
  committed_value_digest : Vector (SP1Word32 F) 8
  prev_deferred_proofs_digest : Vector F 8
  deferred_proofs_digest : Vector F 8
  pc_start : SP1Word48 F
  next_pc : SP1Word48 F
  prev_exit_code : F
  exit_code : F
  is_execution_shard : F
  previous_init_addr : SP1Word48 F
  last_init_addr : SP1Word48 F
  previous_finalize_addr : SP1Word48 F
  last_finalize_addr : SP1Word48 F
  previous_init_page_idx : SP1Word48 F
  last_init_page_idx : SP1Word48 F
  previous_finalize_page_idx : SP1Word48 F
  last_finalize_page_idx : SP1Word48 F
  initial_timestamp : SP1Timestamp F
  last_timestamp : SP1Timestamp F
  is_timestamp_high_eq : F
  inv_timestamp_high : F
  is_timestamp_low_eq : F
  inv_timestamp_low : F
  global_init_count : F
  global_finalize_count : F
  global_page_prot_init_count : F
  global_page_prot_finalize_count : F
  global_count : F
  global_cumulative_sum : SP1SepticDigest F
  prev_commit_syscall : F
  commit_syscall : F
  prev_commit_deferred_syscall : F
  commit_deferred_syscall : F
  initial_timestamp_inv : F
  last_timestamp_inv : F
  is_first_execution_shard : F
  is_untrusted_programs_enabled : F
  mprotect : Option (SP1MProtectPublicValues F)
  proof_nonce : Vector F 4
  empty : Vector F 4

/-- Flatten the base (non-`mprotect`) Rust layout in exact `#[repr(C)]` field order.

The result type is the upstream `SP1_PROOF_NUM_PV_ELTS = 160` tripwire.  This is the sole adapter
passed to the generated public-value and row oracles; semantic code should continue to use the
named structure fields.  A feature-enabled layout needs a separately sized encoder rather than
silently inserting or deleting the optional fields here. -/
def SP1PublicValues.toBaseVector {F : Type} (pv : SP1PublicValues F) : Vector F 160 :=
  pv.prev_committed_value_digest.flatten ++
  pv.committed_value_digest.flatten ++
  pv.prev_deferred_proofs_digest ++
  pv.deferred_proofs_digest ++
  pv.pc_start ++ pv.next_pc ++
  #v[pv.prev_exit_code, pv.exit_code, pv.is_execution_shard] ++
  pv.previous_init_addr ++ pv.last_init_addr ++
  pv.previous_finalize_addr ++ pv.last_finalize_addr ++
  pv.previous_init_page_idx ++ pv.last_init_page_idx ++
  pv.previous_finalize_page_idx ++ pv.last_finalize_page_idx ++
  pv.initial_timestamp ++ pv.last_timestamp ++
  #v[pv.is_timestamp_high_eq, pv.inv_timestamp_high,
    pv.is_timestamp_low_eq, pv.inv_timestamp_low,
    pv.global_init_count, pv.global_finalize_count,
    pv.global_page_prot_init_count, pv.global_page_prot_finalize_count,
    pv.global_count] ++
  pv.global_cumulative_sum.x ++ pv.global_cumulative_sum.y ++
  #v[pv.prev_commit_syscall, pv.commit_syscall,
    pv.prev_commit_deferred_syscall, pv.commit_deferred_syscall,
    pv.initial_timestamp_inv, pv.last_timestamp_inv,
    pv.is_first_execution_shard, pv.is_untrusted_programs_enabled] ++
  pv.proof_nonce ++ pv.empty

/-- The Rust feature selection is verifier configuration, not witness data. -/
inductive SP1PublicValuesLayout
  | base
  | mprotect
deriving DecidableEq, Repr

/-- The actual public statement presented to one upstream shard verifier.  The guest program is not
embedded here: it is bound by the verifying key's preprocessed commitment. -/
structure SP1ShardStatement (F Digest : Type) where
  verifyingKey : SP1MachineVerifyingKey F Digest
  publicValues : SP1PublicValues F

/-- Public input to the composed execution theorem.  A proof-system adapter may expose only the
final recursive public values, but its recursion theorem must recover this ordered shard ledger
before the AIR results can be composed. -/
structure SP1ExecutionStatement (F Digest : Type) where
  verifyingKey : SP1MachineVerifyingKey F Digest
  shards : List (SP1PublicValues F)

/-- View every entry in a composed ledger as a shard statement under the one machine verifying
key. -/
def SP1ExecutionStatement.shardStatements {F Digest : Type}
    (statement : SP1ExecutionStatement F Digest) : List (SP1ShardStatement F Digest) :=
  statement.shards.map fun publicValues => ⟨statement.verifyingKey, publicValues⟩

/-- A field element used as a Boolean selector. -/
def FieldBool {p : ℕ} (value : ZMod p) : Prop := value = 0 ∨ value = 1

/-- Canonical byte-limb encoding of a 32-bit public-value word. -/
def SP1Word32.WellFormed {p : ℕ} (word : SP1Word32 (ZMod p)) : Prop :=
  ∀ value ∈ word.toList, value.val < 2 ^ 8

/-- Canonical 16-bit-limb encoding of a 48-bit address or pc. -/
def SP1Word48.WellFormed {p : ℕ} (word : SP1Word48 (ZMod p)) : Prop :=
  ∀ value ∈ word.toList, value.val < 2 ^ 16

/-- Canonical `(16, 8, 8, 16)` limb encoding of an upstream timestamp. -/
def SP1Timestamp.WellFormed {p : ℕ} (timestamp : SP1Timestamp (ZMod p)) : Prop :=
  timestamp[0].val < 2 ^ 16 ∧ timestamp[1].val < 2 ^ 8 ∧
    timestamp[2].val < 2 ^ 8 ∧ timestamp[3].val < 2 ^ 16

/-- The feature-dependent portion agrees with the verifier's compiled layout. -/
def SP1PublicValues.ConformsLayout {p : ℕ} (layout : SP1PublicValuesLayout)
    (pv : SP1PublicValues (ZMod p)) : Prop :=
  match layout with
  | .base => pv.mprotect = none
  | .mprotect => ∃ values, pv.mprotect = some values ∧ FieldBool values.enable_trap_handler

/-- The verifying key agrees with the verifier's compiled public-values/configuration layout. -/
def SP1UntrustedConfig.WellFormed {p : ℕ} (layout : SP1PublicValuesLayout)
    (config : SP1UntrustedConfig (ZMod p)) : Prop :=
  FieldBool config.enable_untrusted_programs ∧ match layout with
    | .base => config.mprotect = none
    | .mprotect => ∃ values, config.mprotect = some values ∧
        FieldBool values.enable_trap_handler ∧
        (∀ address ∈ values.trap_context.toList, address.WellFormed) ∧
        ∀ address ∈ values.untrusted_memory.toList, address.WellFormed

/-- Range and selector hygiene for the field-valued part of the machine verifying key.  The PCS
adapter is separately responsible for validating `preprocessed_commit`. -/
def SP1MachineVerifyingKey.WellFormed {p : ℕ} {Digest : Type}
    (layout : SP1PublicValuesLayout) (vk : SP1MachineVerifyingKey (ZMod p) Digest) : Prop :=
  vk.pc_start.WellFormed ∧ vk.untrusted_config.WellFormed layout

/-- Public configuration cells are copies of verifier-key metadata, not prover-selected flags. -/
def SP1ShardStatement.ConfigurationMatches {p : ℕ} {Digest : Type}
    (statement : SP1ShardStatement (ZMod p) Digest) : Prop :=
  statement.publicValues.is_untrusted_programs_enabled =
      statement.verifyingKey.untrusted_config.enable_untrusted_programs ∧
    statement.publicValues.mprotect = statement.verifyingKey.untrusted_config.mprotect

/-- The execution-coordinate projection of one adjacent shard link. -/
def SP1PublicValues.ExecutionContinues (previous next : SP1PublicValues (ZMod p)) : Prop :=
  previous.next_pc = next.pc_start ∧
    previous.last_timestamp = next.initial_timestamp ∧
    previous.exit_code = next.prev_exit_code

/-- Pairwise execution-coordinate continuity of an ordered shard ledger. -/
def SP1PublicValues.ExecutionContinuous : List (SP1PublicValues (ZMod p)) → Prop
  | [] | [_] => True
  | previous :: next :: rest =>
      previous.ExecutionContinues next ∧ ExecutionContinuous (next :: rest)

/-- Decode an upstream three-limb pc/address as a natural number. -/
def SP1Word48.toNat {p : ℕ} (word : SP1Word48 (ZMod p)) : ℕ :=
  word[0].val + word[1].val * 2 ^ 16 + word[2].val * 2 ^ 32

/-- Decode one four-byte public-value digest word in little-endian order. -/
def SP1Word32.toNat {p : ℕ} (word : SP1Word32 (ZMod p)) : ℕ :=
  word[0].val + word[1].val * 2 ^ 8 + word[2].val * 2 ^ 16 + word[3].val * 2 ^ 24

/-- Decode an upstream timestamp using its `(16, 8, 8, 16)` big-endian limb weights. -/
def SP1Timestamp.toNat {p : ℕ} (timestamp : SP1Timestamp (ZMod p)) : ℕ :=
  timestamp[0].val * 2 ^ 32 + timestamp[1].val * 2 ^ 24 +
    timestamp[2].val * 2 ^ 16 + timestamp[3].val

/-! ## Concrete recursive-shard ledger

The recursion circuit does substantially more than the execution-coordinate projection above.  Its
sequential compression loop carries every rolling value forward and checks it against the next
shard's `prev_*` field.  The definitions below transcribe that loop directly.  They intentionally do
not define septic-curve addition or deferred-proof verification: those are proof-system relations,
not equality links between public records. -/

/-- Every field element in a fixed-size vector is zero. -/
def SP1VectorZero {p n : ℕ} (values : Vector (ZMod p) n) : Prop :=
  ∀ value ∈ values.toList, value = 0

/-- The byte-word public-values digest is the all-zero digest. -/
def SP1WordDigestZero {p : ℕ} (digest : Vector (SP1Word32 (ZMod p)) 8) : Prop :=
  ∀ word ∈ digest.toList, SP1VectorZero word

/-- Exact intra-shard transition laws for the public-output digest and rolling COMMIT flag.  These
are consequences of the machine-level public-values AIR; importantly, they permit an unbacked
`0 → 1` flag transition and therefore assert no syscall-row existence. -/
structure SP1PublicValues.PublicCommitTransitionValid {p : ℕ}
    (publicValues : SP1PublicValues (ZMod p)) : Prop where
  monotone : publicValues.prev_commit_syscall = 1 → publicValues.commit_syscall = 1
  nonExecutionStable : publicValues.is_execution_shard = 0 →
    publicValues.prev_commit_syscall = publicValues.commit_syscall ∧
      publicValues.prev_committed_value_digest = publicValues.committed_value_digest
  nonzeroDigestStable : ¬ SP1WordDigestZero publicValues.prev_committed_value_digest →
    publicValues.prev_committed_value_digest = publicValues.committed_value_digest
  committedStable : publicValues.prev_commit_syscall = 1 →
    publicValues.prev_committed_value_digest = publicValues.committed_value_digest

/-- Deferred-proof counterpart of `PublicCommitTransitionValid`. -/
structure SP1PublicValues.DeferredCommitTransitionValid {p : ℕ}
    (publicValues : SP1PublicValues (ZMod p)) : Prop where
  monotone : publicValues.prev_commit_deferred_syscall = 1 →
    publicValues.commit_deferred_syscall = 1
  nonExecutionStable : publicValues.is_execution_shard = 0 →
    publicValues.prev_commit_deferred_syscall = publicValues.commit_deferred_syscall ∧
      publicValues.prev_deferred_proofs_digest = publicValues.deferred_proofs_digest
  nonzeroDigestStable : ¬ SP1VectorZero publicValues.prev_deferred_proofs_digest →
    publicValues.prev_deferred_proofs_digest = publicValues.deferred_proofs_digest
  committedStable : publicValues.prev_commit_deferred_syscall = 1 →
    publicValues.prev_deferred_proofs_digest = publicValues.deferred_proofs_digest

/-- All intra-shard rolling COMMIT transition laws enforced by the public-values AIR. -/
structure SP1PublicValues.CommitTransitionValid {p : ℕ}
    (publicValues : SP1PublicValues (ZMod p)) : Prop where
  publicCommit : publicValues.PublicCommitTransitionValid
  deferredCommit : publicValues.DeferredCommitTransitionValid

/-- Every equality checked between two consecutive core-shard public records by recursion's
compression loop.  Per-shard cumulative sums are deliberately absent: recursion combines them with
septic-curve addition rather than carrying one into the next record. -/
def SP1PublicValues.LedgerContinues (previous next : SP1PublicValues (ZMod p)) : Prop :=
  previous.committed_value_digest = next.prev_committed_value_digest ∧
    previous.deferred_proofs_digest = next.prev_deferred_proofs_digest ∧
    previous.next_pc = next.pc_start ∧
    previous.last_timestamp = next.initial_timestamp ∧
    previous.last_init_addr = next.previous_init_addr ∧
    previous.last_finalize_addr = next.previous_finalize_addr ∧
    previous.last_init_page_idx = next.previous_init_page_idx ∧
    previous.last_finalize_page_idx = next.previous_finalize_page_idx ∧
    previous.exit_code = next.prev_exit_code ∧
    previous.commit_syscall = next.prev_commit_syscall ∧
    previous.commit_deferred_syscall = next.prev_commit_deferred_syscall ∧
    previous.proof_nonce = next.proof_nonce

/-- Exact pairwise continuity of an ordered core-shard ledger. -/
def SP1PublicValues.LedgerContinuous : List (SP1PublicValues (ZMod p)) → Prop
  | [] | [_] => True
  | previous :: next :: rest =>
      previous.LedgerContinues next ∧ LedgerContinuous (next :: rest)

/-- Initial aggregate boundary imposed when a recursive proof is marked complete.  The timestamp
encoding is compared semantically (`toNat = 1`); `WellFormed` supplies its canonical limb bounds. -/
def SP1PublicValues.InitialLedgerBoundary (publicValues : SP1PublicValues (ZMod p)) : Prop :=
  SP1WordDigestZero publicValues.prev_committed_value_digest ∧
    SP1VectorZero publicValues.prev_deferred_proofs_digest ∧
    publicValues.initial_timestamp.toNat = 1 ∧
    publicValues.previous_init_addr.toNat = 0 ∧
    publicValues.previous_finalize_addr.toNat = 0 ∧
    publicValues.previous_init_page_idx.toNat = 0 ∧
    publicValues.previous_finalize_page_idx.toNat = 0 ∧
    publicValues.prev_exit_code = 0 ∧
    publicValues.prev_commit_syscall = 0 ∧
    publicValues.prev_commit_deferred_syscall = 0

/-- Terminal aggregate boundary imposed by SP1 recursion for a complete proof.  `haltPc` is an
explicit parameter so this public-values module remains independent of the syscall semantics module;
the current Core target instantiates it with `1`. -/
def SP1PublicValues.FinalLedgerBoundary (haltPc : ℕ)
    (publicValues : SP1PublicValues (ZMod p)) : Prop :=
  publicValues.next_pc.toNat = haltPc ∧
    publicValues.last_init_addr.toNat ≠ 0 ∧
    publicValues.last_finalize_addr.toNat ≠ 0 ∧
    publicValues.commit_syscall = 1 ∧
    publicValues.commit_deferred_syscall = 1

/-- Exactly one included record is the first execution shard.  Using `filter.length`, rather than
uniqueness of record *values*, also detects a duplicated identical record. -/
def SP1PublicValues.HasUniqueFirstExecutionShard
    (shards : List (SP1PublicValues (ZMod p))) : Prop :=
  (shards.filter fun publicValues => publicValues.is_first_execution_shard = 1).length = 1

/-- Public-record checks performed by recursive composition, except for septic-curve aggregation
and deferred-proof authentication.  Those two external checks have their own narrow theorem
parameters at the execution boundary; they are not hidden inside this ledger predicate. -/
def SP1PublicValues.AuthenticatedLedger (haltPc : ℕ)
    (shards : List (SP1PublicValues (ZMod p))) : Prop :=
  ∃ first rest final,
    shards = first :: rest ∧
      shards.getLast? = some final ∧
      first.InitialLedgerBoundary ∧
      final.FinalLedgerBoundary haltPc ∧
      LedgerContinuous shards ∧
      HasUniqueFirstExecutionShard shards

/-- The full ledger continuity implies its execution-coordinate projection. -/
theorem SP1PublicValues.executionContinuous_of_ledgerContinuous
    {shards : List (SP1PublicValues (ZMod p))}
    (continuous : LedgerContinuous shards) : ExecutionContinuous shards := by
  induction shards with
  | nil => trivial
  | cons first rest ih =>
      cases rest with
      | nil => trivial
      | cons next tail =>
          obtain ⟨-, -, pc, timestamp, -, -, -, -, exitCode, -, -, -⟩ := continuous.1
          exact ⟨⟨pc, timestamp, exitCode⟩, ih continuous.2⟩

/-- Once the rolling COMMIT flag is set, ledger continuity and the public-values AIR transition
laws force that shard's committed digest to equal the terminal digest.  This theorem uses no
converse from a flag to syscall-row existence. -/
theorem SP1PublicValues.committedDigest_eq_last_of_flag
    {first : SP1PublicValues (ZMod p)} {rest : List (SP1PublicValues (ZMod p))}
    {final : SP1PublicValues (ZMod p)}
    (last : (first :: rest).getLast? = some final)
    (continuous : LedgerContinuous (first :: rest))
    (transitions : ∀ publicValues ∈ first :: rest,
      publicValues.CommitTransitionValid)
    (committed : first.commit_syscall = 1) :
    first.committed_value_digest = final.committed_value_digest := by
  induction rest generalizing first with
  | nil =>
      simp at last
      subst final
      rfl
  | cons next tail ih =>
      obtain ⟨digest, -, -, -, -, -, -, -, -, flag, -, -⟩ := continuous.1
      have nextTransition := (transitions next (by simp)).publicCommit
      have nextPrev : next.prev_commit_syscall = 1 := by
        rw [← flag]
        exact committed
      calc
        first.committed_value_digest = next.prev_committed_value_digest := digest
        _ = next.committed_value_digest := nextTransition.committedStable nextPrev
        _ = final.committed_value_digest := by
          apply ih
          · simpa using last
          · exact continuous.2
          · intro publicValues member
            exact transitions publicValues (by simp [member])
          · exact nextTransition.monotone nextPrev

/-- Range and Boolean hygiene common to the full upstream public-input AIR.  Digest and septic-curve
relations are intentionally separate semantic integrity predicates; this definition only prevents
non-canonical limb/selector encodings. -/
def SP1PublicValues.WellFormed {p : ℕ} (layout : SP1PublicValuesLayout)
    (pv : SP1PublicValues (ZMod p)) : Prop :=
  (∀ word ∈ pv.prev_committed_value_digest.toList, word.WellFormed) ∧
  (∀ word ∈ pv.committed_value_digest.toList, word.WellFormed) ∧
  pv.pc_start.WellFormed ∧ pv.next_pc.WellFormed ∧
  pv.previous_init_addr.WellFormed ∧ pv.last_init_addr.WellFormed ∧
  pv.previous_finalize_addr.WellFormed ∧ pv.last_finalize_addr.WellFormed ∧
  pv.previous_init_page_idx.WellFormed ∧ pv.last_init_page_idx.WellFormed ∧
  pv.previous_finalize_page_idx.WellFormed ∧ pv.last_finalize_page_idx.WellFormed ∧
  pv.initial_timestamp.WellFormed ∧ pv.last_timestamp.WellFormed ∧
  FieldBool pv.is_execution_shard ∧ FieldBool pv.is_timestamp_high_eq ∧
  FieldBool pv.is_timestamp_low_eq ∧ FieldBool pv.prev_commit_syscall ∧
  FieldBool pv.commit_syscall ∧ FieldBool pv.prev_commit_deferred_syscall ∧
  FieldBool pv.commit_deferred_syscall ∧ FieldBool pv.is_first_execution_shard ∧
  FieldBool pv.is_untrusted_programs_enabled ∧ pv.ConformsLayout layout

/-- Project the execution-shard selector's canonical Boolean encoding from public-value hygiene. -/
theorem SP1PublicValues.executionShard_bool {p : ℕ} {layout : SP1PublicValuesLayout}
    {pv : SP1PublicValues (ZMod p)} (wellFormed : pv.WellFormed layout) :
    pv.is_execution_shard = 0 ∨ pv.is_execution_shard = 1 := by
  unfold SP1PublicValues.WellFormed FieldBool at wellFormed; tauto

/-- The shard's initial pc as a Sail-width bit-vector. -/
def SP1PublicValues.pcStartBits {p : ℕ} (pv : SP1PublicValues (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 pv.pc_start.toNat

/-- The shard's final/next pc as a Sail-width bit-vector. -/
def SP1PublicValues.nextPcBits {p : ℕ} (pv : SP1PublicValues (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 pv.next_pc.toNat

/-- The committed exit code as a Sail-width bit-vector. -/
def SP1PublicValues.exitCodeBits {p : ℕ} (pv : SP1PublicValues (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 pv.exit_code.val

/-- The native boundary's committed exit code as a Sail-width bit-vector — the same decode as
`SP1PublicValues.exitCodeBits`, on the prefix carrier. -/
def SP1StateBoundary.exitCodeBits {p : ℕ} (b : SP1StateBoundary (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 b.exit_code.val

end SP1Clean
