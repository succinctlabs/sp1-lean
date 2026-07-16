import Clean.Utils.Tactics.ProvableStructDeriving

/-! # Public values on the formal-model audit surface

This file deliberately separates the small State boundary consumed by the current 25-chip ensemble
from SP1's real shard public-values record.  The latter mirrors
`sp1_hypercube::air::PublicValues<[F; 4], [F; 3], [F; 4], F>`; keeping the distinction in the type
names prevents a supported-core theorem from silently presenting itself as full SP1 AIR soundness. -/

namespace SP1Clean

/-- The two State-bus endpoints committed by the current Clean ensemble. -/
structure SP1StateBoundary (F : Type) where
  init_clk_high : F
  init_clk_low : F
  init_pc0 : F
  init_pc1 : F
  init_pc2 : F
  final_clk_high : F
  final_clk_low : F
  final_pc0 : F
  final_pc1 : F
  final_pc2 : F
deriving ProvableStruct

/-- Compatibility name used by the existing circuit layer. -/
abbrev SP1PublicIO := SP1StateBoundary

/-- Exact public-values type of the supported-core prefix theorem.  Naming the prefix explicitly
prevents callers from importing the terminal-only `exit_code` below into a statement that the current
Clean ensemble does not constrain. -/
abbrev SupportedCorePrefixPublicValues := SP1StateBoundary

/-- Legacy terminal-state scaffold: State endpoints plus an exit code.  The current Clean ensemble
only receives `toStateBoundary`, so this type must not be used by `supported_core_air_sound`.  It is
retained solely for the older target-execution theorem, whose separate halt premise constrains the
exit code. -/
structure SupportedCorePublicValues (F : Type) where
  init_clk_high : F
  init_clk_low : F
  init_pc0 : F
  init_pc1 : F
  init_pc2 : F
  final_clk_high : F
  final_clk_low : F
  final_pc0 : F
  final_pc1 : F
  final_pc2 : F
  exit_code : F
deriving ProvableStruct

/-- Forget the exit code and retain the State-bus boundary consumed by the current ensemble. -/
def SupportedCorePublicValues.toStateBoundary {F : Type} (pv : SupportedCorePublicValues F) :
    SP1StateBoundary F :=
  { init_clk_high := pv.init_clk_high
    init_clk_low := pv.init_clk_low
    init_pc0 := pv.init_pc0
    init_pc1 := pv.init_pc1
    init_pc2 := pv.init_pc2
    final_clk_high := pv.final_clk_high
    final_clk_low := pv.final_clk_low
    final_pc0 := pv.final_pc0
    final_pc1 := pv.final_pc1
    final_pc2 := pv.final_pc2 }

/-- Compatibility name for the legacy target-execution scaffold. -/
abbrev SP1TargetPublicIO := SupportedCorePublicValues

/-- Compatibility projection for the legacy target-execution scaffold. -/
abbrev SP1TargetPublicIO.toLegacy {F : Type} (pv : SP1TargetPublicIO F) : SP1PublicIO F :=
  pv.toStateBoundary

/-! ## The real SP1 shard public-values layout

The aliases below name the three Rust word representations directly.  They are semantic data types,
not yet a `ProvableType`: the full AIR will receive its own verifier/public-input circuit only when all
fields below are constrained and extraction-faithful. -/

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
the `Option` is a type-level rendering of the compile-time `mprotect` layout choice, not data a prover
may select independently of the verifier. -/
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

/-- Public input to the composed execution theorem.  A proof-system adapter may expose only the final
recursive public values, but its recursion theorem must recover this ordered shard ledger before the
AIR results can be composed. -/
structure SP1ExecutionStatement (F Digest : Type) where
  verifyingKey : SP1MachineVerifyingKey F Digest
  shards : List (SP1PublicValues F)

/-- View every entry in a composed ledger as a shard statement under the one machine verifying key. -/
def SP1ExecutionStatement.shardStatements {F Digest : Type}
    (statement : SP1ExecutionStatement F Digest) : List (SP1ShardStatement F Digest) :=
  statement.shards.map fun publicValues => ⟨statement.verifyingKey, publicValues⟩

/-- A field element used as a Boolean selector. -/
def FieldBool {p : ℕ} (value : ZMod p) : Prop := value = 0 ∨ value = 1

def SP1Word32.WellFormed {p : ℕ} (word : SP1Word32 (ZMod p)) : Prop :=
  ∀ value ∈ word.toList, value.val < 2 ^ 8

def SP1Word48.WellFormed {p : ℕ} (word : SP1Word48 (ZMod p)) : Prop :=
  ∀ value ∈ word.toList, value.val < 2 ^ 16

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

/-- The execution-coordinate continuity required between adjacent shard records.  Other recursive
accumulators (committed-value digests, deferred proofs, global memory, syscalls, and nonce integrity)
belong to the separate shard-integrity relation; naming this projection prevents them from being
mistaken for execution semantics. -/
def SP1PublicValues.ExecutionContinues (previous next : SP1PublicValues (ZMod p)) : Prop :=
  previous.next_pc = next.pc_start ∧
    previous.last_timestamp = next.initial_timestamp ∧
    previous.exit_code = next.prev_exit_code

/-- Pairwise execution-coordinate continuity of an ordered shard ledger. -/
def SP1PublicValues.ExecutionContinuous : List (SP1PublicValues (ZMod p)) → Prop
  | [] | [_] => True
  | previous :: next :: rest =>
      previous.ExecutionContinues next ∧ ExecutionContinuous (next :: rest)

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

/-- Decode an upstream three-limb pc/address as a natural number. -/
def SP1Word48.toNat {p : ℕ} (word : SP1Word48 (ZMod p)) : ℕ :=
  word[0].val + word[1].val * 2 ^ 16 + word[2].val * 2 ^ 32

/-- Decode an upstream timestamp using its `(16, 8, 8, 16)` big-endian limb weights. -/
def SP1Timestamp.toNat {p : ℕ} (timestamp : SP1Timestamp (ZMod p)) : ℕ :=
  timestamp[0].val * 2 ^ 32 + timestamp[1].val * 2 ^ 24 +
    timestamp[2].val * 2 ^ 16 + timestamp[3].val

/-- The shard's initial pc as a Sail-width bit-vector. -/
def SP1PublicValues.pcStartBits {p : ℕ} (pv : SP1PublicValues (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 pv.pc_start.toNat

/-- The shard's final/next pc as a Sail-width bit-vector. -/
def SP1PublicValues.nextPcBits {p : ℕ} (pv : SP1PublicValues (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 pv.next_pc.toNat

/-- The committed exit code as a Sail-width bit-vector. -/
def SP1PublicValues.exitCodeBits {p : ℕ} (pv : SP1PublicValues (ZMod p)) : BitVec 64 :=
  BitVec.ofNat 64 pv.exit_code.val

end SP1Clean
