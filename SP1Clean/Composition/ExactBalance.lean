import SP1Clean.Composition.Balance

/-! # Exact AIR balance transported through the native access projection

`Transport/Balance.lean` converts the exact AIR's natural sent/received equality into a signed
integer sum for each exact `AirInteraction` payload.  Native bus arguments group the projected
`LookupAccess` list by `LookupKey`, so one further fact is load-bearing: the projection from an
exact payload to its native compatibility key must not identify two different payloads.

This module proves that fact for the complete pinned interaction vocabulary, including every raw
system-bus discriminator, and closes the projection step.  Under the already-explicit small-count
bound, exact `Balance.Valid` now yields native `LookupAccessList.isConsistentBalanced` for the
entire projected interaction list.  Byte is handled with its intentional global sign reversal;
the reversal changes a sum by `-1`, so it preserves zero.
-/

set_option autoImplicit false

namespace SP1Clean.Composition

open SP1Clean.CoreAIR.Current
open SP1Clean.Extracted (AirInteraction AirInteractionKind)
open SP1Clean.LookupAccessList

variable {p : ℕ} [Fact p.Prime]

/-- The exact payload's native compatibility key, with the interaction direction and multiplicity
removed.  This is exactly `keyOf (Interaction.toAccess i)`. -/
def exactPayloadKey : AirInteraction (ZMod p) → LookupKey
  | .byte opcode a b c =>
      (.Byte, "SP1Byte", [opcode.val, a.val, b.val, c.val])
  | .state a b c d e =>
      (.State, "SP1State", [a.val, b.val, c.val, d.val, e.val])
  | .memory a b c d e f g h i =>
      (.Memory, "SP1Memory",
        [a.val, b.val, c.val, d.val, e.val, f.val, g.val, h.val, i.val])
  | .program a b c op d e f g h i j k l m n o =>
      (.Program, "SP1Program",
        [a.val, b.val, c.val, op, d.val, e.val, f.val, g.val, h.val,
         i.val, j.val, k.val, l.val, m.val, n.val, o.val])
  | .raw kind values =>
      (.State, "SP1Raw/" ++ kind.lookupName, values.map ZMod.val)

/-- The stable raw-system table names preserve the complete exact interaction discriminator. -/
theorem exactKindName_injective :
    Function.Injective AirInteractionKind.lookupName := by
  intro left right h
  cases left <;> cases right <;>
    simp_all [AirInteractionKind.lookupName]

/-- Prefixing by the reserved raw-table marker retains discriminator injectivity. -/
theorem exactRawName_injective : Function.Injective
    (fun kind : AirInteractionKind => "SP1Raw/" ++ kind.lookupName) := by
  intro left right h
  cases left <;> cases right <;>
    simp_all [AirInteractionKind.lookupName]

private theorem exactRawName_ne_byte (kind : AirInteractionKind) :
    "SP1Raw/" ++ kind.lookupName ≠ "SP1Byte" := by
  cases kind <;> decide

private theorem exactRawName_ne_state (kind : AirInteractionKind) :
    "SP1Raw/" ++ kind.lookupName ≠ "SP1State" := by
  cases kind <;> decide

private theorem exactRawName_ne_memory (kind : AirInteractionKind) :
    "SP1Raw/" ++ kind.lookupName ≠ "SP1Memory" := by
  cases kind <;> decide

private theorem exactRawName_ne_program (kind : AirInteractionKind) :
    "SP1Raw/" ++ kind.lookupName ≠ "SP1Program" := by
  cases kind <;> decide

/-- The compatibility key is lossless on exact payloads.  In particular, raw system buses cannot
collide with one another or with the typed State bus, and `ZMod.val` loses no field information. -/
theorem exactPayloadKey_injective : Function.Injective (exactPayloadKey (p := p)) := by
  have valueListInjective :
      Function.Injective (List.map (ZMod.val : ZMod p → ℕ)) :=
    List.map_injective_iff.mpr (ZMod.val_injective p)
  intro left right h
  cases left <;> cases right <;>
    simp_all [exactPayloadKey, AirInteractionKind.lookupName,
      (ZMod.val_injective p).eq_iff, valueListInjective.eq_iff]
  · exact (exactRawName_ne_state _) h.1.symm
  · exact (exactRawName_ne_state _) h.1
  · exact exactKindName_injective h.1

omit [Fact p.Prime] in
/-- Projecting an interaction and then forgetting its multiplicity gives its payload key. -/
@[simp] theorem keyOf_exactInteraction_toAccess
    (interaction : SP1Clean.Extracted.Interaction (ZMod p)) :
    keyOf interaction.toAccess = exactPayloadKey interaction.payload := by
  rcases interaction with ⟨direction, payload, multiplicity⟩
  cases payload <;> rfl

/-- Byte is the one exact bus whose compatibility projection reverses polarity. -/
def payloadOrientation {F : Type} : AirInteraction F → ℤ
  | .byte _ _ _ _ => -1
  | _ => 1

/-- The projected integer multiplicity is the exact signed multiplicity, with the documented Byte
orientation applied. -/
theorem multOf_exactInteraction_toAccess (hp : 2 < p)
    (interaction : SP1Clean.Extracted.Interaction (ZMod p)) :
    multOf interaction.toAccess =
      payloadOrientation interaction.payload * signedMult interaction := by
  rcases interaction with ⟨direction, payload, multiplicity⟩
  cases payload <;>
    simp only [SP1Clean.Extracted.Interaction.toAccess, payloadOrientation, multOf, signedMult]
  · rw [SP1Clean.signedVal_neg hp]
    ring
  all_goals ring

/-- At the key of a chosen payload, the projected list's multiplicity sum is its exact signed sum,
up to the fixed Byte orientation. -/
theorem multiplicitySum_projected_at
    (all : List (SP1Clean.Extracted.Interaction (ZMod p))) (hp : 2 < p)
    (payload : AirInteraction (ZMod p)) :
    multiplicitySum (all.map SP1Clean.Extracted.Interaction.toAccess) (exactPayloadKey payload) =
      payloadOrientation payload * signedSum all payload := by
  induction all with
  | nil => simp only [List.map_nil, multiplicitySum_nil, signedSum_nil, mul_zero]
  | cons interaction rest ih =>
    rw [List.map_cons, multiplicitySum_cons, signedSum_cons, ih,
      keyOf_exactInteraction_toAccess,
      multOf_exactInteraction_toAccess hp interaction]
    by_cases samePayload : interaction.payload = payload
    · rw [samePayload]
      simp
      ring
    · have differentKey : exactPayloadKey interaction.payload ≠ exactPayloadKey payload :=
        fun keyEq => samePayload (exactPayloadKey_injective keyEq)
      simp [samePayload, differentKey]

/-- **Exact balance survives the complete native compatibility projection.**  The only additional
premise beyond exact `Balance.Valid` is the non-wrapping multiplicity bound already identified at
the cryptographic extraction boundary. -/
theorem projectedInteractions_balanced
    (all : List (SP1Clean.Extracted.Interaction (ZMod p))) (hp : 2 < p)
    (valid : Balance.Valid all) (small : SmallMultiplicities all) :
    isConsistentBalanced (all.map SP1Clean.Extracted.Interaction.toAccess) := by
  intro key
  by_cases observed : ∃ interaction ∈ all, exactPayloadKey interaction.payload = key
  · obtain ⟨interaction, -, keyEq⟩ := observed
    rw [← keyEq, multiplicitySum_projected_at all hp interaction.payload,
      signedSum_eq_zero all hp valid small interaction.payload]
    ring
  · have filtered :
        filterKey (all.map SP1Clean.Extracted.Interaction.toAccess) key = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro access accessMem accessKey
      obtain ⟨interaction, interactionMem, rfl⟩ := List.mem_map.mp accessMem
      apply observed
      exact ⟨interaction, interactionMem, by simpa using accessKey⟩
    simp [multiplicitySum, filtered]

/-- Zero-multiplicity padding may be discarded after projection without changing the transported
balance.  This is the exact shape consumed by the row/table access-permutation theorems. -/
theorem projectedActiveInteractions_balanced
    (all : List (SP1Clean.Extracted.Interaction (ZMod p))) (hp : 2 < p)
    (valid : Balance.Valid all) (small : SmallMultiplicities all) :
    isConsistentBalanced
      (active (all.map SP1Clean.Extracted.Interaction.toAccess)) := by
  intro key
  rw [multiplicitySum_active]
  exact projectedInteractions_balanced all hp valid small key

/-- A valid exact Core cluster exposes a balanced projected interaction ledger once its extractor
supplies the small-count bound.  This theorem is cluster-generic: execution and memory-boundary
witnesses both carry their own exact `allInteractions` balance. -/
theorem exactRelation_projectedInteractions_balanced {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    {cluster : CoreAIR.Cluster}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (valid : CoreAIR.Current.Relation binds cluster statement witness)
    (small : SmallMultiplicities
      (CoreAIR.Current.allInteractions statement.publicValues witness))
    (hp : 2 < p) :
    isConsistentBalanced
      ((CoreAIR.Current.allInteractions statement.publicValues witness).map
        SP1Clean.Extracted.Interaction.toAccess) := by
  have global := valid.2.2.2
  exact projectedInteractions_balanced _ hp global.2.2.2.2.1 small

/-- Active-list form of `exactRelation_projectedInteractions_balanced`. -/
theorem exactRelation_projectedActiveInteractions_balanced {Digest : Type}
    {binds : CoreAIR.Current.PreprocessedBinding p Digest}
    {cluster : CoreAIR.Cluster}
    (statement : SP1ShardStatement (ZMod p) Digest)
    (witness : CoreAIR.Witness (CoreAIR.Current.Row p))
    (valid : CoreAIR.Current.Relation binds cluster statement witness)
    (small : SmallMultiplicities
      (CoreAIR.Current.allInteractions statement.publicValues witness))
    (hp : 2 < p) :
    isConsistentBalanced
      (active ((CoreAIR.Current.allInteractions statement.publicValues witness).map
        SP1Clean.Extracted.Interaction.toAccess)) := by
  have global := valid.2.2.2
  exact projectedActiveInteractions_balanced _ hp global.2.2.2.2.1 small

end SP1Clean.Composition
