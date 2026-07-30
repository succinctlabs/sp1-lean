import SP1Clean.Extracted.ExtractionDSL
import SP1Clean.Model.InteractionProjection
import SP1Clean.Model.ByteTable

/-! # Syntactic projection of the EXTRACTED interaction ADT to `LookupAccess`

The extracted-side counterpart of `AbstractInteraction.toAccess` (`Model/InteractionProjection.lean`).
The extracted `Interaction (ZMod p)` (the SP1-oracle bus vocabulary, `Extracted/ExtractionDSL.lean`)
projected to the **same** `LookupAccess` tuple `(kind, table, argvals, signedmult)` that the Clean
circuit's emitted interactions project to. Equality of the two `.map toAccess` lists is the *syntactic*
faithfulness bridge: it compares the channel, the message arg **values**, and the **signed
multiplicity/direction** — not byte semantics (unlike `Interaction.toProp`, which collapses every
non-byte interaction to `True` and reasons about `op.constrain`/`< 65536`).

## Sign convention (the one modeling gap the syntactic comparison surfaces)

Clean models the byte lookup as a **pull** — `byteChannel.pullIf is_real` → `pullIf`, with
multiplicity `-is_real` on `byteChannel.toRaw` (`Operations/AddOperation/Extracted.lean`). SP1's
`send_byte` is the dual **source** endpoint (`Extracted/AddOperation.lean`: `⟨.send, .byte 6 v 16 0,
is_real⟩`). Same physical lookup, opposite source/sink convention — so the `.byte` arm records the
**sink** sign `signedVal (-mult)`, matching Clean's pull, while the message tuple
`[opcode.val, a.val, b.val, c.val]` preserves Rust's raw field-valued opcode. The dynamic buses
(State/Memory/Program) use the natural `Dir.sign`
(`pushIf` send `+mult`, receive `-mult`) — byte is the sole *pull* bus
(`Model/Channels.lean` `byteChannel` docstring), hence its hardcoded `-mult`. -/

namespace SP1Clean.Extracted

open SP1Clean

variable {p : ℕ}

/-- The signed multiplicity of an extracted interaction by direction. Local and global sends are
positive; local and global receives are negative, matching the upstream interaction polarity. -/
def Dir.sign (d : Dir) (mult : ZMod p) : ZMod p :=
  match d with
  | .send | .sendGlobal => mult
  | .receive | .receiveGlobal => -mult

/-- Stable names for the exact upstream bus discriminator when it passes through the older
four-bus `LookupAccess` compatibility projection. The full Core relation does not use this
encoding: it compares `AirInteractionKind` and `AirInteraction.raw` directly. -/
def AirInteractionKind.lookupName : AirInteractionKind → String
  | .memory => "memory"
  | .program => "program"
  | .byte => "byte"
  | .state => "state"
  | .syscall => "syscall"
  | .global => "global"
  | .shaExtend => "sha-extend"
  | .shaCompress => "sha-compress"
  | .keccak => "keccak"
  | .globalAccumulation => "global-accumulation"
  | .memoryGlobalInitControl => "memory-global-init-control"
  | .memoryGlobalFinalizeControl => "memory-global-finalize-control"
  | .instructionFetch => "instruction-fetch"
  | .instructionDecode => "instruction-decode"
  | .pageProt => "page-prot"
  | .pageProtAccess => "page-prot-access"
  | .pageProtGlobalInitControl => "page-prot-global-init-control"
  | .pageProtGlobalFinalizeControl => "page-prot-global-finalize-control"

/-- Project one extracted interaction to its legacy `LookupAccess` compatibility representation.
The `.byte` arm uses the sink sign `signedVal (-mult)` (Clean's pull convention); the dynamic buses
use `Dir.sign`.

`LookupAccess` predates the full Core AIR and has only four coarse kinds. A raw system bus therefore
uses a reserved `"SP1Raw/<kind>"` table name (which preserves its exact discriminator and cannot
collide with `SP1State`) and the `.State` compatibility bucket. This arm only makes the legacy
projection total; `CoreAIR.Current.Balance.Valid` compares the exact raw payload ADT and never passes
through this encoding. -/
def Interaction.toAccess (intr : Interaction (ZMod p)) : LookupAccess :=
  match intr.payload with
  | .byte opcode a b c =>
      (InteractionKind.Byte, "SP1Byte",
        [opcode.val, a.val, b.val, c.val], signedVal (- intr.mult))
  | .state a b c d e =>
      (InteractionKind.State, "SP1State",
        [a.val, b.val, c.val, d.val, e.val], signedVal (intr.dir.sign intr.mult))
  | .memory a b c d e f g h i =>
      (InteractionKind.Memory, "SP1Memory",
        [a.val, b.val, c.val, d.val, e.val, f.val, g.val, h.val, i.val],
        signedVal (intr.dir.sign intr.mult))
  | .program a b c op d e f g h i j k l m n o =>
      (InteractionKind.Program, "SP1Program",
        [a.val, b.val, c.val, op, d.val, e.val, f.val, g.val, h.val,
         i.val, j.val, k.val, l.val, m.val, n.val, o.val],
        signedVal (intr.dir.sign intr.mult))
  | .raw kind values =>
      (InteractionKind.State, "SP1Raw/" ++ kind.lookupName, values.map ZMod.val,
        signedVal (intr.dir.sign intr.mult))

/-- The `.byte` arm of `Interaction.toAccess` as a `rfl`-`simp` lemma (independent of the `Dir`, which
the byte arm ignores — it records the sink sign `-mult`). Drives the syntactic faithfulness proofs. -/
@[simp] lemma Interaction.toAccess_byte (opcode a b c mult : ZMod p) (d : Dir) :
    (⟨d, .byte opcode a b c, mult⟩ : Interaction (ZMod p)).toAccess
      = (InteractionKind.Byte, "SP1Byte",
        [opcode.val, a.val, b.val, c.val], signedVal (-mult)) :=
  rfl

end SP1Clean.Extracted
