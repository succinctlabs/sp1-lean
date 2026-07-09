import SP1Clean.Model.SailWrap

/-! # Reducing the official Sail decoder `ext_decode` — the W3-A / W7 decode foundation

`try_step` decodes via `ext_decode = encdec_backwards` (`LeanRV64D/InstsEnd.lean`), a `noncomputable`
~280-branch nested `match`/`if` cascade. Both the W3 decode-bound discharge (`decodedInROM`, the
committed Program-bus columns are the decode of the guest ROM) and the W7 step-lift's decode stage need
to reduce `(ext_decode w).run s` to the concrete instruction for a given encoded word `w`.

**Why brute force fails.** `simp [encdec_backwards]` explodes (bottom-up: it normalizes under every
monadic bind's lambda — with the bind variable still symbolic — before any guard can prune the untaken
branch, so all ~280 float-op arms are simplified). `rfl`/`with_unfolding_all rfl` get stuck (they don't
apply the `@[simp_sail]` rewrite for `Sail.BitVec.extractLsb`, and hit the
`sys_enable_experimental_extensions` axiom).

**The technique that works — a lazy branch-skip walk in `.run s` form** (`rw` does not descend into
untaken branches). `run_bind_ok_none`/`run_bind_ok_some` peel one cascade branch each; the
`refine (run_bind_ok_none _ _ _ ?_).trans ?_` form exposes the "guard runs to `none`" obligation as a
real tactic goal (NOT an embedded `by`, which Lean's error recovery would *sorry* — making the `repeat`
walk past the matching arm), so a failing discharge throws and `repeat` stops cleanly at the matching
branch. Each branch's discharge is a *small* `simp` (one guard block), so no explosion.

**State requirement.** Almost every branch is pure, but the Zicfilp/forward-CFI branch reads
`cur_privilege` then `get_xLPE` (privilege-dependent CSRs). Its guard is false for a base-ISA encoding,
but the monadic *computation* still reads those CSRs, so the reduction needs `s.isInitialized` (CSRs
present) **and** `cur_privilege = Machine` (so the `match cur_privilege` resolves) — i.e. exactly the
`SailConfigured` "machine mode" residue. `decode_ADD_example` below proves the reduction for a concrete
ADD against the real decoder, axiom-clean modulo the Sail model's own axioms.

**Scope note (concrete is enough).** The decode reduction is only ever applied to *concrete* instruction
words: in the non-vacuity witness (a concrete `GuestProgram`), `RomLoaded` ties the fetched word to a
concrete `prog.rom` entry, so both the W3 `decodedInROM` discharge and the W7 decode stage decode
concrete words — the `decode_ADD_example` recipe (re-run per opcode with the matching literal +
instruction) covers them. A *symbolic*-register `ext_decode_RTYPE` would need `bv_decide` per cascade
branch (the `decide := true` discharger cannot rule out a branch when the register fields are symbolic),
which is costly and unnecessary for this scope, so it is deliberately not pursued; the general `∀ prog`
statement instead keeps `decodedInROM` a trusted decode-chip assumption (cf. `ProgramRowSpec`). -/

open LeanRV64D.Defs
namespace SP1Clean.SailDecode

open Sail LeanRV64D LeanRV64D.Functions

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSimpArgs false

/-- Peel one **non-matching** decoder branch: if the guard block runs to `.ok none s` (guard false,
state-preserving), `match (← gb) with | some r => pure r | none => rest` collapses to `rest`. Stated in
`.run s` form so `rw`/`refine` apply it without descending into the (untaken) rest of the cascade. -/
theorem run_bind_ok_none {α β} (m : SailM (Option α)) (k : Option α → SailM β) (s : SailState)
    (h : EStateM.run m s = .ok none s) :
    EStateM.run (m >>= k) s = EStateM.run (k none) s := by
  simp only [bind, EStateM.bind, EStateM.run] at h ⊢; rw [h]

/-- Take the **matching** decoder branch: the guard block runs to `.ok (some r) s`. -/
theorem run_bind_ok_some {α β} (m : SailM (Option α)) (k : Option α → SailM β) (s : SailState)
    (r : α) (h : EStateM.run m s = .ok (some r) s) :
    EStateM.run (m >>= k) s = EStateM.run (k (some r)) s := by
  simp only [bind, EStateM.bind, EStateM.run] at h ⊢; rw [h]

/-- **Worked example / proof-of-technique: the official Sail decoder on a concrete ADD.**
`0x003100B3` = `ADD x1, x2, x3` (funct7=0, rs2=3, rs1=2, funct3=0, rd=1, opcode=0110011). Reduces the
real `noncomputable` `ext_decode` to `RTYPE (x3, x2, x1, ADD)` under the `SailConfigured` residue
(`isInitialized` + machine mode). This is the foundation the W3-A `decodedInROM` discharge and the W7
decode stage are built on (generalizing the encoding to symbolic register fields / other R-type funct
codes is the next step). -/
theorem decode_ADD_example (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine) :
    (ext_decode 0x003100B3#32).run s
      = .ok (instruction.RTYPE (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, rop.ADD)) s := by
  rw [ext_decode]
  unfold encdec_backwards
  repeat (refine (run_bind_ok_none _ _ _ ?_).trans ?_
          · -- discharge "this branch's guard runs to none"; HARD-fails at the matching arm
            simp (config := { decide := true }) [currentlyEnabled, hartSupports, simp_sail,
              bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
              get, getThe, MonadStateOf.get, MonadState.get, EStateM.get,
              get_xLPE, LeanRV64D.readReg, PreSail.readReg, bool_bit_backwards, hpriv,
              encdec_cbop_zicbop_backwards_matches, encdec_reg_backwards_matches,
              Std.ExtDHashMap.get?_eq_some_get (hs _), Bool.and_false, Bool.false_and, reduceCtorEq]
          dsimp only [])
  -- parked at the ADD arm: take it (explicit instruction so the discharge has no metavariable).
  rw [run_bind_ok_some _ _ _
      (instruction.RTYPE (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, rop.ADD)) (by
    simp (config := { decide := true }) [encdec_reg_backwards, encdec_reg_backwards_matches,
      simp_sail, bind, EStateM.bind, EStateM.run, pure, EStateM.pure,
      Functions.regidx_bit_width, reduceCtorEq])]
  rfl

end SP1Clean.SailDecode
