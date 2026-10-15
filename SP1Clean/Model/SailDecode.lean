import SP1Clean.Model.SailWrap

/-! # Reducing the official Sail decoder `ext_decode` — the per-family decode witnesses

`try_step` decodes via `ext_decode = encdec_backwards` (`LeanRV64D/InstsEnd.lean`), a `noncomputable`
~395-arm nested cascade. The `decodedInROM` Program-channel contract demands, per committed row, the
∀-state fact `∀ s, SailConfigured s → (ext_decode w).run s = .ok I s`; nothing else in the tree
derives that fact, so its satisfiability needs a concrete witness per instruction family — the
external PR110 report's Finding 3 ("a mis-transcribed `instrToProgramRow` family would make the
capstone silently vacuous for its rows, with no test failing"). This file proves the decode half of
those witnesses: one `(ext_decode w).run s = .ok I s` reduction per supported instruction family,
against the real generated decoder, axiom-clean, at the default elaboration budget.

**The technique: a `whnf` cascade with per-read "unstick" rewrites.** The generated cascade is
`if`-headed per arm (the 4.32 do-elaborator's join-point rewrite), and every arm guard except a
handful is a pure bit test on the literal word — kernel-reducible. So `conv_lhs => whnf` drives the
whole pure prefix in one step, at native reduction speed, without ever traversing the untaken arms'
bodies (weak-head only). It parks exactly at the guards that consult machine state, each of which is
whnf-opaque for a *stated* reason:

* `currentlyEnabled` is **well-founded-recursive** (its extension graph is not structural on the
  flat `extension` enum), so even its config-constant arms never whnf-reduce — `cePause_apply`
  unsticks the PAUSE-arm head, whose value is the config constant `hartSupports Ext_Zihintpause`.
* the Zicfilp/forward-CFI cluster reads `cur_privilege` and `mseccfg.MLPE` — a genuine state read;
  `ceZicfilp_bind_apply` resolves it to `false` from the machine-mode and MLPE-off `SailConfigured`
  residues (the same fields `update_elp_state_of_isInitialized` consumes on the execute side).

After the unsticks, `whnf` runs through the remaining pure arms **into** the matching arm's body,
computing the register/immediate fields to literals, and the goal closes by `rfl`. The retired
2026-08 predecessor (`decode_ADD_example`) walked the cascade arm-by-arm with per-branch `simp`
discharges and needed an 8-million-heartbeat ceiling; this recipe closes each witness in ~200
heartbeats at the default budget and the default recursion depth.

**Hypothesis shape.** Witnesses are stated over the raw register facts (`isInitialized`, the
machine-mode `cur_privilege`, the `mseccfg` bit-10 pin) rather than `SailConfigured`, which lives
above this file; `Soundness/Decode.lean` instantiates them from a `SailConfigured` bundle when
assembling the per-family `decodedInROM` examples.

**Scope note (concrete is enough).** The decode reduction is only ever applied to *concrete*
instruction words: in the non-vacuity witnesses `RomLoaded` ties the fetched word to a concrete
`prog.rom` entry, so both the `decodedInROM` discharges and the step-lift's decode stage decode
concrete words. A *symbolic*-register `ext_decode_RTYPE` would need `bv_decide` per cascade branch,
which is costly and unnecessary for this scope, so it is deliberately not pursued; the general
`∀ prog` statement instead keeps `decodedInROM` a Program-channel contract discharged per row. -/

open LeanRV64D.Defs
namespace SP1Clean.SailDecode

open Sail Sail.ConcurrencyInterfaceV1 LeanRV64D LeanRV64D.Functions

set_option linter.unusedSimpArgs false

/-- Peel one **non-matching** decoder branch at a bind-headed node: if the guard block runs to
`.ok none s` (guard false, state-preserving), `match (← gb) with | some r => pure r | none => rest`
collapses to `rest`. Stated in `.run s` form so `rw`/`refine` apply it without descending into the
(untaken) rest of the cascade. The `whnf` cascade below supersedes it on the pure prefix; it remains
the tool for bind-headed read-guard arms a future deeper walk may meet. -/
theorem run_bind_ok_none {α β} (m : SailM (Option α)) (k : Option α → SailM β) (s : SailState)
    (h : EStateM.run m s = .ok none s) :
    EStateM.run (m >>= k) s = EStateM.run (k none) s := by
  simp only [bind, EStateM.bind, EStateM.run] at h ⊢; rw [h]

/-- Take the **matching** decoder branch at a bind-headed node: the guard block runs to
`.ok (some r) s`. -/
theorem run_bind_ok_some {α β} (m : SailM (Option α)) (k : Option α → SailM β) (s : SailState)
    (r : α) (h : EStateM.run m s = .ok (some r) s) :
    EStateM.run (m >>= k) s = EStateM.run (k (some r)) s := by
  simp only [bind, EStateM.bind, EStateM.run] at h ⊢; rw [h]

/-! ## The unstick rewrites — one per whnf-opaque guard head on the base-family walk -/

/-- The PAUSE-arm guard head: `currentlyEnabled Ext_Zihintpause` is the config constant
`hartSupports Ext_Zihintpause` (no state read), but `currentlyEnabled` is well-founded-recursive so
it never whnf-reduces; this equation lets the walk continue. Stated applied to `s` — the form the
whnf'd goal exposes. -/
theorem cePause_apply (s : SailState) :
    currentlyEnabled extension.Ext_Zihintpause s = EStateM.Result.ok true s := by
  simp [currentlyEnabled, hartSupports, pure, EStateM.pure]

/-- The Zicfilp/forward-CFI cluster head: under machine mode with `mseccfg.MLPE = 0` (bit 10, the
`SailConfigured.mseccfg_disabled` residue), `currentlyEnabled Ext_Zicfilp` resolves to `false` —
the LPAD arm is dead and the walk continues into the base-ISA arms. Mirrors the execute-side
`update_elp_state_of_isInitialized` (`Model/SailMemory.lean`). -/
theorem ceZicfilp_bind_apply {α : Type} (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1)
    (k : Bool → SailM α) :
    (currentlyEnabled extension.Ext_Zicfilp >>= k) s = k false s := by
  have hpriv' : s.regs.get Register.cur_privilege (hs _) = Privilege.Machine := by
    rwa [Std.ExtDHashMap.get?_eq_some_get (hs _), Option.some_inj] at hpriv
  have hmlpe : Sail.BitVec.extractLsb (s.regs.get Register.mseccfg (hs _)) 10 10 = 0#1 := by
    apply BitVec.eq_of_toNat_eq
    rw [Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat]
    have h2 := congrArg BitVec.toNat hseccfg
    simp only [BitVec.toNat_ofNat] at h2 ⊢
    omega
  show ((currentlyEnabled extension.Ext_Zicfilp >>= k) : SailM α).run s = (k false).run s
  simp only [currentlyEnabled, get_xLPE, hartSupports, _get_Seccfg_MLPE,
    bool_bit_backwards, pure_bind, bind_assoc,
    run_readReg_bind_of_isInitialized s _ hs, hpriv', hmlpe,
    Bool.true_and, Bool.and_false, Bool.false_and, if_false]
  rfl

/-! ## The base-family decode witnesses

One representative word per `instrToProgramRow` family whose arms live in the guard-free base
cluster of the cascade (arms 5–33). Every proof is the same six-line walk; only the word and the
decoded instruction differ. The M-extension families (MUL/MULW/DIV/DIVW/REM/REMW, arms 45–50)
additionally require the `misa.M` pin and their own unsticks — see the section below. -/

/-- The fixed RV64 `ECALL` word.  This decoder fact is used only negatively by the ordinary-shard
bridge: a successful supported Program-row projection cannot be this constructor. -/
theorem decode_ECALL (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x00000073#32).run s = .ok (instruction.ECALL ()) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf

/-- `ADD x1, x2, x3` (R-type). -/
theorem decode_ADD (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x003100B3#32).run s
      = .ok (instruction.RTYPE (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, rop.ADD))
          s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-- `ADDI x1, x2, 5` (I-type ALU). -/
theorem decode_ADDI (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x00510093#32).run s
      = .ok (instruction.ITYPE (5#12, regidx.Regidx 2#5, regidx.Regidx 1#5, iop.ADDI)) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-- `SLLI x1, x2, 3` (I-type shift). -/
theorem decode_SLLI (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x00311093#32).run s
      = .ok (instruction.SHIFTIOP (3#6, regidx.Regidx 2#5, regidx.Regidx 1#5, sop.SLLI)) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-- `ADDIW x1, x2, 5` (the W-form I-type). -/
theorem decode_ADDIW (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x0051009B#32).run s
      = .ok (instruction.ADDIW (5#12, regidx.Regidx 2#5, regidx.Regidx 1#5)) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-- `ADDW x1, x2, x3` (the W-form R-type). -/
theorem decode_ADDW (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x003100BB#32).run s
      = .ok (instruction.RTYPEW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5,
          ropw.ADDW)) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-- `SLLIW x1, x2, 3` (the W-form I-type shift). -/
theorem decode_SLLIW (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x0031109B#32).run s
      = .ok (instruction.SHIFTIWOP (3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, sopw.SLLIW)) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-- `LUI x1, 1` (U-type). -/
theorem decode_LUI (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x000010B7#32).run s
      = .ok (instruction.UTYPE (1#20, regidx.Regidx 1#5, uop.LUI)) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-- `JAL x1, 8` (J-type). -/
theorem decode_JAL (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x008000EF#32).run s
      = .ok (instruction.JAL (8#21, regidx.Regidx 1#5)) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-- `JALR x1, x2, 4`. -/
theorem decode_JALR (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x004100E7#32).run s
      = .ok (instruction.JALR (4#12, regidx.Regidx 2#5, regidx.Regidx 1#5)) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-- `BEQ x1, x2, 8` (B-type). -/
theorem decode_BEQ (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x00208463#32).run s
      = .ok (instruction.BTYPE (8#13, regidx.Regidx 2#5, regidx.Regidx 1#5, bop.BEQ)) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-- `LW x1, 0(x2)` (load; the LOAD arm covers all widths/signs via its parameters). -/
theorem decode_LW (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x00012083#32).run s
      = .ok (instruction.LOAD (0#12, regidx.Regidx 2#5, regidx.Regidx 1#5, false, 4)) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-- `SW x1, 0(x2)` (store; the STORE arm covers all widths via its parameter). -/
theorem decode_SW (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1) :
    (ext_decode 0x00112023#32).run s
      = .ok (instruction.STORE (0#12, regidx.Regidx 1#5, regidx.Regidx 2#5, 4)) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  rfl

/-! ## The M-extension family — the `misa.M` unsticks and witnesses

The MUL/DIV arms guard on `currentlyEnabled Ext_M` (directly, or through `Ext_Zmmul`, whose
`hartSupports` is `false` in this configuration so it reduces to the same `misa.M` test). The bit is
pinned by `SailConfigured.misa_m` — without it these witnesses would be unprovable and `decodedInROM`
unsatisfiable for every M-family row (the vacuity hazard the pin closes). The whnf walk parks at the
matching arm's own guard here (the reads sit inside the taken arm), so the take goes through
`run_match_step` — a generic peel of the `EStateM`-bind match at a state-preserving `.ok`. -/

/-- Peel an `EStateM` bind-match whose scrutinee runs to a state-preserving `.ok v s` — the applied
form `whnf` exposes. Generic; the decode walks feed it guard-block and `currentlyEnabled` values. -/
theorem run_match_step {ε σ α β : Type} (m : EStateM ε σ α) (v : α)
    (k : α → σ → EStateM.Result ε σ β) (e : ε → σ → EStateM.Result ε σ β)
    (s : σ) (h : m s = .ok v s) :
    (match m s with
      | EStateM.Result.ok a s' => k a s'
      | EStateM.Result.error err s' => e err s') = k v s := by rw [h]

/-- `currentlyEnabled Ext_M` is `true` under the `misa.M` pin (`hartSupports Ext_M` is a config
`true`; the guard is exactly the `misa.M` bit). -/
theorem ceM_apply (s : SailState) (hs : s.isInitialized)
    (hmisa : _get_Misa_M (s.regs.get Register.misa (hs Register.misa)) = 1#1) :
    currentlyEnabled extension.Ext_M s = EStateM.Result.ok true s := by
  show (currentlyEnabled extension.Ext_M).run s = .ok true s
  simp only [currentlyEnabled, hartSupports, pure_bind, bind_assoc,
    run_readReg_bind_of_isInitialized s _ hs, hmisa, Bool.true_and, beq_self_eq_true]
  rfl

/-- `currentlyEnabled Ext_Zmmul` reduces to `currentlyEnabled Ext_M` (`hartSupports Ext_Zmmul` is a
config `false`), hence `true` under the same pin. -/
theorem ceZmmul_apply (s : SailState) (hs : s.isInitialized)
    (hmisa : _get_Misa_M (s.regs.get Register.misa (hs Register.misa)) = 1#1) :
    currentlyEnabled extension.Ext_Zmmul s = EStateM.Result.ok true s := by
  show (currentlyEnabled extension.Ext_Zmmul).run s = .ok true s
  simp only [currentlyEnabled, hartSupports, pure_bind, bind_assoc,
    run_readReg_bind_of_isInitialized s _ hs, hmisa, Bool.true_and, Bool.false_or,
    beq_self_eq_true]
  rfl

/-- `MUL x1, x2, x3`. -/
theorem decode_MUL (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1)
    (hmisa : _get_Misa_M (s.regs.get Register.misa (hs Register.misa)) = 1#1) :
    (ext_decode 0x023100B3#32).run s
      = .ok (instruction.MUL (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5,
          { result_part := VectorHalf.Low, signed_rs1 := Signedness.Signed,
            signed_rs2 := Signedness.Signed })) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  refine (run_match_step _
      (some (instruction.MUL (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5,
        { result_part := VectorHalf.Low, signed_rs1 := Signedness.Signed,
          signed_rs2 := Signedness.Signed }))) _ _ s ?_).trans (by conv_lhs => whnf)
  · conv_lhs => whnf
    refine (run_match_step _ true _ _ s (ceM_apply s hs hmisa)).trans ?_
    conv_lhs => whnf
    refine (run_match_step _ true _ _ s (ceZmmul_apply s hs hmisa)).trans ?_
    rfl

/-- `MULW x1, x2, x3`. -/
theorem decode_MULW (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1)
    (hmisa : _get_Misa_M (s.regs.get Register.misa (hs Register.misa)) = 1#1) :
    (ext_decode 0x023100BB#32).run s
      = .ok (instruction.MULW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5)) s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  refine (run_match_step _
      (some (instruction.MULW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5)))
      _ _ s ?_).trans (by conv_lhs => whnf)
  · conv_lhs => whnf
    refine (run_match_step _ true _ _ s (ceM_apply s hs hmisa)).trans ?_
    conv_lhs => whnf
    refine (run_match_step _ true _ _ s (ceZmmul_apply s hs hmisa)).trans ?_
    rfl

/-- `DIV x1, x2, x3` (signed). -/
theorem decode_DIV (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1)
    (hmisa : _get_Misa_M (s.regs.get Register.misa (hs Register.misa)) = 1#1) :
    (ext_decode 0x023140B3#32).run s
      = .ok (instruction.DIV (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false))
          s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  refine (run_match_step _
      (some (instruction.DIV (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false)))
      _ _ s ?_).trans (by conv_lhs => whnf)
  · conv_lhs => whnf
    refine (run_match_step _ true _ _ s (ceM_apply s hs hmisa)).trans ?_
    rfl

/-- `REM x1, x2, x3` (signed). -/
theorem decode_REM (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1)
    (hmisa : _get_Misa_M (s.regs.get Register.misa (hs Register.misa)) = 1#1) :
    (ext_decode 0x023160B3#32).run s
      = .ok (instruction.REM (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false))
          s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  refine (run_match_step _
      (some (instruction.REM (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false)))
      _ _ s ?_).trans (by conv_lhs => whnf)
  · conv_lhs => whnf
    refine (run_match_step _ true _ _ s (ceM_apply s hs hmisa)).trans ?_
    rfl

/-- `DIVW x1, x2, x3` (signed). -/
theorem decode_DIVW (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1)
    (hmisa : _get_Misa_M (s.regs.get Register.misa (hs Register.misa)) = 1#1) :
    (ext_decode 0x023140BB#32).run s
      = .ok (instruction.DIVW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false))
          s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  refine (run_match_step _
      (some (instruction.DIVW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false)))
      _ _ s ?_).trans (by conv_lhs => whnf)
  · conv_lhs => whnf
    refine (run_match_step _ true _ _ s (ceM_apply s hs hmisa)).trans ?_
    rfl

/-- `REMW x1, x2, x3` (signed). -/
theorem decode_REMW (s : SailState) (hs : s.isInitialized)
    (hpriv : s.regs.get? Register.cur_privilege = some Privilege.Machine)
    (hseccfg :
      BitVec.ofNat 1 ((s.regs.get Register.mseccfg (hs Register.mseccfg)).toNat >>> 10) = 0#1)
    (hmisa : _get_Misa_M (s.regs.get Register.misa (hs Register.misa)) = 1#1) :
    (ext_decode 0x023160BB#32).run s
      = .ok (instruction.REMW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false))
          s := by
  conv_lhs => whnf
  rw [cePause_apply]
  conv_lhs => whnf
  rw [ceZicfilp_bind_apply s hs hpriv hseccfg]
  conv_lhs => whnf
  refine (run_match_step _
      (some (instruction.REMW (regidx.Regidx 3#5, regidx.Regidx 2#5, regidx.Regidx 1#5, false)))
      _ _ s ?_).trans (by conv_lhs => whnf)
  · conv_lhs => whnf
    refine (run_match_step _ true _ _ s (ceM_apply s hs hmisa)).trans ?_
    rfl

end SP1Clean.SailDecode
