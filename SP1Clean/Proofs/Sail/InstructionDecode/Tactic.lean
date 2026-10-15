import SP1Clean.Model.Core.InstructionDecode
import SP1Clean.Model.SailDecode

/-! # Symbolic reduction of the pinned Sail instruction decoder

The generated decoder has a large ordered cascade. These tactics reduce only its current guard
or monadic scrutinee, keeping untaken continuations opaque. Bit-field guards use kernel-checked
arithmetic and propositional reasoning; configured CSR reads use the existing Sail lemmas.
No tactic executes the generated model through the native compiler.
-/

namespace SP1Clean.SailDecode.Symbolic

open LeanRV64D.Defs LeanRV64D.Functions Sail
open SP1Clean SP1Clean.Soundness.Target SP1Clean.SailDecode
open SP1Clean.Model.Core.InstructionDecode

private theorem run_guard_true {α : Type} (b : Bool) (yes no : SailM α) (s : SailState)
    (hb : b = true) : (if b then yes else no) s = yes s := by rw [hb]; rfl

private theorem run_guard_false {α : Type} (b : Bool) (yes no : SailM α) (s : SailState)
    (hb : b = false) : (if b then yes else no) s = no s := by rw [hb]; rfl

private theorem ntl_matches (v : BitVec 5) : encdec_ntl_backwards_matches v =
    (v.toNat == 2 || v.toNat == 3 || v.toNat == 4 || v.toNat == 5) := by
  unfold encdec_ntl_backwards_matches
  split <;> simp_all [BitVec.toNat_eq]

private theorem cbop_matches (v : BitVec 5) : encdec_cbop_zicbop_backwards_matches v =
    (v.toNat == 0 || v.toNat == 1 || v.toNat == 3) := by
  unfold encdec_cbop_zicbop_backwards_matches
  split <;> simp_all [BitVec.toNat_eq]

private theorem bool_matches (v : BitVec 1) : bool_bit_backwards_matches v = true := by
  have hv := v.isLt
  unfold bool_bit_backwards_matches
  split <;> simp_all [BitVec.toNat_eq]
  all_goals omega

private theorem width_matches (v : BitVec 2) : width_enc_backwards_matches v = true := by
  have hv := v.isLt
  unfold width_enc_backwards_matches
  split <;> simp_all [BitVec.toNat_eq]
  all_goals omega

private theorem ceCfi (s : SailState) (cfg : SailConfigured s) :
    currentlyEnabled extension.Ext_Zicfilp s = .ok false s := by
  have h := ceZicfilp_bind_apply s cfg.init cfg.priv cfg.mseccfg_disabled
    (fun b => pure b)
  have h' : currentlyEnabled extension.Ext_Zicfilp s = (pure false : SailM Bool) s := by
    simpa only [bind_pure] using h
  exact h'.trans rfl

private theorem run_match_congr {ε σ α β : Type} (r r' : EStateM.Result ε σ α)
    (k : α → σ → EStateM.Result ε σ β) (e : ε → σ → EStateM.Result ε σ β)
    (h : r = r') :
    (match (generalizing := false) r with | .ok a s => k a s | .error err s => e err s) =
    (match (generalizing := false) r' with | .ok a s => k a s | .error err s => e err s) := by rw [h]

private theorem run_result_step {ε σ α β : Type} (r : EStateM.Result ε σ α)
    (v : α) (k : α → σ → EStateM.Result ε σ β)
    (e : ε → σ → EStateM.Result ε σ β) (s : σ) (h : r = .ok v s) :
    (match (generalizing := false) r with | .ok a s' => k a s' | .error err s' => e err s') =
      k v s := by rw [h]

/-- Rewrite known whole bit fields before converting remaining guards to natural arithmetic.
That order keeps the generated encoding maps reducible at symbolic operand values. -/
macro "sail_decode_guard" : tactic => `(tactic| (
  simp_all only [SP1Clean.Model.Core.InstructionDecode.bits, Sail.BitVec.extractLsb,
    BitVec.extractLsb, BitVec.extractLsb']
  all_goals simp_all [bool_matches, width_matches, ntl_matches, cbop_matches,
    SP1Clean.Model.Core.InstructionDecode.reservedHint, LeanRV64D.Functions.base_E_enabled,
    LeanRV64D.Functions.not, encdec_reg_backwards_matches, encdec_uop_backwards_matches,
    encdec_iop_backwards_matches, encdec_bop_backwards_matches, Bool.and_eq_true,
    Bool.and_eq_false_iff, Bool.or_eq_true, Bool.or_eq_false_iff,
    beq_iff_eq, bne_iff_ne, BitVec.toNat_eq, SP1Clean.Model.Core.InstructionDecode.bits,
    Sail.BitVec.extractLsb, BitVec.extractLsb, BitVec.extractLsb'_toNat,
    BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow, Nat.reducePow, Nat.reduceSub,
    Nat.reduceAdd, Nat.div_one, Nat.mod_self, Nat.reduceMod]
  all_goals first | omega | tauto))

/-- Reduce one decoder guard or state-preserving monadic scrutinee at a time. The continuation
stays opaque until that step has a proof; no rewrite searches the untaken decoder suffix. -/
syntax "sail_decode_walk " term ", " term ", " term : tactic
macro_rules
| `(tactic| sail_decode_walk $s, $cfg, $inst) => `(tactic| (
  conv_lhs => whnf
  all_goals first
  | rfl
  | (refine (run_guard_false _ _ _ $s ?_).trans ?_
     · sail_decode_guard)
  | (refine (run_guard_true _ _ _ $s ?_).trans ?_
     · sail_decode_guard)
  | (refine (run_result_step _ true _ _ $s (cePause_apply $s)).trans ?_)
  | (refine (run_result_step _ false _ _ $s (ceCfi $s $cfg)).trans ?_)
  | (refine (run_result_step _ true _ _ $s (ceM_apply $s ($cfg).init ($cfg).misa_m)).trans ?_)
  | (refine (run_result_step _ true _ _ $s (ceZmmul_apply $s ($cfg).init ($cfg).misa_m)).trans ?_)
  | (refine (run_match_congr _ _ _ _
       (ceZicfilp_bind_apply $s ($cfg).init ($cfg).priv ($cfg).mseccfg_disabled _)).trans ?_)
  | (refine (run_result_step _ none _ _ $s ?_).trans ?_
     · sail_decode_walk $s, $cfg, $inst)
  | (refine (run_result_step _ (some $inst) _ _ $s ?_).trans ?_
     · sail_decode_walk $s, $cfg, $inst)
  | (refine (run_result_step _ ?value _ _ $s ?_).trans ?_
     rotate_left
     · simp_all only [SP1Clean.Model.Core.InstructionDecode.bits, Sail.BitVec.extractLsb,
         BitVec.extractLsb, BitVec.extractLsb']
       all_goals simp_all [LeanRV64D.Functions.base_E_enabled, LeanRV64D.Functions.not,
         encdec_uop_backwards_matches, encdec_reg_backwards_matches, encdec_uop_backwards,
         encdec_reg_backwards, encdec_iop_backwards,
         encdec_bop_backwards, Sail.BitVec.extractLsb, BitVec.extractLsb,
         LeanRV64D.Functions.regidx_bit_width, SP1Clean.Model.Core.InstructionDecode.bits,
         BitVec.extractLsb', BitVec.toNat_eq, pure, EStateM.pure]
       all_goals rfl)
  | (refine congrArg (fun value => EStateM.Result.ok value $s) ?_
     simp_all only [SP1Clean.Model.Core.InstructionDecode.bits, Sail.BitVec.extractLsb,
       BitVec.extractLsb, BitVec.extractLsb']
     all_goals simp_all [width_enc_backwards, bool_bit_backwards, Sail.BitVec.extractLsb,
       BitVec.extractLsb, LeanRV64D.Functions.regidx_bit_width,
       SP1Clean.Model.Core.InstructionDecode.bits, BitVec.extractLsb']
     all_goals and_intros
     all_goals first | rfl | apply BitVec.eq_of_toNat_eq
     all_goals simp only [BitVec.toNat, BitVec.ofNat, Fin.Internal.ofNat_eq_ofNat,
       Fin.ofNat, Nat.mod_mod])
  all_goals sail_decode_walk $s, $cfg, $inst
))

end SP1Clean.SailDecode.Symbolic
