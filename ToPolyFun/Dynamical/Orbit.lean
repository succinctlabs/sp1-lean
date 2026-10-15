module

public import PolyFun.PFunctor.Dynamical.Run

/-! # Composition of finite orbits

## Gap against upstream

PolyFun's `DynSystem.ReachableIn` comes with `refl`, `step`, and `reachableIn_zero_iff` but no
composition or decomposition: two consecutive orbits cannot be joined into one, an orbit cannot be
cut, and the length of an orbit's event trace is not recorded. These are the lemmas a
shard-composition argument needs, stated on a bare `DynSystem` in PolyFun's own namespace so they
can be contributed as they are. -/

@[expose] public section

namespace PFunctor.DynSystem

universe u uA uB w

variable {S : Type u} {p : PFunctor.{uA, uB}} {s : DynSystem S p}

/-- Join an orbit with an orbit starting at its last state. -/
def Prefix.append : {st : S} → {m : ℕ} → (pre : Prefix s st m) → {n : ℕ} →
    Prefix s pre.last n → Prefix s st (n + m)
  | _, _, .nil, _, post => post
  | _, _, .step d tail, _, post => .step d (tail.append post)

@[simp] theorem Prefix.append_nil {st : S} {n : ℕ} (post : Prefix s st n) :
    (Prefix.nil (s := s) (st := st)).append post = post := rfl

@[simp] theorem Prefix.append_step {st : S} {m n : ℕ} (d : p.B (s.expose st))
    (tail : Prefix s (s.update st d) m) (post : Prefix s (Prefix.step d tail).last n) :
    (Prefix.step d tail).append post = .step d (tail.append post) := rfl

theorem Prefix.last_append {st : S} {m n : ℕ} (pre : Prefix s st m) (post : Prefix s pre.last n) :
    (pre.append post).last = post.last := by
  induction pre with
  | nil => rfl
  | step d tail ih => exact ih post

theorem Prefix.events_append {Event : Type w} (eventMap : s.EventMap Event) {st : S} {m n : ℕ}
    (pre : Prefix s st m) (post : Prefix s pre.last n) :
    (pre.append post).events eventMap = pre.events eventMap ++ post.events eventMap := by
  induction pre with
  | nil => rfl
  | step d tail ih => simpa using ih post

/-- An orbit's event trace has the orbit's length. -/
theorem Prefix.length_events {Event : Type w} (eventMap : s.EventMap Event) {st : S} {n : ℕ}
    (pre : Prefix s st n) : (pre.events eventMap).length = n := by
  induction pre with
  | nil => rfl
  | step _ _ ih => exact congrArg Nat.succ ih

/-- Reachability composes, with the second orbit's length first (the definitional order). -/
theorem ReachableIn.add' {m n : ℕ} {st mid st' : S} (first : s.ReachableIn m st mid)
    (second : s.ReachableIn n mid st') : s.ReachableIn (n + m) st st' := by
  obtain ⟨pre, rfl⟩ := first
  obtain ⟨post, rfl⟩ := second
  exact ⟨pre.append post, pre.last_append post⟩

/-- Reachability composes. -/
theorem ReachableIn.add {m n : ℕ} {st mid st' : S} (first : s.ReachableIn m st mid)
    (second : s.ReachableIn n mid st') : s.ReachableIn (m + n) st st' :=
  Nat.add_comm n m ▸ first.add' second

/-- An orbit of length `n + m` cuts after its first `m` steps. -/
theorem ReachableIn.split : ∀ {m : ℕ} {st : S} {n : ℕ} {st' : S},
    s.ReachableIn (n + m) st st' → ∃ mid, s.ReachableIn m st mid ∧ s.ReachableIn n mid st'
  | 0, st, _, _, h => ⟨st, ReachableIn.refl s st, h⟩
  | m + 1, _, _, _, ⟨.step d tail, hlast⟩ =>
      let ⟨mid, hm, hn⟩ := ReachableIn.split (m := m) ⟨tail, hlast⟩
      ⟨mid, ReachableIn.step d hm, hn⟩

end PFunctor.DynSystem
