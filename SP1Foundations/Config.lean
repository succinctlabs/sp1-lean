import SP1Foundations.Field

/-- dt: this is a hack to semi-resemble eventual goals for the code.
should be a more general initial config setup for the lemmas with register initialization etc. -/

opaque public_value : Unit → ℕ → Fin KB := fun _ => 0

@[simp] axiom mprotect_disabled : public_value () 151 = 0
