import SP1Foundations
import SP1Operations

structure SP1Chip where
  /-- Set of constraints extracted from source code. -/
  constraint_set : Finset SP1Constraint
  /-- Proposition corresponding to constraints, see `constraints_sound` for correctness. -/
  constraint_prop : Prop
  /-- The expected computational behavior of the chip. -/
  compute_spec : Prop
  /-- The expected control flow effect of the chip. -/
  flow_spec : Prop
  /-- The expected memory effects of the chip. -/
  memory_spec : Prop

namespace SP1Chip

/-- TODO: Should this be an `iff`? Or should we allow the constraint set to be stronger than the prop? -/
def constraints_sound (chip : SP1Chip) : Prop :=
  constraintSet_toProp chip.constraint_set ↔ chip.constraint_prop

/-- Constraints are enough to imply computation is correct -/
def compute_correct (chip : SP1Chip) : Prop :=
  chip.constraint_prop → chip.compute_spec

/-- Constraints are enough to imply control flow is correct -/
def flow_correct (chip : SP1Chip) : Prop :=
  chip.constraint_prop → chip.flow_spec

/-- Constraints are enough to imply memort is correct -/
def memory_correct (chip : SP1Chip) : Prop :=
  chip.constraint_prop → chip.memory_spec

end SP1Chip
