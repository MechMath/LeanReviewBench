import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Real.Basic
import Mathlib.Logic.Equiv.Defs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

namespace FormalSLT.Rademacher.FiniteSample

open Finset

open scoped BigOperators

/-- Rademacher sign of a Boolean: `false ↦ -1`, `true ↦ +1`. -/
def signOfBool : Bool → ℝ
  | false => -1
  | true  => 1

variable {n : ℕ}

variable {ι Z : Type*} [Fintype ι] [Nonempty ι]

end FormalSLT.Rademacher.FiniteSample
