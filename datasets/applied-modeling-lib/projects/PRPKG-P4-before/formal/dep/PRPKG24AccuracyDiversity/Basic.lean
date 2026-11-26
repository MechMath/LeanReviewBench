import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.Compact
import dep.AppliedModelingLib.Applications.RecommenderSystems.Allocation
import dep.AppliedModelingLib.Foundations.Probability.PMFKernel

open scoped BigOperators

open AppliedModelingLib

namespace PRPKG24AccuracyDiversity

/-- Item types in the recommendation-diversity model. -/
abbrev ItemType (T : ℕ) := Fin T

/-- A count allocation: how many recommended items are drawn from each type. -/
abbrev CountAllocation (T : ℕ) := AppliedModelingLib.Allocation (ItemType T)

/--
Generic finite abstraction of the paper's consumption-constrained objective.

`likelihood t` is the probability that the user prefers type `t`.
`valueOfCount t q` is the expected user value from recommending `q` items of type `t`,
conditional on the user preferring type `t`.

The paper's equation (3) has exactly this form:
`∑_t likelihood t * valueOfCount t (count t)`.
-/
structure ConsumptionModel (T : ℕ) where
  likelihood : ItemType T → ℝ
  valueOfCount : ItemType T → ℕ → ℝ

namespace ConsumptionModel

/-- The finite count-objective induced by a consumption model. -/
noncomputable def objective {T : ℕ}
    (M : ConsumptionModel T) (a : CountAllocation T) : ℝ := AppliedModelingLib.Allocation.objective a M.likelihood M.valueOfCount

/-- `a` is feasible for a slate/recommendation set of size `N`. -/
def FeasibleAtTotal {T : ℕ} (N : ℕ) (a : CountAllocation T) : Prop := AppliedModelingLib.Allocation.HasTotal a N

/-- `a` maximizes the consumption-constrained objective among allocations of size `N`. -/
def IsOptimalAtTotal {T : ℕ}
    (M : ConsumptionModel T) (N : ℕ) (a : CountAllocation T) : Prop :=
  FeasibleAtTotal N a ∧
    ∀ b : CountAllocation T, FeasibleAtTotal N b → M.objective b ≤ M.objective a

/-- Marginal gain from adding one more item of type `t` after already recommending `q`. -/
noncomputable def marginalValue {T : ℕ}
    (M : ConsumptionModel T) (t : ItemType T) (q : ℕ) : ℝ := AppliedModelingLib.Allocation.marginal M.valueOfCount t q

end ConsumptionModel

end PRPKG24AccuracyDiversity
