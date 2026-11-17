import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Convex.StdSimplex
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import dep.EconCSLib.Applications.RecommenderSystems.Classwise
import dep.EconCSLib.Applications.RecommenderSystems.Policy
import dep.EconCSLib.Foundations.Math.FiniteOptimization
import dep.EconCSLib.Foundations.Probability.FiniteExpectation
import dep.GCG24UserItemFairness.Basic
import dep.GCG24UserItemFairness.LPReduction
import dep.GCG24UserItemFairness.Optimization
import dep.GCG24UserItemFairness.Symmetry

namespace GCG24UserItemFairness

namespace OpposingTypes

/-- The opposite item index `n - j + 1` in zero-based `Fin n` notation. -/
def reverseItem {n : ℕ} (j : Item n) : Item n :=
  ⟨n - 1 - j.val, sorry⟩

/-- Values are strictly decreasing in the item index, matching `v₁ > ... > vₙ`. -/
def StrictlyDecreasingByIndex {n : ℕ} (v : Item n → ℝ) : Prop :=
  ∀ ⦃i j : Item n⦄, i.val < j.val → v j < v i

/--
The reduced two-type model for the opposing-preference setting in Theorem 3.
Type `0` has values `v_j`; type `1` has reversed values `v_{n-j+1}`.
-/
noncomputable def twoTypeReducedModel {n : ℕ}
    (alpha : ℝ) (v : Item n → ℝ) :
    TypeWeightedRecommendationModel 2 n where
  utility := fun k j => if k = 0 then v j else v (reverseItem j)
  weight := fun k => if k = 0 then alpha else 1 - alpha

end OpposingTypes

end GCG24UserItemFairness
