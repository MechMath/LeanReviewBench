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
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Order.Compact
import dep.EconCSLib.Applications.RecommenderSystems.Classwise
import dep.EconCSLib.Applications.RecommenderSystems.Policy
import dep.EconCSLib.Foundations.Math.FiniteOptimization
import dep.EconCSLib.Foundations.Probability.FiniteExpectation
import dep.GCG24UserItemFairness.Basic
import dep.GCG24UserItemFairness.Optimization
import dep.GCG24UserItemFairness.Symmetry

open scoped BigOperators

open EconCSLib

namespace GCG24UserItemFairness

namespace RecommendationModel

/--
The source-shaped user-coordinate equality LP from Proposition 1, specialized
to the symmetric policy set `S_symm` used in Proposition 2.  The variables are
the original user-item policy coordinates together with the objective coordinate
`ell`; type-level coordinates are not part of this object.
-/
structure UserSymmetricEqualityLP (m n K : ℕ) where
  model : RecommendationModel m n
  types : UserTypeAssignment m K

namespace UserSymmetricEqualityLP

end UserSymmetricEqualityLP

end RecommendationModel

namespace RecommendationModel.UserTypeAssignment

/-- The cardinality of a user type, viewed as the size of its fiber. -/
def typeCard {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (k : UserType K) : ℕ :=
  (Finset.univ.filter fun u => τ.toType u = k).card

/-- The same multiplicity, but as a real weight for the reduced LP. -/
noncomputable def typeWeight {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) (k : UserType K) : ℝ :=
  (typeCard τ k : ℝ)

end RecommendationModel.UserTypeAssignment

/--
A type-weighted reduction of the recommendation problem. This is the natural LP-side
object once users with identical utility rows have been merged into types.
-/
structure TypeWeightedRecommendationModel (K n : ℕ) where
  utility : UserType K → Item n → ℝ
  weight : UserType K → ℝ

namespace TypeWeightedRecommendationModel

end TypeWeightedRecommendationModel

/--
A witness connecting the original user-level model with a chosen type-level reduction.
The equality clauses are intentionally exact, so Codex can later prove preservation of
utilities, fairness functionals, and feasible regions by rewriting.
-/
structure ReductionWitness (m n K : ℕ) where
  data : RecommendationModel.SymmetricData m n K
  reduced : TypeWeightedRecommendationModel K n
  utility_agrees : ∀ u j,
    data.model.utility u j = reduced.utility (data.types.toType u) j
  weight_eq_typeWeight : ∀ k,
    reduced.weight k = RecommendationModel.UserTypeAssignment.typeWeight data.types k

/-- The canonical type-level reduction constructed from the source symmetric
data, rather than supplied as an additional theorem premise. -/
noncomputable def RecommendationModel.SymmetricData.canonicalReduction
    {m n K : ℕ}
    (S : RecommendationModel.SymmetricData m n K)
    (reps : UserTypeAssignment.TypeRepresentatives S.types) :
    ReductionWitness m n K where
  data := S
  reduced := {
    utility := fun k j => S.model.utility (reps.repr k) j
    weight := UserTypeAssignment.typeWeight S.types
  }
  utility_agrees := sorry
  weight_eq_typeWeight := sorry

/--
Construct the canonical reduction from the source-level condition that every
declared user type is represented by at least one user. Representatives are
chosen internally and are not an additional paper-facing certificate.
-/
noncomputable def RecommendationModel.SymmetricData.canonicalReductionOfSurjective
    {m n K : ℕ}
    (S : RecommendationModel.SymmetricData m n K)
    (hTypes : Function.Surjective S.types.toType) :
    ReductionWitness m n K :=
  S.canonicalReduction
    (EconCSLib.Policy.FiberRepresentatives.ofSurjective hTypes)

namespace ReductionWitness

end ReductionWitness

end GCG24UserItemFairness
