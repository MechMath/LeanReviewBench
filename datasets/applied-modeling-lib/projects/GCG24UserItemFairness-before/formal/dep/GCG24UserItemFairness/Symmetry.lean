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

open EconCSLib

namespace GCG24UserItemFairness

abbrev UserType (K : ℕ) := Fin K

abbrev TypePolicy (K n : ℕ) := EconCSLib.Policy (UserType K) (Item n)

namespace RecommendationModel

/--
A recommendation model together with a user-type map for which equal types have
identical utility rows. This is the data needed to formalize the paper's `S_symm`.
-/
structure SymmetricData (m n K : ℕ) where
  model : RecommendationModel m n
  types : UserTypeAssignment m K
  agreeWithinTypes : UtilitiesAgreeWithinTypes model types

end RecommendationModel

namespace UserTypeAssignment

/-- Chosen representative user for each declared user type. -/
abbrev TypeRepresentatives {m K : ℕ}
    (τ : RecommendationModel.UserTypeAssignment m K) :=
  EconCSLib.Policy.FiberRepresentatives τ.toType

end UserTypeAssignment

namespace TypePolicy

/-- Variables of the reduced equality-form LP: one coordinate for every
type-item probability and one coordinate for the objective `ell`. -/
abbrev ReducedEqualityLPVariable (K n : ℕ) :=
  (UserType K × Item n) ⊕ Unit

/-- Constraints of the reduced equality-form LP.  The left summand contains
the `n` item-equalization equations and `K` row-sum equations; the right
summand contains the `nK` nonnegativity constraints. -/
abbrev ReducedEqualityLPConstraint (K n : ℕ) :=
  (Item n ⊕ UserType K) ⊕ (UserType K × Item n)

/-- A reduced LP candidate as a real vector, including the objective
coordinate. -/
noncomputable def reducedEqualityLPCandidate {K n : ℕ}
    (ρ : TypePolicy K n) (ell : ℝ) : ReducedEqualityLPVariable K n → ℝ
  | Sum.inl (k, j) => (ρ k j).toReal
  | Sum.inr _ => ell

/-- Coefficient vector of a constraint in a reduced equality-form LP.  Item
equation normals are supplied by the concrete utility model. -/
noncomputable def reducedEqualityLPConstraintNormal {K n : ℕ}
    (itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ) :
    ReducedEqualityLPConstraint K n →
      ReducedEqualityLPVariable K n → ℝ
  | Sum.inl (Sum.inl j), v => itemNormal j v
  | Sum.inl (Sum.inr k), Sum.inl (k', _j) => if k' = k then 1 else 0
  | Sum.inl (Sum.inr _k), Sum.inr _ => 0
  | Sum.inr (k, j), Sum.inl (k', j') => if k' = k ∧ j' = j then 1 else 0
  | Sum.inr (_k, _j), Sum.inr _ => 0

/-- A constraint is active at `(ρ, ell)` exactly in the source LP sense. -/
def ReducedEqualityLPConstraintActive {K n : ℕ}
    (itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ)
    (ρ : TypePolicy K n) (ell : ℝ) :
    ReducedEqualityLPConstraint K n → Prop
  | Sum.inl (Sum.inl j) =>
      (∑ v : ReducedEqualityLPVariable K n,
        itemNormal j v * reducedEqualityLPCandidate ρ ell v) = 0
  | Sum.inl (Sum.inr k) => (∑ j : Item n, (ρ k j).toReal) = 1
  | Sum.inr (k, j) => ρ k j = 0

/--
The standard active-basis definition of a basic feasible solution for the
paper's reduced equality-form LP.  In particular, the support bound is not a
field: it will be derived from the independent active basis below.
-/
structure ReducedEqualityLPActiveBasis {K n : ℕ}
    (itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ)
    (ρ : TypePolicy K n) (ell : ℝ) where
  equality_feasible :
    ∀ j : Item n,
      (∑ v : ReducedEqualityLPVariable K n,
        itemNormal j v * reducedEqualityLPCandidate ρ ell v) = 0
  basis : Finset (ReducedEqualityLPConstraint K n)
  basis_card : basis.card = n * K + 1
  basis_independent :
    LinearIndependent ℝ
      (fun c : {c // c ∈ basis} =>
        reducedEqualityLPConstraintNormal itemNormal c.1)
  basis_active :
    ∀ c ∈ basis, ReducedEqualityLPConstraintActive itemNormal ρ ell c

/-- A reduced policy is basic feasible when its equality-form LP constraints
contain a full active basis. -/
abbrev ReducedEqualityLPBasicFeasible {K n : ℕ}
    (itemNormal : Item n → ReducedEqualityLPVariable K n → ℝ)
    (ρ : TypePolicy K n) (ell : ℝ) : Prop :=
  Nonempty (ReducedEqualityLPActiveBasis itemNormal ρ ell)

namespace ReducedEqualityLPBasicFeasible

end ReducedEqualityLPBasicFeasible

end TypePolicy

end GCG24UserItemFairness
