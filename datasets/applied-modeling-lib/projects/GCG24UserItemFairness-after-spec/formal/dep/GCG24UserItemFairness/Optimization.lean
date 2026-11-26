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
import dep.EconCSLib.Applications.RecommenderSystems.Policy
import dep.EconCSLib.Foundations.Math.FiniteOptimization
import dep.EconCSLib.Foundations.Probability.FiniteExpectation
import dep.GCG24UserItemFairness.Basic

open scoped BigOperators

open EconCSLib

namespace GCG24UserItemFairness

/-- The set of recommendation-model values in which the estimated and true utilities differ. -/
structure EstimatedRecommendationModel (m n : ℕ) where
  trueModel : RecommendationModel m n
  estimatedUtility : User m → Item n → ℝ

namespace EstimatedRecommendationModel

end EstimatedRecommendationModel

namespace RecommendationModel

/-- Attainable minimum item-fairness values. -/
def attainableItemFairnessSet {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) : Set ℝ :=
  {r | ∃ ρ : Policy m n, r = itemFairness W ρ}

/-- `I^*_min(w)` in the paper. -/
noncomputable def optimalItemFairness {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) : ℝ :=
  sSup (attainableItemFairnessSet W)

/-- Feasibility for the paper's `γ`-constrained problem. -/
def feasibleAtLevel {m n : ℕ} [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) (ρ : Policy m n) : Prop :=
  γ * optimalItemFairness W ≤ itemFairness W ρ

/-- Attainable minimum user-fairness values subject to the item constraint. -/
def attainableUserFairnessAtLevel {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : Set ℝ :=
  {r | ∃ ρ : Policy m n, feasibleAtLevel W γ ρ ∧ r = userFairness W ρ}

/-- `U^*_min(γ, w)` in the paper. -/
noncomputable def optimalUserFairnessAtLevel {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : ℝ :=
  sSup (attainableUserFairnessAtLevel W γ)

/-- The paper's price of fairness, generalized to an arbitrary `γ`. -/
noncomputable def priceOfFairnessAt {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) (γ : ℝ) : ℝ :=
  let base := optimalUserFairnessAtLevel W 0
  if h : base = 0 then 0 else (base - optimalUserFairnessAtLevel W γ) / base

/-- The price of maximal item fairness on user fairness. -/
noncomputable def priceOfFairness {m n : ℕ} [NeZero m] [NeZero n]
    (W : RecommendationModel m n) : ℝ :=
  priceOfFairnessAt W 1

/-- The two comparison forms needed for a finite linear description of `S`. -/
inductive PolicyLinearComparison where
  | eq
  | le
deriving DecidableEq

/-- A coefficient-level linear expression in the real policy coordinates. -/
noncomputable def policyLinearExpression {m n : ℕ}
    (a : User m → Item n → ℝ) (ρ : Policy m n) : ℝ :=
  ∑ u : User m, ∑ j : Item n, a u j * (ρ u j).toReal

/-- Satisfaction of one equality or weak-inequality policy constraint. -/
def policyLinearConstraintHolds {m n : ℕ}
    (a : User m → Item n → ℝ) (b : ℝ) (rel : PolicyLinearComparison)
    (ρ : Policy m n) : Prop :=
  match rel with
  | .eq => policyLinearExpression a ρ = b
  | .le => policyLinearExpression a ρ ≤ b

/-- A source condition-(i) witness: membership in `S` is exactly satisfaction
of a finite, explicitly coefficient-level family of linear constraints. -/
structure FiniteLinearPolicySetDescription {m n : ℕ}
    (S : Set (Policy m n)) where
  ConstraintIndex : Type
  constraintFintype : Fintype ConstraintIndex
  coefficient : ConstraintIndex → User m → Item n → ℝ
  rhs : ConstraintIndex → ℝ
  comparison : ConstraintIndex → PolicyLinearComparison
  mem_iff :
    ∀ ρ : Policy m n,
      ρ ∈ S ↔
        ∀ c : ConstraintIndex,
          policyLinearConstraintHolds (coefficient c) (rhs c) (comparison c) ρ

namespace FiniteLinearPolicySetDescription

end FiniteLinearPolicySetDescription

end RecommendationModel

namespace EstimatedRecommendationModel

end EstimatedRecommendationModel

end GCG24UserItemFairness
