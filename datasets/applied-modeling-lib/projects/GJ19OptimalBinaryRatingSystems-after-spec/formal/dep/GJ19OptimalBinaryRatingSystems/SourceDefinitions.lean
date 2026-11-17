import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.DerivativeTest
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.MeanInequalities
import Mathlib.Analysis.Real.Cardinality
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Lattice.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Preimage
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Choose.Vandermonde
import Mathlib.Data.Prod.Lex
import Mathlib.Data.Real.Archimedean
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Data.Set.Basic
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Union
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Module.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Topology.MetricSpace.Pseudo.Real
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.UniformSpace.UniformConvergence
import dep.EconCSLib.Foundations.Math.FiniteOptimization
import dep.EconCSLib.Foundations.Optimization.Certificate
import dep.EconCSLib.Foundations.Probability.BinaryRatingLDP
import dep.EconCSLib.Foundations.Probability.FiniteExpectation
import dep.EconCSLib.Foundations.Probability.FiniteMeasurablePartition
import dep.EconCSLib.Foundations.Probability.FiniteProductMultinomialCounts
import dep.EconCSLib.Foundations.Probability.FiniteRankingEvents
import dep.EconCSLib.Foundations.Probability.FiniteRatingComparison
import dep.EconCSLib.Foundations.Probability.FiniteSupportMGF
import dep.EconCSLib.Foundations.Probability.IIDLargeDeviations
import dep.EconCSLib.Foundations.Probability.IndependentProduct
import dep.EconCSLib.Foundations.Probability.IntegralLargeDeviations
import dep.EconCSLib.Foundations.Probability.LargeDeviations
import dep.GJ19OptimalBinaryRatingSystems.MainTheorems

open scoped BigOperators ENNReal

namespace GJ19OptimalBinaryRatingSystems

noncomputable section

open MeasureTheory

/-- The source-normalized quality/rank domain: a unit mass continuum `[0,1]`. -/
def sourceQualityDomain : Set ℝ := Set.Icc (0 : ℝ) 1

/--
Source assumptions on the matching function: it is nondecreasing, bounded by
one, and bounded strictly away from zero on the quality domain.
-/
def SourceMatchingFunction (g : ℝ → ℝ) : Prop :=
  MonotoneOn g sourceQualityDomain ∧
    (∀ θ ∈ sourceQualityDomain, g θ ≤ 1) ∧
    ∃ c : ℝ, 0 < c ∧ ∀ θ ∈ sourceQualityDomain, c < g θ

/--
Theorem 3.1 cell sample rate `g_i`: the infimum of the source matching
function over the closed quality cell selected by adjacent cutpoints.
-/
noncomputable def sourceCellMatchingRate
    {m : ℕ} (cut : ℕ → ℝ) (g : ℝ → ℝ) (i : Fin (m + 2)) : ℝ :=
  sInf (g '' Set.Icc (cut i.val) (cut (i.val + 1)))

end

end GJ19OptimalBinaryRatingSystems
