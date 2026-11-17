import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.List.GetD
import Mathlib.Data.List.Sort
import Mathlib.Data.Real.Basic
import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.MeasureTheory.Measure.Support
import Mathlib.Order.Interval.Set.LinearOrder
import Mathlib.Probability.CDF
import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Tactic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Order.ProjIcc
import dep.AppliedModelingLib.Foundations.Math.Asymptotics

open Filter Topology MeasureTheory

open scoped BigOperators ProbabilityTheory

namespace AppliedModelingLib

namespace Probability

noncomputable section

/--
Top-`k` sum from bottom-indexed expected order-statistic means.  The rank
argument is one-based: rank `a` is the largest item in an `a`-sample.
-/
def orderStatisticTopKSumFromMean
    (μ : ℕ → ℕ → ℝ) (k a : ℕ) : ℝ :=
  ∑ i ∈ Finset.range (min k a), μ (a - i) a

/--
Oracle for the expected value of the best `k` consumed items among `q` sampled
items of a type/category.
-/
structure TopKExpectationOracle (τ : Type*) where
  expectedTopSum : ℕ → τ → ℕ → ℝ

namespace TopKExpectationOracle

variable {τ : Type*}

/-- Marginal expected top-`k` value from adding one more sampled item. -/
def marginalTopK (O : TopKExpectationOracle τ)
    (k : ℕ) (t : τ) (q : ℕ) : ℝ :=
  O.expectedTopSum k t (q + 1) - O.expectedTopSum k t q

/--
Certificate that all finite type-specific top-`k` marginals share a common
asymptotic scale, up to a positive type weight:

`marginal(k,t,q) / (scale q * weight t) -> 1`.

This is the probability-facing object that bounded, exponential, Pareto, or
finite-discrete order-statistic calculations should produce before the
optimization layer consumes marginal comparisons.
-/
structure ScaledMarginalLimitCertificate [Fintype τ]
    (O : TopKExpectationOracle τ) (k : ℕ)
    (scale : ℕ → ℝ) (weight : τ → ℝ) where
  scale_pos_eventually : ∀ᶠ q in atTop, 0 < scale q
  weight_pos : ∀ t, 0 < weight t
  marginal_ratio_tendsto :
    ∀ t,
      Tendsto
        (fun q => O.marginalTopK k t q / (scale q * weight t))
        atTop (nhds 1)

namespace ScaledMarginalLimitCertificate

variable [Fintype τ]

variable {k : ℕ}

variable {scale : ℕ → ℝ} {weight : τ → ℝ}

end ScaledMarginalLimitCertificate

end TopKExpectationOracle

/--
Distribution-neutral source certificate for fixed-`k` order-statistic marginal
asymptotics.  Bounded, Pareto, exponential, and finite-discrete sources can keep
family-specific scale definitions while delegating the finite-sum and top-k
oracle packaging to this structure.
-/
structure OrderStatisticScaledMarginalCertificate
    (μ : ℕ → ℕ → ℝ) (k : ℕ)
    (scale : ℕ → ℝ) (limitCoeff : ℝ) : Prop where
  k_pos : 0 < k
  coeff_pos : 0 < limitCoeff
  scale_pos_eventually : ∀ᶠ q in atTop, 0 < scale q
  marginal_ratio_tendsto :
    Tendsto
      (fun q : ℕ =>
        (orderStatisticTopKSumFromMean μ k (q + 1) -
            orderStatisticTopKSumFromMean μ k q) /
          (scale q * limitCoeff))
      atTop (nhds 1)

namespace OrderStatisticScaledMarginalCertificate

variable {μ : ℕ → ℕ → ℝ} {k : ℕ}

variable {scale : ℕ → ℝ} {limitCoeff : ℝ}

end OrderStatisticScaledMarginalCertificate

end

end Probability

end AppliedModelingLib
