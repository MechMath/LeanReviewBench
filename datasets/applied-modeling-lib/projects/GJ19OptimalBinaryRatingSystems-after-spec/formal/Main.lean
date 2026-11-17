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
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
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
import Mathlib.Data.Set.Disjoint
import Mathlib.LinearAlgebra.AffineSpace.Ordered
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Indicator
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Measure.OpenPos
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.Finite
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Order.Interval.Set.Union
import Mathlib.Probability.CDF
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.StrongLaw
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
import dep.GJ19OptimalBinaryRatingSystems.AppendixB
import dep.GJ19OptimalBinaryRatingSystems.MainTheorems
import dep.GJ19OptimalBinaryRatingSystems.SourceDefinitions
import dep.GJ19OptimalBinaryRatingSystems.SourceTheorem31

namespace GJ19OptimalBinaryRatingSystems

namespace PaperInterface

open EconCSLib.Probability

open Filter

open Topology

open MeasureTheory



open scoped BigOperators

open scoped Function

open scoped ProbabilityTheory

noncomputable section

/-- Source-facing semantic target for `theorem31_source_matching_function_unique_value_argmax_lexicographic`. -/
def theorem31_source_matching_function_unique_value_argmax_lexicographicSpec
    (μ : Measure ℝ) [IsFiniteMeasure (μ.prod μ)]
    [Measure.IsOpenPosMeasure (μ.prod μ)]
    (S : Theorem31SourceFiniteDiscretizationWeightedModel μ)
    (limitingValue : (ℕ → ℝ) → ℝ)
    (rate : (ℕ → ℝ) → (Fin (S.m + 2) → ℝ) → ℝ)
    (hcut_value :
      EconCSLib.Optimization.IsMaximizerOn
        (monotoneIntervalCutpointsEndpointFeasible (S.m + 2))
        limitingValue S.cut)
    (hcut_value_unique :
      ∀ cut : ℕ → ℝ,
        monotoneIntervalCutpointsEndpointFeasible (S.m + 2) cut →
          limitingValue cut = limitingValue S.cut → cut = S.cut)
    (hrate_cut :
      ∀ levels : Fin (S.m + 2) → ℝ, BinaryEndpointLevelVector levels →
        rate S.cut levels =
          binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) : Prop :=
  ∃ levels : Fin (S.m + 2) → ℝ,
    ∃ hlevels : BinaryEndpointLevelVector levels,
      BinaryEndpointAwareAdjacentRatesEqualize levels S.sampleRate ∧
        ExponentialRateCertificate
          (theorem31SourceWbar μ S.cut S.hcut_mono S.sampleRate levels
            hlevels S.weight)
          (binaryEndpointAwareAdjacentRateObjective levels S.sampleRate) ∧
        EconCSLib.Optimization.IsLexicographicMaximizerOn
          (fun design : (ℕ → ℝ) × (Fin (S.m + 2) → ℝ) =>
            monotoneIntervalCutpointsEndpointFeasible (S.m + 2) design.1 ∧
              BinaryEndpointLevelVector design.2)
          (fun design : (ℕ → ℝ) × (Fin (S.m + 2) → ℝ) =>
            limitingValue design.1)
          (fun design : (ℕ → ℝ) × (Fin (S.m + 2) → ℝ) =>
            rate design.1 design.2)
          (S.cut, levels)

end

end PaperInterface

end GJ19OptimalBinaryRatingSystems
